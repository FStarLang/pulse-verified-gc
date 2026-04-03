/// ---------------------------------------------------------------------------
/// GC.Spec.Allocator - Pure specification of first-fit free-list allocation
/// ---------------------------------------------------------------------------
///
/// This module defines the pure specification for a first-fit free-list
/// allocator. The free list is threaded through dead objects' first fields
/// (1-based index: field 1 = first word after header), matching the sweep
/// phase's convention.
///
/// Algorithm (matches allocator.c):
/// 1. Walk the free list starting from fp
/// 2. For each blue (free) block, check if wosize >= requested
/// 3. If leftover >= 2: split — create remainder block
/// 4. If leftover < 2: use entire block (no split)
/// 5. Recolor allocated block's header to White, tag 0
/// 6. Zero all fields of allocated block
/// 7. Return (updated heap, new free pointer, allocated obj_addr)

module GC.Spec.Allocator

open FStar.Seq
open FStar.Mul

module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.HeapGraph

/// ---------------------------------------------------------------------------
/// Header Construction (pure, for spec use)
/// ---------------------------------------------------------------------------

/// Build a header word from wosize, color (as 2-bit value), and tag
let make_header (wz: U64.t{U64.v wz < pow2 54}) (color_bits: U64.t{U64.v color_bits < 4}) (tag: U64.t{U64.v tag < 256}) : U64.t =
  let wz_shifted = U64.shift_left wz 10ul in
  let c_shifted = U64.shift_left color_bits 8ul in
  U64.logor wz_shifted (U64.logor c_shifted tag)

/// White color bits = 0
let white_bits : U64.t = 0UL

/// Blue color bits = 2
let blue_bits : U64.t = 2UL

/// ---------------------------------------------------------------------------
/// Zero a range of fields in the heap (pure spec)
/// ---------------------------------------------------------------------------

/// Zero n words starting at byte address addr
let rec zero_fields (g: heap) (addr: U64.t) (n: nat)
  : GTot heap (decreases n)
  = if n = 0 then g
    else if U64.v addr + 8 > heap_size then g
    else if U64.v addr >= heap_size then g
    else if U64.v addr % 8 <> 0 then g
    else
      let g' = write_word g (addr <: hp_addr) 0UL in
      if U64.v addr + 8 >= pow2 64 then g'
      else
        zero_fields g' (U64.uint_to_t (U64.v addr + 8)) (n - 1)

/// ---------------------------------------------------------------------------
/// Allocation Result
/// ---------------------------------------------------------------------------

/// Result of an allocation attempt
type alloc_result = {
  heap_out : heap;         // Updated heap
  fp_out   : U64.t;        // New free-list head
  obj_out  : U64.t;        // Allocated object address, or 0UL if OOM
}

/// ---------------------------------------------------------------------------
/// Single-Block Allocation (split or exact fit)
/// ---------------------------------------------------------------------------

/// Allocate from a specific free block.
/// Pre: block at obj_addr is blue with wosize >= requested_wz
/// Returns updated heap, new fp for the unlinked portion, and the allocated obj_addr.
let alloc_from_block (g: heap) (obj: obj_addr) (requested_wz: nat) (next_fp: U64.t)
  : GTot (heap & U64.t)
  = let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let leftover = block_wz - requested_wz in
    if leftover >= 2 then begin
      // Split: allocated block gets requested_wz words
      let alloc_hdr = make_header (U64.uint_to_t requested_wz) white_bits 0UL in
      let g1 = write_word g hd alloc_hdr in
      // Remainder block starts after allocated block
      let rem_hd_nat = U64.v hd + (1 + requested_wz) * 8 in
      if rem_hd_nat >= heap_size || rem_hd_nat >= pow2 64 ||
         rem_hd_nat % 8 <> 0 then
        // Can't create remainder — shouldn't happen if block is well-formed
        (g1, next_fp)
      else
        let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
        let rem_wz = leftover - 1 in  // One word for remainder header
        let rem_hdr = make_header (U64.uint_to_t rem_wz) blue_bits 0UL in
        let g2 = write_word g1 rem_hd rem_hdr in
        // Remainder's first field links to rest of free list
        let rem_obj_nat = rem_hd_nat + 8 in
        if rem_obj_nat >= heap_size || rem_obj_nat >= pow2 64 ||
           rem_obj_nat % 8 <> 0 then
          (g2, U64.uint_to_t rem_obj_nat)
        else
          let rem_field : hp_addr = U64.uint_to_t rem_obj_nat in
          let g3 = write_word g2 rem_field next_fp in
          (g3, U64.uint_to_t rem_obj_nat)
    end
    else begin
      // Exact fit (or leftover = 1, use whole block)
      let alloc_hdr = make_header (U64.uint_to_t block_wz) white_bits 0UL in
      let g1 = write_word g hd alloc_hdr in
      (g1, next_fp)
    end

/// ---------------------------------------------------------------------------
/// Free-List Search (first-fit)
/// ---------------------------------------------------------------------------

/// Walk the free list looking for a block with wosize >= requested.
/// Returns: (updated heap, new free-list head, allocated obj or 0)
///
/// prev_fp: the address of the previous block's link field (or 0 for head)
/// cur_fp: current free-list node (obj_addr), or 0 = end of list
let rec alloc_search (g: heap) (head_fp: U64.t) (prev_fp: U64.t)
                     (cur_fp: U64.t) (requested_wz: nat) (fuel: nat)
  : GTot alloc_result (decreases fuel)
  = if fuel = 0 then { heap_out = g; fp_out = head_fp; obj_out = 0UL }
    else if cur_fp = 0UL then { heap_out = g; fp_out = head_fp; obj_out = 0UL }
    else if U64.v cur_fp < U64.v mword then { heap_out = g; fp_out = head_fp; obj_out = 0UL }
    else if U64.v cur_fp >= heap_size then { heap_out = g; fp_out = head_fp; obj_out = 0UL }
    else if U64.v cur_fp % U64.v mword <> 0 then { heap_out = g; fp_out = head_fp; obj_out = 0UL }
    else begin
      let obj : obj_addr = cur_fp in
      let hd = hd_address obj in
      let hdr = read_word g hd in
      let block_wz = U64.v (getWosize hdr) in
      // Read the link to next free block (field 1 = first word of object)
      let next_fp =
        if U64.v hd + 16 <= heap_size then
          read_word g obj  // obj = hd + 8, so read at obj gives field[0]
        else 0UL
      in
      if block_wz >= requested_wz then begin
        // Found a suitable block
        let (g', new_remainder_fp) = alloc_from_block g obj requested_wz next_fp in
        // Update the previous link to point to remainder (or next)
        if prev_fp = 0UL then
          // Updating head: new_remainder_fp becomes the head
          let g_zeroed = zero_fields g' obj requested_wz in
          { heap_out = g_zeroed; fp_out = new_remainder_fp; obj_out = cur_fp }
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size && U64.v prev_fp % U64.v mword = 0 then
          // Update previous block's link field
          let g2 = write_word g' (prev_fp <: hp_addr) new_remainder_fp in
          let g_zeroed = zero_fields g2 obj requested_wz in
          { heap_out = g_zeroed; fp_out = head_fp; obj_out = cur_fp }
        else
          // Invalid prev_fp — shouldn't happen
          let g_zeroed = zero_fields g' obj requested_wz in
          { heap_out = g_zeroed; fp_out = new_remainder_fp; obj_out = cur_fp }
      end
      else
        // Block too small, continue search
        alloc_search g head_fp cur_fp next_fp requested_wz (fuel - 1)
    end

/// ---------------------------------------------------------------------------
/// Top-Level Allocation
/// ---------------------------------------------------------------------------

/// Allocate an object of the given word size from the free list.
/// fp: current free-list head (obj_addr of first free block, or 0)
/// requested_wz: number of words needed (will be bumped to 1 if 0)
///
/// Returns alloc_result with:
///   - heap_out: updated heap
///   - fp_out: new free-list head
///   - obj_out: allocated object address (0UL = OOM)
let alloc_spec (g: heap) (fp: U64.t) (requested_wz: nat) : GTot alloc_result =
  let wz = if requested_wz = 0 then 1 else requested_wz in
  alloc_search g fp 0UL fp wz (heap_size / U64.v mword)

/// ---------------------------------------------------------------------------
/// Heap Initialization
/// ---------------------------------------------------------------------------

/// Initialize a zero heap as one big free block.
/// Returns (initialized heap, free pointer).
let init_heap_spec (g: heap) : GTot (heap & U64.t) =
  let total_words = heap_size / U64.v mword in
  if total_words < 2 then (g, 0UL)
  else
    let wz = total_words - 1 in
    // Header at offset 0: wosize=wz, color=blue(2), tag=0
    let hdr = make_header (U64.uint_to_t wz) blue_bits 0UL in
    let g1 = write_word g zero_addr hdr in
    // First field (at offset 8) = 0 (end of free list)
    let obj_addr_nat = U64.v mword in
    let g2 = write_word g1 (mword <: hp_addr) 0UL in
    (g2, mword)  // Free pointer = first object = offset 8
