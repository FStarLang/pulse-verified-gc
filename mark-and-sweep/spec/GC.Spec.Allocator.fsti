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
/// 6. Return (updated heap, new free pointer, allocated obj_addr)
///
/// Note: field zeroing (step 7 in original allocator.c) is specified
/// separately via zero_fields and can be composed with alloc_spec.

module GC.Spec.Allocator

open FStar.Seq

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
[@@"opaque_to_smt"]
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
        // rem_hd_nat < heap_size <= pow2 57, so rem_obj_nat < pow2 64
        FStar.Math.Lemmas.pow2_lt_compat 64 57;
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
          { heap_out = g'; fp_out = new_remainder_fp; obj_out = cur_fp }
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size && U64.v prev_fp % U64.v mword = 0 then
          let g2 = write_word g' (prev_fp <: hp_addr) new_remainder_fp in
          { heap_out = g2; fp_out = head_fp; obj_out = cur_fp }
        else
          { heap_out = g'; fp_out = new_remainder_fp; obj_out = cur_fp }
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

/// ---------------------------------------------------------------------------
/// Helper: the "next_fp" the spec computes for a valid block
/// ---------------------------------------------------------------------------

let spec_next_fp (g: heap) (obj: obj_addr) : GTot U64.t =
  let hd = hd_address obj in
  if U64.v hd + 16 <= heap_size then read_word g obj else 0UL

/// ---------------------------------------------------------------------------
/// Step lemmas for alloc_search (for loop correspondence proofs)
/// ---------------------------------------------------------------------------

/// When fuel = 0: OOM
val alloc_search_fuel_0 (g: heap) (head prev cur: U64.t) (wz: nat)
  : Lemma (alloc_search g head prev cur wz 0 ==
           { heap_out = g; fp_out = head; obj_out = 0UL })

/// When cur is invalid (not a valid obj_addr): OOM
val alloc_search_invalid (g: heap) (head prev cur: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    (cur = 0UL \/
                     U64.v cur < U64.v mword \/
                     U64.v cur >= heap_size \/
                     U64.v cur % U64.v mword <> 0))
          (ensures alloc_search g head prev cur wz fuel ==
                   { heap_out = g; fp_out = head; obj_out = 0UL })

/// When the block is too small: advance to next
val alloc_search_advance (g: heap) (head prev cur: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v cur >= U64.v mword /\
                    U64.v cur < heap_size /\
                    U64.v cur % U64.v mword = 0 /\
                    (let hdr = read_word g (hd_address (cur <: obj_addr)) in
                     U64.v (getWosize hdr) < wz))
          (ensures alloc_search g head prev cur wz fuel ==
                   alloc_search g head cur (spec_next_fp g (cur <: obj_addr)) wz (fuel - 1))

/// When the block fits and prev = 0 (head of list)
val alloc_search_found_head (g: heap) (head prev cur: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v cur >= U64.v mword /\
                    U64.v cur < heap_size /\
                    U64.v cur % U64.v mword = 0 /\
                    prev = 0UL /\
                    (let hdr = read_word g (hd_address (cur <: obj_addr)) in
                     U64.v (getWosize hdr) >= wz))
          (ensures (let obj : obj_addr = cur in
                    let next = spec_next_fp g obj in
                    let (g', new_fp) = alloc_from_block g obj wz next in
                    alloc_search g head prev cur wz fuel ==
                    { heap_out = g'; fp_out = new_fp; obj_out = cur }))

/// When the block fits and prev is a valid hp_addr
val alloc_search_found_prev (g: heap) (head prev cur: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v cur >= U64.v mword /\
                    U64.v cur < heap_size /\
                    U64.v cur % U64.v mword = 0 /\
                    prev <> 0UL /\
                    U64.v prev >= U64.v mword /\
                    U64.v prev < heap_size /\
                    U64.v prev % U64.v mword = 0 /\
                    (let hdr = read_word g (hd_address (cur <: obj_addr)) in
                     U64.v (getWosize hdr) >= wz))
          (ensures (let obj : obj_addr = cur in
                    let next = spec_next_fp g obj in
                    let (g', new_fp) = alloc_from_block g obj wz next in
                    let g2 = write_word g' (prev <: hp_addr) new_fp in
                    alloc_search g head prev cur wz fuel ==
                    { heap_out = g2; fp_out = head; obj_out = cur }))

/// For a valid obj_addr, spec_next_fp always reads the field (condition is always true)
val spec_next_fp_eq (g: heap) (obj: obj_addr)
  : Lemma (spec_next_fp g obj == read_word g obj)

/// ---------------------------------------------------------------------------
/// alloc_from_block unfolding lemmas (for Pulse proof)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 100"

/// Exact fit: leftover < 2
val alloc_from_block_exact (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma (requires (let hdr = read_word g (hd_address obj) in
                     let bwz = U64.v (getWosize hdr) in
                     bwz >= wz /\ bwz - wz < 2))
          (ensures (let hd = hd_address obj in
                    let hdr = read_word g hd in
                    let bwz = U64.v (getWosize hdr) in
                    let ahdr = make_header (U64.uint_to_t bwz) white_bits 0UL in
                    let g1 = write_word g hd ahdr in
                    alloc_from_block g obj wz next == (g1, next)))

/// Split, normal: all bounds pass
val alloc_from_block_split_normal (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma (requires (let hd = hd_address obj in
                     let hdr = read_word g hd in
                     let bwz = U64.v (getWosize hdr) in
                     bwz - wz >= 2 /\
                     U64.v hd + (1 + wz) * 8 < heap_size /\
                     U64.v hd + (1 + wz) * 8 + 8 < heap_size))
          (ensures (let hd = hd_address obj in
                    let hdr = read_word g hd in
                    let bwz = U64.v (getWosize hdr) in
                    let ahdr = make_header (U64.uint_to_t wz) white_bits 0UL in
                    let g1 = write_word g hd ahdr in
                    let rhn = U64.v hd + (1 + wz) * 8 in
                    let rh : hp_addr = U64.uint_to_t rhn in
                    let rw = bwz - wz - 1 in
                    let rhdr = make_header (U64.uint_to_t rw) blue_bits 0UL in
                    let g2 = write_word g1 rh rhdr in
                    let ron = rhn + 8 in
                    let ro : hp_addr = U64.uint_to_t ron in
                    let g3 = write_word g2 ro next in
                    alloc_from_block g obj wz next == (g3, ro)))

/// Split, rem_hd out of bounds
val alloc_from_block_split_rem_hd_oob (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma (requires (let hd = hd_address obj in
                     let hdr = read_word g hd in
                     let bwz = U64.v (getWosize hdr) in
                     bwz - wz >= 2 /\
                     U64.v hd + (1 + wz) * 8 >= heap_size))
          (ensures (let hd = hd_address obj in
                    let ahdr = make_header (U64.uint_to_t wz) white_bits 0UL in
                    let g1 = write_word g hd ahdr in
                    alloc_from_block g obj wz next == (g1, next)))

/// Split, rem_obj out of bounds (rem_hd ok but rem_obj >= heap_size)
val alloc_from_block_split_rem_obj_oob (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma (requires (let hd = hd_address obj in
                     let hdr = read_word g hd in
                     let bwz = U64.v (getWosize hdr) in
                     bwz - wz >= 2 /\
                     U64.v hd + (1 + wz) * 8 < heap_size /\
                     U64.v hd + (1 + wz) * 8 + 8 >= heap_size))
          (ensures (let hd = hd_address obj in
                    let ahdr = make_header (U64.uint_to_t wz) white_bits 0UL in
                    let g1 = write_word g hd ahdr in
                    let rhn = U64.v hd + (1 + wz) * 8 in
                    let rh : hp_addr = U64.uint_to_t rhn in
                    let hdr = read_word g hd in
                    let bwz = U64.v (getWosize hdr) in
                    let rw = bwz - wz - 1 in
                    let rhdr = make_header (U64.uint_to_t rw) blue_bits 0UL in
                    let g2 = write_word g1 rh rhdr in
                    let ron = rhn + 8 in
                    alloc_from_block g obj wz next == (g2, U64.uint_to_t ron)))

#pop-options

/// ---------------------------------------------------------------------------
/// Read-level bridge lemmas for alloc_from_block (split, normal case)
///
/// These provide read_word facts about the post-alloc heap WITHOUT exposing
/// the intermediate write_word chain to the caller. Z3 gets direct
/// read_word equalities instead of chaining through 3 write_words.
/// ---------------------------------------------------------------------------

/// Precondition for the normal split case (shared across all bridge lemmas below)
let alloc_split_normal_pre (g: heap) (obj: obj_addr) (wz: nat) =
  let hd = hd_address obj in
  let hdr = read_word g hd in
  let bwz = U64.v (getWosize hdr) in
  bwz - wz >= 2 /\
  U64.v hd + (1 + wz) * 8 < heap_size /\
  U64.v hd + (1 + wz) * 8 + 8 < heap_size

/// Result heap and fp for the normal split case
let alloc_split_normal_result (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t) : GTot (heap & U64.t) =
  alloc_from_block g obj wz next

/// Result heap shorthand
let alloc_split_normal_heap (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t) : GTot heap =
  fst (alloc_split_normal_result g obj wz next)

/// The result heap has the same length as the input heap
val alloc_split_normal_length (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma (requires alloc_split_normal_pre g obj wz)
          (ensures Seq.length (alloc_split_normal_heap g obj wz next) == Seq.length g)

/// Reading the alloc header: header at hd_address obj == make_header wz white 0
val alloc_split_normal_read_hd (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma (requires alloc_split_normal_pre g obj wz)
          (ensures (let g' = alloc_split_normal_heap g obj wz next in
                    let hd = hd_address obj in
                    read_word g' hd == make_header (U64.uint_to_t wz) white_bits 0UL))

/// Reading the remainder header: header at rem_hd == make_header rem_wz blue 0
val alloc_split_normal_read_rem_hd (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma (requires alloc_split_normal_pre g obj wz)
          (ensures (let g' = alloc_split_normal_heap g obj wz next in
                    let hd = hd_address obj in
                    let hdr = read_word g hd in
                    let bwz = U64.v (getWosize hdr) in
                    let rhn = U64.v hd + (1 + wz) * 8 in
                    let rh : hp_addr = U64.uint_to_t rhn in
                    let rw = bwz - wz - 1 in
                    read_word g' rh == make_header (U64.uint_to_t rw) blue_bits 0UL))

/// Reading the remainder field: read_word g' ro == next_fp
val alloc_split_normal_read_rem_field (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma (requires alloc_split_normal_pre g obj wz)
          (ensures (let g' = alloc_split_normal_heap g obj wz next in
                    let hd = hd_address obj in
                    let rhn = U64.v hd + (1 + wz) * 8 in
                    let ron = rhn + 8 in
                    let ro : hp_addr = U64.uint_to_t ron in
                    read_word g' ro == next))

/// Reading an unwritten address: result equals original
val alloc_split_normal_read_other (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t) (addr: hp_addr)
  : Lemma (requires alloc_split_normal_pre g obj wz /\
                    (let hd = hd_address obj in
                     let rhn = U64.v hd + (1 + wz) * 8 in
                     let ron = rhn + 8 in
                     // addr doesn't overlap any of the 3 written words
                     (U64.v addr + 8 <= U64.v hd \/ U64.v addr >= U64.v hd + 8) /\
                     (U64.v addr + 8 <= rhn \/ U64.v addr >= rhn + 8) /\
                     (U64.v addr + 8 <= ron \/ U64.v addr >= ron + 8)))
          (ensures (let g' = alloc_split_normal_heap g obj wz next in
                    read_word g' addr == read_word g addr))

/// ---------------------------------------------------------------------------
/// Read-level bridge lemmas for alloc_from_block (exact case)
/// ---------------------------------------------------------------------------

let alloc_exact_pre (g: heap) (obj: obj_addr) (wz: nat) =
  let hdr = read_word g (hd_address obj) in
  let bwz = U64.v (getWosize hdr) in
  bwz >= wz /\ bwz - wz < 2

let alloc_exact_heap (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t) : GTot heap =
  fst (alloc_from_block g obj wz next)

val alloc_exact_read_hd (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma (requires alloc_exact_pre g obj wz)
          (ensures (let g' = alloc_exact_heap g obj wz next in
                    let hd = hd_address obj in
                    let bwz = U64.v (getWosize (read_word g hd)) in
                    read_word g' hd == make_header (U64.uint_to_t bwz) white_bits 0UL))

val alloc_exact_read_other (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t) (addr: hp_addr)
  : Lemma (requires alloc_exact_pre g obj wz /\
                    (let hd = hd_address obj in
                     U64.v addr + 8 <= U64.v hd \/ U64.v addr >= U64.v hd + 8))
          (ensures (let g' = alloc_exact_heap g obj wz next in
                    read_word g' addr == read_word g addr))

val alloc_exact_length (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma (requires alloc_exact_pre g obj wz)
          (ensures Seq.length (alloc_exact_heap g obj wz next) == Seq.length g)
