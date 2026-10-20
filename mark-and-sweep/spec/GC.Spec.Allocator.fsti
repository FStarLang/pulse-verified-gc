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
/// Returns updated heap and the value that replaces `obj` in the free list.
///
/// The allocated block is RIGHT-JUSTIFIED inside the free block, as stock
/// OCaml's `nf_allocate_block` does (runtime/freelist.c): its header sits
/// `leftover` words above `hd`, so on a split the remainder keeps `hd`, keeps
/// its address, and keeps the link word already stored at `hd + 8`.  The free
/// list is therefore untouched by a split.
///
///   leftover = 0    exact fit: header at hd, block detached
///   leftover = 1    the spare word cannot carry a link, so it becomes an
///                   empty block (header only, wosize 0, blue, never linked)
///                   at hd, and the object starts at hd + 8; block detached
///   leftover >= 2   remainder at hd shrinks to `leftover - 1` and stays a
///                   blue, linked cell; object header at hd + leftover * 8
///
/// In every case the allocated block declares EXACTLY `requested_wz`, so
/// `wosize_of_object` of the result is `requested_wz` and never one more.
[@@"opaque_to_smt"]
let alloc_from_block (g: heap) (obj: obj_addr) (requested_wz: nat) (next_fp: U64.t)
  : GTot (heap & U64.t)
  = let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let leftover = block_wz - requested_wz in
    if leftover < 0 then
      // Defensive: the block is too small.  Callers (`alloc_search`) only
      // reach here with block_wz >= requested_wz, and every unfolding lemma
      // requires it, so this arm is unreachable.
      (g, next_fp)
    else
    let alloc_hd_nat = U64.v hd + leftover * 8 in
    if alloc_hd_nat >= heap_size || alloc_hd_nat >= pow2 64 ||
       alloc_hd_nat % 8 <> 0 then
      // Defensive: unreachable for a well-formed block, since
      // hd + (block_wz + 1) * 8 <= heap_size and leftover <= block_wz.
      (g, next_fp)
    else
      let alloc_hd : hp_addr = U64.uint_to_t alloc_hd_nat in
      // requested_wz <= block_wz < pow2 54, so the header is well-typed.
      let alloc_hdr = make_header (U64.uint_to_t requested_wz) white_bits 0UL in
      if leftover >= 1 then
        // A split and a one-word leftover write the SAME two words: the
        // remainder header at hd, of wosize `leftover - 1` -- which at
        // leftover = 1 is exactly the empty block, header only -- and the
        // object header right-justified above it.  They differ only in what
        // replaces `obj` in the free list: a split leaves the cell in place at
        // `obj`, keeping the link already at hd + 8, whereas a one-word
        // leftover has no body word to hold a link, so `fl_cell` (which
        // demands wosize >= 1) correctly excludes it and the whole block
        // leaves the list.  The next fused sweep absorbs it into an adjacent
        // run.
        let rem_hdr = make_header (U64.uint_to_t (leftover - 1)) blue_bits 0UL in
        let g1 = write_word g hd rem_hdr in
        let g2 = write_word g1 alloc_hd alloc_hdr in
        (g2, (if leftover >= 2 then (obj <: U64.t) else next_fp))
      else
        // Exact fit: alloc_hd = hd.  Detach the block.
        let g1 = write_word g hd alloc_hdr in
        (g1, next_fp)

/// The value that replaces `obj` in the free list, as a TRANSPARENT function.
///
/// This mirrors `snd (alloc_from_block ...)` exactly, but without the
/// `opaque_to_smt` attribute, so Z3 can evaluate it directly.  That matters
/// because `alloc_search` needs the replacement pointer in order to build the
/// heap it then passes BACK to `alloc_from_block`:
///
///     let gw = write_word g prev (alloc_replacement_fp g obj wz next_fp) in
///     let g2 = fst (alloc_from_block gw obj wz next_fp) in
///
/// Written with `snd (alloc_from_block g ...)` instead, that definition
/// contains two applications of an opaque function, one nested in the other's
/// argument, and every downstream query has to carry and relate both.  Using
/// the transparent mirror leaves exactly one.
let alloc_replacement_fp (g: heap) (obj: obj_addr) (requested_wz: nat) (next_fp: U64.t)
  : GTot U64.t
  = let hd = hd_address obj in
    let block_wz = U64.v (getWosize (read_word g hd)) in
    let leftover = block_wz - requested_wz in
    if leftover < 2 then next_fp
    else
      let alloc_hd_nat = U64.v hd + leftover * 8 in
      if alloc_hd_nat >= heap_size || alloc_hd_nat >= pow2 64 ||
         alloc_hd_nat % 8 <> 0 then next_fp
      else (obj <: U64.t)

/// The mirror is faithful.
val alloc_replacement_fp_eq (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (snd (alloc_from_block g obj wz next_fp) ==
           alloc_replacement_fp g obj wz next_fp)

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
    else if U64.v cur_fp < U64.v zero_addr + U64.v mword then { heap_out = g; fp_out = head_fp; obj_out = 0UL }
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
        // Found a suitable block.  The object is right-justified inside it, so
        // it starts `leftover` words above the block's own object address.
        let leftover = block_wz - requested_wz in
        let alloc_hd_nat = U64.v hd + leftover * 8 in
        // Strictly stronger than alloc_from_block's own guard: we need the
        // OBJECT address in bounds, not just its header, since obj_out carries
        // an hp_addr refinement.  Bailing here means alloc_from_block is only
        // ever called when its own guard also passes, so the two agree and its
        // defensive arm stays unreachable from the search.
        if alloc_hd_nat + 8 >= heap_size || alloc_hd_nat >= pow2 64 ||
           alloc_hd_nat % 8 <> 0 then
          { heap_out = g; fp_out = head_fp; obj_out = 0UL }
        else
        let alloc_obj = U64.add cur_fp (U64.uint_to_t (leftover * 8)) in
        // The replacement for `obj` in the free list is a pure projection, so
        // it can be read off WITHOUT applying the block writes.
        let new_remainder_fp = alloc_replacement_fp g obj requested_wz next_fp in
        // Order matters, and not for the heap -- the two writes are disjoint,
        // so the final state is the same either way.  It matters for the
        // PROOF.  Rewiring `prev` first means the link write happens while
        // `obj` is still a well-formed cell of wosize >= 1; doing it second
        // would require `fl_valid` to hold of an intermediate heap in which
        // `obj` has already become the wosize-0 empty block, which at
        // leftover = 1 is false.  Choosing the good order here is what avoids
        // needing a write_word commutation lemma.
        if prev_fp = 0UL then
          let g' = fst (alloc_from_block g obj requested_wz next_fp) in
          { heap_out = g'; fp_out = new_remainder_fp; obj_out = alloc_obj }
        // `prev_fp <> hd` rules out one degenerate shape: the predecessor's
        // OBJECT address being this block's HEADER word, which means the
        // predecessor has wosize 0.  `fl_valid` excludes that -- a cell keeps
        // its link in field 0, so it has wosize >= 1 -- but `alloc_search` is
        // total and assumes nothing, and letting it through would have the
        // link write clobber the header the block writes then read back.
        // Such a `prev` is treated exactly like an invalid one.
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 && U64.v prev_fp <> U64.v hd then
          let gw = write_word g (prev_fp <: hp_addr) new_remainder_fp in
          let g2 = fst (alloc_from_block gw obj requested_wz next_fp) in
          { heap_out = g2; fp_out = head_fp; obj_out = alloc_obj }
        else
          let g' = fst (alloc_from_block g obj requested_wz next_fp) in
          { heap_out = g'; fp_out = new_remainder_fp; obj_out = alloc_obj }
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
  alloc_search g fp 0UL fp wz heap_words

/// ---------------------------------------------------------------------------
/// Heap Initialization
/// ---------------------------------------------------------------------------

/// Initialize a zero heap as one big free block.
/// Returns (initialized heap, free pointer).
let init_heap_spec (g: heap) : GTot (heap & U64.t) =
  let total_words = heap_words in
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
                    (U64.v cur < U64.v zero_addr + U64.v mword \/
                     U64.v cur >= heap_size \/
                     U64.v cur % U64.v mword <> 0))
          (ensures alloc_search g head prev cur wz fuel ==
                   { heap_out = g; fp_out = head; obj_out = 0UL })

/// When the block is too small: advance to next
val alloc_search_advance (g: heap) (head prev cur: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v cur >= U64.v zero_addr + U64.v mword /\
                    U64.v cur < heap_size /\
                    U64.v cur % U64.v mword = 0 /\
                    (let hdr = read_word g (hd_address (cur <: obj_addr)) in
                     U64.v (getWosize hdr) < wz))
          (ensures alloc_search g head prev cur wz fuel ==
                   alloc_search g head cur (spec_next_fp g (cur <: obj_addr)) wz (fuel - 1))

/// When the block fits and prev = 0 (head of list)
val alloc_search_found_head (g: heap) (head prev cur: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v cur >= U64.v zero_addr + U64.v mword /\
                    U64.v cur < heap_size /\
                    U64.v cur % U64.v mword = 0 /\
                    (let hd = hd_address (cur <: obj_addr) in
                     let bwz = U64.v (getWosize (read_word g hd)) in
                     // `prev` is not usable as a predecessor: either there is
                     // none, or it is out of range / misaligned, or it is the
                     // degenerate wosize-0 shape.  All three take the same
                     // arm -- allocate, and report the block's replacement as
                     // the new head.
                     (prev = 0UL \/
                      U64.v prev < U64.v mword \/ U64.v prev >= heap_size \/
                      U64.v prev % U64.v mword <> 0 \/ U64.v prev = U64.v hd) /\
                     bwz >= wz /\
                     // the right-justified object must be in bounds, matching
                     // the guard in alloc_search
                     U64.v hd + (bwz - wz) * 8 + 8 < heap_size))
          (ensures (let obj : obj_addr = cur in
                    let next = spec_next_fp g obj in
                    let g' = fst (alloc_from_block g obj wz next) in
                    // stated via the transparent mirror, matching the definition
                    let new_fp = alloc_replacement_fp g obj wz next in
                    let leftover = U64.v (getWosize (read_word g (hd_address obj))) - wz in
                    let alloc_obj = U64.add cur (U64.uint_to_t (leftover * 8)) in
                    alloc_search g head prev cur wz fuel ==
                    { heap_out = g'; fp_out = new_fp; obj_out = alloc_obj }))

/// When the block fits and prev is a valid hp_addr
val alloc_search_found_prev (g: heap) (head prev cur: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v cur >= U64.v zero_addr + U64.v mword /\
                    U64.v cur < heap_size /\
                    U64.v cur % U64.v mword = 0 /\
                    prev <> 0UL /\
                    U64.v prev >= U64.v mword /\
                    U64.v prev < heap_size /\
                    U64.v prev % U64.v mword = 0 /\
                    (let hd = hd_address (cur <: obj_addr) in
                     let bwz = U64.v (getWosize (read_word g hd)) in
                     // see the note on the degenerate shape in `alloc_search`
                     U64.v prev <> U64.v hd /\
                     bwz >= wz /\
                     U64.v hd + (bwz - wz) * 8 + 8 < heap_size))
          (ensures (let obj : obj_addr = cur in
                    let next = spec_next_fp g obj in
                    // The prev-link rewrite comes FIRST, on `g`, where `obj` is
                    // still a well-formed cell.  See the note in alloc_search.
                    let new_fp = alloc_replacement_fp g obj wz next in
                    let gw = write_word g (prev <: hp_addr) new_fp in
                    let g2 = fst (alloc_from_block gw obj wz next) in
                    let leftover = U64.v (getWosize (read_word g (hd_address obj))) - wz in
                    let alloc_obj = U64.add cur (U64.uint_to_t (leftover * 8)) in
                    alloc_search g head prev cur wz fuel ==
                    { heap_out = g2; fp_out = head; obj_out = alloc_obj }))

/// The block fits, but the right-justified object header (or the word after
/// it) would fall outside the heap, so the search bails with OOM and leaves
/// the heap untouched.  Unreachable for a well-formed block once `wz >= 1`,
/// since then `hd + (bwz - wz + 1) * 8 <= hd + bwz * 8 < heap_size`; the
/// implementation still needs the arm because the loop invariant does not
/// carry well-formedness of the current cell.
val alloc_search_found_oob (g: heap) (head prev cur: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v cur >= U64.v zero_addr + U64.v mword /\
                    U64.v cur < heap_size /\
                    U64.v cur % U64.v mword = 0 /\
                    (let hd = hd_address (cur <: obj_addr) in
                     let bwz = U64.v (getWosize (read_word g hd)) in
                     bwz >= wz /\
                     (let ahn = U64.v hd + (bwz - wz) * 8 in
                      ahn + 8 >= heap_size \/ ahn >= pow2 64 \/ ahn % 8 <> 0)))
          (ensures alloc_search g head prev cur wz fuel ==
                   { heap_out = g; fp_out = head; obj_out = 0UL })

/// For a valid obj_addr, spec_next_fp always reads the field (condition is always true)
val spec_next_fp_eq (g: heap) (obj: obj_addr)
  : Lemma (spec_next_fp g obj == read_word g obj)

/// ---------------------------------------------------------------------------
/// alloc_from_block unfolding lemmas (for Pulse proof)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 25"

/// Exact fit: leftover < 2
/// Exact fit (leftover = 0): the block is handed over whole, and since
/// bwz = wz the header already declares exactly the request.
val alloc_from_block_exact (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma (requires (let hdr = read_word g (hd_address obj) in
                     let bwz = U64.v (getWosize hdr) in
                     bwz == wz))
          (ensures (let hd = hd_address obj in
                    let ahdr = make_header (U64.uint_to_t wz) white_bits 0UL in
                    let g1 = write_word g hd ahdr in
                    alloc_from_block g obj wz next == (g1, next)))

/// Any leftover (>= 1): the object is right-justified, so the remainder keeps
/// `hd`.  At leftover >= 2 its address and its link at hd + 8 are untouched and
/// the free list is unchanged; at leftover = 1 the remainder is the empty block
/// and the whole block leaves the list.  The two cases write the same heap.
val alloc_from_block_split_normal (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma (requires (let hd = hd_address obj in
                     let bwz = U64.v (getWosize (read_word g hd)) in
                     bwz - wz >= 1 /\
                     U64.v hd + (bwz - wz) * 8 < heap_size))
          (ensures (let hd = hd_address obj in
                    let bwz = U64.v (getWosize (read_word g hd)) in
                    let leftover = bwz - wz in
                    let rhdr = make_header (U64.uint_to_t (leftover - 1)) blue_bits 0UL in
                    let g1 = write_word g hd rhdr in
                    let ahn = U64.v hd + leftover * 8 in
                    let ah : hp_addr = U64.uint_to_t ahn in
                    let ahdr = make_header (U64.uint_to_t wz) white_bits 0UL in
                    let g2 = write_word g1 ah ahdr in
                    alloc_from_block g obj wz next ==
                      (g2, (if leftover >= 2 then (obj <: U64.t) else next))))

/// The right-justified object header would fall outside the heap.  Unreachable
/// for a well-formed block (hd + (bwz + 1) * 8 <= heap_size and leftover <= bwz),
/// but the definition guards it.  Replaces the old `_split_rem_hd_oob` /
/// `_split_rem_obj_oob` pair, which described a high-end remainder that the
/// right-justified layout no longer has.
val alloc_from_block_oob (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma (requires (let hd = hd_address obj in
                     let bwz = U64.v (getWosize (read_word g hd)) in
                     bwz >= wz /\
                     U64.v hd + (bwz - wz) * 8 >= heap_size))
          (ensures alloc_from_block g obj wz next == (g, next))

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
  let bwz = U64.v (getWosize (read_word g hd)) in
  bwz - wz >= 2 /\
  U64.v hd + (bwz - wz) * 8 < heap_size

/// Result heap and fp for the normal split case
let alloc_split_normal_result (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t) : GTot (heap & U64.t) =
  alloc_from_block g obj wz next

/// Result heap shorthand
let alloc_split_normal_heap (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t) : GTot heap =
  fst (alloc_split_normal_result g obj wz next)

/// Allocation only ever writes inside the free block it was given: the header
/// at `hd`, and (when the object is right-justified above a remainder or a
/// fragment) the object header at `hd + leftover * 8`, which is still below
/// `hd + (bwz + 1) * 8`.  So any address disjoint from the block is untouched.
///
/// Stated once, for every case at once, so callers never have to know which
/// arm they are in.  That matters: at an `alloc_search` call site the context
/// is large enough that even `bwz - wz == 1` does not discharge, whereas this
/// lemma's own proof runs in a tiny context.
val alloc_from_block_read_outside
  (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t) (addr: hp_addr)
  : Lemma (requires (let hd = hd_address obj in
                     let bwz = U64.v (getWosize (read_word g hd)) in
                     bwz >= wz /\
                     (U64.v addr + 8 <= U64.v hd \/
                      U64.v addr >= U64.v hd + (bwz + 1) * 8)))
          (ensures (let (g', _) = alloc_from_block g obj wz next in
                    read_word g' addr == read_word g addr))

/// The remainder keeps `hd`; its header is shrunk to `leftover - 1`, blue.
val alloc_split_normal_read_rem_hd (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma (requires alloc_split_normal_pre g obj wz)
          (ensures (let g' = alloc_split_normal_heap g obj wz next in
                    let hd = hd_address obj in
                    let bwz = U64.v (getWosize (read_word g hd)) in
                    read_word g' hd == make_header (U64.uint_to_t (bwz - wz - 1)) blue_bits 0UL))

/// The remainder's link word is at `obj` (= hd + 8) and is NOT written: the
/// cell keeps the successor it already had, which is what makes the free list
/// bit-identical across a split.  (Under the old low-end layout this lemma
/// said the fresh remainder's field was set to `next`; right-justification
/// makes it a preservation fact instead.)
val alloc_split_normal_read_rem_field (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma (requires alloc_split_normal_pre g obj wz)
          (ensures (let g' = alloc_split_normal_heap g obj wz next in
                    read_word g' (obj <: hp_addr) == read_word g (obj <: hp_addr)))

/// Reading an unwritten address: result equals original.  Only two words are
/// written now -- the remainder header at `hd` and the object header at
/// `hd + leftover * 8`.
val alloc_split_normal_read_other (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t) (addr: hp_addr)
  : Lemma (requires alloc_split_normal_pre g obj wz /\
                    (let hd = hd_address obj in
                     let bwz = U64.v (getWosize (read_word g hd)) in
                     let ahn = U64.v hd + (bwz - wz) * 8 in
                     (U64.v addr + 8 <= U64.v hd \/ U64.v addr >= U64.v hd + 8) /\
                     (U64.v addr + 8 <= ahn \/ U64.v addr >= ahn + 8)))
          (ensures (let g' = alloc_split_normal_heap g obj wz next in
                    read_word g' addr == read_word g addr))


/// ---------------------------------------------------------------------------
/// Read-level bridge lemmas for alloc_from_block (exact case)
/// ---------------------------------------------------------------------------
