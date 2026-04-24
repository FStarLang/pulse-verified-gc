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
/// Bridge: make_header == GC.Impl.Object.makeHeader (for extraction)
/// ---------------------------------------------------------------------------

/// The spec's make_header with blue_bits matches GC.Impl.Object.makeHeader with blue
/// because pack_color Blue = 2 = blue_bits.
/// This is needed to connect the Pulse implementation to the pure spec.

module ImplObject = GC.Spec.Object

let make_header_eq_impl (wz: U64.t{U64.v wz < pow2 54}) (c: U64.t{U64.v c < 4}) (tag: U64.t{U64.v tag < 256})
  : Lemma (make_header wz c tag == 
           (let wz_shifted = U64.shift_left wz 10ul in
            let c_shifted = U64.shift_left c 8ul in
            U64.logor wz_shifted (U64.logor c_shifted tag)))
  = ()

/// ---------------------------------------------------------------------------
/// Step lemmas for alloc_search (for loop correspondence proofs)
/// ---------------------------------------------------------------------------

/// When fuel = 0: OOM
let alloc_search_fuel_0 (g: heap) (head prev cur: U64.t) (wz: nat)
  : Lemma (alloc_search g head prev cur wz 0 ==
           { heap_out = g; fp_out = head; obj_out = 0UL })
  = ()

/// When cur is invalid (not a valid obj_addr): OOM
let alloc_search_invalid (g: heap) (head prev cur: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    (cur = 0UL \/
                     U64.v cur < U64.v mword \/
                     U64.v cur >= heap_size \/
                     U64.v cur % U64.v mword <> 0))
          (ensures alloc_search g head prev cur wz fuel ==
                   { heap_out = g; fp_out = head; obj_out = 0UL })
  = ()

/// When the block is too small: advance to next
let alloc_search_advance (g: heap) (head prev cur: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v cur >= U64.v mword /\
                    U64.v cur < heap_size /\
                    U64.v cur % U64.v mword = 0 /\
                    (let hdr = read_word g (hd_address (cur <: obj_addr)) in
                     U64.v (getWosize hdr) < wz))
          (ensures alloc_search g head prev cur wz fuel ==
                   alloc_search g head cur (spec_next_fp g (cur <: obj_addr)) wz (fuel - 1))
  = ()

/// When the block fits and prev = 0 (head of list)
let alloc_search_found_head (g: heap) (head prev cur: U64.t) (wz: nat) (fuel: nat)
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
  = ()

/// When the block fits and prev is a valid hp_addr
let alloc_search_found_prev (g: heap) (head prev cur: U64.t) (wz: nat) (fuel: nat)
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
  = ()

/// Helper: for multiples of d, a < b implies a + d <= b
let multiple_gap_lemma (a b: nat) (d: pos)
  : Lemma (requires a % d == 0 /\ b % d == 0 /\ a < b)
          (ensures a + d <= b)
  = FStar.Math.Lemmas.lemma_div_exact a d;
    FStar.Math.Lemmas.lemma_div_exact b d

/// For a valid obj_addr, spec_next_fp always reads the field (condition is always true)
let spec_next_fp_eq (g: heap) (obj: obj_addr)
  : Lemma (spec_next_fp g obj == read_word g obj)
  = hd_address_bounds obj;  // U64.v (hd_address obj) + 8 < heap_size
    hd_address_spec obj;    // U64.v (hd_address obj) = U64.v obj - 8
    // hd + 8 < heap_size, both multiples of 8, so hd + 16 <= heap_size
    multiple_gap_lemma (U64.v (hd_address obj) + U64.v mword) heap_size (U64.v mword)

/// ---------------------------------------------------------------------------
/// alloc_from_block unfolding lemmas (for Pulse proof)
/// ---------------------------------------------------------------------------

/// Exact fit: leftover < 2
#push-options "--z3rlimit 100"
let alloc_from_block_exact (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma (requires (let hdr = read_word g (hd_address obj) in
                     let bwz = U64.v (getWosize hdr) in
                     bwz >= wz /\ bwz - wz < 2))
          (ensures (let hd = hd_address obj in
                    let hdr = read_word g hd in
                    let bwz = U64.v (getWosize hdr) in
                    let ahdr = make_header (U64.uint_to_t bwz) white_bits 0UL in
                    let g1 = write_word g hd ahdr in
                    alloc_from_block g obj wz next == (g1, next)))
  = hd_address_spec obj; hd_address_bounds obj;
    reveal_opaque (`%alloc_from_block) alloc_from_block
#pop-options

/// Split, normal: all bounds pass
#push-options "--z3rlimit 100 --fuel 1"
let alloc_from_block_split_normal (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
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
  = hd_address_spec obj; hd_address_bounds obj;
    reveal_opaque (`%alloc_from_block) alloc_from_block
#pop-options

/// Split, rem_hd out of bounds
#push-options "--z3rlimit 100"
let alloc_from_block_split_rem_hd_oob (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma (requires (let hd = hd_address obj in
                     let hdr = read_word g hd in
                     let bwz = U64.v (getWosize hdr) in
                     bwz - wz >= 2 /\
                     U64.v hd + (1 + wz) * 8 >= heap_size))
          (ensures (let hd = hd_address obj in
                    let ahdr = make_header (U64.uint_to_t wz) white_bits 0UL in
                    let g1 = write_word g hd ahdr in
                    alloc_from_block g obj wz next == (g1, next)))
  = hd_address_spec obj; hd_address_bounds obj;
    reveal_opaque (`%alloc_from_block) alloc_from_block
#pop-options

/// Split, rem_obj out of bounds (rem_hd ok but rem_obj >= heap_size)
#push-options "--z3rlimit 100 --fuel 1"
let alloc_from_block_split_rem_obj_oob (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
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
  = hd_address_spec obj; hd_address_bounds obj;
    reveal_opaque (`%alloc_from_block) alloc_from_block
#pop-options

/// ---------------------------------------------------------------------------
/// Read-level bridge lemmas for alloc_from_block (split, normal case)
///
/// These provide read_word facts about the post-alloc heap WITHOUT exposing
/// the intermediate write_word chain to the caller. Z3 gets direct
/// read_word equalities instead of chaining through 3 write_words.
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 100 --fuel 1"
/// The result heap has the same length as the input heap
let alloc_split_normal_length (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma (requires alloc_split_normal_pre g obj wz)
          (ensures Seq.length (alloc_split_normal_heap g obj wz next) == Seq.length g)
  = alloc_from_block_split_normal g obj wz next;
    let hd = hd_address obj in
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
    let _g3 = write_word g2 ro next in
    ()
#pop-options

#push-options "--z3rlimit 100 --fuel 1"
/// Reading the alloc header: header at hd_address obj == make_header wz white 0
let alloc_split_normal_read_hd (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma (requires alloc_split_normal_pre g obj wz)
          (ensures (let g' = alloc_split_normal_heap g obj wz next in
                    let hd = hd_address obj in
                    read_word g' hd == make_header (U64.uint_to_t wz) white_bits 0UL))
  = alloc_from_block_split_normal g obj wz next;
    let hd = hd_address obj in
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
    // hd < rh < ro, so read_word g3 hd chains back through:
    // g3 = write_word g2 ro next, ro > hd, so read_word g3 hd == read_word g2 hd
    read_write_different g2 ro hd next;
    // g2 = write_word g1 rh rhdr, rh > hd, so read_word g2 hd == read_word g1 hd
    read_write_different g1 rh hd rhdr;
    // g1 = write_word g hd ahdr, so read_word g1 hd == ahdr
    read_write_same g hd ahdr
#pop-options

#push-options "--z3rlimit 100 --fuel 1"
/// Reading the remainder header: header at rem_hd == make_header rem_wz blue 0
let alloc_split_normal_read_rem_hd (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma (requires alloc_split_normal_pre g obj wz)
          (ensures (let g' = alloc_split_normal_heap g obj wz next in
                    let hd = hd_address obj in
                    let hdr = read_word g hd in
                    let bwz = U64.v (getWosize hdr) in
                    let rhn = U64.v hd + (1 + wz) * 8 in
                    let rh : hp_addr = U64.uint_to_t rhn in
                    let rw = bwz - wz - 1 in
                    read_word g' rh == make_header (U64.uint_to_t rw) blue_bits 0UL))
  = alloc_from_block_split_normal g obj wz next;
    let hd = hd_address obj in
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
    // ro > rh, so read_word g3 rh == read_word g2 rh
    read_write_different g2 ro rh next;
    // read_word g2 rh == rhdr
    read_write_same g1 rh rhdr
#pop-options

#push-options "--z3rlimit 100 --fuel 1"
/// Reading the remainder field: read_word g' ro == next_fp
let alloc_split_normal_read_rem_field (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma (requires alloc_split_normal_pre g obj wz)
          (ensures (let g' = alloc_split_normal_heap g obj wz next in
                    let hd = hd_address obj in
                    let rhn = U64.v hd + (1 + wz) * 8 in
                    let ron = rhn + 8 in
                    let ro : hp_addr = U64.uint_to_t ron in
                    read_word g' ro == next))
  = alloc_from_block_split_normal g obj wz next;
    let hd = hd_address obj in
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
    let _g3 = write_word g2 ro next in
    read_write_same g2 ro next
#pop-options

#push-options "--z3rlimit 100 --fuel 1"
/// Reading an unwritten address: result equals original
let alloc_split_normal_read_other (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t) (addr: hp_addr)
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
  = alloc_from_block_split_normal g obj wz next;
    let hd = hd_address obj in
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
    read_write_different g2 ro addr next;
    read_write_different g1 rh addr rhdr;
    read_write_different g hd addr ahdr
#pop-options

/// ---------------------------------------------------------------------------
/// Read-level bridge lemmas for alloc_from_block (exact case)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 100"
let alloc_exact_read_hd (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma (requires alloc_exact_pre g obj wz)
          (ensures (let g' = alloc_exact_heap g obj wz next in
                    let hd = hd_address obj in
                    let bwz = U64.v (getWosize (read_word g hd)) in
                    read_word g' hd == make_header (U64.uint_to_t bwz) white_bits 0UL))
  = alloc_from_block_exact g obj wz next;
    let hd = hd_address obj in
    let bwz = U64.v (getWosize (read_word g hd)) in
    let ahdr = make_header (U64.uint_to_t bwz) white_bits 0UL in
    read_write_same g hd ahdr
#pop-options

#push-options "--z3rlimit 100"
let alloc_exact_read_other (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t) (addr: hp_addr)
  : Lemma (requires alloc_exact_pre g obj wz /\
                    (let hd = hd_address obj in
                     U64.v addr + 8 <= U64.v hd \/ U64.v addr >= U64.v hd + 8))
          (ensures (let g' = alloc_exact_heap g obj wz next in
                    read_word g' addr == read_word g addr))
  = alloc_from_block_exact g obj wz next;
    let hd = hd_address obj in
    let bwz = U64.v (getWosize (read_word g hd)) in
    let ahdr = make_header (U64.uint_to_t bwz) white_bits 0UL in
    read_write_different g hd addr ahdr
#pop-options

#push-options "--z3rlimit 100"
let alloc_exact_length (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma (requires alloc_exact_pre g obj wz)
          (ensures Seq.length (alloc_exact_heap g obj wz next) == Seq.length g)
  = alloc_from_block_exact g obj wz next
#pop-options
