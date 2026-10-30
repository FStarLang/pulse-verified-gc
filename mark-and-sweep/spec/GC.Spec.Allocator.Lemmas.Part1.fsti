(*
   GC.Spec.Allocator.Lemmas.Part1 — Interface for Section P1 proofs.

   alloc_spec / alloc_from_block preserve object membership under
   well_formed_heap_part1 (weaker precondition than well_formed_heap).
*)
module GC.Spec.Allocator.Lemmas.Part1

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
module U64 = FStar.UInt64
module Seq = FStar.Seq

/// Helper: establish all common facts from split precondition under part1
/// (fuel 0: the well-formedness goals of this signature are pure arithmetic;
/// with fuel, unfolding the heap/bit-vector definitions in the hypotheses
/// makes the `U64.uint_to_t next_hd_nat` typing goal time out)
#push-options "--fuel 0 --ifuel 0"
val alloc_split_facts_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  (tag: U64.t{U64.v tag < 256}) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   let block_wz = U64.v (getWosize hdr) in
                   block_wz >= wz /\ block_wz - wz >= 1))
        (ensures (let hd = hd_address obj in
                  let hdr = read_word g hd in
                  let block_wz = U64.v (getWosize hdr) in
                  let leftover = block_wz - wz in
                  // Right-justified: remainder keeps hd, object header sits
                  // `leftover` words above it.
                  let ahn = U64.v hd + leftover * 8 in
                  let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
                  let rem_wz = leftover - 1 in
                  ahn >= 8 /\
                  ahn < heap_size /\
                  next_hd_nat <= heap_size /\
                  next_hd_nat % 8 == 0 /\
                  ahn % 8 == 0 /\
                  ahn < pow2 64 /\
                  next_hd_nat < pow2 64 /\
                  wz < pow2 54 /\
                  rem_wz < pow2 54 /\
                  getWosize (make_header (U64.uint_to_t wz) white_bits tag) == U64.uint_to_t wz /\
                  getWosize (make_header (U64.uint_to_t rem_wz) blue_bits 0UL) == U64.uint_to_t rem_wz /\
                  (let rem_hdr = make_header (U64.uint_to_t rem_wz) blue_bits 0UL in
                   let g1 = write_word g hd rem_hdr in
                   let ah : hp_addr = U64.uint_to_t ahn in
                   let alloc_hdr = make_header (U64.uint_to_t wz) white_bits tag in
                   let g2 = write_word g1 ah alloc_hdr in
                   alloc_from_block g obj wz tag next_fp ==
                     (g2, (if leftover >= 2 then (obj <: U64.t) else next_fp)) /\
                   Seq.length g2 == Seq.length g /\
                   read_word g2 hd == rem_hdr /\
                   read_word g2 ah == alloc_hdr /\
                   getWosize (read_word g2 hd) == U64.uint_to_t rem_wz /\
                   getWosize (read_word g2 ah) == U64.uint_to_t wz /\
                   (next_hd_nat < heap_size ==>
                     objects (U64.uint_to_t next_hd_nat) g2 ==
                     objects (U64.uint_to_t next_hd_nat) g))))
#pop-options

/// Helper: g3 agrees with g at non-write positions under part1
val alloc_split_g3_agrees_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) -> (p: hp_addr) ->
  (tag: U64.t{U64.v tag < 256}) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hd = hd_address obj in
                   let hdr = read_word g hd in
                   let block_wz = U64.v (getWosize hdr) in
                   block_wz >= wz /\ block_wz - wz >= 1 /\
                   // Right-justified: only two words are written, the
                   // remainder header at hd and the object header above it.
                   (let ahn = U64.v hd + (block_wz - wz) * 8 in
                    U64.v p <> U64.v hd /\
                    U64.v p <> ahn)))
        (ensures (let (g3, _) = alloc_from_block g obj wz tag next_fp in
                  read_word g3 p == read_word g p))

/// Old objects are in new objects after split (part1 variant)
val alloc_split_old_in_new_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) -> (h: obj_addr) ->
  (tag: U64.t{U64.v tag < 256}) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   let block_wz = U64.v (getWosize hdr) in
                   block_wz >= wz /\ block_wz - wz >= 1) /\
                  Seq.mem h (objects zero_addr g))
        (ensures (let (g3, _) = alloc_from_block g obj wz tag next_fp in
                  Seq.mem h (objects zero_addr g3)))

/// alloc_from_block preserves objects membership under part1
val alloc_from_block_objects_facts_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  (tag: U64.t{U64.v tag < 256}) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   U64.v (getWosize hdr) >= wz))
        (ensures (let (g', rem_fp) = alloc_from_block g obj wz tag next_fp in
                  (forall (h: obj_addr). Seq.mem h (objects zero_addr g) ==> Seq.mem h (objects zero_addr g'))))

/// Writing within an object body preserves the objects enumeration
val write_body_preserves_objects_local :
  (start: hp_addr) -> (g: heap) -> (obj: obj_addr) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (requires
      Seq.mem obj (objects start g) /\
      U64.v addr >= U64.v obj /\
      U64.v addr < U64.v obj + (U64.v (wosize_of_object obj g) * 8) /\
      U64.v addr % 8 = 0)
    (ensures objects start (write_word g addr v) == objects start g)
    (decreases (Seq.length g - U64.v start))

/// Writing within an object body preserves well_formed_heap_part1: the write
/// lands strictly above `hd_address obj`, so no header moves and the objects
/// enumeration -- hence every size bound -- is unchanged.
val write_body_preserves_wfh_part1 :
  (g: heap) -> (obj: obj_addr) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  U64.v addr >= U64.v obj /\
                  U64.v addr < U64.v obj + (U64.v (wosize_of_object obj g) * 8) /\
                  U64.v addr % 8 = 0)
        (ensures well_formed_heap_part1 (write_word g addr v))

/// **Theorem**: alloc_from_block preserves object membership under just
/// well_formed_heap_part1. (Public wrapper for internal part1 proof.)
val alloc_from_block_preserves_objects_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  (tag: U64.t{U64.v tag < 256}) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   U64.v (getWosize hdr) >= wz))
        (ensures (let (g', _) = alloc_from_block g obj wz tag next_fp in
                  (forall (h: obj_addr). Seq.mem h (objects zero_addr g) ==> Seq.mem h (objects zero_addr g'))))

/// **Theorem**: In the split case (block_wz - wz >= 2), the remainder fp
/// returned by alloc_from_block is a valid pointer AND is in objects of
/// the output heap. Requires only well_formed_heap_part1.
/// The ALLOCATED block is an object of the output heap.
///
/// Under right-justification the allocated piece is the newly created block --
/// the remainder keeps `obj` and stays an old object -- so this is the
/// counterpart of `alloc_from_block_rem_in_objects_part1` under the old
/// low-end layout, where those roles were the other way round.  Holds for any
/// leftover >= 1, since a split and a one-word leftover build the same tiling.
val alloc_from_block_alloc_in_objects_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  (tag: U64.t{U64.v tag < 256}) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hd = hd_address obj in
                   let bwz = U64.v (getWosize (read_word g hd)) in
                   bwz >= wz /\ bwz - wz >= 1 /\
                   // the OBJECT address must be in bounds for f_address; this
                   // is exactly what alloc_search's guard establishes
                   U64.v hd + (bwz - wz) * 8 + 8 < heap_size))
        (ensures (let hd = hd_address obj in
                  let bwz = U64.v (getWosize (read_word g hd)) in
                  let ahn = U64.v hd + (bwz - wz) * 8 in
                  let (g', _) = alloc_from_block g obj wz tag next_fp in
                  ahn % U64.v mword == 0 /\ ahn + 8 < heap_size /\
                  Seq.mem (f_address (U64.uint_to_t ahn <: hp_addr))
                          (objects zero_addr g')))

val alloc_from_block_rem_in_objects_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  (tag: U64.t{U64.v tag < 256}) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   let bwz = U64.v (getWosize hdr) in
                   // Only the true split keeps a cell: at leftover = 1 the
                   // replacement is `next_fp`, not a block in this heap.
                   bwz >= wz /\ bwz - wz >= 2))
        (ensures (let (g', rem_fp) = alloc_from_block g obj wz tag next_fp in
                  is_pointer_field rem_fp /\
                  Seq.mem rem_fp (objects zero_addr g')))
