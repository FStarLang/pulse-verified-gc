(*
   GC.Spec.Allocator.Lemmas.Split — Exact-fit and split-case allocation lemmas.

   Sections 5+6+7: proves alloc_from_block preserves well_formed_heap
   for both exact-fit and split cases.
*)
module GC.Spec.Allocator.Lemmas.Split

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
open GC.Spec.Allocator.Lemmas.Header
module U64 = FStar.UInt64
module Seq = FStar.Seq

/// Named precondition for split-case lemmas
let alloc_split_pre (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) : prop =
  well_formed_heap g /\
  Seq.mem obj (objects zero_addr g) /\
  (let hdr = read_word g (hd_address obj) in
   let block_wz = U64.v (getWosize hdr) in
   block_wz >= wz /\ block_wz - wz >= 2) /\
  (is_pointer_field next_fp ==> Seq.mem next_fp (objects zero_addr g))

/// Section 5: Exact-fit preserves well_formed_heap
val alloc_exact_preserves_wf :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  Lemma (requires well_formed_heap g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   let block_wz = U64.v (getWosize hdr) in
                   block_wz >= wz /\ block_wz - wz < 2))
        (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                  well_formed_heap g' /\
                  objects zero_addr g' == objects zero_addr g))

/// Helper: next_hd objects agree after split
val split_next_hd_objects_eq :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  Lemma (requires well_formed_heap g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   let block_wz = U64.v (getWosize hdr) in
                   block_wz >= wz /\ block_wz - wz >= 2))
        (ensures (let hd = hd_address obj in
                  let hdr = read_word g hd in
                  let block_wz = U64.v (getWosize hdr) in
                  let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
                  let (g3, _) = alloc_from_block g obj wz next_fp in
                  next_hd_nat < heap_size ==>
                  (let next_hd : hp_addr = U64.uint_to_t next_hd_nat in
                   objects next_hd g3 == objects next_hd g)))

/// Part1 variant: same as split_next_hd_objects_eq but uses well_formed_heap_part1
val split_next_hd_objects_eq_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   let block_wz = U64.v (getWosize hdr) in
                   block_wz >= wz /\ block_wz - wz >= 2))
        (ensures (let hd = hd_address obj in
                  let hdr = read_word g hd in
                  let block_wz = U64.v (getWosize hdr) in
                  let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
                  let (g3, _) = alloc_from_block g obj wz next_fp in
                  next_hd_nat < heap_size ==>
                  (let next_hd : hp_addr = U64.uint_to_t next_hd_nat in
                   objects next_hd g3 == objects next_hd g)))

/// If h ∈ objects(start, g), then f_address start ∈ objects(start, g)
val objects_nonempty_first_mem :
  (start: hp_addr) -> (g: heap) -> (h: obj_addr) ->
  Lemma (requires Seq.mem h (objects start g))
        (ensures Seq.mem (f_address start) (objects start g))

/// If h ∈ objects(later, g) and later is reachable from start, then h ∈ objects(start, g)
val objects_later_in_earlier :
  (start: hp_addr) -> (g: heap) -> (later: hp_addr) -> (h: obj_addr) ->
  Lemma (requires U64.v start <= U64.v later /\
                  Seq.mem h (objects later g) /\
                  (U64.v start = U64.v later \/ Seq.mem (f_address later) (objects start g)))
        (ensures Seq.mem h (objects start g))
        (decreases (Seq.length g - U64.v start))

/// Objects in g3 are either from g or the remainder object
val split_new_mem_in_old_or_rem :
  (start: hp_addr) -> (g: heap) -> (g3: heap) ->
  (obj: obj_addr) -> (wz: nat) -> (block_wz: nat) ->
  (h: obj_addr) ->
  Lemma (requires
      Seq.length g3 == Seq.length g /\
      well_formed_heap g /\
      Seq.mem obj (objects zero_addr g) /\
      (let hd = hd_address obj in
       let hdr = read_word g hd in
       U64.v (getWosize hdr) == block_wz /\
       block_wz >= wz /\ block_wz - wz >= 2 /\
       (let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
        let rem_obj_nat = rem_hd_nat + 8 in
        let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
        rem_hd_nat < heap_size /\
        rem_obj_nat < heap_size /\
        next_hd_nat <= heap_size /\
        (forall (p: hp_addr). U64.v p < U64.v hd ==> read_word g3 p == read_word g p) /\
        getWosize (read_word g3 hd) == U64.uint_to_t wz /\
        (rem_hd_nat < heap_size ==>
          getWosize (read_word g3 (U64.uint_to_t rem_hd_nat <: hp_addr)) == U64.uint_to_t (block_wz - wz - 1)) /\
        (next_hd_nat < heap_size ==>
          objects (U64.uint_to_t next_hd_nat <: hp_addr) g3 == objects (U64.uint_to_t next_hd_nat <: hp_addr) g) /\
        U64.v start <= U64.v hd)) /\
      Seq.mem h (objects start g3) /\
      (U64.v start = U64.v zero_addr \/ Seq.mem (f_address start) (objects zero_addr g)) /\
      Seq.mem obj (objects start g))
    (ensures (let rem_hd_nat = U64.v (hd_address obj) + (1 + wz) * 8 in
              let rem_obj_nat = rem_hd_nat + 8 in
              Seq.mem h (objects start g) \/ U64.v h == rem_obj_nat))
    (decreases (Seq.length g3 - U64.v start))

/// Per-point g3 agreement: at any hp_addr p that is not one of the 3 write
/// positions, g3 returns the same read_word as g.
val alloc_split_g3_agrees :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) -> (p: hp_addr) ->
  Lemma (requires alloc_split_pre g obj wz next_fp /\
                  (let hd = hd_address obj in
                   let hdr = read_word g hd in
                   let block_wz = U64.v (getWosize hdr) in
                   let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
                   let rem_obj_nat = rem_hd_nat + 8 in
                   U64.v p <> U64.v hd /\
                   U64.v p <> rem_hd_nat /\
                   U64.v p <> rem_obj_nat))
        (ensures (let (g3, _) = alloc_from_block g obj wz next_fp in
                  read_word g3 p == read_word g p))

/// Establish ALL common facts from alloc_split_pre.
val alloc_split_facts :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  Lemma (requires alloc_split_pre g obj wz next_fp)
        (ensures (let hd = hd_address obj in
                  let hdr = read_word g hd in
                  let block_wz = U64.v (getWosize hdr) in
                  let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
                  let rem_obj_nat = rem_hd_nat + 8 in
                  let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
                  let rem_wz = block_wz - wz - 1 in
                  rem_hd_nat >= 8 /\
                  rem_obj_nat >= 16 /\
                  rem_hd_nat < heap_size /\
                  rem_obj_nat < heap_size /\
                  next_hd_nat <= heap_size /\
                  next_hd_nat % 8 == 0 /\
                  rem_hd_nat % 8 == 0 /\
                  rem_obj_nat % 8 == 0 /\
                  rem_hd_nat < pow2 64 /\
                  rem_obj_nat < pow2 64 /\
                  next_hd_nat < pow2 64 /\
                  wz < pow2 54 /\
                  rem_wz < pow2 54 /\
                  getWosize (make_header (U64.uint_to_t wz) white_bits 0UL) == U64.uint_to_t wz /\
                  getWosize (make_header (U64.uint_to_t rem_wz) blue_bits 0UL) == U64.uint_to_t rem_wz /\
                  (let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
                   let g1 = write_word g hd alloc_hdr in
                   let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
                   let rem_hdr = make_header (U64.uint_to_t rem_wz) blue_bits 0UL in
                   let g2 = write_word g1 rem_hd rem_hdr in
                   let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
                   let g3 = write_word g2 rem_obj next_fp in
                   alloc_from_block g obj wz next_fp == (g3, rem_obj) /\
                   Seq.length g3 == Seq.length g /\
                   read_word g3 hd == alloc_hdr /\
                   read_word g3 rem_hd == rem_hdr /\
                   getWosize (read_word g3 hd) == U64.uint_to_t wz /\
                   getWosize (read_word g3 rem_hd) == U64.uint_to_t rem_wz /\
                   (next_hd_nat < heap_size ==>
                     objects (U64.uint_to_t next_hd_nat <: hp_addr) g3 ==
                     objects (U64.uint_to_t next_hd_nat <: hp_addr) g))))

/// Old objects are in new objects list after split
val alloc_split_old_in_new :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) -> (h: obj_addr) ->
  Lemma (requires alloc_split_pre g obj wz next_fp /\
                  Seq.mem h (objects zero_addr g))
        (ensures (let (g3, _) = alloc_from_block g obj wz next_fp in
                  Seq.mem h (objects zero_addr g3)))

/// Remainder object is in post-split objects list
val alloc_split_rem_in_objects :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  Lemma (requires alloc_split_pre g obj wz next_fp)
        (ensures (let (g3, rem_fp) = alloc_from_block g obj wz next_fp in
                  is_pointer_field rem_fp /\
                  (is_pointer_field rem_fp ==> Seq.mem rem_fp (objects zero_addr g3))))

/// Split case preserves well_formed_heap
val alloc_split_preserves_wf :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  Lemma (requires alloc_split_pre g obj wz next_fp)
        (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                  well_formed_heap g'))

/// Combined: alloc_from_block preserves well_formed_heap
val alloc_from_block_preserves_wf :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  Lemma (requires well_formed_heap g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   U64.v (getWosize hdr) >= wz) /\
                  (is_pointer_field next_fp ==> Seq.mem next_fp (objects zero_addr g)))
        (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                  well_formed_heap g'))
