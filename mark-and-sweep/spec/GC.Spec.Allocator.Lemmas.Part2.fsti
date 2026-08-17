(*
   GC.Spec.Allocator.Lemmas.Part2 — Interface for P2-P5 proofs.

   alloc_spec preserves well_formed_heap_part1, fl_valid, fl_chain_terminates,
   and various framing properties under the weaker part1 precondition.
*)
module GC.Spec.Allocator.Lemmas.Part2

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
open GC.Spec.Allocator.Lemmas.Common
open GC.Spec.Allocator.Lemmas.Chain
module U64 = FStar.UInt64
module Seq = FStar.Seq

/// alloc_from_block preserves well_formed_heap_part1.
val alloc_from_block_preserves_wfh_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   U64.v (getWosize hdr) >= wz))
        (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                  well_formed_heap_part1 g'))

/// **Theorem**: alloc_spec preserves well_formed_heap_part1.
val alloc_spec_preserves_wfh_part1 : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp heap_words /\
                  fl_chain_terminates g fp heap_words)
        (ensures (let r = alloc_spec g fp requested_wz in
                  well_formed_heap_part1 r.heap_out))

/// **Theorem**: alloc_spec preserves fl_valid under well_formed_heap_part1.
val alloc_spec_preserves_fl_valid_part1 : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp heap_words /\
                  fl_chain_terminates g fp heap_words)
        (ensures (let r = alloc_spec g fp requested_wz in
                  fl_valid r.heap_out r.fp_out heap_words))

/// **Theorem**: alloc_spec preserves fl_chain_terminates under well_formed_heap_part1.
val alloc_spec_preserves_fl_chain_terminates_part1 : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp heap_words /\
                  fl_chain_terminates g fp heap_words)
        (ensures (let r = alloc_spec g fp requested_wz in
                  fl_chain_terminates r.heap_out r.fp_out heap_words))

/// **Theorem**: alloc_spec removes obj_out from the chain, under well_formed_heap_part1.
val alloc_spec_obj_not_in_chain_part1 : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp heap_words /\
                  fl_chain_terminates g fp heap_words /\
                  requested_wz >= 1 /\
                  (alloc_spec g fp requested_wz).obj_out <> 0UL)
        (ensures (let r = alloc_spec g fp requested_wz in
                  chain_avoids r.heap_out r.fp_out r.obj_out heap_words = true))

/// ---------------------------------------------------------------------------
/// Allocation framing: alloc_spec preserves reads in the body of the
/// allocated object (it only modifies headers/links, not the body itself).
/// ---------------------------------------------------------------------------

/// **Theorem**: alloc_spec does not modify the body of the allocated block.
/// For any address in [obj_out, obj_out + requested_wz * 8), the read after
/// allocation equals the read before allocation.
val alloc_spec_read_body : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) -> (addr: hp_addr) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp heap_words /\
                  fl_chain_terminates g fp heap_words /\
                  requested_wz >= 1 /\
                  (alloc_spec g fp requested_wz).obj_out <> 0UL /\
                  (let r = alloc_spec g fp requested_wz in
                   U64.v addr >= U64.v r.obj_out /\
                   U64.v addr + 8 <= U64.v r.obj_out + requested_wz * 8))
        (ensures (let r = alloc_spec g fp requested_wz in
                  read_word r.heap_out addr == read_word g addr))

/// **Theorem**: alloc_spec does not modify the body of a different object
/// that is separated from the free-list writes.
/// addr is in the body of some already-allocated object (not in the free list).
val alloc_spec_read_other : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
                            (other: obj_addr) -> (addr: hp_addr) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp heap_words /\
                  fl_chain_terminates g fp heap_words /\
                  requested_wz >= 1 /\
                  Seq.mem other (objects zero_addr g) /\
                  // other is NOT in the free-list chain
                  chain_avoids g fp other heap_words = true /\
                  // addr is in the body of other
                  U64.v addr >= U64.v other /\
                  U64.v addr + 8 <= U64.v other + U64.v (wosize_of_object other g) * 8)
        (ensures (let r = alloc_spec g fp requested_wz in
                  read_word r.heap_out addr == read_word g addr))

/// **Theorem**: alloc_spec preserves chain_avoids for an excluded object.
/// If excl was not in the free-list chain before alloc, it's not in the chain after.
val alloc_spec_preserves_chain_avoids_other : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
                                              (excl: U64.t) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp heap_words /\
                  fl_chain_terminates g fp heap_words /\
                  requested_wz >= 1 /\
                  chain_avoids g fp excl heap_words = true /\
                  U64.v excl >= U64.v mword /\ U64.v excl < heap_size /\
                  U64.v excl % U64.v mword == 0 /\
                  Seq.mem (excl <: obj_addr) (objects zero_addr g))
        (ensures (let r = alloc_spec g fp requested_wz in
                  chain_avoids r.heap_out r.fp_out excl heap_words = true))

/// **Theorem**: alloc_spec preserves well_formed_heap_part4 (no infix objects).
/// Under just well_formed_heap_part1, fl_valid, fl_chain_terminates.
/// All newly created headers (allocated block + remainder) have tag=0 ≠ infix_tag.
/// Existing non-free-list objects have unchanged headers.
val alloc_spec_preserves_wfh_part4 : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap_part1 g /\
                  well_formed_heap_part4 g /\
                  fl_valid g fp heap_words /\
                  fl_chain_terminates g fp heap_words)
        (ensures (let r = alloc_spec g fp requested_wz in
                  well_formed_heap_part4 r.heap_out))

/// ---------------------------------------------------------------------------
/// Allocation framing: field reads for non-allocated objects
/// ---------------------------------------------------------------------------

/// **Theorem**: alloc_spec preserves reads at non-first-field positions
/// of objects that are NOT the allocated block.
/// (Works for objects ON the free-list chain too — no chain_avoids needed.)
val alloc_spec_read_field_gt0 :
  (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  (src: obj_addr) -> (j: nat) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp heap_words /\
                  fl_chain_terminates g fp heap_words /\
                  requested_wz >= 1 /\
                  (alloc_spec g fp requested_wz).obj_out <> 0UL /\
                  Seq.mem src (objects zero_addr g) /\
                  src <> (alloc_spec g fp requested_wz).obj_out /\
                  j > 0 /\
                  j < U64.v (wosize_of_object src g) /\
                  U64.v src + j * 8 + 8 <= heap_size)
        (ensures (let r = alloc_spec g fp requested_wz in
                  let addr : hp_addr = U64.uint_to_t (U64.v src + j * 8) in
                  read_word r.heap_out addr == read_word g addr))

/// **Theorem**: In the split case (block_wz - wz >= 2), the remainder fp
/// returned by alloc_from_block is a valid pointer AND is in objects of
/// the output heap. Requires only well_formed_heap_part1.
val alloc_from_block_rem_in_objects_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   let bwz = U64.v (getWosize hdr) in
                   bwz >= wz /\ bwz - wz >= 2))
        (ensures (let (g', rem_fp) = alloc_from_block g obj wz next_fp in
                  is_pointer_field rem_fp /\
                  Seq.mem rem_fp (objects zero_addr g')))

/// **Theorem**: alloc_from_block preserves object membership under just
/// well_formed_heap_part1. (Public wrapper for internal part1 proof.)
val alloc_from_block_preserves_objects_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   U64.v (getWosize hdr) >= wz))
        (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                  (forall (h: obj_addr). Seq.mem h (objects zero_addr g) ==> Seq.mem h (objects zero_addr g'))))

/// **Theorem**: Any object in the post-alloc heap that was NOT in the pre-alloc
/// heap is blue. (The only possible new object is the remainder block,
/// which receives a blue header.)
val alloc_spec_new_objects_blue_part1 :
  (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp heap_words /\
                  fl_chain_terminates g fp heap_words /\
                  requested_wz >= 1 /\
                  (alloc_spec g fp requested_wz).obj_out <> 0UL)
        (ensures (let r = alloc_spec g fp requested_wz in
                  forall (x: obj_addr).
                    Seq.mem x (objects zero_addr r.heap_out) /\
                    ~(Seq.mem x (objects zero_addr g)) ==>
                    is_blue x r.heap_out = true))

/// **Theorem**: Backward inclusion for alloc_from_block (split case).
/// If h is in objects of the output heap but NOT in objects of the input heap,
/// then h must be the remainder address returned by alloc_from_block.
val alloc_from_block_objects_backward_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) -> (h: obj_addr) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   let bwz = U64.v (getWosize hdr) in
                   bwz >= wz /\ wz >= 1 /\ bwz - wz >= 2) /\
                  (let (g', _) = alloc_from_block g obj wz next_fp in
                   Seq.mem h (objects zero_addr g') /\
                   ~(Seq.mem h (objects zero_addr g))))
        (ensures h == snd (alloc_from_block g obj wz next_fp))

/// **Theorem**: alloc_spec preserves no_black_objects under well_formed_heap_part1.
///
/// Proof sketch: For each object h in the post-alloc heap:
/// - If h is new (not in pre-alloc): alloc_spec_new_objects_blue_part1 → blue → not black
/// - If h == obj_out (the allocated block): header is make_header wz white_bits → not black
/// - If h is a pre-existing object != obj_out: header unchanged by alloc → not black
val alloc_spec_preserves_no_black_part1 : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires GC.Spec.Mark.no_black_objects g /\
                  well_formed_heap_part1 g /\
                  fl_valid g fp heap_words /\
                  fl_chain_terminates g fp heap_words)
        (ensures (let r = alloc_spec g fp requested_wz in
                  GC.Spec.Mark.no_black_objects r.heap_out))
