module GC.Gen.PostCollectionShape

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module Corr = GC.Spec.Correctness
module Sweep = GC.Spec.Sweep
module SweepInv = GC.Spec.SweepInv
module Mark = GC.Spec.Mark
module Coalesce = GC.Spec.Coalesce
module Shape = GC.Spec.Coalesce.Shape
module CD = GC.Spec.Coalesce.Descending
module CDense = GC.Spec.Coalesce.Dense
module CC = GC.Spec.Coalesce.Complete
module AllocLemmas = GC.Spec.Allocator.Lemmas
module FreeListShape = GC.Gen.FreeListShape
module Promote = GC.Gen.Promote
module GenInv = GC.Gen.HeapInvariant
module HA = GC.Spec.HeapAgree
module HeapGraph = GC.Spec.HeapGraph

#set-options "--fuel 0 --ifuel 0 --z3rlimit 60"

#push-options "--fuel 1 --ifuel 1 --z3rlimit 80"
/// The colour clauses.  `coalesce_all_white_or_blue` says every object of the
/// coalesced walk is white or blue; black and gray are the other two cases of
/// the colour type, so both clauses follow by exhaustiveness.
private let coalesced_no_black_no_gray (g: heap)
  : Lemma
    (requires Coalesce.post_sweep g)
    (ensures (let g' = fst (Coalesce.coalesce g) in
              Mark.no_black_objects g' /\ SweepInv.no_gray_objects g'))
  = let g' = fst (Coalesce.coalesce g) in
    Coalesce.coalesce_all_white_or_blue g;
    let aux (x: obj_addr)
      : Lemma (ensures Seq.mem x (objects zero_addr g') ==>
                       ~(is_black x g') /\ ~(is_gray x g'))
      = if Seq.mem x (objects zero_addr g') then begin
          is_white_iff x g'; is_blue_iff x g';
          is_black_iff x g'; is_gray_iff x g'
        end
    in
    FStar.Classical.forall_intro aux;
    SweepInv.no_gray_intro g'
#pop-options

/// The link-word clause, packaged behind `blue_link_fields_valid`'s intro.
private let coalesced_blue_link_fields_valid (g: heap)
  : Lemma
    (requires Coalesce.post_sweep g)
    (ensures FreeListShape.blue_link_fields_valid (fst (Coalesce.coalesce g)))
  = let g' = fst (Coalesce.coalesce g) in
    FreeListShape.blue_link_fields_valid_intro g' (Shape.coalesce_blue_link_fields_valid g)

/// The free-list-avoidance clause, packaged behind `chain_objects_blue`.
private let coalesced_chain_objects_blue (g: heap)
  : Lemma
    (requires Coalesce.post_sweep g)
    (ensures (let r = Coalesce.coalesce g in
              Promote.chain_objects_blue (fst r) (snd r)))
  = let r = Coalesce.coalesce g in
    reveal_opaque (`%Promote.chain_objects_blue)
      (Promote.chain_objects_blue (fst r) (snd r));
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires (Shape.coalesce_chain_objects_blue g))

/// **The coalescer's output satisfies every clause of `major_heap_shape`.**
///
/// The clauses come from four places: the walk-transfer lemmas of
/// `GC.Spec.Coalesce.Shape`, the descending-chain argument of
/// `GC.Spec.Coalesce.Descending`, the `walk_end` argument of
/// `GC.Spec.Coalesce.Dense`, and the collector-level theorems of
/// `GC.Spec.Correctness`.
private let coalesce_major_heap_shape (g: heap)
  : Lemma
    (requires
      Coalesce.post_sweep_strong g /\
      heap_objects_dense g /\
      Seq.length (objects zero_addr g) > 0)
    (ensures (let r = Coalesce.coalesce g in
              GenInv.major_heap_shape (fst r) (snd r)))
  = let r = Coalesce.coalesce g in
    let g' = fst r in
    let fp' = snd r in
    // 1. well-formedness
    Coalesce.coalesce_preserves_wf g;
    // the rebuilt free list is exact: it holds exactly the blue cells
    CC.coalesce_exact g;
    GenInv.free_list_exact_iff g' fp';
    // 2, 3. the allocator's entry conditions on the rebuilt free list
    CD.coalesce_fl_entry g;
    // 4. the head is null or a pointer
    Shape.coalesce_fp_pointer_or_zero g;
    // 5. every cell's link word is null or a pointer
    coalesced_blue_link_fields_valid g;
    // 6, 8. the walk still tiles the heap, and is non-empty
    CDense.coalesce_dense g;
    // 7. no live object is on the free list
    coalesced_chain_objects_blue g;
    // 9, 10. the head is a well-formed free-list entry
    FreeListShape.fp_pointer_or_zero_fl_valid_implies_fp_valid fp' g' heap_words;
    FreeListShape.fp_pointer_or_zero_implies_fp_in_heap fp' g';
    // 11, 12. the collector leaves only white and blue behind
    coalesced_no_black_no_gray g;
    // 13. nothing live points into the free list
    Shape.coalesce_no_pointer_to_blue g;
    GenInv.major_heap_shape_intro g' fp'

let major_gc_restores_major_heap_shape major h_mark roots fp =
  let g = fst (Sweep.sweep h_mark fp) in
  Corr.sweep_post_sweep_strong_gen major h_mark roots fp;
  Corr.coalesce_precondition_bridge_gen major h_mark roots fp;
  Corr.mark_post_elim_wfh major h_mark roots fp;
  Corr.mark_post_elim_no_grey major h_mark roots fp;
  Corr.mark_post_elim_fp major h_mark roots fp;
  coalesce_major_heap_shape g

/// The shape invariant reads nothing that `heaps_agree_mod_free` lets differ.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
private let major_heap_shape_agree (s2 c: heap) (fp: U64.t)
  : Lemma (requires GenInv.major_heap_shape c fp /\ HA.heaps_agree_mod_free s2 c)
          (ensures GenInv.major_heap_shape s2 fp)
  = GenInv.major_heap_shape_elim c fp;
    HA.agree_objects s2 c;
    HA.agree_well_formed_heap s2 c;
    HA.agree_no_pointer_to_blue s2 c;
    HA.agree_fl_valid s2 c fp heap_words;
    HA.agree_fl_chain_terminates s2 c fp heap_words;
    GenInv.free_list_exact_iff c fp;
    GenInv.free_list_exact_iff s2 fp;
    HA.agree_fl_exact s2 c fp;
    HA.agree_dense s2 c;
    let blk (x: obj_addr)
      : Lemma (Seq.mem x (objects zero_addr c) ==>
               is_blue x s2 == is_blue x c /\ is_black x s2 == is_black x c /\
               is_gray x s2 == is_gray x c /\
               wosize_of_object x s2 == wosize_of_object x c)
      = if Seq.mem x (objects zero_addr c) then HA.agree_block s2 c x
    in
    FStar.Classical.forall_intro blk;
    // link words
    let link (src: obj_addr)
      : Lemma (requires Seq.mem src (objects zero_addr s2) /\ is_blue src s2 /\
                        U64.v (wosize_of_object src s2) >= 1 /\
                        U64.v (hd_address src) + 16 <= heap_size)
              (ensures (let v = read_word s2 src in v = 0UL \/ HeapGraph.is_pointer_field v))
      = HA.agree_field0 s2 c src;
        FreeListShape.blue_link_fields_valid_elim c src
    in
    FreeListShape.blue_link_fields_valid_intro s2 link;
    // nothing live on the free list
    reveal_opaque (`%Promote.chain_objects_blue) (Promote.chain_objects_blue c fp);
    reveal_opaque (`%Promote.chain_objects_blue) (Promote.chain_objects_blue s2 fp);
    let avoid (obj: obj_addr)
      : Lemma (requires Seq.mem obj (objects zero_addr s2) /\ ~(is_blue obj s2))
              (ensures AllocLemmas.chain_avoids s2 fp obj heap_words = true)
      = HA.agree_chain_avoids s2 c fp obj heap_words
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires avoid);
    // colours
    let ng (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr s2)) (ensures ~(is_gray x s2))
      = SweepInv.no_gray_elim x c
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires ng);
    SweepInv.no_gray_intro s2;
    FreeListShape.fp_pointer_or_zero_fl_valid_implies_fp_valid fp s2 heap_words;
    FreeListShape.fp_pointer_or_zero_implies_fp_in_heap fp s2;
    GenInv.major_heap_shape_intro s2 fp
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
let major_gc_restores_major_heap_shape_of_source h_init s2 roots fp final_fp =
  let pick (h_mark: heap)
    : Lemma
      (requires Corr.mark_post h_init h_mark roots fp /\
                (let r = Coalesce.coalesce (fst (Sweep.sweep h_mark fp)) in
                 HA.heaps_agree_mod_free s2 (fst r) /\ final_fp == snd r))
      (ensures GenInv.major_heap_shape s2 final_fp)
    = let r = Coalesce.coalesce (fst (Sweep.sweep h_mark fp)) in
      major_gc_restores_major_heap_shape h_init h_mark roots fp;
      major_heap_shape_agree s2 (fst r) (snd r)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires pick)
#pop-options
