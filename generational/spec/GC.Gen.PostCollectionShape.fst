/// ---------------------------------------------------------------------------
/// GC.Gen.PostCollectionShape -- the collector re-establishes `major_heap_shape`
/// ---------------------------------------------------------------------------
///
/// `GC.Spec.CollectLists.gc_coalesce_source_lists` relates the collector's
/// heap and lists to `coalesce (sweep h_mark 0UL)` for a correct mark
/// `h_mark`: the heap agrees with the coalesced one modulo free blocks' bodies
/// and link words, and the lists are the coalescer's one list split by class.
/// The heap-wide facts transfer through the agreement; the facts about the
/// lists are `gc_coalesce_source_lists_facts`.

module GC.Gen.PostCollectionShape

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module FLs = GC.Spec.FreeLists
module SC = GC.Spec.SizeClass
module CL = GC.Spec.CollectLists
module Corr = GC.Spec.Correctness
module Sweep = GC.Spec.Sweep
module SweepInv = GC.Spec.SweepInv
module Mark = GC.Spec.Mark
module Coalesce = GC.Spec.Coalesce
module Shape = GC.Spec.Coalesce.Shape
module CDense = GC.Spec.Coalesce.Dense
module FreeListShape = GC.Gen.FreeListShape
module Promote = GC.Gen.Promote
module GenInv = GC.Gen.HeapInvariant
module HA = GC.Spec.HeapAgree
module HeapGraph = GC.Spec.HeapGraph

#set-options "--fuel 0 --ifuel 0 --z3rlimit 60"

#push-options "--fuel 1 --ifuel 1 --z3rlimit 80"
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

/// The heap-wide part of the shape, carried from the coalesced heap `c` to a
/// heap that agrees with it modulo free blocks' bodies and links.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
private let heap_facts (g s2: heap)
  : Lemma
    (requires
      Coalesce.post_sweep_strong g /\
      heap_objects_dense g /\
      Seq.length (objects zero_addr g) > 0 /\
      HA.heaps_agree_mod_free_links s2 (fst (Coalesce.coalesce g)))
    (ensures well_formed_heap s2 /\
             heap_objects_dense s2 /\
             Seq.length (objects zero_addr s2) > 0 /\
             Mark.no_black_objects s2 /\
             SweepInv.no_gray_objects s2 /\
             Mark.no_pointer_to_blue s2)
  = let c = fst (Coalesce.coalesce g) in
    Coalesce.coalesce_preserves_wf g;
    CDense.coalesce_dense g;
    coalesced_no_black_no_gray g;
    Shape.coalesce_no_pointer_to_blue g;
    HA.agree_objects_links s2 c;
    HA.agree_well_formed_heap_links s2 c;
    HA.agree_no_pointer_to_blue_links s2 c;
    HA.agree_dense_links s2 c;
    let blk (x: obj_addr)
      : Lemma (Seq.mem x (objects zero_addr c) ==>
               is_black x s2 == is_black x c /\ is_gray x s2 == is_gray x c)
      = if Seq.mem x (objects zero_addr c) then HA.agree_block_links s2 c x
    in
    FStar.Classical.forall_intro blk;
    let ng (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr s2)) (ensures ~(is_gray x s2))
      = SweepInv.no_gray_elim x c
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires ng);
    SweepInv.no_gray_intro s2
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
let major_gc_restores_major_heap_shape_of_source h_init s2 roots fls =
  CL.gc_coalesce_source_lists_facts h_init s2 roots fls;
  let pick (h_mark: heap)
    : Lemma
      (requires Corr.mark_post h_init h_mark roots 0UL /\
                (let r = Coalesce.coalesce (fst (Sweep.sweep h_mark 0UL)) in
                 HA.heaps_agree_mod_free_links s2 (fst r) /\
                 CL.fls_of_chain s2 fls (fst r) (snd r)))
      (ensures well_formed_heap s2 /\
               heap_objects_dense s2 /\
               Seq.length (objects zero_addr s2) > 0 /\
               Mark.no_black_objects s2 /\
               SweepInv.no_gray_objects s2 /\
               Mark.no_pointer_to_blue s2)
    = let g = fst (Sweep.sweep h_mark 0UL) in
      Corr.sweep_post_sweep_strong_gen h_init h_mark roots 0UL;
      Corr.coalesce_precondition_bridge_gen h_init h_mark roots 0UL;
      heap_facts g s2
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires pick);
  // the free lists
  GenInv.free_list_exact_iff s2 fls;
  FreeListShape.fls_pointer_or_zero_iff fls;
  FreeListShape.blue_link_fields_valid_intro s2 (fun src -> ());
  reveal_opaque (`%Promote.chain_objects_blue) (Promote.chain_objects_blue s2 fls);
  FreeListShape.fls_pointer_or_zero_implies_fp_valid fls s2;
  GenInv.major_heap_shape_intro s2 fls
#pop-options
