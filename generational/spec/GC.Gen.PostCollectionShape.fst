module GC.Gen.PostCollectionShape

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module Corr = GC.Spec.Correctness
module SweepInv = GC.Spec.SweepInv
module Mark = GC.Spec.Mark
module AllocLemmas = GC.Spec.Allocator.Lemmas
module FreeListShape = GC.Gen.FreeListShape
module Promote = GC.Gen.Promote
module GenInv = GC.Gen.HeapInvariant
module HeapGraph = GC.Spec.HeapGraph
module FS = GC.Spec.FusedSweep
module FSE = GC.Spec.FusedSweep.End
module FLA = GC.Spec.FreeList.Ascending
module FL = GC.Spec.FreeList

/// The shape invariant, read off the fused sweep's end lemma.
#push-options "--fuel 0 --ifuel 1 --z3rlimit 60"
let major_gc_restores_major_heap_shape major h_mark roots fp =
  let r = FS.fused_sweep_coalesce h_mark fp in
  let g = fst r in
  let fp' = snd r in
  Corr.fused_post_gen major h_mark roots fp;
  FSE.sweep_post_elim h_mark g fp';
  FLA.fl_ascending_valid g fp';
  FLA.fl_ascending_exact g fp';
  GenInv.free_list_exact_iff g fp';
  FLA.fl_ascending_head_cell g fp';
  (if fp' <> 0UL then FLA.fl_cell_facts g fp');
  assert (FreeListShape.fp_pointer_or_zero fp');
  // every free block's link is null or a cell
  let link (src: obj_addr)
    : Lemma (requires Seq.mem src (objects zero_addr g) /\ is_blue src g /\
                      U64.v (wosize_of_object src g) >= 1 /\
                      U64.v (hd_address src) + 16 <= heap_size)
            (ensures (let v = read_word g src in v = 0UL \/ HeapGraph.is_pointer_field v))
    = assert (FL.fl_cell g (src <: U64.t));
      FLA.fl_ascending_next_cell g fp' (src <: U64.t);
      let n = FL.fl_next g (src <: U64.t) in
      if n <> 0UL then FLA.fl_cell_facts g n
  in
  FreeListShape.blue_link_fields_valid_intro g link;
  // nothing live is on the list
  reveal_opaque (`%Promote.chain_objects_blue) (Promote.chain_objects_blue g fp');
  let avoid (obj: obj_addr)
    : Lemma (requires Seq.mem obj (objects zero_addr g) /\ ~(is_blue obj g))
            (ensures AllocLemmas.chain_avoids g fp' obj heap_words = true)
    = FLA.fl_ascending_avoids g fp' (obj <: U64.t) heap_words
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires avoid);
  // colours
  let col (x: obj_addr)
    : Lemma (Seq.mem x (objects zero_addr g) ==> ~(is_black x g) /\ ~(is_gray x g))
    = if Seq.mem x (objects zero_addr g) then begin
        FSE.sweep_post_white_or_blue h_mark g fp' x;
        Mark.colors_exclusive x g
      end
  in
  FStar.Classical.forall_intro col;
  SweepInv.no_gray_intro g;
  FreeListShape.fp_pointer_or_zero_fl_valid_implies_fp_valid fp' g heap_words;
  FreeListShape.fp_pointer_or_zero_implies_fp_in_heap fp' g;
  GenInv.major_heap_shape_intro g fp'
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let major_gc_restores_major_heap_shape_of_source h_init s2 roots fp final_fp =
  let pick (h_mark: heap)
    : Lemma
      (requires Corr.mark_post h_init h_mark roots fp /\
                (s2, final_fp) == FS.fused_sweep_coalesce h_mark fp)
      (ensures GenInv.major_heap_shape s2 final_fp)
    = major_gc_restores_major_heap_shape h_init h_mark roots fp
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires pick)
#pop-options
