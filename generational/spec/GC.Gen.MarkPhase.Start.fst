module GC.Gen.MarkPhase.Start

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module GenInv = GC.Gen.HeapInvariant
module GI = GC.Gen.Incremental
module GMM = GC.Gen.MarkPhase.Minor
module MP = GC.Spec.MarkPhase
module MB = GC.Impl.MarkBounded
module MBP = GC.Impl.MarkBoundedPrecondition
module GMP = GC.Gen.MajorPrecondition
module MBI = GC.Spec.MarkBoundedInv
module PCS = GC.Gen.PostCollectionShape
module Mark = GC.Spec.Mark
module Promote = GC.Gen.Promote

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

#push-options "--z3rlimit 20"
let roots_grey (g: heap) (fp: U64.t) (rs: seq U64.t)
  : Lemma (requires MBP.darken_precondition g Seq.empty rs fp (Seq.length rs + 1))
          (ensures MP.held_reached (darkened g rs) (GMM.roots_held (darkened g rs) rs))
  = let cap = Seq.length rs + 1 in
    let r = MB.darken_roots_bounded_spec g Seq.empty rs cap in
    let g' = fst r in
    MBP.darken_establishes_precondition g Seq.empty rs fp cap;
    MBP.darken_roots_match_stack g Seq.empty rs fp cap;
    let aux (w: obj_addr)
      : Lemma (requires GMM.roots_held g' rs w) (ensures ~(is_white w g'))
      = eliminate exists (q: U64.t). Seq.mem q rs /\ is_pointer q /\ resolve_object (q <: obj_addr) g' == w
        with begin
          MB.darken_roots_bounded_spec_preserves_resolve g Seq.empty rs cap (q <: obj_addr);
          assert (Seq.mem w (snd r));
          Mark.colors_exclusive w g'
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 30"
let mark_start_shape minor g fp rs =
  let cap = Seq.length rs + 1 in
  let g' = darkened g rs in
  GMP.darken_precondition_of_shape minor g fp rs cap;
  MBP.darken_establishes_precondition g Seq.empty rs fp cap;
  roots_grey g fp rs;
  let st' = snd (MB.darken_roots_bounded_spec g Seq.empty rs cap) in
  assert (MBI.bounded_mark_inv g' st' cap);
  // the major shape at `free_stw`, while marking
  free_stw_ok ();
  Promote.free_stw_allocations_not_free Ph.Marking;
  PCS.free_list_shape_of_ascending g' fp;
  GenInv.major_shape_with_intro Ph.Marking free_stw g' fp;
  // the empty nursery
  GenInv.collection_heap_shape_elim minor g fp;
  GenInv.minor_reset_minor_major_fields_no_blue minor g';
  GenInv.minor_major_fields_not_free_stw minor g';
  GenInv.collection_shape_with_intro Ph.Marking free_stw minor g' fp;
  // the marking invariant: nothing black, and the empty nursery holds nothing
  MP.no_black_tri_color g';
  FStar.Classical.forall_intro (GMM.nursery_held_reset minor);
  MP.marking_inv_start g' (GMM.nursery_held minor);
  GI.phase_shape_marking minor g' fp
#pop-options
