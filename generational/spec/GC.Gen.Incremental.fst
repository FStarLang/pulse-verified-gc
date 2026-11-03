module GC.Gen.Incremental

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.SweepPhase.Intrinsic
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module GenInv = GC.Gen.HeapInvariant
module SL = GC.Spec.SweepPhase.Slice
module CA = GC.Gen.CheneyAt
module Paint = GC.Gen.Paint
module Cheney = GC.Gen.Cheney
module Promote = GC.Gen.Promote
module SPM = GC.Gen.SweepPhase.Minor
module SPE = GC.Spec.SweepPhase.Intrinsic.End
module FSI = GC.Spec.FusedSweep.Inv
module PCS = GC.Gen.PostCollectionShape
module Mark = GC.Spec.Mark
module SweepInv = GC.Spec.SweepInv
module Util = GC.Spec.SweepPhase.Util
module CV = GC.Gen.CheneyView

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

let phase_shape_idle minor g fp = reveal_opaque (`%phase_shape) (phase_shape minor g fp Ph.Idle)

let phase_shape_sweeping minor g fp st =
  reveal_opaque (`%phase_shape) (phase_shape minor g fp (Ph.Sweeping st))

/// The cross-generation condition carries over to a heap whose view counts
/// at least the blocks the view counted before.
let fields_in_view_transport (minor: minor_state) (g g': heap) (v v': view)
  : Lemma (requires GenInv.minor_major_fields_in_view v minor g /\
                    (forall (x: obj_addr). v g x ==> v' g' x))
          (ensures GenInv.minor_major_fields_in_view v' minor g')
  = GenInv.minor_major_fields_in_view_intro v' minor g'
      (fun obj j -> GenInv.minor_major_fields_in_view_elim v minor g obj j)

let phase_shape_collection minor g fp ph =
  match ph with
  | Ph.Idle ->
      phase_shape_idle minor g fp;
      GenInv.collection_heap_shape_as_view minor g fp;
      assert_norm (phase_view g Ph.Idle == allocated);
      assert (Paint.phase_at ph g == ph)
  | Ph.Sweeping st ->
      phase_shape_sweeping minor g fp st;
      SPM.sweep_collection_shape minor g fp st;
      sweep_phase_inv_elim g fp st;
      FSI.tail_ok_elim g (U64.v st.cursor) st.swept_tail;
      Paint.phase_at_self ph g;
      assert_norm (phase_view g (Ph.Sweeping st) == surviving_from st g)

let phase_view_ok minor g fp roots ph =
  match ph with
  | Ph.Idle ->
      assert_norm (phase_view g Ph.Idle == allocated);
      CV.allocated_promotion_in_view minor g fp roots;
      Paint.allocated_colour_blind ()
  | Ph.Sweeping st ->
      assert_norm (phase_view g (Ph.Sweeping st) == surviving_from st g);
      surviving_from_fresh st g (Cheney.cheney_promote minor g fp roots).Promote.major_final;
      Paint.surviving_from_colour_blind st g

let phase_shape_start minor g fp =
  SPM.sweep_major_shape g fp sweep_start;
  GenInv.collection_shape_view_after_minor_reset (surviving sweep_start) minor g fp;
  GenInv.collection_shape_view_elim (surviving sweep_start) (minor_reset minor) g fp;
  phase_shape_sweeping (minor_reset minor) g fp sweep_start

#push-options "--z3rlimit 20"
let sweep_end_shape minor g fp st =
  phase_shape_sweeping minor g fp st;
  SPE.sweep_phase_end g fp st;
  PCS.free_list_shape_of_ascending g fp;
  let col (x: obj_addr)
    : Lemma (Seq.mem x (objects zero_addr g) ==> ~(is_black x g) /\ ~(is_gray x g))
    = if Seq.mem x (objects zero_addr g) then Mark.colors_exclusive x g
  in
  FStar.Classical.forall_intro col;
  SweepInv.no_gray_intro g;
  GenInv.major_heap_shape_intro g fp;
  // nothing is condemned, so the cross-generation condition is the idle one
  fields_in_view_transport minor g g (surviving st) allocated;
  GenInv.minor_major_fields_in_view_allocated minor g;
  GenInv.collection_heap_shape_intro minor g fp
#pop-options

#push-options "--z3rlimit 20"
let phase_slice_shape minor g fp ph budget =
  match ph with
  | Ph.Idle -> ()
  | Ph.Sweeping st ->
      phase_shape_sweeping minor g fp st;
      SL.sweep_slice_phase g fp st budget;
      let (g', fp', st') = SL.sweep_slice g fp st budget in
      fields_in_view_transport minor g g' (surviving st) (surviving st');
      phase_shape_sweeping minor g' fp' st';
      if sweep_done st' then begin
        sweep_end_shape minor g' fp' st';
        phase_shape_idle minor g' fp'
      end
#pop-options

let phase_slice_finishes minor g fp ph budget =
  match ph with
  | Ph.Idle -> ()
  | Ph.Sweeping st ->
      phase_shape_sweeping minor g fp st;
      SL.sweep_slice_phase g fp st budget

#push-options "--z3rlimit 20"
let minor_keeps_phase_shape minor g fp st roots =
  phase_shape_sweeping minor g fp st;
  SPM.minor_keeps_sweep_phase minor g fp st roots;
  let v = surviving_from st g in
  let (res, ph') = CA.cheney_collect_spec_view_at (Ph.Sweeping st) v minor g fp roots in
  let st' = SPM.state_after st (Cheney.cheney_collect_spec_view v minor g fp roots).Promote.mc_major in
  GenInv.collection_shape_view_elim v res.Promote.mc_minor res.Promote.mc_major res.Promote.mc_fp;
  fields_in_view_transport res.Promote.mc_minor res.Promote.mc_major res.Promote.mc_major
    v (surviving st');
  phase_shape_sweeping res.Promote.mc_minor res.Promote.mc_major res.Promote.mc_fp st'
#pop-options

let phase_view_idle g = assert_norm (phase_view g Ph.Idle == allocated)

let phase_view_sweeping g st = assert_norm (phase_view g (Ph.Sweeping st) == surviving_from st g)
