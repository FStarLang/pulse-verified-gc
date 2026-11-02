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

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

let phase_shape_idle minor g fp = reveal_opaque (`%phase_shape) (phase_shape minor g fp Ph.Idle)

let phase_shape_sweeping minor g fp st =
  reveal_opaque (`%phase_shape) (phase_shape minor g fp (Ph.Sweeping st))

/// The cross-generation condition carries over to a heap with at least the
/// same not-freed objects.
let fields_not_freed_transport (minor: minor_state) (g g': heap) (pf pf': obj_addr -> prop)
  : Lemma (requires GenInv.minor_major_fields_not_freed minor g pf /\
                    (forall (x: obj_addr). not_freed g pf x ==> not_freed g' pf' x))
          (ensures GenInv.minor_major_fields_not_freed minor g' pf')
  = GenInv.minor_major_fields_not_freed_intro minor g' pf'
      (fun obj j -> GenInv.minor_major_fields_not_freed_elim minor g pf obj j)

let phase_shape_collection minor g fp ph =
  match ph with
  | Ph.Idle ->
      phase_shape_idle minor g fp;
      GenInv.collection_heap_shape_no_pending minor g fp;
      assert_norm (phase_pending g Ph.Idle == no_pending);
      assert (Paint.phase_at ph g == ph)
  | Ph.Sweeping st ->
      phase_shape_sweeping minor g fp st;
      SPM.sweep_collection_shape minor g fp st;
      sweep_phase_inv_elim g fp st;
      FSI.tail_ok_elim g (U64.v st.cursor) st.swept_tail;
      Paint.phase_at_self ph g;
      assert_norm (phase_pending g (Ph.Sweeping st) == pending g st)

let phase_shape_start minor g fp =
  SPM.sweep_major_shape g fp sweep_start;
  GenInv.collection_shape_except_after_minor_reset minor g fp (pending g sweep_start);
  GenInv.collection_shape_except_elim (minor_reset minor) g fp (pending g sweep_start);
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
  // nothing is pending, so the cross-generation condition is the idle one
  fields_not_freed_transport minor g g (pending g st) no_pending;
  GenInv.minor_major_fields_not_freed_no_pending minor g;
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
      fields_not_freed_transport minor g g' (pending g st) (pending g' st');
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
  let (res, ph') = CA.cheney_collect_spec_except_at (Ph.Sweeping st) minor g fp roots (pending g st) in
  let st' = SPM.state_after st (Cheney.cheney_collect_spec_except minor g fp roots (pending g st)).Promote.mc_major in
  GenInv.collection_shape_except_elim res.Promote.mc_minor res.Promote.mc_major res.Promote.mc_fp (pending g st);
  fields_not_freed_transport res.Promote.mc_minor res.Promote.mc_major res.Promote.mc_major
    (pending g st) (pending res.Promote.mc_major st');
  phase_shape_sweeping res.Promote.mc_minor res.Promote.mc_major res.Promote.mc_fp st'
#pop-options

let phase_pending_idle g = assert_norm (phase_pending g Ph.Idle == no_pending)

let phase_pending_sweeping g st = assert_norm (phase_pending g (Ph.Sweeping st) == pending g st)
