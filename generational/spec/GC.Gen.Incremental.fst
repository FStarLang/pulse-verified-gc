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
module ST = GC.Gen.SweptTail
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

/// The cross-generation condition carries over to a heap in which every block
/// non-free under `free` before is non-free under `free'`.
let fields_not_free_transport (minor: minor_state) (g g': heap) (free free': free_def)
  : Lemma (requires GenInv.minor_major_fields_not_free free minor g /\
                    (forall (x: obj_addr). in_use free g x ==> in_use free' g' x))
          (ensures GenInv.minor_major_fields_not_free free' minor g')
  = GenInv.minor_major_fields_not_free_intro free' minor g'
      (fun obj j -> GenInv.minor_major_fields_not_free_elim free minor g obj j)

let phase_shape_collection minor g fp ph =
  match ph with
  | Ph.Idle ->
      phase_shape_idle minor g fp;
      GenInv.collection_heap_shape_as_free_stw minor g fp;
      assert_norm (phase_free Ph.Idle == free_stw);
      assert (ST.phase_at ph g == ph)
  | Ph.Sweeping st ->
      phase_shape_sweeping minor g fp st;
      SPM.sweep_collection_shape minor g fp st;
      sweep_phase_inv_elim g fp st;
      FSI.tail_ok_elim g (U64.v st.cursor) st.swept_tail;
      ST.phase_at_self ph g;
      assert_norm (phase_free (Ph.Sweeping st) == free_incremental st)

let phase_shape_start minor g fp =
  SPM.sweep_major_shape g fp sweep_start;
  GenInv.collection_shape_with_after_minor_reset (Ph.Sweeping sweep_start) (free_incremental sweep_start) minor g fp;
  GenInv.collection_shape_with_elim (Ph.Sweeping sweep_start) (free_incremental sweep_start) (minor_reset minor) g fp;
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
  // nothing is pending free, so the cross-generation condition is the idle one
  fields_not_free_transport minor g g (free_incremental st) free_stw;
  GenInv.minor_major_fields_not_free_stw minor g;
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
      fields_not_free_transport minor g g' (free_incremental st) (free_incremental st');
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
  let free = free_incremental st in
  let res = SPM.collect_at st minor g fp roots in
  let st' = SPM.state_after st res.Promote.mc_major in
  GenInv.collection_shape_with_elim (Ph.Sweeping st) free res.Promote.mc_minor res.Promote.mc_major res.Promote.mc_fp;
  fields_not_free_transport res.Promote.mc_minor res.Promote.mc_major res.Promote.mc_major
    free (free_incremental st');
  phase_shape_sweeping res.Promote.mc_minor res.Promote.mc_major res.Promote.mc_fp st'
#pop-options

let phase_free_idle () = assert_norm (phase_free Ph.Idle == free_stw)

let phase_free_sweeping st = assert_norm (phase_free (Ph.Sweeping st) == free_incremental st)
