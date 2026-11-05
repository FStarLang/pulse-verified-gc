module GC.Gen.MarkPhase.Safety

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module Mark = GC.Spec.Mark
module MP = GC.Spec.MarkPhase
module GI = GC.Gen.Incremental
module GMM = GC.Gen.MarkPhase.Minor
module SPI = GC.Spec.SweepPhase.Intrinsic
module CG = GC.Gen.CombinedGraph
module RBridge = GC.Gen.ReachabilityBridge
module GenInv = GC.Gen.HeapInvariant
module MPC = GC.Spec.MarkPhase.Completeness
module SL = GC.Spec.SweepPhase.Slice
module SPE = GC.Spec.SweepPhase.Intrinsic.End

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// What every phase's state gives: the heap well formed for the phase's
/// definition of free, and the nursery's shape.
let phase_facts (minor: minor_state) (g: heap) (fp: U64.t) (ph: Ph.gc_phase)
  : Lemma (requires GI.phase_shape minor g fp ph)
          (ensures free_def_ok (GI.phase_free ph) /\ well_formed_heap_with (GI.phase_free ph) g /\
                   minor_wf minor /\ GenInv.minor_major_fields_not_free (GI.phase_free ph) minor g)
  = GI.phase_shape_collection minor g fp ph;
    GenInv.collection_shape_with_elim ph (GI.phase_free ph) minor g fp;
    GenInv.major_shape_with_elim ph (GI.phase_free ph) g fp;
    GenInv.minor_heap_shape_elim minor

let cycle_reachable_not_free minor g fp ph roots a =
  phase_facts minor g fp ph;
  RBridge.reachable_not_free (GI.phase_free ph) minor g roots

let handover_roots minor g fp rs =
  GI.phase_shape_marking minor g fp;
  SPI.free_incremental_ok zero_addr;
  wf_with_parts ();
  let one (r: U64.t)
    : Lemma (Seq.mem r rs /\ ~(GC.Gen.Promote.is_minor_pointer r) /\ is_val_addr r ==>
             (is_block g (r <: obj_addr) ==> not (SPI.free_incremental zero_addr g (r <: obj_addr))))
    = if Seq.mem r rs && is_val_addr r then begin
        let ro : obj_addr = r in
        if is_block g ro then begin
          objects_addresses_gt_start zero_addr g ro;
          RBridge.aligned_gt_ge_plus_mword (U64.v ro) (U64.v zero_addr);
          resolve_non_infix ro g;
          assert (GMM.roots_held g rs ro);
          if is_white ro g then MP.marker_will_reach_elim g ro
        end
      end
  in
  FStar.Classical.forall_intro one

#push-options "--ifuel 1"
let cycle_slice_keeps minor g fp ph budget g' fp' ph' x =
  match ph with
  | Ph.Marking ->
      GI.phase_shape_marking minor g fp;
      GI.phase_free_marking ();
      MPC.mark_steps_keep_blocks g g';
      (match ph' with
       | Ph.Marking -> ()
       | Ph.Sweeping c -> GI.phase_free_sweeping c; SPI.free_incremental_ok c
       | Ph.Idle -> ())
  | Ph.Idle ->
      GI.phase_free_idle ()
  | Ph.Sweeping c ->
      GI.phase_shape_sweeping minor g fp c;
      GI.phase_free_sweeping c;
      SPI.free_incremental_ok c;
      free_def_ok_elim (SPI.free_incremental c);
      SL.sweep_slice_phase g fp c budget;
      let (g1, fp1, st1) = SL.sweep_slice g fp (SPI.state_at g c) budget in
      let c1 = st1.GC.Spec.FusedSweep.cursor in
      SPI.free_incremental_ok c1;
      free_def_ok_elim (SPI.free_incremental c1);
      if SPI.sweep_done c1 then GI.phase_free_idle ()
      else GI.phase_free_sweeping c1
#pop-options

let slice_keeps_reachable minor g fp ph budget g' fp' ph' roots a =
  cycle_reachable_not_free minor g fp ph roots a;
  cycle_slice_keeps minor g fp ph budget g' fp' ph' (a <: obj_addr)
