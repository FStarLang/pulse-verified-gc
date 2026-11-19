/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Invariant.Collector - the run invariant across collector steps
/// ---------------------------------------------------------------------------
///
/// Proofs for `GC.Gen.Run.Invariant`'s collector-step lemmas.  The
/// definitions of `GC.Gen.Run.Invariant.{phase_shape, snapshot_accounting,
/// run_invariant}` are repeated here verbatim (suffixed `_`): this module
/// cannot depend on `GC.Gen.Run.Invariant`, whose implementation calls it
/// (F* reports a dependency cycle, error 308).  The two copies are equal by
/// unfolding, which is how `GC.Gen.Run.Invariant` uses the lemmas below.

module GC.Gen.Run.Invariant.Collector

open FStar.Seq
open FStar.List.Tot
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Gen.Run.Step
open GC.Gen.Run.History

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module MP = GC.Spec.MarkPhase
module MPC = GC.Spec.MarkPhase.Completeness
module SPC = GC.Spec.SweepPhase.Completeness
module SA = GC.Spec.Allocator
module AC = GC.Spec.Allocator.Cursor
module LL = GC.Spec.FusedSweep.Lossless
module W = GC.Spec.Walk
module GI = GC.Gen.Incremental
module RT = GC.Gen.RefTable
module GenInv = GC.Gen.HeapInvariant
module I = GC.Model.Ideal

/// ---------------------------------------------------------------------------
/// The invariant (copied)
/// ---------------------------------------------------------------------------

/// **The shape of the real state**, at its phase.
let phase_shape_ (r: real_state) : prop =
  let g = r.memory.major in
  let free = GI.phase_free r.phase in
  GI.phase_shape r.memory.nursery g r.free_list r.phase r.scan_pos /\
  RT.ref_table_covers_with free g r.ref_table (Seq.length r.ref_table) /\
  RT.ref_table_sound_with free g r.ref_table (Seq.length r.ref_table) /\
  W.walk_end g zero_addr + 8 >= heap_size

/// **The snapshot accounting** (B1-B5, and the phase's additions).
let snapshot_accounting_ (r: real_state) (h: cycle_history) : prop =
  let g = r.memory.major in
  let g0 = h.start_memory.major in
  // B1
  MPC.within_snapshot (kept h) g /\
  GenInv.minor_major_fields_not_free (MPC.outside_snapshot (kept h)) r.memory.nursery g /\
  // B2
  (forall (x: obj_addr). snapshot h x ==>
     Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ wosize_of_object x g == wosize_of_object x g0) /\
  // B3
  (forall (x: obj_addr). h.allocated_during_cycle x ==> is_allocated r.memory (Major x) /\ ~(snapshot h x)) /\
  // B4
  (forall (x: obj_addr). is_allocated r.memory (Major x) ==>
     snapshot h x \/ h.allocated_during_cycle x \/ garbage_at_start h x) /\
  // B5
  (forall (p: nat). LL.blue_covered g p \/ SPC.new_covered h.allocated_during_cycle g p ==>
     reclaimable_at_start h p) /\
  (match r.phase with
   | Ph.Marking ->
       MP.outside_refs_reached g r.scan_pos (snapshot h) /\
       (forall (x: obj_addr). h.allocated_during_cycle x ==> is_black x g)
   | Ph.Sweeping c -> MPC.sweep_in_snapshot (kept h) g c
   | Ph.Idle -> forall (x: obj_addr). is_allocated r.memory (Major x) ==> ~(garbage_at_start h x))

/// **The run invariant.**
let run_invariant_ (r: real_state) (h: cycle_history) : prop =
  phase_shape_ r /\ snapshot_accounting_ r h


/// ---------------------------------------------------------------------------
/// The lemmas
/// ---------------------------------------------------------------------------

/// **The start of a cycle establishes the invariant** for the new cycle.
val start_keeps (r: real_state) (h: cycle_history) (roots: seq U64.t) (r': real_state)
  : Lemma (requires run_invariant_ r h /\ step r (StartCycle roots) r')
          (ensures run_invariant_ r' (update_history h r (StartCycle roots) r'))

/// **At idle, what was reachable survives** (from B2, B3).
val idle_survives (r: real_state) (h: cycle_history)
  : Lemma (requires run_invariant_ r h /\ r.phase == Ph.Idle)
          (ensures forall (x: obj_addr). snapshot h x ==>
                     is_allocated r.memory (Major x) /\
                     wosize_of_object x r.memory.major == wosize_of_object x h.start_memory.major /\
                     ~(h.allocated_during_cycle x))
