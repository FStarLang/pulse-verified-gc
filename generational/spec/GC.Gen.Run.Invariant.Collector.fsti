/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Invariant.Collector - the run invariant across collector steps
/// ---------------------------------------------------------------------------
///
/// Proofs for `GC.Gen.Run.Invariant`'s collector-step lemmas, over the
/// definitions in `GC.Gen.Run.Invariant.Defs`.
///
/// Proved here: the start of a cycle, idle slices, mark slices (staying
/// marking, and the hand-over to the sweep), and `idle_survives`;
/// `idle_lossless` (`idle_lossless_with`, whose `snapshot_in_start` is a
/// clause of B2).  The sweep's slices are in `GC.Gen.Run.Invariant.SweepSlice`, the
/// initial state in `GC.Gen.Run.Invariant.Initial`.

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

open GC.Gen.Run.Invariant.Defs

/// ---------------------------------------------------------------------------
/// The lemmas
/// ---------------------------------------------------------------------------

/// **The start of a cycle establishes the invariant** for the new cycle.
val start_keeps (r: real_state) (h: cycle_history) (roots: seq U64.t) (r': real_state)
  : Lemma (requires run_invariant r h /\ step r (StartCycle roots) r')
          (ensures run_invariant r' (update_history h r (StartCycle roots) r'))

/// **A slice keeps it, idle** (a no-op).
val slice_keeps_idle (r: real_state) (h: cycle_history) (budget: nat) (r': real_state)
  : Lemma (requires run_invariant r h /\ step r (Slice budget) r' /\ r.phase == Ph.Idle)
          (ensures run_invariant r' (update_history h r (Slice budget) r'))

/// **A mark slice that stays marking keeps it.**  (The hand-over to the
/// sweep, and the sweep's slices, are not covered: see the report on
/// `GC.Gen.Run.Invariant.slice_keeps_run_invariant`.)
val slice_keeps_marking (r: real_state) (h: cycle_history) (budget: nat) (r': real_state)
  : Lemma (requires run_invariant r h /\ step r (Slice budget) r' /\
                    r.phase == Ph.Marking /\ r'.phase == Ph.Marking)
          (ensures run_invariant r' (update_history h r (Slice budget) r'))

/// **The slice that hands over to the sweep keeps it.**
val slice_keeps_handover (r: real_state) (h: cycle_history) (budget: nat) (r': real_state)
  : Lemma (requires run_invariant r h /\ step r (Slice budget) r' /\
                    r.phase == Ph.Marking /\ Ph.Sweeping? r'.phase)
          (ensures run_invariant r' (update_history h r (Slice budget) r'))

/// The snapshot's objects are allocated blocks of the start memory (a
/// clause of B2).
let snapshot_in_start (h: cycle_history) : prop =
  forall (x: obj_addr). snapshot h x ==> is_allocated h.start_memory (Major x)

/// **At idle the cycle is lossless, word by word**, given the snapshot's
/// objects are blocks of the start memory.
val idle_lossless_with (r: real_state) (h: cycle_history)
  : Lemma (requires run_invariant r h /\ r.phase == Ph.Idle /\ snapshot_in_start h)
          (ensures forall (p: nat). p < heap_size ==>
                     (reclaimable_at_start h p <==>
                      LL.blue_covered r.memory.major p \/ SPC.new_covered h.allocated_during_cycle r.memory.major p))

/// **At idle, what was reachable survives** (from B2, B3).
val idle_survives (r: real_state) (h: cycle_history)
  : Lemma (requires run_invariant r h /\ r.phase == Ph.Idle)
          (ensures forall (x: obj_addr). snapshot h x ==>
                     is_allocated r.memory (Major x) /\
                     wosize_of_object x r.memory.major == wosize_of_object x h.start_memory.major /\
                     ~(h.allocated_during_cycle x))
