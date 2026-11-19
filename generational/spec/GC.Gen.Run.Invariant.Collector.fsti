/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Invariant.Collector - the run invariant across collector steps
/// ---------------------------------------------------------------------------
///
/// Proofs for `GC.Gen.Run.Invariant`'s collector-step lemmas, over the
/// definitions in `GC.Gen.Run.Invariant.Defs`.
///
/// Proved: the start of a cycle, an idle slice, a mark slice that stays
/// marking, and `idle_survives`.  False as stated at ab5bad3d (so not proved):
///   * `initial_run_invariant`: `SA.init_heap_spec` writes its block header at
///     `zero_addr` (>= 2048) with wosize `heap_words - 1`, so the block runs
///     past the heap and `objects zero_addr g` is empty: no shape holds.
///   * the hand-over slice: a stale remembered slot in a block left white
///     (unreachable) by marking is sound for `free_stw` but not for
///     `free_incremental zero_addr`, which counts that block as free.
///   * sweep slices: nothing says a kept block past the cursor is black, so
///     a white snapshot object past the cursor satisfies the invariant and
///     is freed by the slice (B2 fails); B5 also needs garbage blocks to keep
///     their start size.
///   * minor collections: a scanned nursery field holding a nursery-looking
///     word that names no nursery object is copied verbatim, so the empty
///     remembered set does not cover the result; and at idle a promoted copy
///     may reuse the address of a block that was garbage at the start, which
///     the idle clause forbids.
///   * `idle_lossless`: `phase_shape` allows the walk to end at
///     `heap_size - 8`; with a start memory whose walk ends at `heap_size`,
///     the last word is reclaimable at the start but covered by no block now.

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

/// **At idle, what was reachable survives** (from B2, B3).
val idle_survives (r: real_state) (h: cycle_history)
  : Lemma (requires run_invariant r h /\ r.phase == Ph.Idle)
          (ensures forall (x: obj_addr). snapshot h x ==>
                     is_allocated r.memory (Major x) /\
                     wosize_of_object x r.memory.major == wosize_of_object x h.start_memory.major /\
                     ~(h.allocated_during_cycle x))
