/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Invariant.SweepSlice - the run invariant across a sweep slice
/// ---------------------------------------------------------------------------

module GC.Gen.Run.Invariant.SweepSlice

open GC.Spec.Base
open GC.Gen.Run.Step
open GC.Gen.Run.History
open GC.Gen.Run.Invariant.Defs

module Ph = GC.Spec.Phase

/// **A slice of the sweep keeps it**, mid-sweep or at its end.
val slice_keeps_sweeping (r: real_state) (h: cycle_history) (budget: nat) (r': real_state)
  : Lemma (requires run_invariant r h /\ step r (Slice budget) r' /\ Ph.Sweeping? r.phase)
          (ensures run_invariant r' (update_history h r (Slice budget) r'))
