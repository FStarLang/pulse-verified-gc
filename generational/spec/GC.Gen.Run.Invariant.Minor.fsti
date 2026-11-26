/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Invariant.Minor - the run invariant across a minor collection
/// ---------------------------------------------------------------------------
///
/// A minor collection (`minor_step`) at any phase keeps the run invariant,
/// with the blocks it made (its promoted copies) counted as allocated during
/// the cycle (`update_history`).  Every block that was allocated before is
/// one after, with its header; the walk ends where it did; the nursery and
/// the remembered set are emptied.  The made blocks lie over free words of
/// the heap before, and so does every free block after.

module GC.Gen.Run.Invariant.Minor

open FStar.Seq
open GC.Gen.Run.Step
open GC.Gen.Run.History
open GC.Gen.Run.Invariant.Defs

module U64 = FStar.UInt64

/// **A minor collection keeps the run invariant**, at any phase.
val minor_keeps (r: real_state) (h: cycle_history) (roots: seq U64.t) (r': real_state)
  : Lemma (requires run_invariant r h /\ step r (Minor roots) r')
          (ensures run_invariant r' (update_history h r (Minor roots) r'))
