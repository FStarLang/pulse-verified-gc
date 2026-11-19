/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Invariant.Initial - the run invariant holds at start-up
/// ---------------------------------------------------------------------------
///
/// The initial state (`initial_state`: one free block from `zero_addr` to the
/// end of the heap, the empty nursery, the empty remembered set, idle) with
/// the history before any cycle (`initial_history`: the start memory is the
/// initial memory, no roots, nothing allocated since) satisfies the run
/// invariant.  The snapshot is empty (no roots), nothing is allocated (the
/// only block is blue), so the accounting is vacuous but for coverage, which
/// the start memory being the current memory gives.

module GC.Gen.Run.Invariant.Initial

open GC.Gen.Run.Step
open GC.Gen.Run.History
open GC.Gen.Run.Invariant.Defs

val initial_run_invariant (_: unit) : Lemma (run_invariant (initial_state ()) (initial_history ()))
