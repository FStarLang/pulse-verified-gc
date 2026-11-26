/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Snapshot - a cycle frees exactly the garbage at its start
/// ---------------------------------------------------------------------------
///
/// **Snapshot at the beginning**, for a whole cycle of an arbitrary run (any
/// interleaving of program and collector events, any slice budgets): of the
/// objects that have a block when the cycle starts, the cycle frees exactly
/// those the program could not reach at its start.  That is exactly what a
/// stop-the-world collection at the start would free.
///
///   * Nothing reachable at the start is freed (the snapshot): an object
///     reachable when the cycle starts still has a block when it ends, even
///     if the program dropped it in between.
///   * Everything unreachable at the start is freed
///     (`GC.Gen.Run.FloatingGarbage.floating_garbage_freed`).
///
/// Objects are ideal ids (allocation numbers), shared by every run of the
/// same program, so "which objects have a block" compares across runs: a
/// run and its hoisted run (`GC.Gen.Run.Step.hoist`, each cycle collected
/// stop-the-world right after its start) free the same objects during the
/// cycle (`snapshot_hoisted`).
///
/// The proof is address-free: the start of the cycle makes the accounting's
/// kept set (`GC.Gen.Run.IdAccounting`) what the program can reach; no other
/// cycle starts, so until the cycle ends the kept set only grows; idle, the
/// objects with a block are exactly the accounting's
/// (`GC.Gen.Run.Hoisted.ids_at_idle`).
///
/// A point of a run is a run `rn1` that the rest of the run, `rn2`, extends
/// (`GC.Gen.Run.FloatingGarbage.run_append rn1 rn2`).
module GC.Gen.Run.Snapshot

open FStar.List.Tot
open GC.Gen.Run.Step
open GC.Model.Represents
open GC.Gen.Run.Simulation
open GC.Gen.Run.FloatingGarbage

module Ph = GC.Spec.Phase
module I = GC.Model.Ideal

/// **One whole cycle's events**: they begin with the cycle's start and
/// start no other cycle.  (A run whose events these are and that ends idle
/// has carried that cycle to its end, and only it.)
let one_cycle (es: list event) : bool =
  match es with
  | StartCycle _ :: rest -> not (starts_a_cycle rest)
  | _ -> false

/// **Snapshot at the beginning.**  The run carries out a well-formed
/// program `ps1 @ ps2`, its part `rn1` (to the cycle's start) carrying out
/// `ps1`.  The rest of the run, `rn2`, is one whole cycle and ends idle.
/// Then an object with a block at the cycle's start has none at its end
/// exactly when the program could not reach it at the start.
val snapshot_at_the_beginning
      (#es1: list event) (#r1: real_state) (rn1: run (initial_state ()) es1 r1)
      (#es2: list event) (#r2: real_state) (rn2: run r1 es2 r2)
      (ps1 ps2: list I.program_event) (id: I.obj_id)
  : Lemma (requires I.wf_program (ps1 @ ps2) /\ executes rn1 ps1 /\ executes (run_append rn1 rn2) (ps1 @ ps2) /\
                    one_cycle es2 /\ r2.phase == Ph.Idle /\ ~(no_block rn1 id))
          (ensures no_block (run_append rn1 rn2) id <==> ~(I.reachable (I.ideal_run ps1) id))

/// **The snapshot direction alone**: an object reachable when the cycle
/// starts has a block when it ends (no hypothesis on its block at the start).
val reachable_at_start_survives
      (#es1: list event) (#r1: real_state) (rn1: run (initial_state ()) es1 r1)
      (#es2: list event) (#r2: real_state) (rn2: run r1 es2 r2)
      (ps1 ps2: list I.program_event) (id: I.obj_id)
  : Lemma (requires I.wf_program (ps1 @ ps2) /\ executes rn1 ps1 /\ executes (run_append rn1 rn2) (ps1 @ ps2) /\
                    one_cycle es2 /\ r2.phase == Ph.Idle /\ I.reachable (I.ideal_run ps1) id)
          (ensures ~(no_block (run_append rn1 rn2) id))

/// Hoisting commutes with cutting a schedule: the hoisted run of
/// `rn1` then `rn2` is the hoisted `rn1` then the hoisted `rn2`.
val hoist_append (ks1 ks2: list kind)
  : Lemma (hoist (ks1 @ ks2) == hoist ks1 @ hoist ks2)

/// **The incremental cycle frees what its hoisted run frees.**  Two runs
/// carry out the same program, cut at the start of a cycle as in
/// `snapshot_at_the_beginning`; up to the cut, the second (`rnh1`) is the
/// hoisted run of the first (`hoist_append`); after it, `rnh2` is any whole
/// cycle carrying out the same events -- in particular the hoisted cycle,
/// collected stop-the-world right after its start.  An object with a block
/// at the cycle's start in the first has one in the second too, and the
/// cycle frees it in the first exactly when it does in the second.
val snapshot_hoisted
      (#es1: list event) (#r1: real_state) (rn1: run (initial_state ()) es1 r1)
      (#es2: list event) (#r2: real_state) (rn2: run r1 es2 r2)
      (#eh1: list event) (#sh1: real_state) (rnh1: run (initial_state ()) eh1 sh1)
      (#eh2: list event) (#sh2: real_state) (rnh2: run sh1 eh2 sh2)
      (ps1 ps2: list I.program_event) (id: I.obj_id)
  : Lemma (requires I.wf_program (ps1 @ ps2) /\
                    executes rn1 ps1 /\ executes (run_append rn1 rn2) (ps1 @ ps2) /\
                    one_cycle es2 /\ r2.phase == Ph.Idle /\
                    executes rnh1 ps1 /\ executes (run_append rnh1 rnh2) (ps1 @ ps2) /\
                    one_cycle eh2 /\ sh2.phase == Ph.Idle /\
                    kinds eh1 == hoist (kinds es1) /\
                    ~(no_block rn1 id))
          (ensures ~(no_block rnh1 id) /\
                   (no_block (run_append rn1 rn2) id <==> no_block (run_append rnh1 rnh2) id))
