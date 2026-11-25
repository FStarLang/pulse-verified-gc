/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Hoisted - the incremental run and its hoisted run
/// ---------------------------------------------------------------------------
///
/// The corollary of the simulation (`GC.Gen.Run.Simulation`): once the incremental collector
/// is idle, the real memory is isomorphic, on every allocated block, to the
/// memory of the hoisted run -- the same program with each cycle's slices
/// moved to right after its start.  Stated here rather than in
/// `GC.Gen.Run.Simulation` because its proof goes through the simulation.
module GC.Gen.Run.Hoisted

open FStar.Seq
open FStar.List.Tot
open GC.Gen.Run.Step
open GC.Gen.Run.History
open GC.Model.Represents
open GC.Gen.Run.Simulation

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module I = GC.Model.Ideal

/// The three facts about the real steps the id-level accounting uses
/// (`GC.Gen.Run.Hoisted.Steps.step_hyps`: the nursery frames, the snapshot of
/// a cycle start, what a minor collection promotes) hold.
val step_hyps_hold (_: unit) : Lemma GC.Gen.Run.Hoisted.Steps.step_hyps

/// **Idle, the objects with a block are those the accounting names**
/// (`GC.Gen.Run.IdAccounting.live_ids`).
val ids_at_idle (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
                (ps: list I.program_event)
  : Lemma (requires I.wf_program ps /\ executes rn ps /\ GC.Gen.Run.Hoisted.Steps.step_hyps /\ r.phase == Ph.Idle)
          (ensures forall (id: I.obj_id). (exists (b: block_addr). ids_of_run rn b == Some id) <==>
                                          GC.Gen.Run.IdAccounting.live_ids ps (kinds es) id)

/// At every point of a run, the objects with a nursery block are the
/// accounting's `nurs`.
val nursery_ids (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
                (ps: list I.program_event)
  : Lemma (requires I.wf_program ps /\ executes rn ps)
          (ensures forall (id: I.obj_id).
                     (GC.Gen.Run.IdAccounting.account GC.Gen.Run.IdAccounting.empty_acc (kinds es) ps).GC.Gen.Run.IdAccounting.nurs id <==>
                     (exists (o: U64.t). ids_of_run rn (Nursery o) == Some id))

/// **The incremental run and its hoisted run are isomorphic** on every
/// allocated block, whenever the incremental collector is idle.  The hoisted
/// run carries out the same program, with the same allocation sites and the
/// same minor collections, but each cycle collects stop-the-world right
/// after its start (`hoist`: its slices moved there, run to the end).  So
/// snapshot-at-the-beginning is a theorem: once a cycle has ended, the
/// incremental collector has left exactly what collecting at the cycle's
/// start would have, plus nothing else.
val hoisted_isomorphic (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
                       (#es_h: list event) (#r_h: real_state) (rn_h: run (initial_state ()) es_h r_h)
                       (ps: list I.program_event)
  : Lemma (requires I.wf_program ps /\ executes rn ps /\ executes rn_h ps /\
                    kinds es_h == hoist (kinds es) /\ r.phase == Ph.Idle)
          (ensures isomorphic r.memory r_h.memory)
