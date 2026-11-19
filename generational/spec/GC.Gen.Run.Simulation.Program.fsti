/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Simulation.Program - the simulation across the program's steps
/// ---------------------------------------------------------------------------
///
/// The program-step half of `GC.Gen.Run.Simulation`: the joint invariant at
/// the start, across a read or new roots, the allocation count of a run,
/// reads agreeing, and what a well-formed program's step needs of the real
/// state.  `GC.Gen.Run.Simulation` cannot be opened here (it calls these
/// lemmas), so the statements below spell out `sim_inv` and its
/// `reachable_in_kept` clause (`sim_inv_parts`); they are the same
/// definitions, unfolded.

module GC.Gen.Run.Simulation.Program

open FStar.Seq
open FStar.List.Tot
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Gen.Run.Step
open GC.Gen.Run.History
open GC.Gen.Run.Invariant
open GC.Model.Represents

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module I = GC.Model.Ideal

/// `GC.Gen.Run.Simulation.reachable_in_kept`, verbatim.
let reachable_in_kept (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) : prop =
  forall (x: obj_addr) (id: I.obj_id). ids (Major x) == Some id /\ I.reachable im id ==> kept h x

/// `GC.Gen.Run.Simulation.sim_inv`, verbatim.
let sim_inv_parts (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) : prop =
  run_invariant r h /\ represents r h im ids /\ I.wf_memory im /\ I.wf_objects im /\
  reachable_in_kept h im ids

/// ---------------------------------------------------------------------------
/// The ideal side
/// ---------------------------------------------------------------------------

/// **Reachability is the least set closed under the edges**: a set holding
/// what the roots name and closed along the edges holds every reachable
/// object.
val reachable_closed (m: I.ideal_memory) (c: I.obj_id -> prop) (id: I.obj_id)
  : Lemma (requires (forall (r: I.obj_id). I.root_names m r ==> c r) /\
                    (forall (u v: I.obj_id). c u /\ I.points_to m u v ==> c v) /\
                    I.reachable m id)
          (ensures c id)

/// One edge more.
val reachable_step (m: I.ideal_memory) (u v: I.obj_id)
  : Lemma (requires I.reachable m u /\ I.points_to m u v) (ensures I.reachable m v)

/// What a root names is reachable.
val reachable_root (m: I.ideal_memory) (v: I.obj_id)
  : Lemma (requires I.root_names m v) (ensures I.reachable m v)

/// ---------------------------------------------------------------------------
/// The map
/// ---------------------------------------------------------------------------

/// `represents` and `reachable_in_kept` depend on the map only through its
/// values.
val represents_ext (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids ids': block_id_map)
  : Lemma (requires represents r h im ids /\ reachable_in_kept h im ids /\ (forall (b: block_addr). ids' b == ids b))
          (ensures represents r h im ids' /\ reachable_in_kept h im ids')

/// Keeping the entries of the allocated blocks changes nothing.
val restrict_keyed (m: real_memory) (ids: block_id_map) (b: block_addr)
  : Lemma (requires keyed m ids) (ensures restrict m ids b == ids b)

/// ---------------------------------------------------------------------------
/// The lemmas of `GC.Gen.Run.Simulation`
/// ---------------------------------------------------------------------------

/// `GC.Gen.Run.Simulation.initial_sim_inv`.
val initial_sim_inv (_: unit)
  : Lemma (sim_inv_parts (initial_state ()) (initial_history ()) I.empty_ideal empty_ids)

/// `GC.Gen.Run.Simulation.read_roots_keep_sim_inv`.
val read_roots_keep_sim_inv (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (e: event) (pe: I.program_event) (r': real_state)
  : Lemma (requires sim_inv_parts r h im ids /\ I.wf_event im pe /\ translates ids e pe /\ step r e r' /\
                    (Read? e \/ SetRoots? e))
          (ensures sim_inv_parts r' (update_history h r e r') (I.ideal_step im pe)
                     (update_block_ids ids (Seq.length im.I.objects) r e r'))

/// `GC.Gen.Run.Simulation.reads_agree_state`.
val reads_agree_state (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
                      (obj: I.obj_id) (i: nat)
  : Lemma (requires represents r h im ids /\ I.wf_event im (I.Read obj i))
          (ensures exists (b: block_addr). ids b == Some obj /\ is_allocated r.memory b /\
                     i < block_size r.memory b /\
                     content_rep ids (I.field_at (Seq.index im.I.objects obj) i) (block_field r.memory b i))

/// One step of `GC.Gen.Run.Simulation.executes_alloc_count`: a real program
/// step that carries out `pe` adds one object exactly when it allocates.
val step_alloc_count (ids: block_id_map) (r: real_state) (e: event) (r': real_state)
                     (im: I.ideal_memory) (pe: I.program_event)
  : Lemma (requires translates ids e pe /\ step r e r')
          (ensures Seq.length (I.ideal_step im pe).I.objects ==
                   Seq.length im.I.objects + (if Alloc? e then 1 else 0))

val alloc_count_snoc (es: list event) (e: event)
  : Lemma (alloc_count (es @ [e]) == alloc_count es + (if Alloc? e then 1 else 0))
