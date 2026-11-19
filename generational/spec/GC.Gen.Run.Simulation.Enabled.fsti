/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Simulation.Enabled - a well-formed program's step can be taken
/// ---------------------------------------------------------------------------
///
/// What `GC.Gen.Run.Simulation.program_step_enabled` and the program steps'
/// preservation lemmas need of a value the program stores: that its real
/// word is one the runtime may store (`storable_value`: the obligations the
/// barrier, the initialising writes and the nursery trust today) and that it
/// points at a kept block (`in_kept`).  Both follow from the invariant,
/// `represents`, the value being usable, and the trusted layout of the
/// event's words (`GC.Model.Represents.word_layout`).  An infix pointer is
/// resolved through its infix header, which `GC.Model.Ideal.valid_value`
/// makes name the offset, of at least two words (stage 0e) -- what the real
/// heap's `infix_addr_conds` asks.  Mid-sweep, a kept block is not pending
/// free: stage 0b's sweeping clause (`kept_not_pending_holds`).

module GC.Gen.Run.Simulation.Enabled

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Gen.Run.Step
open GC.Gen.Run.History
open GC.Gen.Run.Invariant
open GC.Model.Represents
open GC.Gen.Run.Simulation.Program

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module SPI = GC.Spec.SweepPhase.Intrinsic
module SA = GC.Spec.Allocator
module AC = GC.Spec.Allocator.Cursor
module GBase = GC.Gen.Base
module I = GC.Model.Ideal

/// Mid-sweep, no kept block is pending free.
let kept_not_pending (r: real_state) (h: cycle_history) : prop =
  match r.phase with
  | Ph.Sweeping c -> forall (x: obj_addr). kept h x /\ is_allocated r.memory (Major x) ==>
                       ~(SPI.pending_free c r.memory.major x)
  | _ -> True

/// `GC.Gen.Run.Simulation.room_for`, verbatim.
let room_for (r: real_state) (e: event) : prop =
  match e with
  | Alloc InNursery _ size _ -> size <= GBase.max_young_wosize /\ minor_can_alloc r.memory.nursery size
  | Alloc InMajor tag size _ -> (AC.alloc_phase r.memory.major r.free_list r.phase size tag).SA.obj_out <> 0UL
  | _ -> True

/// Mid-sweep, no kept block is pending free: the invariant's sweeping
/// clause.
val kept_not_pending_holds (r: real_state) (h: cycle_history)
  : Lemma (requires run_invariant r h) (ensures kept_not_pending r h)

/// A block holding a reachable object is not free at the phase.
val reachable_in_use (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (x: obj_addr) (id: I.obj_id)
  : Lemma (requires sim_inv_parts r h im ids /\
                    ids (Major x) == Some id /\ I.reachable im id)
          (ensures in_use (GC.Gen.Incremental.phase_free r.phase) r.memory.major x)

/// **A value the program can use is storable, and points at a kept block.**
val usable_storable (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (v: I.value) (w: U64.t)
  : Lemma (requires sim_inv_parts r h im ids /\
                    I.usable im v /\ value_rep ids v w /\ word_layout ids v w)
          (ensures storable_value r w /\ in_kept r h w)

/// **`GC.Gen.Run.Simulation.program_step_enabled`.**
val program_step_enabled (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (e: event) (pe: I.program_event)
  : Lemma (requires sim_inv_parts r h im ids /\ I.wf_event im pe /\ translates r.memory ids e pe /\ room_for r e)
          (ensures exists (r': real_state). step r e r')

/// **What a well-formed program's step stores points at kept blocks**
/// (`stores_in_kept`, the hypothesis of the run invariant's program-step
/// lemmas).
val stores_in_kept_given (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (e: event) (pe: I.program_event)
  : Lemma (requires sim_inv_parts r h im ids /\ I.wf_event im pe /\ translates r.memory ids e pe)
          (ensures stores_in_kept r h e)
