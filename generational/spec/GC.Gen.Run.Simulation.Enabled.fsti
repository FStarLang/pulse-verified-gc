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
/// event's words (`GC.Model.Represents.word_layout`) -- plus one fact the
/// stage-0c statement still does not provide, made an explicit hypothesis
/// here:
///
///   * **`infix_exact`**: an infix pointer `Ptr { head; k }` has `k <> 1`,
///     i.e. `k >= 2`.  Stage 0c's `GC.Model.Ideal.valid_value` makes the
///     infix header's size `k` (so the real word resolves to the closure),
///     but still allows `k = 1`: field 0 of a closure an infix header of
///     size 1.  The real heap's well-formedness rejects that
///     (`GC.Spec.Object.infix_addr_conds`: `w >= 2`; the nursery's
///     `minor_infix_wf` likewise), so the barrier cannot store such a
///     pointer (`SPI.storable` asks `infix_addr_wf`): with a closure
///     `[Word (infix header, size 1); ...]` reachable and a scannable major
///     object reachable, `Write obj 0 (Ptr { head = closure; infix_offset = 1 })`
///     is well formed but no `step` carries it out.  OCaml never builds it
///     (`Infix_offset_val >= 3` words, `runtime/interp.c`).  The fix is
///     `infix_offset >= 2` in `valid_value`.
///
/// (Stage 0 also lacked "mid-sweep, a kept block is not pending free";
/// stage 0b's sweeping clause -- kept blocks past the cursor are black --
/// gives it: `kept_not_pending_holds`.)

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

/// An infix pointer is at least two words into its closure.
let infix_exact (im: I.ideal_memory) (v: I.value) : prop =
  match v with
  | I.Word _ -> True
  | I.Ptr { infix_offset } -> infix_offset <> 1

/// The values an event stores are `infix_exact`.
let event_infix_exact (im: I.ideal_memory) (pe: I.program_event) : prop =
  match pe with
  | I.Alloc _ _ (I.Scannable vs) -> forall (i: nat). i < Seq.length vs ==> infix_exact im (Seq.index vs i)
  | I.Write _ _ v -> infix_exact im v
  | _ -> True

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
                    I.usable im v /\ infix_exact im v /\ value_rep ids v w /\ word_layout ids v w)
          (ensures storable_value r w /\ in_kept r h w)

/// **`GC.Gen.Run.Simulation.program_step_enabled`, given `infix_exact`.**
val program_step_enabled_given (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (e: event) (pe: I.program_event)
  : Lemma (requires sim_inv_parts r h im ids /\ I.wf_event im pe /\ translates ids e pe /\ room_for r e /\
                    event_infix_exact im pe)
          (ensures exists (r': real_state). step r e r')

/// **What a well-formed program's step stores points at kept blocks**
/// (`stores_in_kept`, the hypothesis of the run invariant's program-step
/// lemmas), given `infix_exact`.
val stores_in_kept_given (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (e: event) (pe: I.program_event)
  : Lemma (requires sim_inv_parts r h im ids /\ I.wf_event im pe /\ translates ids e pe /\
                    event_infix_exact im pe)
          (ensures stores_in_kept r h e)
