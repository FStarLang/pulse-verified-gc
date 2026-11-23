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
/// makes name the offset, of at least two words -- what the real heap's
/// `infix_addr_conds` asks.  Mid-sweep, a kept block is not pending free:
/// the run invariant's sweeping clause (`kept_not_pending_holds`).

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

/// The state a nursery allocation leaves (`nursery_alloc_step`).
let nursery_after_alloc (r: real_state) (tag: I.tag_t) (size: nat{size > 0 /\ size <= GBase.max_young_wosize})
    (init: seq U64.t) : GTot minor_state =
  let t = if U64.v tag = 249 then 0 else U64.v tag in
  let res = minor_alloc_spec r.memory.nursery size t in
  { res.ms_out with data = write_nursery_fields res.ms_out.data res.obj_addr init 0 }

/// The state a nursery store leaves (`nursery_write_step`).
let nursery_after_store (r: real_state) (o: U64.t) (i: nat) (v: U64.t) : minor_state =
  let ms = r.memory.nursery in
  { ms with data = minor_write_word_t ms.data (nursery_slot o i) v }

/// **What the nursery steps trust**, which a well-formed program does
/// not give: the nursery after the step has the frame -- in particular its
/// shape, `GenInv.minor_heap_shape`, the trusted mutator obligation -- and
/// no major interior (infix) pointer is stored into a scannable nursery
/// object (`nursery_storable`, a known provisional restriction of 0d,
/// pending the decision on lifting it).  A hypothesis of
/// `GC.Gen.Run.Simulation.program_step_enabled`: the nursery steps are on
/// the trusted boundary.
let nursery_trusted (r: real_state) (e: event) : prop =
  match e with
  | Alloc InNursery tag size init ->
      (I.tag_scannable tag ==>
         (forall (j: nat). j < Seq.length init ==>
            (is_pointer (Seq.index init j) ==> ~(is_infix (Seq.index init j <: obj_addr) r.memory.major)))) /\
      (size > 0 /\ size <= GBase.max_young_wosize /\ U64.v tag <> 249 ==>
         nursery_alloc_frame r.memory.nursery (nursery_after_alloc r tag size init)
           (minor_alloc_spec r.memory.nursery size (U64.v tag)).obj_addr (U64.v tag) init)
  | Write (Nursery o) i v ->
      (minor_tag r.memory.nursery o < 251 ==> (is_pointer v ==> ~(is_infix (v <: obj_addr) r.memory.major))) /\
      nursery_store_frame r.memory.nursery (nursery_after_store r o i v) o i v
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
                    I.usable im v /\ value_rep ids v w /\ word_layout ids v w)
          (ensures storable_value r w /\ in_kept r h w)

/// **`GC.Gen.Run.Simulation.program_step_enabled`, given what the
/// nursery steps trust (`nursery_trusted`).**
val program_step_enabled_given (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (e: event) (pe: I.program_event)
  : Lemma (requires sim_inv_parts r h im ids /\ I.wf_event im pe /\ translates r.memory ids e pe /\ room_for r e /\
                    nursery_trusted r e)
          (ensures exists (r': real_state). step r e r')

/// **What a well-formed program's step stores points at kept blocks**
/// (`stores_in_kept`, the hypothesis of the run invariant's program-step
/// lemmas).
val stores_in_kept_given (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (e: event) (pe: I.program_event)
  : Lemma (requires sim_inv_parts r h im ids /\ I.wf_event im pe /\ translates r.memory ids e pe)
          (ensures stores_in_kept r h e)
