/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Invariant - what every state of a run carries
/// ---------------------------------------------------------------------------
///
/// `run_invariant r h` = `phase_shape r` /\ `snapshot_accounting r h`.
/// Every step keeps it
/// (`step_keeps_run_invariant`, one lemma per kind of step), so by induction
/// it holds at every state of a run (`run_invariant_along`).  Nothing happens
/// between steps: every change is a step.
///
///   * **`phase_shape r`**, about the real state alone: the collector's
///     state at its phase (`GI.phase_shape`: well-formedness, what the colours
///     mean in each phase, the generational shape), the remembered set
///     covering every nursery pointer of a block not free at the phase and
///     naming only such blocks' fields (`RT.ref_table_covers_with`,
///     `RT.ref_table_sound_with`), the heap walk reaching the end of the
///     heap, the nursery's pointers naming nursery objects
///     (`nursery_fields_valid`), and the remembered set empty when the
///     nursery is.  What the Pulse code maintains; proved here by the steps rather
///     than assumed at each call.
///   * **`snapshot_accounting r h`**, how the state relates to the cycle's
///     start (`GC.Gen.Run.History`), with `kept` the snapshot and the blocks
///     allocated since:
///       - B1 (closed): what is dark is kept, and a kept block points only at
///         kept blocks (`MPC.within_snapshot`); the nursery points only at
///         kept blocks; every remembered slot is a field of a kept block;
///       - B2 (kept): every snapshot object was an allocated block of the
///         start memory and still is one, at its size there; so is every garbage block not yet
///         freed (nor its address reused); the walk ends where it did;
///       - B3 (new objects): the blocks allocated since are allocated, and
///         not in the snapshot;
///       - B4 (nothing else): every allocated block is kept or garbage at
///         the start;
///       - B5 (only dead memory reclaimed): every word now free, or in a
///         block allocated since, was in a free or garbage block at the start;
///       - while marking: every white snapshot object is one the marker will
///         reach, and the blocks allocated since are black;
///       - mid-sweep: every block not free at the cursor is kept, and every
///         kept block past the cursor is black;
///       - idle: every allocated block is kept.
///
/// The program's events keep it only if what they store points at kept
/// blocks, and what they write into is kept (`stores_in_kept`): OCaml's type safety, which
/// `GC.Gen.Run.Simulation` derives from the program's well-formedness.
///
/// At idle, the invariant is the incremental cycle's losslessness, per word
/// (`idle_lossless`) and per object (`idle_survives`); over runs,
/// `cycle_lossless` and `cycle_survives`.

module GC.Gen.Run.Invariant

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

include GC.Gen.Run.Invariant.Defs

/// ---------------------------------------------------------------------------
/// What the program's events owe
/// ---------------------------------------------------------------------------

/// (`in_kept`, `stores_in_kept`: in `GC.Gen.Run.Invariant.Defs`.)


/// The same at every step of a run, from the history `h0`.
let rec stores_in_kept_along (h0: cycle_history) (#r0: real_state) (#es: list event) (#r1: real_state)
                             (rn: run r0 es r1)
  : GTot prop (decreases rn) =
  match rn with
  | Done _ -> True
  | Step #_ #_ #r1' rn' e _ _ -> stores_in_kept_along h0 rn' /\ stores_in_kept r1' (history_along h0 rn') e

/// ---------------------------------------------------------------------------
/// The initial state, and every step
/// ---------------------------------------------------------------------------

/// **The initial state carries it**, with the initial history.
val initial_run_invariant (_: unit)
  : Lemma (run_invariant (initial_state ()) (initial_history ()))

/// **An allocation keeps it** (nursery or major), the new major block among
/// the blocks allocated since.
val alloc_keeps_run_invariant (r: real_state) (h: cycle_history)
    (site: alloc_site) (tag: I.tag_t) (size: nat) (init: seq U64.t) (r': real_state)
  : Lemma (requires run_invariant r h /\ stores_in_kept r h (Alloc site tag size init) /\
                    step r (Alloc site tag size init) r')
          (ensures run_invariant r' (update_history h r (Alloc site tag size init) r'))

/// **A write keeps it** (the barrier, a raw no-scan store, or a nursery
/// store).
val write_keeps_run_invariant (r: real_state) (h: cycle_history)
    (b: block_addr) (i: nat) (v: U64.t) (r': real_state)
  : Lemma (requires run_invariant r h /\ stores_in_kept r h (Write b i v) /\ step r (Write b i v) r')
          (ensures run_invariant r' (update_history h r (Write b i v) r'))

/// **A minor collection keeps it**, its promoted copies among the blocks
/// allocated since.
val minor_keeps_run_invariant (r: real_state) (h: cycle_history) (roots: seq U64.t) (r': real_state)
  : Lemma (requires run_invariant r h /\ step r (Minor roots) r')
          (ensures run_invariant r' (update_history h r (Minor roots) r'))

/// **The start of a cycle establishes it** for the new cycle.
val start_keeps_run_invariant (r: real_state) (h: cycle_history) (roots: seq U64.t) (r': real_state)
  : Lemma (requires run_invariant r h /\ step r (StartCycle roots) r')
          (ensures run_invariant r' (update_history h r (StartCycle roots) r'))

/// **A slice keeps it**, at whatever phase it leaves (marking, the
/// hand-over to the sweep, the sweep, its end).
val slice_keeps_run_invariant (r: real_state) (h: cycle_history) (budget: nat) (r': real_state)
  : Lemma (requires run_invariant r h /\ step r (Slice budget) r')
          (ensures run_invariant r' (update_history h r (Slice budget) r'))

/// **Every step keeps it.**  (Reads and new roots change nothing.)
val step_keeps_run_invariant (r: real_state) (h: cycle_history) (e: event) (r': real_state)
  : Lemma (requires run_invariant r h /\ stores_in_kept r h e /\ step r e r')
          (ensures run_invariant r' (update_history h r e r'))

/// **It holds at every state of a run** whose program events store only
/// pointers to kept blocks.
val run_invariant_along (h0: cycle_history) (#r0: real_state) (#es: list event) (#r1: real_state)
                        (rn: run r0 es r1)
  : Lemma (requires run_invariant r0 h0 /\ stores_in_kept_along h0 rn)
          (ensures run_invariant r1 (history_along h0 rn))
          (decreases rn)

/// ---------------------------------------------------------------------------
/// The allocator meets the relational step
/// ---------------------------------------------------------------------------

/// (`write_major_fields`, `alloc_then_init`: in `GC.Gen.Run.Invariant.Defs`.)

/// **`alloc_phase` is a direct major allocation**: when the allocator finds a
/// block, the allocation followed by the initialising writes of storable
/// values is a `major_alloc_step` -- properties (1)-(4).  So every run of
/// the real allocator is a run of `step`; a change of policy only needs to
/// meet (1)-(4).
val alloc_phase_major_alloc_step (r: real_state) (tag: I.tag_t) (size: nat) (init: seq U64.t)
  : Lemma (requires phase_shape r /\ size >= 1 /\ Seq.length init == size /\ tag <> infix_tag /\
                    init_storable r tag init /\
                    (AC.alloc_phase r.memory.major r.free_list r.phase size tag).SA.obj_out <> 0UL)
          (ensures major_alloc_step r tag size init (alloc_then_init r tag size init))

/// ---------------------------------------------------------------------------
/// At idle: the cycle is lossless
/// ---------------------------------------------------------------------------

/// **Lossless, word by word**: idle, a word was in a free or garbage block of
/// the start memory exactly when it is in a free block now or in a block
/// allocated since.
val idle_lossless (r: real_state) (h: cycle_history)
  : Lemma (requires run_invariant r h /\ r.phase == Ph.Idle)
          (ensures forall (p: nat). p < heap_size ==>
                     (reclaimable_at_start h p <==>
                      LL.blue_covered r.memory.major p \/ SPC.new_covered h.allocated_during_cycle r.memory.major p))

/// **What was reachable survives**: idle, every snapshot object is an
/// allocated block at the address and size it had, never handed out again.
val idle_survives (r: real_state) (h: cycle_history)
  : Lemma (requires run_invariant r h /\ r.phase == Ph.Idle)
          (ensures forall (x: obj_addr). snapshot h x ==>
                     is_allocated r.memory (Major x) /\
                     wosize_of_object x r.memory.major == wosize_of_object x h.start_memory.major /\
                     ~(h.allocated_during_cycle x))

/// **The incremental cycle is lossless, up to what it handed out** (over runs
/// of `step`): once a run is idle,
/// a word of the major heap lay in a block unreachable from the roots when
/// the last cycle started (dead, or free) exactly when it lies in a free
/// block, or in a block allocated or promoted since.
val cycle_lossless (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
  : Lemma (requires r.phase == Ph.Idle /\ stores_in_kept_along (initial_history ()) rn)
          (ensures (let h = history_of_run rn in
                    forall (p: nat). p < heap_size ==>
                      (reclaimable_at_start h p <==>
                       LL.blue_covered r.memory.major p \/
                       SPC.new_covered h.allocated_during_cycle r.memory.major p)))

/// **What was reachable when the cycle started survives it** (over runs of
/// `step`).
val cycle_survives (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
  : Lemma (requires r.phase == Ph.Idle /\ stores_in_kept_along (initial_history ()) rn)
          (ensures (let h = history_of_run rn in
                    forall (x: obj_addr). snapshot h x ==>
                      is_allocated r.memory (Major x) /\
                      wosize_of_object x r.memory.major == wosize_of_object x h.start_memory.major /\
                      ~(h.allocated_during_cycle x)))
