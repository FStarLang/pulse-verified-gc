/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Simulation.Collector - the simulation across collector steps
/// ---------------------------------------------------------------------------
///
/// The collector's half of `GC.Gen.Run.Simulation`, stated on the joint
/// invariant's parts (this module does not depend on `GC.Gen.Run.Simulation`,
/// which calls it):
///   * `start_keeps`: the start of a cycle keeps the joint invariant -- it
///     only recolours, and an object the program can reach is reachable from
///     the real roots in the real heap (infix pointers resolve to their
///     closures: `GC.Model.Ideal.valid_value`), so in the snapshot;
///   * `full_gc_end`: after `full_gc` -- a minor collection, the start of a
///     cycle, two unbounded slices -- the collector is idle, the nursery
///     empty, and a block holds an object only if the program can still
///     reach it: an object reachable from the real roots in the real heap is
///     reachable in the ideal memory.  `GC.Gen.Run.Simulation.full_gc_collects`
///     takes the run apart (`full_gc_events_snoc`, `snoc_inj`) and applies it.

module GC.Gen.Run.Simulation.Collector

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
module SPI = GC.Spec.SweepPhase.Intrinsic
module SL = GC.Spec.SweepPhase.Slice

/// **The start of a cycle keeps the joint invariant** (`sim_inv`, spelled
/// out; nothing is needed of the program's reach before the step: idle,
/// every allocated block is kept).
val start_keeps (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (roots: seq U64.t) (r': real_state)
  : Lemma (requires run_invariant r h /\ represents r h im ids /\ I.wf_memory im /\ I.wf_objects im /\
                    roots_represented ids (ptr_values im.I.roots) roots /\ step r (StartCycle roots) r')
          (ensures (let h' = update_history h r (StartCycle roots) r' in
                    let ids' = update_block_ids ids (Seq.length im.I.objects) r (StartCycle roots) r' in
                    run_invariant r' h' /\ represents r' h' im ids' /\
                    (forall (x: obj_addr) (id: I.obj_id).
                       ids' (Major x) == Some id /\ I.reachable im id ==> kept h' x)))

val snoc_inj (l1 l2: list event) (a b: event)
  : Lemma (requires l1 @ [a] == l2 @ [b]) (ensures l1 == l2 /\ a == b)

val snoc_nonempty (l: list event) (a: event) : Lemma (~(l @ [a] == []))

/// **What `full_gc` leaves**, from the states along it: `r1` after the minor
/// collection, `r2` after the start of the cycle (from the roots `rs'`),
/// `r3` after the mark slice, `r` after the sweep slice; `ids1` the map at
/// `r1`, `ids` the map at `r` (a restriction of `ids1`), `h` the history at `r`.
val full_gc_end (r1 r2 r3 r: real_state) (rs': seq U64.t) (h1 h: cycle_history) (im: I.ideal_memory)
                (ids1 ids: block_id_map)
  : Lemma (requires run_invariant r1 h1 /\ represents r1 h1 im ids1 /\ I.wf_memory im /\ I.wf_objects im /\
                    start_step r1 rs' r2 /\
                    slice_step r2 unbounded_budget r3 /\ slice_step r3 unbounded_budget r /\
                    phase_shape r3 /\ run_invariant r h /\ represents r h im ids /\
                    h.start_memory == r1.memory /\ h.start_roots == rs' /\
                    (forall (x: obj_addr). ~(h.allocated_during_cycle x)) /\
                    roots_represented ids1 (ptr_values im.I.roots) rs' /\
                    (forall (b: block_addr) (id: I.obj_id). ids b == Some id ==> ids1 b == Some id))
          (ensures r.phase == Ph.Idle /\ r.memory.nursery == minor_reset r.memory.nursery /\
                   (forall (b: block_addr) (id: I.obj_id). ids b == Some id ==> I.reachable im id))

/// `full_gc`'s events, one at a time from the end.
val full_gc_events_snoc (es0: list event) (rs rs': seq U64.t)
  : Lemma (es0 @ full_gc_events rs rs' ==
           (((es0 @ [Minor rs]) @ [StartCycle rs']) @ [Slice unbounded_budget]) @ [Slice unbounded_budget])

/// **The frame of the sweep**: a slice leaves the heap from its new cursor on
/// unchanged, so the blocks still pending free keep their headers and
/// fields.  A fact of `GC.Spec.FusedSweep.Step`'s steps (`step_frame`, in its
/// .fst) that its interface does not export yet; a hypothesis of
/// `slice_keeps` until it does.
let sweep_frame : prop =
  forall (g: heap) (fp: U64.t) (c: U64.t) (budget: nat).
    SPI.sweep_inv_incremental g fp c ==>
    (let (g', _, st') = SL.sweep_slice g fp (SPI.state_at g c) budget in
     forall (a: hp_addr). U64.v a >= U64.v st'.GC.Spec.FusedSweep.cursor ==> read_word g' a == read_word g a)

/// **A slice keeps the joint invariant** (`sim_inv`, spelled out), given the
/// sweep's frame: mark moves recolour; a sweep slice frees only blocks that
/// are not kept, whose entries go; what kept blocks and the nursery point at
/// is kept, so not freed.
val slice_keeps (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (budget: nat) (r': real_state)
  : Lemma (requires run_invariant r h /\ represents r h im ids /\ I.wf_memory im /\ I.wf_objects im /\
                    (forall (x: obj_addr) (id: I.obj_id). ids (Major x) == Some id /\ I.reachable im id ==> kept h x) /\
                    step r (Slice budget) r' /\ sweep_frame)
          (ensures (let h' = update_history h r (Slice budget) r' in
                    let ids' = update_block_ids ids (Seq.length im.I.objects) r (Slice budget) r' in
                    run_invariant r' h' /\ represents r' h' im ids' /\
                    (forall (x: obj_addr) (id: I.obj_id).
                       ids' (Major x) == Some id /\ I.reachable im id ==> kept h' x)))
