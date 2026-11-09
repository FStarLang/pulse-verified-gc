/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Allocator - the page allocator, as a component
/// ---------------------------------------------------------------------------
///
/// The OCaml 5-style page allocator (docs/pages-allocator-proof-plan.md),
/// independent of any particular collector.  A collector uses it through
/// this interface alone.  Here are:
///
///   1. its state and invariants, per phase (`inv`);
///   2. allocation, as an instance of `GC.Spec.AllocIface` (`pages_allocator`),
///      with the new object's colour set by the phase and only swept pages
///      used;
///   3. the sweep: of one pool page, of one run, and of everything, as a
///      step function iterated to completion with an invariant proved at
///      every step (`sweep_step`, `sweep_inv`), as on `akhil/sweep-refactor`;
///   4. the contract a collector meets to use it: what its mark leaves
///      (`mark_done` for the sweep's safety, `mark_exact` for liveness).
///
/// The sequential collector runs `Idle -> Marking -> Sweeping -> Idle` with
/// no allocation inside a collection; an incremental one allocates in every
/// phase.  See plan §12 for what is proved of each phase.

module GC.Spec.Pages.Allocator

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map

module U64 = FStar.UInt64
module Seq = FStar.Seq
module I = GC.Spec.AllocIface
module Inv = GC.Spec.Pages.Inv
module Th = GC.Spec.Pages.Theorems
module AP = GC.Spec.Pages.AllocPhase
module MP = GC.Spec.Pages.MarkPhase
module SA = GC.Spec.Pages.SweepAll
module SU = GC.Spec.Pages.SweepUnits
module SO = GC.Spec.Pages.SweepOrder
module SW = GC.Spec.Pages.SweepWf
module SS = GC.Spec.Pages.StartSweep
module Mark = GC.Spec.Mark

/// ---------------------------------------------------------------------------
/// 1. State and invariants
/// ---------------------------------------------------------------------------

/// The page map, the lists of pages with a free slot, the large lists.
let pstate = Inv.pstate

/// L1–L10 (plan §1.4).
let pages_ok (g: heap) (st: pstate) : prop = Inv.pages_ok g st

/// `pages_ok` up to the colours of objects that are not free.
let pages_ok_mc (g: heap) (st: pstate) : prop = AP.pages_ok_mc g st

let all_swept (st: pstate) : prop = MP.all_swept st

/// What the allocator needs and keeps, by phase.
///   - `Idle`: everything, every page swept.
///   - `Marking`: the same up to the colours of live objects, which the mark
///     changes; every page swept, since the sweep has finished.
///   - `Sweeping`: the same up to colours; pages may be unswept, and
///     allocation leaves them alone.
let inv (ph: I.phase) (g: heap) (st: pstate) : prop =
  match ph with
  | I.Idle -> pages_ok g st /\ well_formed_heap g /\ all_swept st
  | I.Marking -> pages_ok_mc g st /\ all_swept st
  | I.Sweeping -> pages_ok_mc g st

/// ---------------------------------------------------------------------------
/// 2. Allocation
/// ---------------------------------------------------------------------------

/// The new object's header has the phase's colour; the rest is the
/// allocator of stage 2.
let alloc (ph: I.phase) (g: heap) (st: pstate) (wz: nat) : GTot (heap & pstate & U64.t) =
  AP.alloc_col (I.new_colour ph) g st wz

/// The words of unswept pages.
let unswept (st: pstate) (b: hp_addr) : prop =
  exists (i: nat{i < n_pages}).
    not (entry st.pm i).swept /\ page_base i <= U64.v b /\ U64.v b < page_base (i + 1)

let pages_allocator : I.allocator = {
  ast = pstate;
  inv = inv;
  alloc = alloc;
  unswept = unswept;
}

/// **The page allocator meets the interface**, in every phase, and its
/// invariant follows the collector's phase.
val pages_allocator_ok : unit -> Lemma (I.allocator_ok pages_allocator /\ I.phase_ok pages_allocator)

/// When nothing fits, there was no room (`Th.no_fit`).
val alloc_no_fit (ph: I.phase) (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires inv ph g st)
          (ensures (let (_, _, o) = alloc ph g st wz in
                    o == 0UL /\ wz + 1 < pow2 54 ==> Th.no_fit g st (wz + 1)))

/// In `Idle` the allocator is stage 2's `alloc`, and meets its exact
/// statement (`Th.alloc_ok`), with `pages_ok /\ well_formed_heap` of the
/// caller's heap.
val alloc_idle (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires pages_ok g st /\ well_formed_heap g)
          (ensures alloc I.Idle g st wz == GC.Spec.Pages.Alloc.alloc g st wz /\
                   (let (g', st', o) = alloc I.Idle g st wz in Th.alloc_ok g g' st st' wz o))

/// For any colour but blue (`AP.alloc_ok_col`).
val alloc_col_correct (col: color) (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires pages_ok_mc g st /\ col <> Blue)
          (ensures (let (g', st', o) = AP.alloc_col col g st wz in AP.alloc_ok_col col g g' st st' wz o))

/// ---------------------------------------------------------------------------
/// 3. The sweep
/// ---------------------------------------------------------------------------

/// One pool page, with a frame (plan §2.1).
let sweep_page = GC.Spec.Pages.SweepPage.sweep_page
val sweep_page_correct : unit -> Lemma (Th.sweep_page_meets sweep_page)

/// One run, with a frame.
let sweep_run = GC.Spec.Pages.SweepRun.sweep_run
val sweep_run_correct : unit -> Lemma (Th.sweep_run_meets sweep_run)

/// Sweeping two units in either order gives the same result.
val sweep_commute (g: heap) (pm: page_map) (i j: nat) (fpi fpj: U64.t)
  : Lemma (requires SO.two_units pm i j)
          (ensures (let t1 = SO.sweep_unit g pm i fpi in
                    let t12 = SO.sweep_unit (SO.hp t1) (SO.mp t1) j fpj in
                    let t2 = SO.sweep_unit g pm j fpj in
                    let t21 = SO.sweep_unit (SO.hp t2) (SO.mp t2) i fpi in
                    SO.hp t12 == SO.hp t21 /\ SO.mp t12 == SO.mp t21 /\
                    SO.rp t1 == SO.rp t21 /\ SO.rp t2 == SO.rp t12))

/// Where a sweep starts: the shapes, every page that is not free unswept,
/// the lists empty, no grey block.
let sweep_ready (g: heap) (st: pstate) : prop = SA.sweep_ready g st

/// **One step**: sweep the unit at page `p` (a pool page, a run, or nothing
/// for a free page) and move to the next unit.
let sweep_step (g: heap) (st: pstate) (p: nat{p < n_pages}) : GTot (heap & pstate & nat) =
  let (g', st') = SA.step g st p in (g', st', p + span st.pm p)

/// The invariant at every step: the units before `p` are swept, each
/// holding exactly the mark's survivors made white, with every free block
/// either newly written (tag 0) or a block the mark left, and the rest is as
/// the mark left it.  `g0, st0` is where the sweep started.
let sweep_inv (g0: heap) (st0: pstate) (g: heap) (st: pstate) (p: nat) : prop = SW.inv2 g0 st0 g st p

val sweep_start (g: heap) (st: pstate)
  : Lemma (requires sweep_ready g st) (ensures sweep_inv g st g st 0)

val sweep_step_inv (g0: heap) (st0: pstate) (g: heap) (st: pstate) (p: nat{p < n_pages})
  : Lemma (requires sweep_ready g0 st0 /\ sweep_inv g0 st0 g st p)
          (ensures (let (g', st', p') = sweep_step g st p in p < p' /\ sweep_inv g0 st0 g' st' p'))

/// What the mark guarantees, for the sweep's safety (see 4).
let mark_done (g: heap) : prop = SA.mark_done g

/// **The end**: every page swept, `pages_ok`, `well_formed_heap`, and
/// every unit holds exactly the mark's survivors, made white.
val sweep_end (g0: heap) (st0: pstate) (g: heap) (st: pstate)
  : Lemma (requires sweep_ready g0 st0 /\ mark_done g0 /\ sweep_inv g0 st0 g st n_pages)
          (ensures pages_ok g st /\ well_formed_heap g /\ all_swept st /\
                   (forall (i: nat{i < n_pages}). walk_page st0.pm i ==> SU.unit_ok g0 g i (span st0.pm i)))

/// The whole sweep: the step from page 0 until the end.
let sweep_all (g: heap) (st: pstate) : GTot (heap & pstate) = SA.sweep_all g st

val sweep_all_correct (g: heap) (st: pstate)
  : Lemma (requires sweep_ready g st /\ mark_done g)
          (ensures (let (g', st') = sweep_all g st in
                    pages_ok g' st' /\ well_formed_heap g' /\ all_swept st' /\
                    (forall (i: nat{i < n_pages}). walk_page st.pm i ==> SU.unit_ok g g' i (span st.pm i))))

/// **Before the sweep**: empty the lists and mark every page that is not
/// free unswept.  From the `Marking` invariant and no grey object, this is
/// where the sweep starts.
let start_sweep (st: pstate) : pstate = SS.start_sweep st

val start_ready (g: heap) (st: pstate)
  : Lemma (requires inv I.Marking g st /\ Mark.noGreyObjects g)
          (ensures sweep_ready g (start_sweep st))

/// **The sequential collector's cycle**: once the mark is done, clearing
/// and sweeping bring the `Marking` invariant back to the `Idle` one.
val collection_cycle (g: heap) (st: pstate)
  : Lemma (requires inv I.Marking g st /\ mark_done g)
          (ensures (let (g', st') = sweep_all g (start_sweep st) in inv I.Idle g' st'))

/// ---------------------------------------------------------------------------
/// 4. The collector's contract
/// ---------------------------------------------------------------------------

/// `x` is reachable from `roots` in `h` (as `GC.Spec.Correctness.heap_reachable`).
let reachable (h: heap) (roots: Seq.seq obj_addr) (x: obj_addr) : prop =
  let g = GC.Spec.HeapModel.create_graph h in
  let roots' = GC.Spec.HeapGraph.coerce_to_vertex_list roots in
  GC.Spec.Graph.graph_wf g /\
  GC.Spec.Graph.is_vertex_set roots' /\
  GC.Spec.Graph.subset_vertices roots' g.GC.Spec.Graph.vertices /\
  GC.Spec.Graph.mem_graph_vertex g x /\
  Seq.mem x (GC.Spec.DFS.reachable_set g roots')

/// What a mark must leave for the sweep to be **safe**: a well-formed heap,
/// no grey object, black objects point only to black objects, and nothing
/// points to a free block.  An incremental mark meets it with floating
/// garbage (black objects that are no longer reachable).
///
/// What it must leave for **liveness**: the objects of the heap it started
/// from, black exactly when reachable.  The sequential mark meets it.
let mark_exact (h_init h_mark: heap) (roots: Seq.seq obj_addr) : prop =
  mark_done h_mark /\
  objects zero_addr h_mark == objects zero_addr h_init /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr h_init) ==>
     (is_black x h_mark <==> reachable h_init roots x))

/// Liveness's contract includes safety's.
val mark_exact_done (h_init h_mark: heap) (roots: Seq.seq obj_addr)
  : Lemma (requires mark_exact h_init h_mark roots) (ensures mark_done h_mark)
