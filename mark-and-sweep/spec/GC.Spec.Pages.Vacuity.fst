/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Vacuity - constructive witnesses for the page theorems
/// ---------------------------------------------------------------------------
///
/// The vacuity rule (docs/pages-allocator-proof-plan.md §18): every theorem
/// with hypotheses about heaps has a witness, a state shown to satisfy all
/// its hypotheses, with at least one root, one reachable object, one
/// unreachable object, and where the theorem concerns them, one pool page
/// and one large run.  An `expect_failure` test is not enough: a solver
/// timeout looks the same as success.
///
/// Every witness here is derived from `GC.Spec.Pages.Witness`'s state `W`
/// (roots `[A]`; A in a pool page; B in a run, reachable through A; C
/// unreachable), by the theorems themselves:
///
///   - `W` itself, for `Idle`: `gc_correct_pages`, the cycle, `phases`,
///     `darken_ok`, the allocator in `Idle`;
///   - `hd`, `W` with its roots greyed: the mark (`mark_keeps_inv`), the
///     `Marking` invariant with a grey object;
///   - `hm`, the mark of `hd`, where A and B are black and C is not:
///     `gc_correct_gen`, `start_ready`, `collection_cycle`, `mark_exact`, the
///     allocator in `Marking` with black objects;
///   - `start_sweep` of it, where A's pool page and B's run are unswept: the
///     sweep (`sweep_all_wf`, `sweep_start`, `sweep_step_inv`, `sweep_end`,
///     `Survive.swept`);
///   - the collection's result: `Partition.partitioned`.

module GC.Spec.Pages.Vacuity

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv

module U64 = FStar.UInt64
module Seq = FStar.Seq
module I = GC.Spec.AllocIface
module PA = GC.Spec.Pages.Allocator
module W = GC.Spec.Pages.Witness
module D = GC.Spec.Pages.Darken
module GcC = GC.Spec.Pages.GcCorrect
module GP = GC.Spec.Pages.GcPillars
module MP = GC.Spec.Pages.MarkPhase
module SA = GC.Spec.Pages.SweepAll
module SS = GC.Spec.Pages.StartSweep
module SW = GC.Spec.Pages.SweepWf
module SV = GC.Spec.Pages.Survive
module PT = GC.Spec.Pages.Partition
module WE = GC.Spec.WalkEnd
module Mark = GC.Spec.Mark
module MarkInv = GC.Spec.MarkInv
module Corr = GC.Spec.Correctness
module HeapModel = GC.Spec.HeapModel

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The states
/// ---------------------------------------------------------------------------

let h (g: heap) : GTot heap = W.w_heap g
let st (g: heap) : GTot pstate = W.w_state g
let rs (g: heap) : GTot (Seq.seq obj_addr) = W.w_roots g

/// The roots greyed.
let hd (g: heap) : GTot heap = D.darken (h g) (rs g)

/// The mark.
let hm (g: heap) : GTot heap = Mark.mark (hd g) (rs g)

/// The sweep's start.
let s_sw (g: heap) : GTot pstate = SS.start_sweep (st g)

/// The sweep's end.
let swept_heap (g: heap) : GTot heap = fst (SA.sweep_all (hm g) (s_sw g))
let swept_state (g: heap) : GTot pstate = snd (SA.sweep_all (hm g) (s_sw g))

/// What makes a witness non-trivial, of `W`.
let nontrivial (g: heap) : prop =
  Seq.mem (W.oA g) (rs g) /\ ~(Seq.mem (W.oB g) (rs g)) /\
  Corr.heap_reachable (h g) (rs g) (W.oA g) /\ Corr.heap_reachable (h g) (rs g) (W.oB g) /\
  ~(Corr.heap_reachable (h g) (rs g) (W.oC g)) /\
  Seq.mem (W.oC g) (objects zero_addr (h g)) /\ ~(is_blue (W.oC g) (h g)) /\
  Seq.mem (W.oB g) (objects zero_addr (h g)) /\ ~(is_blue (W.oB g) (h g)) /\
  W.oA g <> W.oB g /\ W.oA g <> W.oC g /\ W.oB g <> W.oC g /\
  (exists (i: nat{i < n_pages}). W.kind_of (st g) i == Pool W.cA /\
     page_base i <= U64.v (W.oA g) - 8 /\ U64.v (W.oA g) - 8 < page_base (i + 1)) /\
  W.i0 < n_pages /\ W.kind_of (st g) W.i0 == LargeHead W.kL /\ U64.v (W.oB g) - 8 == page_base W.i0

/// ---------------------------------------------------------------------------
/// `Idle`: `gc_correct_pages`, the cycle, `phases`, `darken_ok`
/// ---------------------------------------------------------------------------

/// **`gc_correct_pages`**, `GcCorrect.phases` and `Darken.darken_ok`: their
/// hypotheses hold of `W`.
let gc_correct_pages_witness (g: heap)
  : Lemma (requires W.big_enough)
          (ensures D.start_pre (h g) (st g) (rs g) /\ nontrivial g)
  = W.w_ok g

/// **The cycle** (`reach_inv`, `cycle_correct`): `W` is a state of the
/// cycle, and a collection from it, with the roots `[A]`, is one too.
let cycle_witness (g: heap) (_: squash W.big_enough)
  : GTot (GcC.reach (h g) (st g) & GcC.reach (fst (GcC.collection (h g) (st g) (rs g)))
                                            (snd (GcC.collection (h g) (st g) (rs g))))
  = W.w_ok g;
    let r = W.w_reach g () in
    (r, GcC.Collect r (rs g) ())

let cycle_witness_ok (g: heap)
  : Lemma (requires W.big_enough)
          (ensures D.roots_ok (h g) (rs g) /\ nontrivial g)
  = W.w_ok g

/// ---------------------------------------------------------------------------
/// The roots greyed: `mark_keeps_inv`, `Marking` with a grey object
/// ---------------------------------------------------------------------------

/// **`MarkSteps.mark_keeps_inv`**: its hypotheses hold of `hd`, with the
/// roots as a stack that is not empty.
let mark_keeps_inv_witness (g: heap)
  : Lemma (requires W.big_enough)
          (ensures MP.mark_inv (hd g) (st g) /\ well_formed_heap (hd g) /\ Mark.stack_props (hd g) (rs g) /\
                   Seq.length (rs g) > 0 /\ is_gray (W.oA g) (hd g) /\ PA.inv I.Marking (hd g) (st g) /\
                   nontrivial g)
  = W.w_ok g;
    D.darken_ok (h g) (st g) (rs g);
    MarkInv.mark_inv_elim_wfh (hd g) (rs g);
    MarkInv.mark_inv_elim_sp (hd g) (rs g);
    W.coerce_one (W.oA g)

/// ---------------------------------------------------------------------------
/// The mark: `gc_correct_gen`, `start_ready`, `collection_cycle`
/// ---------------------------------------------------------------------------

/// The marked heap: A and B black, C an object that is not black.
#push-options "--z3rlimit 40"
let marked_facts (g: heap)
  : Lemma (requires W.big_enough)
          (ensures GP.marked (h g) (hm g) (rs g) /\ GP.graph_pre (h g) (rs g) /\
                   MP.mark_inv (hm g) (st g) /\ SA.mark_done (hm g) /\
                   objects zero_addr (hm g) == objects zero_addr (h g) /\
                   is_black (W.oA g) (hm g) /\ is_black (W.oB g) (hm g) /\
                   Seq.mem (W.oC g) (objects zero_addr (hm g)) /\ ~(is_black (W.oC g) (hm g)))
  = W.w_ok g;
    GcC.mark_ok (h g) (st g) (rs g);
    let hi = h g in
    let m = hm g in
    let r = rs g in
    Corr.mark_post_elim_wfh hi m r 0UL;
    Corr.mark_post_elim_no_grey hi m r 0UL;
    Corr.mark_post_elim_tri_color hi m r 0UL;
    Corr.mark_post_elim_no_pointer_to_blue hi m r 0UL;
    Corr.mark_post_elim_objects hi m r 0UL;
    Corr.mark_post_elim_black_reachable hi m r 0UL;
    HeapModel.graph_vertices_mem hi (W.oC g)
#pop-options

/// **`gc_correct_gen`**: its hypotheses hold of `W` and its mark.
let gc_correct_gen_witness (g: heap)
  : Lemma (requires W.big_enough)
          (ensures GP.marked (h g) (hm g) (rs g) /\ GP.graph_pre (h g) (rs g) /\ MP.mark_inv (hm g) (st g) /\
                   is_black (W.oA g) (hm g) /\ is_black (W.oB g) (hm g) /\ ~(is_black (W.oC g) (hm g)) /\
                   nontrivial g)
  = W.w_ok g;
    marked_facts g

/// **`start_ready`**, **`collection_cycle`** and the `Marking` invariant
/// with black objects: their hypotheses hold of the mark.
let start_ready_witness (g: heap)
  : Lemma (requires W.big_enough)
          (ensures MP.mark_inv (hm g) (st g) /\ Mark.noGreyObjects (hm g) /\ SA.mark_done (hm g) /\
                   PA.inv I.Marking (hm g) (st g) /\ PA.inv I.Sweeping (hm g) (st g) /\
                   is_black (W.oA g) (hm g) /\ is_black (W.oB g) (hm g) /\ ~(is_black (W.oC g) (hm g)) /\
                   nontrivial g)
  = W.w_ok g;
    marked_facts g

/// **`PA.mark_exact`** (the collector's contract for liveness): the mark
/// meets it, and it is not trivial: A and B black, C not.
#push-options "--z3rlimit 40"
let mark_exact_witness (g: heap)
  : Lemma (requires W.big_enough)
          (ensures PA.mark_exact (h g) (hm g) (rs g) /\
                   is_black (W.oB g) (hm g) /\ ~(is_black (W.oC g) (hm g)) /\ nontrivial g)
  = W.w_ok g;
    marked_facts g;
    GcC.mark_ok (h g) (st g) (rs g);
    Corr.mark_post_elim_black_reachable (h g) (hm g) (rs g) 0UL;
    let one (x: obj_addr)
      : Lemma (Seq.mem x (objects zero_addr (h g)) ==>
               (is_black x (hm g) <==> PA.reachable (h g) (rs g) x))
      = HeapModel.graph_vertices_mem (h g) x
    in
    FStar.Classical.forall_intro one
#pop-options

/// ---------------------------------------------------------------------------
/// The sweep
/// ---------------------------------------------------------------------------

/// The sweep starts with A's pool page and B's run unswept.
#push-options "--z3rlimit 40"
let sweep_witness (g: heap)
  : Lemma (requires W.big_enough)
          (ensures SA.sweep_ready (hm g) (s_sw g) /\ SA.mark_done (hm g) /\
                   PA.sweep_ready (hm g) (s_sw g) /\ PA.mark_done (hm g) /\
                   PA.sweep_inv (hm g) (s_sw g) (hm g) (s_sw g) 0 /\
                   PA.sweep_inv (hm g) (s_sw g) (swept_heap g) (swept_state g) n_pages /\
                   SV.swept (hm g) (s_sw g) (swept_heap g) (swept_state g) /\
                   (exists (i: nat{i < n_pages}). W.kind_of (s_sw g) i == Pool W.cA /\
                      not (entry (s_sw g).pm i).swept /\
                      page_base i <= U64.v (W.oA g) - 8 /\ U64.v (W.oA g) - 8 < page_base (i + 1)) /\
                   W.i0 < n_pages /\ W.kind_of (s_sw g) W.i0 == LargeHead W.kL /\ not (entry (s_sw g).pm W.i0).swept /\
                   is_black (W.oB g) (hm g) /\ ~(is_black (W.oC g) (hm g)) /\ nontrivial g)
  = W.w_ok g;
    marked_facts g;
    SS.start_ready (hm g) (st g);
    PA.sweep_start (hm g) (s_sw g);
    SW.sweep_all_inv2 (hm g) (s_sw g);
    SV.swept_of (hm g) (s_sw g)
#pop-options

/// ---------------------------------------------------------------------------
/// The collection's result: `Partition.partitioned`
/// ---------------------------------------------------------------------------

/// **`PT.partitioned`**: its hypotheses hold of the heap and state the
/// collection of `W` leaves.
#push-options "--z3rlimit 40"
let partitioned_witness (g: heap)
  : Lemma (requires W.big_enough)
          (ensures (let (g', st') = GcC.collection (h g) (st g) (rs g) in
                    (forall (y: obj_addr). Seq.mem y (objects zero_addr g') ==> PT.block_class g' st' y) /\
                    WE.walk_end g' zero_addr + 8 >= heap_size /\
                    GcC.unreachable_reclaimed (h g) g' (rs g) /\
                    Seq.mem (W.oB g) (objects zero_addr g') /\ is_white (W.oB g) g' /\
                    nontrivial g))
  = W.w_ok g;
    GcC.gc_correct_pages (h g) (st g) (rs g);
    let (g', st') = GcC.collection (h g) (st g) (rs g) in
    GC.Spec.Pages.Step.pages_ok_elim g' st';
    GC.Spec.Pages.Shape.heap_tiled g' st'.pm
#pop-options

/// ---------------------------------------------------------------------------
/// `idle_mark_pre_empty`: the old hypotheses hold, but only without roots
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let empty_facts (x: heap)
  : Lemma (D.darken x Seq.empty == x /\
           GC.Spec.Graph.is_vertex_set (GC.Spec.HeapGraph.coerce_to_vertex_list (Seq.empty #obj_addr)) /\
           (forall (r: obj_addr). ~(Seq.mem r (Seq.empty #obj_addr))) /\
           (forall (v: GC.Spec.Graph.vertex_id).
              ~(Seq.mem v (GC.Spec.HeapGraph.coerce_to_vertex_list (Seq.empty #obj_addr)))))
  = assert (GC.Spec.HeapGraph.coerce_to_vertex_list (Seq.empty #obj_addr) == Seq.empty)
#pop-options

/// The hypotheses of `GcCorrect.idle_mark_pre_empty` (the old
/// `gc_correct_pages`'s) hold of `W` with no roots and an empty stack; by
/// that lemma, they hold with no other.
let idle_mark_pre_witness (g: heap)
  : Lemma (requires W.big_enough)
          (ensures PA.inv I.Idle (h g) (st g) /\ GcC.mark_pre (h g) Seq.empty Seq.empty)
  = W.w_ok g;
    empty_facts (h g);
    Mark.create_graph_wf_from_heap (h g);
    D.darken_ok (h g) (st g) Seq.empty

/// ---------------------------------------------------------------------------
/// The allocator's interface, phase by phase
/// ---------------------------------------------------------------------------

/// **The interface** (`pages_allocator_ok`, `alloc_no_fit`, `alloc_idle`,
/// `alloc_col_correct`, `MarkPhase.mark_inv_recolour`): each phase's
/// invariant holds of a state with live objects in a pool page and a run:
///   - `Idle`: `W` (all white);
///   - `Marking`: `hd` (A grey) and `hm` (A and B black);
///   - `Sweeping`: `hm`, with every page swept; and `hm` with the sweep's
///     start state, A's pool page and B's run unswept (`sweeping_witness`).
let interface_witness (g: heap)
  : Lemma (requires W.big_enough)
          (ensures PA.inv I.Idle (h g) (st g) /\ PA.pages_ok (h g) (st g) /\ well_formed_heap (h g) /\
                   PA.inv I.Marking (hd g) (st g) /\ is_gray (W.oA g) (hd g) /\
                   PA.inv I.Marking (hm g) (st g) /\ PA.pages_ok_mc (hm g) (st g) /\
                   is_black (W.oA g) (hm g) /\ is_black (W.oB g) (hm g) /\
                   PA.inv I.Sweeping (hm g) (st g) /\
                   MP.mark_inv (hd g) (st g) /\ Seq.mem (W.oA g) (objects zero_addr (hd g)) /\
                   ~(is_blue (W.oA g) (hd g)) /\
                   nontrivial g)
  = W.w_ok g;
    mark_keeps_inv_witness g;
    marked_facts g;
    D.darken_ok (h g) (st g) (rs g)

/// **`Sweeping` with unswept pages**: where the sweep starts, A's pool page
/// and B's run unswept, A and B black (`SweepingStart.sweeping_at_start`).
#push-options "--z3rlimit 40"
let sweeping_witness (g: heap)
  : Lemma (requires W.big_enough)
          (ensures PA.inv I.Sweeping (hm g) (s_sw g) /\
                   (exists (i: nat{i < n_pages}). W.kind_of (s_sw g) i == Pool W.cA /\
                      not (entry (s_sw g).pm i).swept /\
                      page_base i <= U64.v (W.oA g) - 8 /\ U64.v (W.oA g) - 8 < page_base (i + 1)) /\
                   W.i0 < n_pages /\ W.kind_of (s_sw g) W.i0 == LargeHead W.kL /\
                   not (entry (s_sw g).pm W.i0).swept /\
                   is_black (W.oA g) (hm g) /\ is_black (W.oB g) (hm g) /\ nontrivial g)
  = W.w_ok g;
    marked_facts g;
    GC.Spec.Pages.SweepingStart.sweeping_at_start (hm g) (st g);
    FStar.Classical.forall_intro (SS.clear_entry (st g).pm)
#pop-options

/// **The Pulse allocator and sweep** (`GC.Impl.Pages`): `alloc_white` and
/// `alloc` need `Ready.heads_ready`, which `pages_ok` and `pages_ok_mc` give
/// (`Ready.pages_ok_ready`, `Ready.mc_ready`); `sweep` and `sweep_all` need
/// `map_ok`.  All hold of `W`, of its mark, and of the sweep's start.
let pulse_pre_witness (g: heap)
  : Lemma (requires W.big_enough)
          (ensures PA.pages_ok (h g) (st g) /\ PA.pages_ok_mc (hm g) (st g) /\
                   map_ok (st g).pm /\ map_ok (s_sw g).pm /\ nontrivial g)
  = W.w_ok g;
    marked_facts g;
    GC.Spec.Pages.Step.pages_ok_elim (h g) (st g);
    SS.clear_map_ok (st g).pm

/// **`SweepOrder.sweep_commute`**: A's pool page and B's run are two units
/// of the sweep's start, the heap the mark left.
let sweep_commute_witness (g: heap)
  : Lemma (requires W.big_enough)
          (ensures exists (i: nat). GC.Spec.Pages.SweepOrder.two_units (s_sw g).pm i W.i0 /\
                               Pool? (entry (s_sw g).pm i).kind /\
                               LargeHead? (entry (s_sw g).pm W.i0).kind)
  = sweeping_witness g;
    pulse_pre_witness g
