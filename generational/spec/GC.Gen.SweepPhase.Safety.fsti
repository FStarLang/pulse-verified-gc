/// ---------------------------------------------------------------------------
/// GC.Gen.SweepPhase.Safety - the sweep phase never frees what is reachable
/// ---------------------------------------------------------------------------
///
/// Safety over the whole sweep phase, stated on the reachable graph rather
/// than on a heap the sweep started from.  The objects the program can reach
/// are those reachable from its roots in the heap graph on the sweep's view
/// (`GC.Spec.HeapModel.create_graph_view (surviving st)`: a condemned object,
/// like a free block, has no edges):
///
///   * every such object is surviving -- a real, not-free, not-condemned
///     object (`reachable_surviving`, and with the nursery
///     `reachable_surviving_combined`): the roots are surviving, and
///     well-formedness on the view (`well_formed_view (surviving st)`) takes
///     surviving objects only to surviving objects;
///   * a sweep step, and so a slice of `k` steps, frees only condemned
///     objects, so it never frees a reachable one, and leaves its size, tag
///     and fields alone (`step_keeps_reachable`, `steps_keep_reachable`);
///   * a minor collection in between keeps every surviving object surviving
///     (`minor_keeps_surviving`), and the condemned set (step C).

module GC.Gen.SweepPhase.Safety

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.SweepPhase.Intrinsic
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Graph = GC.Spec.Graph
module HeapModel = GC.Spec.HeapModel
module GenInv = GC.Gen.HeapInvariant
module CG = GC.Gen.CombinedGraph
module RBridge = GC.Gen.ReachabilityBridge
module CA = GC.Gen.CheneyAt
module Cheney = GC.Gen.Cheney
module Ph = GC.Spec.Phase

/// The heap graph during the sweep, on the sweep's view: the condemned
/// objects have no edges.
let sweep_graph (g: heap) (st: sweep_state) : GTot Graph.graph_state =
  HeapModel.create_graph_view (surviving st) g

/// `x` is reachable from the root `r` in the sweep's graph.
let reachable_from (g: heap) (st: sweep_state) (r x: obj_addr) : prop =
  Graph.mem_graph_vertex (sweep_graph g st) r /\
  Graph.mem_graph_vertex (sweep_graph g st) x /\
  Graph.reachable (sweep_graph g st) r x

/// **Safety: a reachable object is surviving**: a real, not-free,
/// not-condemned object.
val reachable_surviving (g: heap) (fp: U64.t) (st: sweep_state) (r x: obj_addr)
  : Lemma (requires sweep_phase_inv g fp st /\ surviving st g r /\
                    reachable_from g st r x)
          (ensures surviving st g x)

/// The same over the combined graph of the nursery and the major heap, from
/// the program's roots (`GC.Gen.ReachabilityBridge.reachable_in_view`).
val reachable_surviving_combined (minor: minor_state) (g: heap) (fp: U64.t) (st: sweep_state)
                                 (roots: seq U64.t) (a: U64.t)
  : Lemma (requires sweep_phase_inv g fp st /\ minor_wf minor /\
                    GenInv.minor_major_fields_in_view (surviving st) minor g /\
                    RBridge.roots_in_view (surviving st) roots g /\
                    CG.combined_reachable (CG.build_combined_graph minor g (surviving st))
                      (CG.classify_roots minor roots) (CG.MajorV a))
          (ensures is_obj a /\ surviving st g (a <: obj_addr))

/// **A sweep step never frees a reachable object**, and leaves its size, tag
/// and fields alone.
val step_keeps_reachable (g: heap) (fp: U64.t) (st: sweep_state) (r x: obj_addr)
  : Lemma (requires sweep_phase_inv g fp st /\ U64.v st.cursor + 8 < heap_size /\
                    surviving st g r /\ reachable_from g st r x)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in
                    surviving st' g' x /\ same_block g g' (hd_address x)))

/// Nor does a slice of `k` steps.
val steps_keep_reachable (g: heap) (fp: U64.t) (st: sweep_state) (k: nat) (r x: obj_addr)
  : Lemma (requires sweep_phase_inv g fp st /\ surviving st g r /\ reachable_from g st r x)
          (ensures (let (g', fp', st') = sweep_steps g fp st k in
                    surviving st' g' x /\ same_block g g' (hd_address x)))

/// A minor collection at the sweep's phase keeps every surviving object
/// surviving (in the heap it leaves, at the state after it).
val minor_keeps_surviving (minor: minor_state) (g: heap) (fp: U64.t) (st: sweep_state)
                          (roots: seq U64.t) (x: obj_addr)
  : Lemma (requires sweep_phase_inv g fp st /\ GenInv.minor_heap_shape minor /\
                    GenInv.minor_major_fields_in_view (surviving st) minor g /\
                    surviving st g x)
          (ensures (let v = surviving_from st g in
                    let (res, ph') = CA.cheney_collect_spec_view_at (Ph.Sweeping st) v minor g fp roots in
                    let st' = GC.Gen.SweepPhase.Minor.state_after st
                                (Cheney.cheney_collect_spec_view v minor g fp roots).GC.Gen.Promote.mc_major in
                    surviving st' res.GC.Gen.Promote.mc_major x))
