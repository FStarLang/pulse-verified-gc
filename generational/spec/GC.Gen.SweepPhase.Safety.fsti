/// ---------------------------------------------------------------------------
/// GC.Gen.SweepPhase.Safety - the sweep phase never frees what is reachable
/// ---------------------------------------------------------------------------
///
/// Safety over the whole sweep phase, stated on the reachable graph rather
/// than on a heap the sweep started from.  The objects the program can reach
/// are those reachable from its roots in the heap graph except the pending
/// objects (`GC.Spec.HeapModel.create_graph_except`: a pending object, like a
/// free block, has no edges):
///
///   * every such object is a real, not-free, not-pending object
///     (`reachable_not_pending`, and with the nursery
///     `reachable_not_pending_combined`): the roots are not pending, and the
///     field closure (`well_formed_heap_except`) takes not-freed objects only to
///     not-freed objects;
///   * a sweep step, and so a slice of `k` steps, frees only pending objects,
///     so it never frees a reachable one, and leaves its size, tag and fields
///     alone (`step_keeps_reachable`, `steps_keep_reachable`);
///   * a minor collection in between keeps every not-freed object not freed
///     (`minor_keeps_not_freed`), and the pending set (step C).

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

/// The heap graph during the sweep: the pending objects have no edges.
let sweep_graph (g: heap) (st: sweep_state) : GTot Graph.graph_state =
  HeapModel.create_graph_except g (pending g st)

/// `x` is reachable from the root `r` in the sweep's graph.
let reachable_from (g: heap) (st: sweep_state) (r x: obj_addr) : prop =
  Graph.mem_graph_vertex (sweep_graph g st) r /\
  Graph.mem_graph_vertex (sweep_graph g st) x /\
  Graph.reachable (sweep_graph g st) r x

/// **Safety: a reachable object is a real, not-free, not-pending object.**
val reachable_not_pending (g: heap) (fp: U64.t) (st: sweep_state) (r x: obj_addr)
  : Lemma (requires sweep_phase_inv g fp st /\ not_freed g (pending g st) r /\
                    reachable_from g st r x)
          (ensures Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ ~(pending g st x))

/// The same over the combined graph of the nursery and the major heap, from
/// the program's roots (`GC.Gen.ReachabilityBridge.reachable_never_pending`).
val reachable_not_pending_combined (minor: minor_state) (g: heap) (fp: U64.t) (st: sweep_state)
                                   (roots: seq U64.t) (v: U64.t)
  : Lemma (requires sweep_phase_inv g fp st /\ minor_wf minor /\
                    GenInv.minor_major_fields_not_freed minor g (pending g st) /\
                    RBridge.roots_not_freed roots g (pending g st) /\
                    CG.combined_reachable (CG.build_combined_graph minor g (pending g st))
                      (CG.classify_roots minor roots) (CG.MajorV v))
          (ensures is_obj v /\ Seq.mem (v <: obj_addr) (objects zero_addr g) /\
                   ~(is_blue (v <: obj_addr) g) /\ ~(pending g st (v <: obj_addr)))

/// **A sweep step never frees a reachable object**, and leaves its size, tag
/// and fields alone.
val step_keeps_reachable (g: heap) (fp: U64.t) (st: sweep_state) (r x: obj_addr)
  : Lemma (requires sweep_phase_inv g fp st /\ U64.v st.cursor + 8 < heap_size /\
                    not_freed g (pending g st) r /\ reachable_from g st r x)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in
                    Seq.mem x (objects zero_addr g') /\ ~(is_blue x g') /\ ~(pending g' st' x) /\
                    same_block g g' (hd_address x)))

/// Nor does a slice of `k` steps.
val steps_keep_reachable (g: heap) (fp: U64.t) (st: sweep_state) (k: nat) (r x: obj_addr)
  : Lemma (requires sweep_phase_inv g fp st /\ not_freed g (pending g st) r /\ reachable_from g st r x)
          (ensures (let (g', fp', st') = sweep_steps g fp st k in
                    Seq.mem x (objects zero_addr g') /\ ~(is_blue x g') /\ ~(pending g' st' x) /\
                    same_block g g' (hd_address x)))

/// A minor collection at the sweep's phase keeps every not-freed object not
/// freed (in the heap it leaves, at the state after it).
val minor_keeps_not_freed (minor: minor_state) (g: heap) (fp: U64.t) (st: sweep_state)
                          (roots: seq U64.t) (x: obj_addr)
  : Lemma (requires sweep_phase_inv g fp st /\ GenInv.minor_heap_shape minor /\
                    GenInv.minor_major_fields_not_freed minor g (pending g st) /\
                    not_freed g (pending g st) x)
          (ensures (let (res, ph') = CA.cheney_collect_spec_except_at (Ph.Sweeping st) minor g fp roots (pending g st) in
                    let st' = GC.Gen.SweepPhase.Minor.state_after st
                                (Cheney.cheney_collect_spec_except minor g fp roots (pending g st)).GC.Gen.Promote.mc_major in
                    not_freed res.GC.Gen.Promote.mc_major (pending res.GC.Gen.Promote.mc_major st') x))
