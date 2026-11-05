/// ---------------------------------------------------------------------------
/// GC.Gen.SweepPhase.Safety - the sweep phase never frees what is reachable
/// ---------------------------------------------------------------------------
///
/// Safety over the whole sweep phase, stated on the reachable graph rather
/// than on a heap the sweep started from.  The objects the program can reach
/// are those reachable from its roots in the heap graph for `free_incremental`
/// (`GC.Spec.HeapModel.create_graph_with (free_incremental c)`: an object
/// pending free, like a blue block, has no edges):
///
///   * every such object is not free -- a real object, neither blue nor
///     pending free (`reachable_not_free`, and with the nursery
///     `reachable_not_free_combined`): the roots are not free, and
///     well-formedness (`well_formed_heap_with (free_incremental c)`) takes
///     non-free objects only to non-free objects;
///   * a sweep step, and so a slice of `k` steps, frees only objects pending
///     free, so it never frees a reachable one, and leaves its size, tag
///     and fields alone (`step_keeps_reachable`, `steps_keep_reachable`);
///   * a minor collection in between keeps every non-free object non-free
///     (`minor_keeps_not_free`), and the pending-free set (step C).

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
module Cheney = GC.Gen.Cheney
module Ph = GC.Spec.Phase

/// The heap graph during the sweep, for `free_incremental`: the objects
/// pending free have no edges.
let sweep_graph (g: heap) (c: U64.t) : GTot Graph.graph_state =
  HeapModel.create_graph_with (free_incremental c) g

/// `x` is reachable from the root `r` in the sweep's graph.
let reachable_from (g: heap) (c: U64.t) (r x: obj_addr) : prop =
  Graph.mem_graph_vertex (sweep_graph g c) r /\
  Graph.mem_graph_vertex (sweep_graph g c) x /\
  Graph.reachable (sweep_graph g c) r x

/// **Safety: a reachable object is not free**: a real object, neither blue
/// nor pending free.
val reachable_not_free (g: heap) (fp: U64.t) (c: U64.t) (r x: obj_addr)
  : Lemma (requires sweep_inv_incremental g fp c /\ in_use (free_incremental c) g r /\
                    reachable_from g c r x)
          (ensures in_use (free_incremental c) g x)

/// The same over the combined graph of the nursery and the major heap, from
/// the program's roots (`GC.Gen.ReachabilityBridge.reachable_not_free`).
val reachable_not_free_combined (minor: minor_state) (g: heap) (fp: U64.t) (c: U64.t)
                                 (roots: seq U64.t) (a: U64.t)
  : Lemma (requires sweep_inv_incremental g fp c /\ minor_wf minor /\
                    GenInv.minor_major_fields_not_free (free_incremental c) minor g /\
                    RBridge.roots_not_free (free_incremental c) roots g /\
                    CG.combined_reachable (CG.build_combined_graph minor g (free_incremental c))
                      (CG.classify_roots minor roots) (CG.MajorV a))
          (ensures is_obj a /\ in_use (free_incremental c) g (a <: obj_addr))

/// **A sweep step never frees a reachable object**, and leaves its size, tag
/// and fields alone.
val step_keeps_reachable (g: heap) (fp: U64.t) (c: U64.t) (r x: obj_addr)
  : Lemma (requires sweep_inv_incremental g fp c /\ U64.v c + 8 < heap_size /\
                    in_use (free_incremental c) g r /\ reachable_from g c r x)
          (ensures can_sweep g (state_at g c) /\
                   (let (g', fp', c') = sweep_step g fp (state_at g c) in
                    in_use (free_incremental c'.cursor) g' x /\ same_block g g' (hd_address x)))

/// Nor does a slice of `k` steps.
val steps_keep_reachable (g: heap) (fp: U64.t) (c: U64.t) (k: nat) (r x: obj_addr)
  : Lemma (requires sweep_inv_incremental g fp c /\ in_use (free_incremental c) g r /\ reachable_from g c r x)
          (ensures (let (g', fp', c') = sweep_steps g fp (state_at g c) k in
                    in_use (free_incremental c'.cursor) g' x /\ same_block g g' (hd_address x)))

/// A minor collection at the sweep's phase keeps every non-free object
/// non-free (in the heap it leaves, at the same cursor).
val minor_keeps_not_free (minor: minor_state) (g: heap) (fp: U64.t) (c: U64.t)
                          (roots: seq U64.t) (x: obj_addr)
  : Lemma (requires sweep_inv_incremental g fp c /\ GenInv.minor_heap_shape minor /\
                    GenInv.minor_major_fields_not_free (free_incremental c) minor g /\
                    in_use (free_incremental c) g x)
          (ensures (let res = GC.Gen.SweepPhase.Minor.collect_at c minor g fp roots in
                    in_use (free_incremental c) res.GC.Gen.Promote.mc_major x))
