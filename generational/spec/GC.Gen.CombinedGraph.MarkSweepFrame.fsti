/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph.MarkSweepFrame — Mark/sweep preserves field structure
/// ---------------------------------------------------------------------------
///
/// Key bridge lemma: after minor_collect produces mc_major, the subsequent
/// mark+sweep preserves the successor structure of reachable objects.
///
/// This composes `end_to_end_correctness` (from GC.Spec.Correctness) with
/// the minor collection result to show that edges in mc_major are preserved
/// in the final swept heap for all reachable objects.

module GC.Gen.CombinedGraph.MarkSweepFrame

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Spec.HeapModel

module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark
module Sweep = GC.Spec.Sweep
module MajorCorrectness = GC.Spec.Correctness
module DFS = GC.Spec.DFS

/// After mark+sweep, the successors of every reachable (black) object
/// in the pre-mark heap equal the successors in the swept heap.
/// This means the graph structure is preserved for all surviving objects.
val mark_sweep_preserves_successors
  (h_init: heap) (st: seq obj_addr) (roots: seq obj_addr) (fp: U64.t)
  (x: obj_addr)
  : Lemma
    (requires
      well_formed_heap h_init /\
      Mark.stack_props h_init st /\
      Mark.root_props h_init roots /\
      Sweep.fp_in_heap fp h_init /\
      Mark.no_black_objects h_init /\
      Mark.no_pointer_to_blue h_init /\
      (forall (r: obj_addr). Seq.mem r roots <==> Seq.mem r st) /\
      (let graph = create_graph h_init in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices) /\
      // x is a reachable object (black after mark and survives sweep)
      is_black x (Mark.mark h_init st) /\
      Seq.mem x (create_graph (fst (Sweep.sweep (Mark.mark h_init st) fp))).vertices)
    (ensures
      (let h_mark = Mark.mark h_init st in
       let h_sweep = fst (Sweep.sweep h_mark fp) in
       let g_init = create_graph h_init in
       let g_sweep = create_graph h_sweep in
       successors g_init x == successors g_sweep x))

/// After mark+sweep, field values of reachable objects are unchanged.
/// This is the per-field version of successor preservation.
val mark_sweep_preserves_field
  (h_init: heap) (st: seq obj_addr) (roots: seq obj_addr) (fp: U64.t)
  (x: obj_addr) (i: U64.t)
  : Lemma
    (requires
      well_formed_heap h_init /\
      Mark.stack_props h_init st /\
      Mark.root_props h_init roots /\
      Sweep.fp_in_heap fp h_init /\
      Mark.no_black_objects h_init /\
      Mark.no_pointer_to_blue h_init /\
      (forall (r: obj_addr). Seq.mem r roots <==> Seq.mem r st) /\
      (let graph = create_graph h_init in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices) /\
      is_black x (Mark.mark h_init st) /\
      Seq.mem x (create_graph (fst (Sweep.sweep (Mark.mark h_init st) fp))).vertices /\
      U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x h_init))
    (ensures
      (let h_sweep = fst (Sweep.sweep (Mark.mark h_init st) fp) in
       HeapGraph.get_field h_init x i == HeapGraph.get_field h_sweep x i))

/// The reachable set after mark is exactly the black objects.
/// Black after mark <==> reachable from roots in the pre-mark graph.
val mark_black_iff_reachable
  (h_init: heap) (st: seq obj_addr) (roots: seq obj_addr) (fp: U64.t)
  (x: obj_addr)
  : Lemma
    (requires
      well_formed_heap h_init /\
      Mark.stack_props h_init st /\
      Mark.root_props h_init roots /\
      Sweep.fp_in_heap fp h_init /\
      Mark.no_black_objects h_init /\
      Mark.no_pointer_to_blue h_init /\
      (forall (r: obj_addr). Seq.mem r roots <==> Seq.mem r st) /\
      (let graph = create_graph h_init in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices) /\
      mem_graph_vertex (create_graph h_init) x)
    (ensures
      (let g_init = create_graph h_init in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       is_black x (Mark.mark h_init st) <==>
       Seq.mem x (DFS.reachable_set g_init roots')))

/// Black objects survive sweep: they appear in the swept graph's vertices.
/// Composes gc_safety (reachable → survives) with black ↔ reachable.
val black_survives_sweep
  (h_init: heap) (st: seq obj_addr) (roots: seq obj_addr) (fp: U64.t)
  (x: obj_addr)
  : Lemma
    (requires
      well_formed_heap h_init /\
      Mark.stack_props h_init st /\
      Mark.root_props h_init roots /\
      Sweep.fp_in_heap fp h_init /\
      Mark.no_black_objects h_init /\
      Mark.no_pointer_to_blue h_init /\
      (forall (r: obj_addr). Seq.mem r roots <==> Seq.mem r st) /\
      (let graph = create_graph h_init in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices) /\
      mem_graph_vertex (create_graph h_init) x /\
      is_black x (Mark.mark h_init st))
    (ensures
      Seq.mem x (create_graph (fst (Sweep.sweep (Mark.mark h_init st) fp))).vertices)
