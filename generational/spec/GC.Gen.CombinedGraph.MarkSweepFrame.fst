/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph.MarkSweepFrame — Implementation
/// ---------------------------------------------------------------------------
///
/// All lemmas follow directly from GC.Spec.Correctness.end_to_end_correctness.
/// That theorem bundles Pillar 5 (field/successor preservation for black objects)
/// and the black <==> reachable characterization.

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

/// Helper: invoke end_to_end_correctness and extract the relevant conjuncts
private let invoke_e2e (h_init: heap) (st: seq obj_addr) (roots: seq obj_addr) (fp: U64.t)
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
       graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
    (ensures
      (let h_mark = Mark.mark h_init st in
       let h_sweep = fst (Sweep.sweep h_mark fp) in
       let g_init = create_graph h_init in
       let g_sweep = create_graph h_sweep in
       // Successor preservation for black objects
       (forall (x: obj_addr).
         Seq.mem x g_sweep.vertices /\ is_black x h_mark ==>
         successors g_init x == successors g_sweep x) /\
       // Field preservation for black objects
       (forall (x: obj_addr) (i: U64.t).
         Seq.mem x g_sweep.vertices /\ is_black x h_mark /\
         U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x h_init) ==>
         HeapGraph.get_field h_init x i == HeapGraph.get_field h_sweep x i) /\
       // Black <==> reachable
       (let roots' = HeapGraph.coerce_to_vertex_list roots in
        graph_wf g_init /\ is_vertex_set roots' /\ subset_vertices roots' g_init.vertices ==>
        (forall (x: obj_addr).
          mem_graph_vertex g_init x ==>
          (is_black x h_mark <==> Seq.mem x (DFS.reachable_set g_init roots'))))))
  = MajorCorrectness.end_to_end_correctness h_init st roots fp

/// Mark+sweep preserves successors: black objects in swept heap have same successor list
let mark_sweep_preserves_successors h_init st roots fp x =
  invoke_e2e h_init st roots fp

/// Mark+sweep preserves individual fields
let mark_sweep_preserves_field h_init st roots fp x i =
  invoke_e2e h_init st roots fp

/// Black <==> reachable from roots in the graph
let mark_black_iff_reachable h_init st roots fp x =
  invoke_e2e h_init st roots fp

/// Black objects survive sweep
let black_survives_sweep h_init st roots fp x =
  // Step 1: black ↔ reachable
  mark_black_iff_reachable h_init st roots fp x;
  // Step 2: reachable → survives sweep (gc_safety)
  MajorCorrectness.gc_safety h_init st roots fp;
  // Step 3: objects zero_addr h_sweep ↔ g_sweep.vertices (graph_vertices_mem)
  let h_sweep = fst (Sweep.sweep (Mark.mark h_init st) fp) in
  graph_vertices_mem h_sweep x
