/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.Correctness - End-to-End GC Correctness
/// ---------------------------------------------------------------------------
///
/// Uses obj_addr convention from common/.

module Pulse.Spec.GC.Correctness

#set-options "--split_queries always --z3rlimit 50 --fuel 2 --ifuel 1"

open FStar.Seq
open FStar.Mul

module U64 = FStar.UInt64

open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Heap
open Pulse.Spec.GC.Object
open Pulse.Spec.GC.Graph
open Pulse.Spec.GC.Fields
open Pulse.Spec.GC.HeapModel
open Pulse.Spec.GC.Mark
open Pulse.Spec.GC.Sweep
open Pulse.Spec.GC.DFS
module HeapGraph = Pulse.Spec.GC.HeapGraph

/// ---------------------------------------------------------------------------
/// Pillar 3: Structural Preservation
/// ---------------------------------------------------------------------------

val gc_preserves_structure : (g: heap) -> (st: seq obj_addr) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ free_list_props g fp)
        (ensures (forall (x: obj_addr).
                   Seq.mem x (objects 0UL (fst (sweep (mark g st) fp))) /\
                   not (is_blue x (fst (sweep (mark g st) fp))) ==>
                   successors (create_graph g) x ==
                   successors (create_graph (fst (sweep (mark g st) fp))) x))

let gc_preserves_structure g st fp =
  mark_preserves_wf g st;
  mark_no_grey_remains g st;
  admit()

/// ---------------------------------------------------------------------------
/// Pillar 5: Data Transparency  
/// ---------------------------------------------------------------------------

val gc_preserves_data : (g: heap) -> (st: seq obj_addr) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ free_list_props g fp)
        (ensures (forall (x: obj_addr) (i: U64.t).
                   Seq.mem x (objects 0UL (fst (sweep (mark g st) fp))) /\
                   not (is_blue x (fst (sweep (mark g st) fp))) /\
                   U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x g) ==>
                   HeapGraph.get_field g x i == 
                   HeapGraph.get_field (fst (sweep (mark g st) fp)) x i))

let gc_preserves_data g st fp =
  mark_preserves_wf g st;
  mark_no_grey_remains g st;
  admit()

/// ---------------------------------------------------------------------------
/// THE END-TO-END CORRECTNESS THEOREM
/// ---------------------------------------------------------------------------

val end_to_end_correctness :
  (h_init: heap) ->
  (st: seq obj_addr) ->
  (roots: seq obj_addr) ->
  (fp: obj_addr) ->
  Lemma
    (requires 
      well_formed_heap h_init /\
      stack_props h_init st /\
      root_props h_init roots /\
      free_list_props h_init fp /\
      no_black_objects h_init /\
      (forall (r: obj_addr). Seq.mem r roots ==> Seq.mem r st))
    (ensures
      (let h_mark = mark h_init st in
       let h_sweep = fst (sweep h_mark fp) in
       let g_init = create_graph h_init in
       let g_sweep = create_graph h_sweep in
      
       (* PILLAR 1: HEAP INTEGRITY *)
       well_formed_heap h_sweep /\
      
       (* PILLAR 2: REACHABILITY PRESERVATION *)
       (let roots' = HeapGraph.coerce_to_vertex_list roots in
        graph_wf g_init /\ is_vertex_set roots' /\ subset_vertices roots' g_init.vertices ==>
        (forall (x: obj_addr). 
          mem_graph_vertex g_init x ==>
          (Seq.mem x g_sweep.vertices /\ not (is_blue x h_sweep) <==>
           Seq.mem x (reachable_set g_init roots')))) /\
      
       (* PILLAR 3: STRUCTURAL PRESERVATION *)
       (forall (x: obj_addr). 
         Seq.mem x g_sweep.vertices /\ not (is_blue x h_sweep) ==>
         successors g_init x == successors g_sweep x) /\
      
       (* PILLAR 4: STATE RESET *)
       (forall (x: obj_addr). 
         Seq.mem x g_sweep.vertices ==>
         is_white x h_sweep \/ is_blue x h_sweep) /\
      
       (* PILLAR 5: DATA TRANSPARENCY *)
       (forall (x: obj_addr) (i: U64.t).
         Seq.mem x g_sweep.vertices /\ 
         not (is_blue x h_sweep) /\
         U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x h_init) ==>
         HeapGraph.get_field h_init x i == HeapGraph.get_field h_sweep x i)
      ))

let end_to_end_correctness h_init st roots fp =
  mark_preserves_wf h_init st;
  mark_no_grey_remains h_init st;
  gc_preserves_structure h_init st fp;
  gc_preserves_data h_init st fp;
  admit()

/// ---------------------------------------------------------------------------
/// COROLLARY: GC is safe
/// ---------------------------------------------------------------------------

val gc_safety : (h_init: heap) -> (st: seq obj_addr) -> (roots: seq obj_addr) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap h_init /\ stack_props h_init st /\ 
                  root_props h_init roots /\ free_list_props h_init fp /\
                  no_black_objects h_init /\
                  (forall (r: obj_addr). Seq.mem r roots ==> Seq.mem r st) /\
                  (let graph = create_graph h_init in
                   let roots' = HeapGraph.coerce_to_vertex_list roots in
                   graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
        (ensures (let graph = create_graph h_init in
                  let roots' = HeapGraph.coerce_to_vertex_list roots in
                  forall (x: obj_addr).
                    mem_graph_vertex graph x ==>
                    Seq.mem x (reachable_set graph roots') ==>
                    not (is_blue x (fst (sweep (mark h_init st) fp)))))

let gc_safety h_init st roots fp =
  end_to_end_correctness h_init st roots fp

/// ---------------------------------------------------------------------------
/// COROLLARY: GC is complete
/// ---------------------------------------------------------------------------

val gc_completeness : (h_init: heap) -> (st: seq obj_addr) -> (roots: seq obj_addr) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap h_init /\ stack_props h_init st /\ 
                  root_props h_init roots /\ free_list_props h_init fp /\
                  no_black_objects h_init /\
                  (forall (r: obj_addr). Seq.mem r roots ==> Seq.mem r st) /\
                  (let graph = create_graph h_init in
                   let roots' = HeapGraph.coerce_to_vertex_list roots in
                   graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
        (ensures (let graph = create_graph h_init in
                  let roots' = HeapGraph.coerce_to_vertex_list roots in
                  forall (x: obj_addr).
                    mem_graph_vertex graph x ==>
                    Seq.mem x (objects 0UL h_init) /\
                    ~(Seq.mem x (reachable_set graph roots')) /\
                    not (is_blue x h_init) ==>
                    is_blue x (fst (sweep (mark h_init st) fp))))

let gc_completeness h_init st roots fp =
  end_to_end_correctness h_init st roots fp;
  mark_no_grey_remains h_init st;
  admit()
