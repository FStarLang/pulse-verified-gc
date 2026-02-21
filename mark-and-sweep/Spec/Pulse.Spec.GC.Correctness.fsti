/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.Correctness - End-to-End GC Correctness Interface
/// ---------------------------------------------------------------------------
///
/// Exposes abstract GC postcondition predicates and the full correctness
/// theorem. Abstract via .fsti -- clients cannot unfold gc_postcondition
/// or full_gc_correctness, preventing quantifier explosion in Pulse VCs.
///
/// Colors used: White (initial/free), Gray (mark frontier), Black (marked/reachable).
/// After mark: black = reachable, white = unreachable, no gray.
/// After sweep: all objects white (black reset to white, white unchanged).

module Pulse.Spec.GC.Correctness

open FStar.Seq
open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Object
open Pulse.Spec.GC.Fields
open Pulse.Spec.GC.Heap
open Pulse.Spec.GC.Graph
open Pulse.Spec.GC.HeapModel
open Pulse.Spec.GC.DFS
open Pulse.Spec.GC.Mark
open Pulse.Spec.GC.Sweep
module HeapGraph = Pulse.Spec.GC.HeapGraph
module U64 = FStar.UInt64

/// ---------------------------------------------------------------------------
/// Abstract GC Postcondition (Pillars 1 + 4)
/// ---------------------------------------------------------------------------

/// Abstract postcondition: well_formed_heap + no gray or black objects
val gc_postcondition (h_final: heap) : prop

/// Abstract: no gray or black objects (pillar 4 -- color reset)
val no_gray_or_black_objects (h_final: heap) : prop

/// Introduce gc_postcondition from its parts
val gc_postcondition_intro : (h_final: heap) ->
  Lemma (requires well_formed_heap h_final /\
                  (forall (x: obj_addr). Seq.mem x (objects zero_addr h_final) ==>
                    is_white x h_final \/ is_blue x h_final))
        (ensures gc_postcondition h_final)

/// Introduce gc_postcondition from well_formed_heap + no_gray_or_black_objects
val gc_postcondition_from_parts : (h_final: heap) ->
  Lemma (requires well_formed_heap h_final /\ no_gray_or_black_objects h_final)
        (ensures gc_postcondition h_final)

/// Eliminate gc_postcondition to recover its parts
val gc_postcondition_elim : (h_final: heap) ->
  Lemma (requires gc_postcondition h_final)
        (ensures well_formed_heap h_final /\
                 (forall (x: obj_addr). Seq.mem x (objects zero_addr h_final) ==>
                   is_white x h_final \/ is_blue x h_final))

/// ---------------------------------------------------------------------------
/// Full GC Correctness -- All 5 pillars as abstract predicate
/// ---------------------------------------------------------------------------
///
/// Wraps all 5 pillars from the end-to-end correctness theorem.
/// Unlike gc_postcondition which only captures pillars 1+4,
/// this predicate also captures:
///   Pillar 2: black after mark <==> reachable from roots
///   Pillar 3: successors preserved for reachable objects
///   Pillar 5: field data preserved for reachable objects
///
/// Kept abstract to prevent quantifier explosion in Pulse VCs.
/// Use full_gc_correctness_elim_* lemmas to recover individual pillars.

/// Abstract predicate wrapping all 5 pillars of correctness
val full_gc_correctness (h_init h_final: heap) (roots: seq obj_addr) : prop

/// Introduce full_gc_correctness from its parts
val full_gc_correctness_intro : (h_init: heap) -> (h_mark: heap) -> (h_final: heap) ->
  (roots: seq obj_addr) ->
  Lemma
    (requires
      (let g_init = create_graph h_init in
       let g_final = create_graph h_final in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       // Pillar 1: heap integrity
       well_formed_heap h_final /\
       // Pillar 2: reachability
       (graph_wf g_init /\ is_vertex_set roots' /\ subset_vertices roots' g_init.vertices ==>
         (forall (x: obj_addr). mem_graph_vertex g_init x ==>
           (is_black x h_mark <==> Seq.mem x (reachable_set g_init roots')))) /\
       // Pillar 3: structural preservation
       (forall (x: obj_addr).
         Seq.mem x g_final.vertices /\ is_black x h_mark ==>
         successors g_init x == successors g_final x) /\
       // Pillar 4: color reset
       (forall (x: obj_addr).
         Seq.mem x g_final.vertices ==>
         (is_white x h_final \/ is_blue x h_final)) /\
       (forall (x: obj_addr).
         Seq.mem x g_final.vertices /\ is_black x h_mark ==>
         is_white x h_final) /\
       // Pillar 5: data transparency
       (forall (x: obj_addr) (i: U64.t).
         Seq.mem x g_final.vertices /\ is_black x h_mark /\
         U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x h_init) ==>
         HeapGraph.get_field h_init x i == HeapGraph.get_field h_final x i)))
    (ensures full_gc_correctness h_init h_final roots)

/// Eliminate: Pillar 1 -- heap integrity
val full_gc_correctness_elim_wfh : h_init:heap -> h_final:heap -> roots:seq obj_addr ->
  Lemma (requires full_gc_correctness h_init h_final roots)
        (ensures well_formed_heap h_final)

/// Eliminate: Pillar 4 -- color reset (all objects white or blue)
val full_gc_correctness_elim_colors : h_init:heap -> h_final:heap -> roots:seq obj_addr ->
  Lemma (requires full_gc_correctness h_init h_final roots)
        (ensures gc_postcondition h_final)

/// ---------------------------------------------------------------------------
/// End-to-End Correctness Theorem
/// ---------------------------------------------------------------------------

val end_to_end_correctness :
  (h_init: heap) ->
  (st: seq obj_addr) ->
  (roots: seq obj_addr) ->
  (fp: U64.t) ->
  Lemma
    (requires
      well_formed_heap h_init /\
      stack_props h_init st /\
      root_props h_init roots /\
      fp_in_heap fp h_init /\
      no_black_objects h_init /\
      no_pointer_to_blue h_init /\
      (forall (r: obj_addr). Seq.mem r roots <==> Seq.mem r st) /\
      (let graph = create_graph h_init in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
    (ensures
      (let h_mark = mark h_init st in
       let h_sweep = fst (sweep h_mark fp) in
       let g_init = create_graph h_init in
       let g_sweep = create_graph h_sweep in
       well_formed_heap h_sweep /\
       (let roots' = HeapGraph.coerce_to_vertex_list roots in
        graph_wf g_init /\ is_vertex_set roots' /\ subset_vertices roots' g_init.vertices ==>
        (forall (x: obj_addr).
          mem_graph_vertex g_init x ==>
          (is_black x h_mark <==> Seq.mem x (reachable_set g_init roots')))) /\
       (forall (x: obj_addr).
         Seq.mem x g_sweep.vertices /\ is_black x h_mark ==>
         successors g_init x == successors g_sweep x) /\
       (forall (x: obj_addr).
         Seq.mem x g_sweep.vertices ==>
         (is_white x h_sweep \/ is_blue x h_sweep)) /\
       (forall (x: obj_addr).
         Seq.mem x g_sweep.vertices /\ is_black x h_mark ==>
         is_white x h_sweep) /\
       (forall (x: obj_addr) (i: U64.t).
         Seq.mem x g_sweep.vertices /\
         is_black x h_mark /\
         U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x h_init) ==>
         HeapGraph.get_field h_init x i == HeapGraph.get_field h_sweep x i)))

/// ---------------------------------------------------------------------------
/// Corollaries and Bridges
/// ---------------------------------------------------------------------------

/// Derive gc_postcondition from end_to_end_correctness
val gc_postcondition_from_correctness :
  (h_init: heap) -> (st: seq obj_addr) -> (roots: seq obj_addr) -> (fp: U64.t) ->
  Lemma
    (requires
      well_formed_heap h_init /\
      stack_props h_init st /\
      root_props h_init roots /\
      fp_in_heap fp h_init /\
      no_black_objects h_init /\
      no_pointer_to_blue h_init /\
      (forall (r: obj_addr). Seq.mem r roots <==> Seq.mem r st) /\
      (let graph = create_graph h_init in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
    (ensures gc_postcondition (fst (sweep (mark h_init st) fp)))

/// Derive full_gc_correctness from end_to_end_correctness
val full_gc_correctness_from_end_to_end :
  (h_init: heap) -> (st: seq obj_addr) -> (roots: seq obj_addr) -> (fp: U64.t) ->
  Lemma
    (requires
      well_formed_heap h_init /\
      stack_props h_init st /\
      root_props h_init roots /\
      fp_in_heap fp h_init /\
      no_black_objects h_init /\
      no_pointer_to_blue h_init /\
      (forall (r: obj_addr). Seq.mem r roots <==> Seq.mem r st) /\
      (let graph = create_graph h_init in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
    (ensures full_gc_correctness h_init (fst (sweep (mark h_init st) fp)) roots)

/// GC safety: reachable objects survive
val gc_safety : (h_init: heap) -> (st: seq obj_addr) -> (roots: seq obj_addr) -> (fp: U64.t) ->
  Lemma (requires well_formed_heap h_init /\ stack_props h_init st /\
                  root_props h_init roots /\
                  fp_in_heap fp h_init /\
                  no_black_objects h_init /\
                  no_pointer_to_blue h_init /\
                  (forall (r: obj_addr). Seq.mem r roots <==> Seq.mem r st) /\
                  (let graph = create_graph h_init in
                   let roots' = HeapGraph.coerce_to_vertex_list roots in
                   graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
        (ensures (let graph = create_graph h_init in
                  let roots' = HeapGraph.coerce_to_vertex_list roots in
                  let h_sweep = fst (sweep (mark h_init st) fp) in
                  forall (x: obj_addr).
                    mem_graph_vertex graph x /\
                    Seq.mem x (reachable_set graph roots') ==>
                    Seq.mem x (objects zero_addr h_sweep)))

/// GC completeness: unreachable objects are not marked
val gc_completeness : (h_init: heap) -> (st: seq obj_addr) -> (roots: seq obj_addr) -> (fp: U64.t) ->
  Lemma (requires well_formed_heap h_init /\ stack_props h_init st /\
                  root_props h_init roots /\
                  no_black_objects h_init /\
                  no_pointer_to_blue h_init /\
                  (forall (r: obj_addr). Seq.mem r roots <==> Seq.mem r st) /\
                  (let graph = create_graph h_init in
                   let roots' = HeapGraph.coerce_to_vertex_list roots in
                   graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
        (ensures (let graph = create_graph h_init in
                  let roots' = HeapGraph.coerce_to_vertex_list roots in
                  let h_mark = mark h_init st in
                  forall (x: obj_addr).
                    mem_graph_vertex graph x /\
                    ~(Seq.mem x (reachable_set graph roots')) ==>
                    ~(is_black x h_mark)))
