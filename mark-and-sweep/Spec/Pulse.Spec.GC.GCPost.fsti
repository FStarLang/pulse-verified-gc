/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.GCPost - Abstract GC Postcondition Predicate
/// ---------------------------------------------------------------------------
///
/// Wraps pillars 1 (heap integrity) and 4 (state reset) from the
/// end-to-end correctness theorem into an abstract predicate.
/// Abstract via .fsti -- clients cannot unfold, preventing quantifier
/// explosion in Pulse postconditions.
///
/// Use gc_postcondition_elim to recover the constituent properties.

module Pulse.Spec.GC.GCPost

open FStar.Seq
open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Object
open Pulse.Spec.GC.Fields

/// Abstract postcondition: well_formed_heap + no gray or black objects
val gc_postcondition (h_final: heap) : prop

/// Abstract: no gray or black objects (pillar 4 -- color reset)
val no_gray_or_black_objects (h_final: heap) : prop

/// Introduce gc_postcondition from its parts
val gc_postcondition_intro : (h_final: heap) ->
  Lemma (requires well_formed_heap h_final /\
                  (forall (x: obj_addr). Seq.mem x (objects 0UL h_final) ==> 
                    is_white x h_final \/ is_blue x h_final))
        (ensures gc_postcondition h_final)

/// Introduce gc_postcondition from well_formed_heap (proven) + no_gray_or_black_objects (abstract)
val gc_postcondition_from_parts : (h_final: heap) ->
  Lemma (requires well_formed_heap h_final /\ no_gray_or_black_objects h_final)
        (ensures gc_postcondition h_final)

/// Eliminate gc_postcondition to recover its parts
val gc_postcondition_elim : (h_final: heap) ->
  Lemma (requires gc_postcondition h_final)
        (ensures well_formed_heap h_final /\
                 (forall (x: obj_addr). Seq.mem x (objects 0UL h_final) ==> 
                   is_white x h_final \/ is_blue x h_final))

/// ---------------------------------------------------------------------------
/// Full GC Correctness -- All 5 pillars as abstract predicate
/// ---------------------------------------------------------------------------
///
/// Wraps all 5 pillars from the end-to-end correctness theorem.
/// Unlike gc_postcondition which only captures pillars 1+4,
/// this predicate also captures:
///   Pillar 2: black after mark ⟺ reachable from roots
///   Pillar 3: successors preserved for reachable objects
///   Pillar 5: field data preserved for reachable objects
///
/// Kept abstract to prevent quantifier explosion in Pulse VCs.
/// Use full_gc_correctness_elim_* lemmas to recover individual pillars.

open Pulse.Spec.GC.Heap
open Pulse.Spec.GC.Graph
open Pulse.Spec.GC.HeapModel
open Pulse.Spec.GC.DFS
module HeapGraph = Pulse.Spec.GC.HeapGraph
module U64 = FStar.UInt64

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
