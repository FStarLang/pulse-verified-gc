/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.GCPost - Implementation
/// ---------------------------------------------------------------------------

module Pulse.Spec.GC.GCPost

open FStar.Seq
open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Object
open Pulse.Spec.GC.Fields
open Pulse.Spec.GC.Heap
open Pulse.Spec.GC.Graph
open Pulse.Spec.GC.HeapModel
open Pulse.Spec.GC.DFS
module HeapGraph = Pulse.Spec.GC.HeapGraph
module U64 = FStar.UInt64

let gc_postcondition (h_final: heap) : prop =
  well_formed_heap h_final /\
  (forall (x: obj_addr). Seq.mem x (objects 0UL h_final) ==> 
    is_white x h_final \/ is_blue x h_final)

let no_gray_or_black_objects (h_final: heap) : prop =
  forall (x: obj_addr). Seq.mem x (objects 0UL h_final) ==> 
    is_white x h_final \/ is_blue x h_final

let gc_postcondition_intro h_final = ()

let gc_postcondition_from_parts h_final = ()

let gc_postcondition_elim h_final = ()

/// Full correctness: all 5 pillars
let full_gc_correctness (h_init h_final: heap) (roots: seq obj_addr) : prop =
  exists (h_mark: heap).
  (let g_init = create_graph h_init in
   let g_final = create_graph h_final in
   let roots' = HeapGraph.coerce_to_vertex_list roots in
   // Pillar 1
   well_formed_heap h_final /\
   // Pillar 2
   (graph_wf g_init /\ is_vertex_set roots' /\ subset_vertices roots' g_init.vertices ==>
     (forall (x: obj_addr). mem_graph_vertex g_init x ==>
       (is_black x h_mark <==> Seq.mem x (reachable_set g_init roots')))) /\
   // Pillar 3
   (forall (x: obj_addr).
     Seq.mem x g_final.vertices /\ is_black x h_mark ==>
     successors g_init x == successors g_final x) /\
   // Pillar 4
   (forall (x: obj_addr).
     Seq.mem x g_final.vertices ==>
     (is_white x h_final \/ is_blue x h_final)) /\
   (forall (x: obj_addr).
     Seq.mem x g_final.vertices /\ is_black x h_mark ==>
     is_white x h_final) /\
   // Pillar 5
   (forall (x: obj_addr) (i: U64.t).
     Seq.mem x g_final.vertices /\ is_black x h_mark /\
     U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x h_init) ==>
     HeapGraph.get_field h_init x i == HeapGraph.get_field h_final x i))

let full_gc_correctness_intro h_init h_mark h_final roots = ()

let full_gc_correctness_elim_wfh h_init h_final roots = ()

let full_gc_correctness_elim_colors h_init h_final roots =
  // full_gc_correctness gives us exists h_mark. ... wfh /\ ... forall x in vertices ...
  // We need to bridge from graph vertices to objects 0UL for gc_postcondition_intro
  let aux () : Lemma
    (requires full_gc_correctness h_init h_final roots)
    (ensures well_formed_heap h_final /\
             (forall (x: obj_addr). Seq.mem x (objects 0UL h_final) ==>
               is_white x h_final \/ is_blue x h_final))
  = // The existential gives us pillar 1 (wfh) and pillar 4 (forall x in vertices)
    // We need: forall x in (objects 0UL h_final) ==> white \/ blue
    // Since create_graph h_final . vertices == objects 0UL h_final (by graph_vertices_mem), done
    let bridge (x: obj_addr) : Lemma
      (Seq.mem x (objects 0UL h_final) <==> Seq.mem x (create_graph h_final).vertices)
    = graph_vertices_mem h_final x
    in
    FStar.Classical.forall_intro bridge
  in
  aux ();
  gc_postcondition_intro h_final
