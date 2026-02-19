/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.Correctness - End-to-End GC Correctness
/// ---------------------------------------------------------------------------
///
/// Uses obj_addr convention from common/.
/// Colors used: White (initial/free), Gray (mark frontier), Black (marked/reachable).
/// After mark: black = reachable, white = unreachable, no gray.
/// After sweep: all objects white (black reset to white, white unchanged).

module Pulse.Spec.GC.Correctness

#set-options "--z3rlimit 50 --fuel 2 --ifuel 1"

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
/// For objects that were black after mark (i.e., reachable), sweep preserves
/// their graph successors. This is because sweep only does set_field on white
/// objects (to link into free list) and makeWhite on black objects (header-only).

val gc_preserves_structure : (g: heap) -> (st: seq obj_addr) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ 
                  (fp = 0UL \/ Seq.mem fp (objects 0UL g)))
        (ensures (forall (x: obj_addr).
                   Seq.mem x (objects 0UL (fst (sweep (mark g st) fp))) /\
                   is_black x (mark g st) ==>
                   successors (create_graph g) x ==
                   successors (create_graph (fst (sweep (mark g st) fp))) x))

let gc_preserves_structure g st fp =
  mark_preserves_wf g st;
  mark_no_grey_remains g st;
  let g_mark = mark g st in
  let g_sweep = fst (sweep g_mark fp) in
  mark_preserves_create_graph g st;
  mark_aux_preserves_objects g st (heap_size / U64.v mword);
  assert (objects 0UL g_mark == objects 0UL g);
  sweep_preserves_objects g_mark fp;
  // objects 0UL g_mark == objects 0UL g_sweep
  objects_is_vertex_set g;
  objects_is_vertex_set g_mark;
  objects_is_vertex_set g_sweep;
  let aux (x: obj_addr) : Lemma
    (requires Seq.mem x (objects 0UL g_sweep) /\ is_black x g_mark)
    (ensures successors (create_graph g) x == successors (create_graph g_sweep) x)
  = // successors(create_graph g) x == successors(create_graph g_mark) x [by mark_preserves_create_graph]
    // successors(create_graph g_mark) x == get_pointer_fields g_mark x [by bridge]
    HeapGraph.successors_eq_pointer_fields g_mark (objects 0UL g_mark) x;
    // get_pointer_fields g_mark x == get_pointer_fields g_sweep x [by sweep_preserves_edges]
    sweep_preserves_edges g_mark fp x;
    // get_pointer_fields g_sweep x == successors(create_graph g_sweep) x [by bridge]
    HeapGraph.successors_eq_pointer_fields g_sweep (objects 0UL g_sweep) x;
    // Chain: successors g x == successors g_mark x == pf g_mark x == pf g_sweep x == successors g_sweep x
    assert (Seq.equal (successors (create_graph g) x) (successors (create_graph g_sweep) x));
    Seq.lemma_eq_elim (successors (create_graph g) x) (successors (create_graph g_sweep) x)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// ---------------------------------------------------------------------------
/// Pillar 5: Data Transparency  
/// ---------------------------------------------------------------------------
/// For objects that were black after mark, sweep preserves their field data.

val gc_preserves_data : (g: heap) -> (st: seq obj_addr) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ 
                  (fp = 0UL \/ Seq.mem fp (objects 0UL g)))
        (ensures (forall (x: obj_addr) (i: U64.t).
                   Seq.mem x (objects 0UL (fst (sweep (mark g st) fp))) /\
                   is_black x (mark g st) /\
                   U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x g) ==>
                   HeapGraph.get_field g x i == 
                   HeapGraph.get_field (fst (sweep (mark g st) fp)) x i))

#push-options "--z3rlimit 100"
let gc_preserves_data g st fp =
  mark_preserves_wf g st;
  mark_no_grey_remains g st;
  mark_aux_preserves_objects g st (heap_size / U64.v mword);
  assert (objects 0UL (mark g st) == objects 0UL g);
  sweep_preserves_objects (mark g st) fp;
  let aux (x: obj_addr) (i: U64.t{U64.v i >= 1}) : Lemma
    (requires Seq.mem x (objects 0UL (fst (sweep (mark g st) fp))) /\
             is_black x (mark g st) /\
             U64.v i <= U64.v (wosize_of_object x g))
    (ensures HeapGraph.get_field g x i == 
             HeapGraph.get_field (fst (sweep (mark g st) fp)) x i)
  = mark_preserves_wosize g st x;
    mark_preserves_get_field g st x i;
    sweep_preserves_field (mark g st) fp x i
  in
  // Universally quantify: for each x, for each i with refinement
  let wrap (x: obj_addr) : Lemma
    (forall (i: U64.t{U64.v i >= 1}). 
      Seq.mem x (objects 0UL (fst (sweep (mark g st) fp))) /\
      is_black x (mark g st) /\
      U64.v i <= U64.v (wosize_of_object x g) ==>
      HeapGraph.get_field g x i == 
      HeapGraph.get_field (fst (sweep (mark g st) fp)) x i)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (aux x))
  in
  FStar.Classical.forall_intro wrap
#pop-options

/// ---------------------------------------------------------------------------
/// THE END-TO-END CORRECTNESS THEOREM
/// ---------------------------------------------------------------------------
/// 
/// Preconditions:
/// - Well-formed heap with valid stack and roots
/// - No black objects initially (all objects are white or gray from root pushing)
///
/// Five pillars of correctness:
/// 1. Heap integrity: well_formed_heap preserved through mark+sweep
/// 2. Reachability: black after mark ⟺ reachable from roots
/// 3. Structure: successors preserved for reachable objects
/// 4. State reset: all objects white after sweep
/// 5. Data: field data preserved for reachable objects

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
      (fp = 0UL \/ Seq.mem fp (objects 0UL h_init)) /\
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
      
       (* PILLAR 1: HEAP INTEGRITY *)
       well_formed_heap h_sweep /\
      
       (* PILLAR 2: REACHABILITY — black after mark ⟺ reachable *)
       (let roots' = HeapGraph.coerce_to_vertex_list roots in
        graph_wf g_init /\ is_vertex_set roots' /\ subset_vertices roots' g_init.vertices ==>
        (forall (x: obj_addr). 
          mem_graph_vertex g_init x ==>
          (is_black x h_mark <==> Seq.mem x (reachable_set g_init roots')))) /\
      
       (* PILLAR 3: STRUCTURAL PRESERVATION for reachable objects *)
       (forall (x: obj_addr). 
         Seq.mem x g_sweep.vertices /\ is_black x h_mark ==>
         successors g_init x == successors g_sweep x) /\
      
       (* PILLAR 4: COLOR RESET — no gray or black after sweep, reachable objects white *)
       (forall (x: obj_addr). 
         Seq.mem x g_sweep.vertices ==>
         (is_white x h_sweep \/ is_blue x h_sweep)) /\
       (forall (x: obj_addr).
         Seq.mem x g_sweep.vertices /\ is_black x h_mark ==>
         is_white x h_sweep) /\
      
       (* PILLAR 5: DATA TRANSPARENCY for reachable objects *)
       (forall (x: obj_addr) (i: U64.t).
         Seq.mem x g_sweep.vertices /\ 
         is_black x h_mark /\
         U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x h_init) ==>
         HeapGraph.get_field h_init x i == HeapGraph.get_field h_sweep x i)
      ))

let end_to_end_correctness h_init st roots fp =
  let h_mark = mark h_init st in
  let h_sweep = fst (sweep h_mark fp) in
  mark_preserves_wf h_init st;
  mark_no_grey_remains h_init st;
  
  mark_aux_preserves_objects h_init st (heap_size / U64.v mword);
  assert (objects 0UL h_mark == objects 0UL h_init);
  assert (fp = 0UL \/ Seq.mem fp (objects 0UL h_mark));
  
  // PILLAR 1: well_formed_heap h_sweep
  sweep_preserves_wf h_mark fp;
  
  // PILLAR 2: Reachability (graph properties now in precondition)
  mark_reachable_is_black h_init st roots;
  mark_black_is_reachable h_init st roots;
  
  // PILLAR 3: Structure preservation
  gc_preserves_structure h_init st fp;
  // Bridge: g_sweep.vertices <-> objects 0UL g_sweep
  sweep_preserves_objects h_mark fp;
  mark_preserves_create_graph h_init st;
  let bridge (x: obj_addr) : Lemma 
    (Seq.mem x (objects 0UL h_sweep) <==> 
     Seq.mem x (create_graph h_sweep).vertices)
    = graph_vertices_mem h_sweep x
  in FStar.Classical.forall_intro bridge;
  let bridge_init (x: obj_addr) : Lemma 
    (Seq.mem x (objects 0UL h_init) <==> 
     Seq.mem x (create_graph h_init).vertices)
    = graph_vertices_mem h_init x
  in FStar.Classical.forall_intro bridge_init;
  
  // PILLAR 4: Colors after sweep (white or blue; reachable objects white)
  sweep_resets_colors h_mark fp;
  sweep_resets_black_to_white h_mark fp;
  
  // PILLAR 5: Data preservation
  gc_preserves_data h_init st fp

/// ---------------------------------------------------------------------------
/// COROLLARY: GC is safe (reachable objects survive)
/// ---------------------------------------------------------------------------

val gc_safety : (h_init: heap) -> (st: seq obj_addr) -> (roots: seq obj_addr) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap h_init /\ stack_props h_init st /\ 
                  root_props h_init roots /\
                  (fp = 0UL \/ Seq.mem fp (objects 0UL h_init)) /\
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
                    Seq.mem x (objects 0UL h_sweep)))

let gc_safety h_init st roots fp =
  end_to_end_correctness h_init st roots fp;
  mark_aux_preserves_objects h_init st (heap_size / U64.v mword);
  mark_preserves_wf h_init st;
  mark_no_grey_remains h_init st;
  sweep_preserves_objects (mark h_init st) fp;
  let bridge (x: obj_addr) : Lemma
    (Seq.mem x (objects 0UL h_init) <==> Seq.mem x (create_graph h_init).vertices)
    = graph_vertices_mem h_init x
  in FStar.Classical.forall_intro bridge

/// ---------------------------------------------------------------------------
/// COROLLARY: GC is complete (unreachable objects are freed)
/// ---------------------------------------------------------------------------
/// After GC, unreachable objects remain white but are NOT black (they were
/// never marked). White objects with ws>0 have their field 1 linked into the
/// free list by sweep.

val gc_completeness : (h_init: heap) -> (st: seq obj_addr) -> (roots: seq obj_addr) -> (fp: obj_addr) ->
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

let gc_completeness h_init st roots fp =
  // mark_black_is_reachable: is_black x h_mark ==> reachable x
  // Contrapositive: ~(reachable x) ==> ~(is_black x h_mark)
  mark_black_is_reachable h_init st roots

/// ---------------------------------------------------------------------------
/// BRIDGE TO ABSTRACT GC POSTCONDITION
/// ---------------------------------------------------------------------------
/// gc_postcondition (from GCPost) wraps pillars 1 and 4 as an abstract prop.
/// This lemma derives gc_postcondition from end_to_end_correctness.

open Pulse.Spec.GC.GCPost

val gc_postcondition_from_correctness :
  (h_init: heap) -> (st: seq obj_addr) -> (roots: seq obj_addr) -> (fp: obj_addr) ->
  Lemma
    (requires 
      well_formed_heap h_init /\
      stack_props h_init st /\
      root_props h_init roots /\
      (fp = 0UL \/ Seq.mem fp (objects 0UL h_init)) /\
      no_black_objects h_init /\
      no_pointer_to_blue h_init /\
      (forall (r: obj_addr). Seq.mem r roots <==> Seq.mem r st) /\
      (let graph = create_graph h_init in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
    (ensures gc_postcondition (fst (sweep (mark h_init st) fp)))

let gc_postcondition_from_correctness h_init st roots fp =
  end_to_end_correctness h_init st roots fp;
  let h_mark = mark h_init st in
  let h_sweep = fst (sweep h_mark fp) in
  // end_to_end_correctness gives: well_formed_heap h_sweep
  // and all objects white in graph vertices
  // Bridge from graph vertices to objects 0UL:
  mark_preserves_wf h_init st;
  mark_no_grey_remains h_init st;
  mark_aux_preserves_objects h_init st (heap_size / U64.v mword);
  sweep_preserves_objects h_mark fp;
  sweep_resets_colors h_mark fp;
  sweep_preserves_wf h_mark fp;
  gc_postcondition_intro h_sweep
