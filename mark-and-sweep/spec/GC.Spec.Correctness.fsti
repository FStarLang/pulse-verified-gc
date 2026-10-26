/// ---------------------------------------------------------------------------
/// GC.Spec.Correctness - End-to-End GC Correctness Interface
/// ---------------------------------------------------------------------------
///
/// Exposes abstract GC postcondition predicates and the full correctness
/// theorem. Abstract via .fsti -- clients cannot unfold gc_postcondition
/// or full_gc_correctness, preventing quantifier explosion in Pulse VCs.
///
/// Colors used: White (initial/free), Gray (mark frontier), Black (marked/reachable).
/// After mark: black = reachable, white = unreachable, no gray.
/// After the sweep: survivors white, everything else blue (free).

module GC.Spec.Correctness

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Heap
open GC.Spec.Graph
open GC.Spec.HeapModel
open GC.Spec.DFS
open GC.Spec.Mark
module HeapGraph = GC.Spec.HeapGraph
module SweepInv = GC.Spec.SweepInv
module FL = GC.Spec.FreeList
module MarkInv = GC.Spec.MarkInv
module FS = GC.Spec.FusedSweep
module FSI = GC.Spec.FusedSweep.Inv
module FSE = GC.Spec.FusedSweep.End
module FLA = GC.Spec.FreeList.Ascending
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

/// ---------------------------------------------------------------------------
/// Generalized Mark Postcondition
/// ---------------------------------------------------------------------------
///
/// Bundles all properties that any correct mark algorithm must establish.
/// Both `mark` (unbounded stack) and `mark_bounded` (bounded stack with
/// overflow handling) satisfy this predicate.
///
/// This allows the GC correctness proofs to be parametric in the mark
/// implementation: `full_gc_correctness_gen` takes any h_mark satisfying
/// mark_post, rather than hardcoding `mark h_init st`.

val mark_post (h_init h_mark: heap) (roots: seq obj_addr) (fp: U64.t) : prop

val mark_post_intro :
  (h_init: heap) -> (h_mark: heap) -> (roots: seq obj_addr) -> (fp: U64.t) ->
  Lemma
    (requires
      well_formed_heap h_init /\ well_formed_heap h_mark /\
      noGreyObjects h_mark /\
      objects zero_addr h_mark == objects zero_addr h_init /\
      heap_objects_dense h_mark /\
      Seq.length (objects zero_addr h_mark) > 0 /\
      no_pointer_to_blue h_mark /\
      tri_color_invariant h_mark /\
      FL.fp_in_heap fp h_init /\
      no_black_objects h_init /\
      no_pointer_to_blue h_init /\
      (let g_init = create_graph h_init in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf g_init /\ is_vertex_set roots' /\ subset_vertices roots' g_init.vertices ==>
       (forall (x: obj_addr). mem_graph_vertex g_init x ==>
         (is_black x h_mark <==> Seq.mem x (reachable_set g_init roots')))) /\
      create_graph h_mark == create_graph h_init /\
      (forall (x: obj_addr). Seq.mem x (objects zero_addr h_init) ==>
        wosize_of_object x h_mark == wosize_of_object x h_init) /\
      (forall (x: obj_addr). Seq.mem x (objects zero_addr h_init) ==>
        is_blue x h_mark == is_blue x h_init) /\
      (forall (x: obj_addr) (i: U64.t). Seq.mem x (objects zero_addr h_init) /\
        U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x h_init) ==>
        HeapGraph.get_field h_mark x i == HeapGraph.get_field h_init x i))
    (ensures mark_post h_init h_mark roots fp)

/// Eliminate mark_post to recover individual properties
val mark_post_elim_wfh : h_init:heap -> h_mark:heap -> roots:seq obj_addr -> fp:U64.t ->
  Lemma (requires mark_post h_init h_mark roots fp) (ensures well_formed_heap h_mark)
val mark_post_elim_no_grey : h_init:heap -> h_mark:heap -> roots:seq obj_addr -> fp:U64.t ->
  Lemma (requires mark_post h_init h_mark roots fp) (ensures noGreyObjects h_mark)
val mark_post_elim_objects : h_init:heap -> h_mark:heap -> roots:seq obj_addr -> fp:U64.t ->
  Lemma (requires mark_post h_init h_mark roots fp)
        (ensures objects zero_addr h_mark == objects zero_addr h_init)
val mark_post_elim_tri_color : h_init:heap -> h_mark:heap -> roots:seq obj_addr -> fp:U64.t ->
  Lemma (requires mark_post h_init h_mark roots fp) (ensures tri_color_invariant h_mark)
val mark_post_elim_no_pointer_to_blue : h_init:heap -> h_mark:heap -> roots:seq obj_addr -> fp:U64.t ->
  Lemma (requires mark_post h_init h_mark roots fp) (ensures no_pointer_to_blue h_mark)
val mark_post_elim_graph : h_init:heap -> h_mark:heap -> roots:seq obj_addr -> fp:U64.t ->
  Lemma (requires mark_post h_init h_mark roots fp)
        (ensures create_graph h_mark == create_graph h_init)
val mark_post_elim_density : h_init:heap -> h_mark:heap -> roots:seq obj_addr -> fp:U64.t ->
  Lemma (requires mark_post h_init h_mark roots fp)
        (ensures heap_objects_dense h_mark)
val mark_post_elim_objects_gt0 : h_init:heap -> h_mark:heap -> roots:seq obj_addr -> fp:U64.t ->
  Lemma (requires mark_post h_init h_mark roots fp)
        (ensures Seq.length (objects zero_addr h_mark) > 0)
val mark_post_elim_fp : h_init:heap -> h_mark:heap -> roots:seq obj_addr -> fp:U64.t ->
  Lemma (requires mark_post h_init h_mark roots fp)
        (ensures FL.fp_in_heap fp h_mark)

/// Marking leaves free blocks -- and so the free list -- alone.
val mark_post_elim_blue : h_init:heap -> h_mark:heap -> roots:seq obj_addr -> fp:U64.t ->
  Lemma (requires mark_post h_init h_mark roots fp)
        (ensures (forall (x: obj_addr). Seq.mem x (objects zero_addr h_init) ==>
                    is_blue x h_mark == is_blue x h_init /\
                    wosize_of_object x h_mark == wosize_of_object x h_init) /\
                 (forall (x: obj_addr) (i: U64.t). Seq.mem x (objects zero_addr h_init) /\
                    U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x h_init) ==>
                    HeapGraph.get_field h_mark x i == HeapGraph.get_field h_init x i) /\
                 objects zero_addr h_mark == objects zero_addr h_init)

let heap_reachable (h: heap) (roots: seq obj_addr) (x: obj_addr) : prop =
  let g = create_graph h in
  let roots' = HeapGraph.coerce_to_vertex_list roots in
  graph_wf g /\
  is_vertex_set roots' /\
  subset_vertices roots' g.vertices /\
  mem_graph_vertex g x /\
  Seq.mem x (reachable_set g roots')

let heap_edge (h: heap) (x y: obj_addr) : prop =
  mem_graph_edge (create_graph h) x y

let major_gc_live_subgraph_isomorphism
  (h_init h_final: heap) (roots: seq obj_addr) : prop =
  (forall (x: obj_addr).
    heap_reachable h_init roots x ==>
    Seq.mem x (objects zero_addr h_final) /\ is_white x h_final) /\
  (forall (x y: obj_addr).
    heap_reachable h_init roots x /\
    heap_reachable h_init roots y ==>
    (heap_edge h_init x y <==> heap_edge h_final x y)) /\
  (forall (x: obj_addr) (i: U64.t).
    heap_reachable h_init roots x /\
    U64.v i >= 1 /\
    U64.v i <= U64.v (wosize_of_object x h_init) ==>
    HeapGraph.get_field h_init x i == HeapGraph.get_field h_final x i) /\
  /// Successor *lists* agree on live objects.  This is strictly stronger than
  /// the edge clause above, which is guarded on both endpoints already being
  /// live; without it, transferring reachability backwards (final ⇒ initial)
  /// would be circular, since the induction meets successors that are not yet
  /// known to be live.  See `GC.Gen.MajorReachabilityTransfer`.
  (forall (x: obj_addr).
    heap_reachable h_init roots x ==>
    mem_graph_vertex (create_graph h_final) x /\
    successors (create_graph h_init) x == successors (create_graph h_final) x)

let major_gc_unreachable_final_blue
  (h_init h_final: heap) (roots: seq obj_addr) : prop =
  forall (x: obj_addr).
    Seq.mem x (objects zero_addr h_final) /\
    ~(heap_reachable h_final roots x) ==>
    is_blue x h_final

/// `mark h_init st` satisfies mark_post under the standard GC preconditions
val mark_satisfies_mark_post :
  (h_init: heap) -> (st: seq obj_addr) -> (roots: seq obj_addr) -> (fp: U64.t) ->
  Lemma
    (requires
      MarkInv.mark_inv h_init st /\
      root_props h_init roots /\
      FL.fp_in_heap fp h_init /\
      no_black_objects h_init /\
      no_pointer_to_blue h_init /\
      (forall (r: obj_addr). Seq.mem r roots <==> Seq.mem r st) /\
      (let graph = create_graph h_init in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
    (ensures mark_post h_init (mark h_init st) roots fp)

/// The mark output that produced a given collector result.
///
/// `GC.Impl.collect_with_roots` runs mark, then the fused sweep, and the
/// intermediate marked heap never escapes.  Downstream clients (notably
/// `GC.Gen.PostCollectionShape`, which re-establishes the generational shape
/// invariant on the collector's output) need to know that the returned heap
/// and free pointer are exactly `fused_sweep_coalesce h_mark fp` for *some*
/// heap `h_mark` satisfying `mark_post`, and that the sweep started from an
/// exact, ascending free list.  This predicate packages that existential so it
/// can be carried across a Pulse postcondition.
let gc_coalesce_source (h_init s2: heap) (roots: seq obj_addr) (fp final_fp: U64.t) : prop =
  FLA.fl_ascending h_init fp /\
  (exists (h_mark: heap).
    mark_post h_init h_mark roots fp /\
    (s2, final_fp) == FS.fused_sweep_coalesce h_mark fp)

val gc_coalesce_source_intro :
  (h_init: heap) -> (h_mark: heap) -> (roots: seq obj_addr) -> (fp: U64.t) ->
  (s2: heap) -> (final_fp: U64.t) ->
  Lemma
    (requires mark_post h_init h_mark roots fp /\ FLA.fl_ascending h_init fp /\
              (s2, final_fp) == FS.fused_sweep_coalesce h_mark fp)
    (ensures gc_coalesce_source h_init s2 roots fp final_fp)

/// ---------------------------------------------------------------------------
/// The theorems, at the heap the fused sweep produces
/// ---------------------------------------------------------------------------
///
/// The collector sweeps with `GC.Spec.FusedSweep.fused_sweep_coalesce`, which
/// keeps the free list across cycles and edits it in place.  It therefore
/// needs the list it is handed to be exact and ascending
/// (`GC.Spec.FreeList.Ascending.fl_ascending`); every other hypothesis is the
/// mark postcondition.  The statements below are the collector's theorems at
/// the heap that pass returns, proved from its end lemma
/// (`GC.Spec.FusedSweep.End`), with no reference heap in between.

/// What the sweep needs, from the mark postcondition and the free list.
val mark_post_sweep_pre :
  (h_init: heap) -> (h_mark: heap) -> (roots: seq obj_addr) -> (fp: U64.t) ->
  Lemma
    (requires mark_post h_init h_mark roots fp /\ FLA.fl_ascending h_init fp)
    (ensures FSI.sweep_pre h_mark fp /\ FSE.marked h_mark)

/// Everything the sweep leaves behind (`FSE.sweep_post`), with well-formedness.
val fused_post_gen :
  (h_init: heap) -> (h_mark: heap) -> (roots: seq obj_addr) -> (fp: U64.t) ->
  Lemma
    (requires mark_post h_init h_mark roots fp /\ FLA.fl_ascending h_init fp)
    (ensures (let r = FS.fused_sweep_coalesce h_mark fp in
              FSE.sweep_post h_mark (fst r) (snd r) /\
              well_formed_heap (fst r) /\ no_pointer_to_blue (fst r)))

val gc_postcondition_fused :
  (h_init: heap) -> (h_mark: heap) -> (roots: seq obj_addr) -> (fp: U64.t) ->
  Lemma
    (requires mark_post h_init h_mark roots fp /\ FLA.fl_ascending h_init fp)
    (ensures gc_postcondition (fst (FS.fused_sweep_coalesce h_mark fp)))

val full_gc_correctness_fused :
  (h_init: heap) -> (h_mark: heap) -> (roots: seq obj_addr) -> (fp: U64.t) ->
  Lemma
    (requires mark_post h_init h_mark roots fp /\ FLA.fl_ascending h_init fp)
    (ensures full_gc_correctness h_init (fst (FS.fused_sweep_coalesce h_mark fp)) roots)

val major_gc_live_subgraph_isomorphism_fused :
  (h_init: heap) -> (h_mark: heap) -> (roots: seq obj_addr) -> (fp: U64.t) ->
  Lemma
    (requires mark_post h_init h_mark roots fp /\ FLA.fl_ascending h_init fp /\
              (let g = create_graph h_init in
               let roots' = HeapGraph.coerce_to_vertex_list roots in
               graph_wf g /\ is_vertex_set roots' /\ subset_vertices roots' g.vertices))
    (ensures major_gc_live_subgraph_isomorphism
      h_init (fst (FS.fused_sweep_coalesce h_mark fp)) roots)

val major_gc_unreachable_final_blue_fused :
  (h_init: heap) -> (h_mark: heap) -> (roots: seq obj_addr) -> (fp: U64.t) ->
  Lemma
    (requires mark_post h_init h_mark roots fp /\ FLA.fl_ascending h_init fp /\
              (let g = create_graph h_init in
               let roots' = HeapGraph.coerce_to_vertex_list roots in
               graph_wf g /\ is_vertex_set roots' /\ subset_vertices roots' g.vertices))
    (ensures major_gc_unreachable_final_blue
      h_init (fst (FS.fused_sweep_coalesce h_mark fp)) roots)

/// All of the above at once: what `GC.Impl.collect_with_roots` promises.
val gc_result_fused :
  (h_init: heap) -> (h_mark: heap) -> (roots: seq obj_addr) -> (fp: U64.t) ->
  Lemma
    (requires mark_post h_init h_mark roots fp /\ FLA.fl_ascending h_init fp)
    (ensures (let s2 = fst (FS.fused_sweep_coalesce h_mark fp) in
              gc_postcondition s2 /\
              full_gc_correctness h_init s2 roots /\
              ((let g = create_graph h_init in
                let roots' = HeapGraph.coerce_to_vertex_list roots in
                graph_wf g /\ is_vertex_set roots' /\ subset_vertices roots' g.vertices) ==>
               major_gc_live_subgraph_isomorphism h_init s2 roots /\
               major_gc_unreachable_final_blue h_init s2 roots)))

/// ---------------------------------------------------------------------------
/// End-to-end, with the unbounded mark
/// ---------------------------------------------------------------------------
///
/// The five pillars for `mark` followed by the fused sweep.  Beyond the mark's
/// own preconditions the sweep needs the heap's walk to cover it
/// (`heap_objects_dense`, a non-empty heap) and the free list it is handed to
/// be exact and ascending.

let e2e_pre (h_init: heap) (st: seq obj_addr) (roots: seq obj_addr) (fp: U64.t) : prop =
  well_formed_heap h_init /\
  stack_props h_init st /\
  root_props h_init roots /\
  heap_objects_dense h_init /\
  Seq.length (objects zero_addr h_init) > 0 /\
  FLA.fl_ascending h_init fp /\
  no_black_objects h_init /\
  no_pointer_to_blue h_init /\
  (forall (r: obj_addr). Seq.mem r roots <==> Seq.mem r st) /\
  (let graph = create_graph h_init in
   let roots' = HeapGraph.coerce_to_vertex_list roots in
   graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices)

val end_to_end_correctness :
  (h_init: heap) -> (st: seq obj_addr) -> (roots: seq obj_addr) -> (fp: U64.t) ->
  Lemma
    (requires e2e_pre h_init st roots fp)
    (ensures
      (let h_mark = mark h_init st in
       let h_final = fst (FS.fused_sweep_coalesce h_mark fp) in
       let g_init = create_graph h_init in
       let g_final = create_graph h_final in
       well_formed_heap h_final /\
       (let roots' = HeapGraph.coerce_to_vertex_list roots in
        graph_wf g_init /\ is_vertex_set roots' /\ subset_vertices roots' g_init.vertices ==>
        (forall (x: obj_addr).
          mem_graph_vertex g_init x ==>
          (is_black x h_mark <==> Seq.mem x (reachable_set g_init roots')))) /\
       (forall (x: obj_addr).
         Seq.mem x g_final.vertices /\ is_black x h_mark ==>
         successors g_init x == successors g_final x) /\
       (forall (x: obj_addr).
         Seq.mem x g_final.vertices ==>
         (is_white x h_final \/ is_blue x h_final)) /\
       (forall (x: obj_addr).
         Seq.mem x g_final.vertices /\ is_black x h_mark ==>
         is_white x h_final) /\
       (forall (x: obj_addr) (i: U64.t).
         Seq.mem x g_final.vertices /\
         is_black x h_mark /\
         U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x h_init) ==>
         HeapGraph.get_field h_init x i == HeapGraph.get_field h_final x i)))

val gc_postcondition_from_correctness :
  (h_init: heap) -> (st: seq obj_addr) -> (roots: seq obj_addr) -> (fp: U64.t) ->
  Lemma (requires e2e_pre h_init st roots fp)
        (ensures gc_postcondition (fst (FS.fused_sweep_coalesce (mark h_init st) fp)))

val full_gc_correctness_from_end_to_end :
  (h_init: heap) -> (st: seq obj_addr) -> (roots: seq obj_addr) -> (fp: U64.t) ->
  Lemma (requires e2e_pre h_init st roots fp)
        (ensures full_gc_correctness h_init (fst (FS.fused_sweep_coalesce (mark h_init st) fp)) roots)

/// GC safety: reachable objects survive.
val gc_safety : (h_init: heap) -> (st: seq obj_addr) -> (roots: seq obj_addr) -> (fp: U64.t) ->
  Lemma (requires e2e_pre h_init st roots fp)
        (ensures (let graph = create_graph h_init in
                  let roots' = HeapGraph.coerce_to_vertex_list roots in
                  let h_final = fst (FS.fused_sweep_coalesce (mark h_init st) fp) in
                  forall (x: obj_addr).
                    mem_graph_vertex graph x /\
                    Seq.mem x (reachable_set graph roots') ==>
                    Seq.mem x (objects zero_addr h_final)))
