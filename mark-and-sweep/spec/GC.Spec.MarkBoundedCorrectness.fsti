/// ---------------------------------------------------------------------------
/// GC.Spec.MarkBoundedCorrectness — Interface
/// ---------------------------------------------------------------------------

module GC.Spec.MarkBoundedCorrectness

open FStar.Seq
open FStar.Mul

module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Graph
open GC.Spec.Fields
open GC.Spec.HeapModel
open GC.Spec.DFS
open GC.Spec.Mark
open GC.Spec.MarkBounded
module HeapGraph = GC.Spec.HeapGraph
module Header = GC.Lib.Header
module SweepInv = GC.Spec.SweepInv
module Correctness = GC.Spec.Correctness

/// Bundled color invariant (exposed for unfolding)
let mark_color_inv (h_init h_cur: heap) : prop =
  well_formed_heap h_cur /\
  Seq.length (objects 0UL h_cur) > 0 /\
  SweepInv.heap_objects_dense h_cur /\
  objects 0UL h_cur == objects 0UL h_init /\
  tri_color_invariant h_cur /\
  no_pointer_to_blue h_cur /\
  create_graph h_cur == create_graph h_init /\
  (forall (x: obj_addr). Seq.mem x (objects 0UL h_init) ==>
    wosize_of_object x h_cur == wosize_of_object x h_init) /\
  (forall (x: obj_addr) (i: U64.t). Seq.mem x (objects 0UL h_init) /\
    U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x h_init) ==>
    HeapGraph.get_field h_cur x i == HeapGraph.get_field h_init x i)

/// Backward reachability: gray/black objects are reachable from roots
let gray_black_reachable (h_init: heap) (h: heap) (roots: seq obj_addr) : prop =
    let graph = create_graph h_init in
    let roots' = HeapGraph.coerce_to_vertex_list roots in
    graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices /\
    (forall (x: obj_addr). Seq.mem x (objects 0UL h) /\ (is_gray x h \/ is_black x h) ==>
      Seq.mem x (reachable_set graph roots'))

/// Color monotonicity
let gray_stays (h_init h: heap) : prop =
    forall (x: obj_addr). Seq.mem x (objects 0UL h_init) /\ is_gray x h_init ==>
      is_gray x h \/ is_black x h

/// Stack elements are reachable from roots
let stack_elems_reachable (h_init: heap) (st: seq obj_addr) (roots: seq obj_addr) : prop =
    let graph = create_graph h_init in
    let roots' = HeapGraph.coerce_to_vertex_list roots in
    graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices /\
    (forall (x: obj_addr). Seq.mem x st ==> Seq.mem x (reachable_set graph roots'))

/// Per-step property preservation
val mark_step_bounded_preserves_create_graph
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st)
          (ensures create_graph (fst (mark_step_bounded g st cap)) == create_graph g)

val mark_step_bounded_preserves_wosize
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat) (x: obj_addr)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                   Seq.mem x (objects 0UL g))
          (ensures wosize_of_object x (fst (mark_step_bounded g st cap)) ==
                   wosize_of_object x g)

val mark_step_bounded_preserves_get_field
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  (x: obj_addr) (j: U64.t)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                   Seq.mem x (objects 0UL g) /\
                   U64.v j >= 1 /\ U64.v j <= U64.v (wosize_of_object x g))
          (ensures HeapGraph.get_field (fst (mark_step_bounded g st cap)) x j ==
                   HeapGraph.get_field g x j)

val mark_step_bounded_preserves_tri_color :
  (g: heap) -> (st: seq obj_addr{Seq.length st > 0}) -> (cap: nat) ->
  Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                  tri_color_invariant g)
        (ensures tri_color_invariant (fst (mark_step_bounded g st cap)))

val mark_step_bounded_preserves_points_to
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  (src dst: obj_addr)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                   Seq.mem src (objects 0UL g))
          (ensures points_to (fst (mark_step_bounded g st cap)) src dst ==
                   points_to g src dst)

val mark_step_bounded_preserves_blue
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat) (x: obj_addr)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                   Seq.mem x (objects 0UL g) /\ is_blue x g)
          (ensures is_blue x (fst (mark_step_bounded g st cap)))

val mark_step_bounded_no_new_blue
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat) (x: obj_addr)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                   Seq.mem x (objects 0UL g) /\ ~(is_blue x g))
          (ensures ~(is_blue x (fst (mark_step_bounded g st cap))))

val mark_step_bounded_preserves_no_pointer_to_blue
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                   no_pointer_to_blue g)
          (ensures no_pointer_to_blue (fst (mark_step_bounded g st cap)))

val mark_step_bounded_preserves_color_inv
  (h_init: heap) (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  : Lemma (requires bounded_stack_props g st /\ mark_color_inv h_init g)
          (ensures mark_color_inv h_init (fst (mark_step_bounded g st cap)))

/// Loop/bounded-level invariants
val mark_inner_loop_preserves_color_inv
  (h_init: heap) (g: heap) (st: seq obj_addr) (cap: nat) (fuel: nat)
  : Lemma (requires bounded_stack_props g st /\ mark_color_inv h_init g)
          (ensures mark_color_inv h_init (fst (mark_inner_loop g st cap fuel)))

val mark_bounded_preserves_color_inv
  (h_init: heap) (g: heap) (cap: nat{cap > 0}) (fuel: nat)
  : Lemma (requires mark_color_inv h_init g)
          (ensures mark_color_inv h_init (mark_bounded g cap fuel))

/// Gray/black monotonicity
val mark_step_bounded_gray_becomes_black :
  (g: heap) -> (st: seq obj_addr{Seq.length st > 0}) -> (cap: nat) -> (x: obj_addr) ->
  Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                  Seq.mem x (objects 0UL g) /\
                  (is_gray x g \/ is_black x g))
        (ensures (let g' = fst (mark_step_bounded g st cap) in
                  is_gray x g' \/ is_black x g'))

val mark_inner_loop_gray_or_black_preserved :
  (g: heap) -> (st: seq obj_addr) -> (cap: nat) -> (fuel: nat) -> (x: obj_addr) ->
  Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                  Seq.length (objects 0UL g) > 0 /\
                  SweepInv.heap_objects_dense g /\
                  Seq.mem x (objects 0UL g) /\
                  (is_gray x g \/ is_black x g))
        (ensures (let g' = fst (mark_inner_loop g st cap fuel) in
                  is_gray x g' \/ is_black x g'))

val mark_bounded_gray_or_black_preserved :
  (g: heap) -> (cap: nat{cap > 0}) -> (fuel: nat) -> (x: obj_addr) ->
  Lemma (requires well_formed_heap g /\
                  Seq.length (objects 0UL g) > 0 /\
                  SweepInv.heap_objects_dense g /\
                  Seq.mem x (objects 0UL g) /\
                  (is_gray x g \/ is_black x g))
        (ensures (let g' = mark_bounded g cap fuel in
                  is_gray x g' \/ is_black x g'))

/// Reachability and backward invariant
val noGreyObjects_from_no_gray (g: heap)
  : Lemma (requires SweepInv.no_gray_objects g)
          (ensures noGreyObjects g)

val mark_bounded_reachable_is_black
  (h_init: heap) (roots: seq obj_addr) (cap: nat{cap > 0}) (fuel: nat)
  : Lemma
    (requires
      well_formed_heap h_init /\
      Seq.length (objects 0UL h_init) > 0 /\
      SweepInv.heap_objects_dense h_init /\
      root_props h_init roots /\
      mark_color_inv h_init h_init /\
      fuel >= count_non_black h_init /\
      (let graph = create_graph h_init in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
    (ensures
      (let h_mark = mark_bounded h_init cap fuel in
       let graph = create_graph h_init in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices ==>
       (forall (x: obj_addr). mem_graph_vertex graph x /\
         Seq.mem x (reachable_set graph roots') ==> is_black x h_mark)))

val mark_color_inv_init (h_init: heap)
  : Lemma
    (requires well_formed_heap h_init /\
             Seq.length (objects 0UL h_init) > 0 /\
             SweepInv.heap_objects_dense h_init /\
             no_black_objects h_init /\
             no_pointer_to_blue h_init)
    (ensures mark_color_inv h_init h_init)

val mark_bounded_satisfies_mark_post
  (h_init: heap) (roots: seq obj_addr) (fp: U64.t)
  (cap: nat{cap > 0}) (fuel: nat)
  : Lemma
    (requires
      well_formed_heap h_init /\
      Seq.length (objects 0UL h_init) > 0 /\
      SweepInv.heap_objects_dense h_init /\
      root_props h_init roots /\
      GC.Spec.Sweep.fp_in_heap fp h_init /\
      no_black_objects h_init /\
      no_pointer_to_blue h_init /\
      fuel >= count_non_black h_init /\
      (forall (x: obj_addr). Seq.mem x (objects 0UL h_init) /\
        (is_gray x h_init \/ is_black x h_init) ==> Seq.mem x roots) /\
      (let graph = create_graph h_init in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
    (ensures Correctness.mark_post h_init (mark_bounded h_init cap fuel) roots fp)

/// Reachability invariant lemmas
val gray_black_reachable_init
  (h_init: heap) (roots: seq obj_addr)
  : Lemma
    (requires
      well_formed_heap h_init /\
      root_props h_init roots /\
      no_black_objects h_init /\
      (forall (x: obj_addr). Seq.mem x (objects 0UL h_init) /\
        (is_gray x h_init \/ is_black x h_init) ==> Seq.mem x roots) /\
      (let graph = create_graph h_init in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
    (ensures gray_black_reachable h_init h_init roots)

val gray_stays_init (h: heap)
  : Lemma (ensures gray_stays h h)

val stack_reachable_from_bsp_gbr
  (h_init: heap) (g: heap) (st: seq obj_addr) (roots: seq obj_addr)
  : Lemma
    (requires bounded_stack_props g st /\
             gray_black_reachable h_init g roots /\
             objects 0UL g == objects 0UL h_init)
    (ensures stack_elems_reachable h_init st roots)

val stack_elems_reachable_empty (h_init: heap) (roots: seq obj_addr)
  : Lemma
    (requires (let graph = create_graph h_init in
               let roots' = HeapGraph.coerce_to_vertex_list roots in
               graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
    (ensures stack_elems_reachable h_init Seq.empty roots)

val mark_step_bounded_preserves_gbr
  (h_init: heap) (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  (roots: seq obj_addr)
  : Lemma
    (requires well_formed_heap g /\ bounded_stack_props g st /\
             Seq.length (objects 0UL g) > 0 /\
             SweepInv.heap_objects_dense g /\
             mark_color_inv h_init g /\
             gray_black_reachable h_init g roots /\
             (forall x. Seq.mem x st ==> Seq.mem x (reachable_set (create_graph h_init) (HeapGraph.coerce_to_vertex_list roots))))
    (ensures (let (g', st') = mark_step_bounded g st cap in
             gray_black_reachable h_init g' roots /\
             (forall x. Seq.mem x st' ==> Seq.mem x (reachable_set (create_graph h_init) (HeapGraph.coerce_to_vertex_list roots)))))

val mark_step_bounded_preserves_gray_stays
  (h_init: heap) (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  : Lemma
    (requires well_formed_heap g /\ bounded_stack_props g st /\
             mark_color_inv h_init g /\
             gray_stays h_init g)
    (ensures gray_stays h_init (fst (mark_step_bounded g st cap)))

val mark_post_from_bounded_mark
  (h_init: heap) (h_mark: heap) (roots: seq obj_addr) (fp: U64.t)
  : Lemma
    (requires
      well_formed_heap h_init /\
      mark_color_inv h_init h_mark /\
      SweepInv.no_gray_objects h_mark /\
      gray_black_reachable h_init h_mark roots /\
      gray_stays h_init h_mark /\
      root_props h_init roots /\
      GC.Spec.Sweep.fp_in_heap fp h_init /\
      no_black_objects h_init /\
      no_pointer_to_blue h_init)
    (ensures Correctness.mark_post h_init h_mark roots fp)
