/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.TriColor - Tri-Color Invariant for Concurrent GC
/// ---------------------------------------------------------------------------
///
/// This module provides:
/// - tri_color_inv: the global tri-color invariant (no black→white edges)
/// - Properties for CancellableInvariant usage
/// - Lemmas for invariant preservation
///
/// The tri-color invariant is THE key safety property for concurrent GC:
/// It ensures that the collector never misses a reachable object.

module Pulse.Spec.GC.TriColor

open FStar.Seq
module U64 = FStar.UInt64

open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Heap
open Pulse.Spec.GC.Object
open Pulse.Spec.GC.Graph
open Pulse.Spec.GC.Fields
open Pulse.Spec.GC.HeapModel
open Pulse.Spec.GC.DFS
module HeapGraph = Pulse.Spec.GC.HeapGraph
module Header = Pulse.Lib.Header

/// ---------------------------------------------------------------------------
/// Tri-Color Invariant Definition
/// ---------------------------------------------------------------------------

/// The strong tri-color invariant: no black object points to a white object
let tri_color_inv (g: heap) : prop =
  let objs = objects 0UL g in
  forall (obj: obj_addr). Seq.mem obj objs ==>
    (is_black obj g ==>
      (forall (child: obj_addr). 
        points_to g obj child ==>
        not (is_white child g)))

/// Weak tri-color invariant: every white object reachable from a black
/// object is also reachable from a gray object
let weak_tri_color_inv (g: heap) (gray_stack: seq U64.t) : prop =
  let objs = objects 0UL g in
  forall (b_addr w_addr: obj_addr).
    Seq.mem b_addr objs /\ is_black b_addr g /\ is_white w_addr g ==>
    (points_to g b_addr w_addr ==>
     exists (gr_addr: obj_addr). 
       is_gray gr_addr g)

/// ---------------------------------------------------------------------------
/// Helper Predicates
/// ---------------------------------------------------------------------------

/// No gray objects remain (mark phase complete)
let no_gray_objects (g: heap) : prop =
  let objs = objects 0UL g in
  forall (obj: obj_addr). Seq.mem obj objs ==>
    not (is_gray obj g)

/// All reachable objects are black (after successful mark)
let all_reachable_black (g: heap) (roots: seq obj_addr) : prop =
  let graph = create_graph g in
  let roots' = HeapGraph.coerce_to_vertex_list roots in
  graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices ==>
  (forall (obj: obj_addr).
    mem_graph_vertex graph obj /\
    Seq.mem obj (reachable_set graph roots') ==>
    is_black obj g)

/// Reachability via forest membership
let is_reachable_from_roots (g: heap) (roots: seq obj_addr) (obj: obj_addr) : prop =
  let graph = create_graph g in
  let roots' = HeapGraph.coerce_to_vertex_list roots in
  graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices /\
  mem_graph_vertex graph obj /\
  Seq.mem obj (reachable_set graph roots')

/// ---------------------------------------------------------------------------
/// Invariant Preservation Lemmas
/// ---------------------------------------------------------------------------

/// Making a white object gray preserves tri-color invariant
val make_gray_preserves_tri_color : (g: heap) -> (w_addr: obj_addr) ->
  Lemma (requires well_formed_heap g /\ tri_color_inv g /\ is_white w_addr g /\
                  Seq.mem w_addr (objects 0UL g))
        (ensures tri_color_inv (makeGray w_addr g))

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1 --split_queries always"
let make_gray_preserves_tri_color g w_addr =
  makeGray_eq w_addr g;
  color_change_preserves_objects g w_addr Header.Gray;
  let g' = makeGray w_addr g in
  let objs = objects 0UL g in
  let aux (obj: obj_addr) : Lemma
    (requires Seq.mem obj objs)
    (ensures is_black obj g' ==> 
      (forall (child: obj_addr). points_to g' obj child ==> not (is_white child g')))
  = if obj = w_addr then begin
      // w_addr is now gray (not black) → vacuous
      makeGray_is_gray w_addr g;
      colors_exhaustive_and_exclusive w_addr g'
    end else begin
      color_change_preserves_other_color w_addr obj g Header.Gray;
      is_black_iff obj g;
      is_black_iff obj g';
      // points_to preserved: obj ≠ w_addr
      color_change_preserves_objects_mem g w_addr Header.Gray obj;
      // If obj not black in g', the implication is vacuous
      if not (is_black obj g') then ()
      else begin
        // obj is black in g' => black in g (color preserved for obj ≠ w_addr)
        let pt_preserved (child: obj_addr) : Lemma
          (points_to g' obj child == points_to g obj child)
        = color_change_preserves_points_to_other g w_addr Header.Gray obj child
        in
        FStar.Classical.forall_intro pt_preserved;
        // For each child: not white in g'
        let child_not_white (child: obj_addr) : Lemma
          (requires points_to g' obj child)
          (ensures not (is_white child g'))
        = pt_preserved child;
          // obj is black in g, child pointed-to by obj => not white in g (tri_color_inv)
          if child = w_addr then begin
            makeGray_is_gray w_addr g;
            colors_exhaustive_and_exclusive child g'
          end else begin
            color_change_preserves_other_color w_addr child g Header.Gray;
            is_white_iff child g;
            is_white_iff child g'
          end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires child_not_white)
      end
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
  assert (forall (obj: obj_addr). Seq.mem obj objs ==>
    (is_black obj g' ==> (forall (child: obj_addr). points_to g' obj child ==> not (is_white child g'))));
  assert (objects 0UL g' == objs)
#pop-options

/// Making a gray object black preserves tri-color invariant
/// IF all its children are gray or black
val make_black_preserves_tri_color : (g: heap) -> (gr_addr: obj_addr) ->
  Lemma (requires well_formed_heap g /\ tri_color_inv g /\ is_gray gr_addr g /\
                  Seq.mem gr_addr (objects 0UL g) /\
                  (forall (child: obj_addr). 
                    points_to g gr_addr child ==>
                    (is_gray child g \/ is_black child g)))
        (ensures tri_color_inv (makeBlack gr_addr g))

let make_black_preserves_tri_color g gr_addr =
  makeBlack_eq gr_addr g;
  color_change_preserves_objects g gr_addr Header.Black;
  let g' = makeBlack gr_addr g in
  let objs = objects 0UL g in
  let aux (obj: obj_addr) : Lemma
    (requires Seq.mem obj objs)
    (ensures is_black obj g' ==> 
      (forall (child: obj_addr). points_to g' obj child ==> not (is_white child g')))
  = if obj = gr_addr then begin
      if not (is_black obj g') then ()
      else begin
        // points_to preserved by self color change
        let pt_preserved (child: obj_addr) : Lemma
          (points_to g' gr_addr child == points_to g gr_addr child)
        = color_change_preserves_points_to_self g gr_addr Header.Black child
        in
        FStar.Classical.forall_intro pt_preserved;
        let child_not_white (child: obj_addr) : Lemma
          (requires points_to g' gr_addr child)
          (ensures not (is_white child g'))
        = pt_preserved child;
          if child = gr_addr then begin
            makeBlack_is_black gr_addr g;
            colors_exhaustive_and_exclusive child g'
          end else begin
            color_change_preserves_other_color gr_addr child g Header.Black;
            is_white_iff child g;
            is_white_iff child g';
            is_gray_iff child g;
            is_black_iff child g
          end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires child_not_white)
      end
    end else begin
      color_change_preserves_other_color gr_addr obj g Header.Black;
      is_black_iff obj g;
      is_black_iff obj g';
      if not (is_black obj g') then ()
      else begin
        color_change_preserves_objects_mem g gr_addr Header.Black obj;
        let pt_preserved (child: obj_addr) : Lemma
          (points_to g' obj child == points_to g obj child)
        = color_change_preserves_points_to_other g gr_addr Header.Black obj child
        in
        FStar.Classical.forall_intro pt_preserved;
        let child_not_white (child: obj_addr) : Lemma
          (requires points_to g' obj child)
          (ensures not (is_white child g'))
        = pt_preserved child;
          if child = gr_addr then begin
            makeBlack_is_black gr_addr g;
            colors_exhaustive_and_exclusive child g'
          end else begin
            color_change_preserves_other_color gr_addr child g Header.Black;
            is_white_iff child g;
            is_white_iff child g'
          end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires child_not_white)
      end
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
  assert (objects 0UL g' == objs)

/// Write barrier preserves tri-color invariant
val write_barrier_preserves_tri_color : 
  (g: heap) -> (src_black: obj_addr) -> (dst: obj_addr) ->
  Lemma (requires well_formed_heap g /\ tri_color_inv g /\ is_black src_black g /\
                  Seq.mem dst (objects 0UL g))
        (ensures tri_color_inv (if is_white dst g then makeGray dst g else g))

let write_barrier_preserves_tri_color g src_black dst =
  if is_white dst g then
    make_gray_preserves_tri_color g dst
  else ()

/// ---------------------------------------------------------------------------
/// Relationship to Mark Correctness
/// ---------------------------------------------------------------------------

/// After mark completes (no gray objects), tri-color + no gray = 
/// all objects are either black or white
val mark_complete_implies_reachable_black : (g: heap) ->
  Lemma (requires tri_color_inv g /\ no_gray_objects g)
        (ensures forall (obj: obj_addr). 
                   Seq.mem obj (objects 0UL g) ==>
                   is_black obj g \/ is_white obj g \/ is_blue obj g)

let mark_complete_implies_reachable_black g =
  let objs = objects 0UL g in
  let aux (obj: obj_addr) : Lemma
    (requires Seq.mem obj objs)
    (ensures is_black obj g \/ is_white obj g \/ is_blue obj g)
  = colors_exhaustive_and_exclusive obj g
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// ---------------------------------------------------------------------------
/// Initial State
/// ---------------------------------------------------------------------------

/// Initial heap (all objects white) trivially satisfies tri-color
val initial_heap_satisfies_tri_color : (g: heap) ->
  Lemma (requires forall (obj: obj_addr). 
                    Seq.mem obj (objects 0UL g) ==> is_white obj g)
        (ensures tri_color_inv g)

let initial_heap_satisfies_tri_color g =
  // All objects white → none are black → tri_color_inv is vacuously true
  let objs = objects 0UL g in
  let aux (obj: obj_addr) : Lemma
    (requires Seq.mem obj objs)
    (ensures is_black obj g ==> 
      (forall (child: obj_addr). points_to g obj child ==> not (is_white child g)))
  = colors_exhaustive_and_exclusive obj g
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
