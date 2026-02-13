/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.GraphBridge - Heap ↔ Graph Reachability Bridge
/// ---------------------------------------------------------------------------
///
/// Bridges heap-level operations (points_to, objects, colors) with
/// graph-level reachability (from common/Spec/Graph, HeapGraph, HeapModel).
///
/// Key definitions:
///   heap_reachable: transitive closure of points_to on heap objects
///   heap_reachable_from_roots: reachable from any root in a set
///
/// Key lemmas:
///   black_reachable_not_white: after marking, all objects reachable from
///     black objects are black or gray (not truly-white)
///   mark_complete_white_unreachable: when no gray objects remain,
///     all truly-white objects are unreachable from black objects

module Pulse.Spec.GC.GraphBridge

open FStar.Seq
open FStar.Classical
open FStar.Mul
module U64 = FStar.UInt64

open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Object
open Pulse.Spec.GC.Fields
open Pulse.Spec.GC.Heap
open Pulse.Spec.GC.TriColor
module Header = Pulse.Lib.Header

/// ===========================================================================
/// Section 1: Heap-Level Reachability
/// ===========================================================================

/// Heap-level reachability: transitive closure of points_to.
/// x reaches y in heap g if there is a chain of points_to edges.
noeq type heap_reach (g: heap) : obj_addr -> obj_addr -> Type =
  | HReachRefl : (x: obj_addr{Seq.mem x (objects zero_addr g)}) ->
                 heap_reach g x x
  | HReachStep : (x: obj_addr) -> (y: obj_addr) -> (z: obj_addr) ->
                 (step: squash (points_to g x y)) ->
                 (rest: heap_reach g y z) ->
                 heap_reach g x z

/// Decidable reachability predicate
let heap_reachable (g: heap) (x y: obj_addr) : prop =
  exists (r: heap_reach g x y). True

/// Reflexivity
val heap_reach_refl : (g: heap) -> (x: obj_addr) ->
  Lemma (requires Seq.mem x (objects zero_addr g))
        (ensures heap_reachable g x x)

let heap_reach_refl g x =
  let r = HReachRefl #g x in
  FStar.Classical.exists_intro (fun (_: heap_reach g x x) -> True) r

/// Transitivity
val heap_reach_trans : (g: heap) -> (x: obj_addr) -> (y: obj_addr) -> (z: obj_addr) ->
  Lemma (requires heap_reachable g x y /\ heap_reachable g y z)
        (ensures heap_reachable g x z)

let rec reach_trans_witness (#g: heap) (#x #y #z: obj_addr)
  (rxy: heap_reach g x y) (ryz: heap_reach g y z)
  : Tot (heap_reach g x z) (decreases rxy)
  = match rxy with
    | HReachRefl _ -> ryz
    | HReachStep a b c step rest ->
      HReachStep a b z step (reach_trans_witness rest ryz)

let heap_reach_trans g x y z =
  let aux (rxy: heap_reach g x y) : Lemma (heap_reachable g x z) =
    let aux2 (ryz: heap_reach g y z) : Lemma (heap_reachable g x z) =
      let r = reach_trans_witness rxy ryz in
      FStar.Classical.exists_intro (fun (_: heap_reach g x z) -> True) r
    in
    forall_intro (move_requires aux2)
  in
  forall_intro (move_requires aux)

/// One-step edge implies reachability
val heap_edge_reach : (g: heap) -> (x: obj_addr) -> (y: obj_addr) ->
  Lemma (requires points_to g x y /\ Seq.mem y (objects zero_addr g))
        (ensures heap_reachable g x y)

let heap_edge_reach g x y =
  let ry = HReachRefl #g y in
  let r = HReachStep x y y () ry in
  FStar.Classical.exists_intro (fun (_: heap_reach g x y) -> True) r

/// ===========================================================================
/// Section 2: Reachability from Roots
/// ===========================================================================

/// An object is reachable from a set of roots if it is reachable from any root
let heap_reachable_from_roots (g: heap) (roots: seq obj_addr) (y: obj_addr) : prop =
  exists (r: obj_addr). Seq.mem r roots /\ heap_reachable g r y

/// Every root is reachable from itself
val root_is_reachable : (g: heap) -> (roots: seq obj_addr) -> (r: obj_addr) ->
  Lemma (requires Seq.mem r roots /\ Seq.mem r (objects zero_addr g))
        (ensures heap_reachable_from_roots g roots r)

let root_is_reachable g roots r =
  heap_reach_refl g r

/// ===========================================================================
/// Section 3: Tri-Color and Reachability
/// ===========================================================================

/// Key safety property: under the tri-color invariant,
/// all objects reachable from a black object via one step are not truly-white.
val black_children_not_truly_white :
  (g: heap) -> (b: obj_addr) ->
  Lemma (requires tri_color_inv g /\ is_black b g /\
                  Seq.mem b (objects zero_addr g))
        (ensures forall (child: obj_addr).
                   points_to g b child ==> not (is_truly_white child g))

let black_children_not_truly_white g b = ()

/// ===========================================================================
/// Section 4: Mark Completion Properties
/// ===========================================================================

/// When marking is complete (no gray objects, no blue objects),
/// every object reachable from a black object is also black.
/// This is the key correctness property for the sweep phase.
val mark_complete_reachable_is_black :
  (g: heap) -> (b: obj_addr) -> (y: obj_addr) ->
  Lemma (requires well_formed_heap g /\
                  tri_color_inv g /\
                  no_gray_objects g /\
                  no_blue_objects g /\
                  is_black b g /\
                  Seq.mem b (objects zero_addr g) /\
                  heap_reachable g b y)
        (ensures is_black y g)

/// Helper: induction on heap_reach witness
#push-options "--z3rlimit 300 --fuel 2 --ifuel 1"
let rec mark_complete_reachable_is_black_aux
  (g: heap) (b: obj_addr) (y: obj_addr) (r: heap_reach g b y)
  : Lemma (requires well_formed_heap g /\
                    tri_color_inv g /\
                    no_gray_objects g /\
                    no_blue_objects g /\
                    is_black b g /\
                    Seq.mem b (objects zero_addr g))
          (ensures is_black y g)
          (decreases r)
  = match r with
    | HReachRefl _ -> ()
    | HReachStep x mid _ step rest ->
      // x is black and in objects (b=x by pattern)
      // points_to g x mid and well_formed_heap ==> mid in objects
      wosize_of_object_bound x g;
      // tri_color_inv_no_blue g: no black→white edges in absence of blue
      tri_color_inv_no_blue g;
      // So mid is not white. no_gray says not gray. Therefore black.
      colors_exhaustive_and_exclusive mid g;
      // Recurse with mid as the new black object
      mark_complete_reachable_is_black_aux g mid y rest
#pop-options

#push-options "--z3rlimit 200"
let mark_complete_reachable_is_black g b y =
  let aux (r: heap_reach g b y) : Lemma (is_black y g) =
    mark_complete_reachable_is_black_aux g b y r
  in
  forall_intro (move_requires aux)
#pop-options

/// Corollary: after complete marking with no blue/gray,
/// all truly-white objects are unreachable from any black object.
val white_unreachable_from_black :
  (g: heap) -> (b: obj_addr) -> (w: obj_addr) ->
  Lemma (requires well_formed_heap g /\
                  tri_color_inv g /\
                  no_gray_objects g /\
                  no_blue_objects g /\
                  is_black b g /\
                  is_truly_white w g /\
                  Seq.mem b (objects zero_addr g))
        (ensures ~(heap_reachable g b w))

let white_unreachable_from_black g b w =
  let aux (r: heap_reach g b w) : Lemma (ensures False) =
    mark_complete_reachable_is_black_aux g b w r;
    colors_exhaustive_and_exclusive w g
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
