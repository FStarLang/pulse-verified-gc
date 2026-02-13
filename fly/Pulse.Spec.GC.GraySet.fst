/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.GraySet - Gray Set Ghost State for Parallel GC
/// ---------------------------------------------------------------------------
///
/// Tracks the set of gray objects as ghost state for the mark phase.
/// The gray set serves as the termination metric: each mark step removes
/// one object (by blackening it) and may add children (by graying them).
///
/// Key invariant: gray_set_inv g gs <==> (obj in gs <==> is_gray obj in heap)
///
/// This module provides the specification-level gray set operations.
/// The Pulse implementation uses GhostSet for the actual ghost state.

module Pulse.Spec.GC.GraySet

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
/// Section 1: Gray Set Type
/// ===========================================================================

/// Ghost set of object addresses representing gray objects
let gray_set = FStar.Set.set obj_addr

/// Empty gray set
let empty_gray_set : gray_set = FStar.Set.empty #obj_addr

/// Singleton gray set
let singleton_gray_set (h: obj_addr) : gray_set = FStar.Set.singleton h

/// Membership
let mem_gray_set (h: obj_addr) (gs: gray_set) : GTot bool =
  FStar.Set.mem h gs

/// Add to gray set
let add_gray_set (h: obj_addr) (gs: gray_set) : gray_set =
  FStar.Set.union gs (FStar.Set.singleton h)

/// Remove from gray set
let remove_gray_set (h: obj_addr) (gs: gray_set) : gray_set =
  FStar.Set.intersect gs (FStar.Set.complement (FStar.Set.singleton h))

/// Union of gray sets
let union_gray_set (gs1 gs2: gray_set) : gray_set =
  FStar.Set.union gs1 gs2

/// ===========================================================================
/// Section 2: Gray Set Invariant
/// ===========================================================================

/// The gray set invariant: for all objects in the heap,
/// an object is in the gray set iff it is gray in the heap.
let gray_set_inv (g: heap) (gs: gray_set) : prop =
  forall (obj: obj_addr). Seq.mem obj (objects zero_addr g) ==>
    (mem_gray_set obj gs <==> is_gray obj g)

/// ===========================================================================
/// Section 3: Gray Set Preservation Lemmas
/// ===========================================================================

/// Graying an object and adding it to the gray set preserves the invariant
val gray_set_add_preserves_inv :
  (g: heap) -> (gs: gray_set) -> (w: obj_addr) ->
  Lemma (requires well_formed_heap g /\
                  gray_set_inv g gs /\
                  is_truly_white w g /\
                  Seq.mem w (objects zero_addr g))
        (ensures gray_set_inv (makeGray w g) (add_gray_set w gs))

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1 --split_queries always"
let gray_set_add_preserves_inv g gs w =
  makeGray_eq w g;
  color_change_preserves_objects g w Header.Gray;
  let g' = makeGray w g in
  let gs' = add_gray_set w gs in
  let objs = objects zero_addr g in
  let aux (obj: obj_addr) : Lemma
    (requires Seq.mem obj objs)
    (ensures mem_gray_set obj gs' <==> is_gray obj g')
  = if obj = w then begin
      makeGray_is_gray w g;
      assert (is_gray w g');
      assert (mem_gray_set w gs')
    end else begin
      color_change_preserves_other_color w obj g Header.Gray;
      is_gray_iff obj g;
      is_gray_iff obj g';
      assert (is_gray obj g' == is_gray obj g);
      // mem_gray_set obj gs' <==> mem_gray_set obj gs (since obj ≠ w)
      assert (mem_gray_set obj gs' <==> (mem_gray_set obj gs \/ obj = w));
      ()
    end
  in
  forall_intro (move_requires aux);
  assert (objects zero_addr g' == objs)
#pop-options

/// Blackening an object and removing it from the gray set preserves the invariant
val gray_set_remove_preserves_inv :
  (g: heap) -> (gs: gray_set) -> (gr: obj_addr) ->
  Lemma (requires well_formed_heap g /\
                  gray_set_inv g gs /\
                  is_gray gr g /\
                  Seq.mem gr (objects zero_addr g))
        (ensures gray_set_inv (makeBlack gr g) (remove_gray_set gr gs))

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1 --split_queries always"
let gray_set_remove_preserves_inv g gs gr =
  makeBlack_eq gr g;
  color_change_preserves_objects g gr Header.Black;
  let g' = makeBlack gr g in
  let gs' = remove_gray_set gr gs in
  let objs = objects zero_addr g in
  let aux (obj: obj_addr) : Lemma
    (requires Seq.mem obj objs)
    (ensures mem_gray_set obj gs' <==> is_gray obj g')
  = if obj = gr then begin
      makeBlack_is_black gr g;
      colors_exhaustive_and_exclusive gr g';
      assert (not (is_gray gr g'));
      assert (not (mem_gray_set gr gs'))
    end else begin
      color_change_preserves_other_color gr obj g Header.Black;
      is_gray_iff obj g;
      is_gray_iff obj g';
      assert (is_gray obj g' == is_gray obj g);
      assert (mem_gray_set obj gs' <==> (mem_gray_set obj gs /\ obj <> gr));
      ()
    end
  in
  forall_intro (move_requires aux);
  assert (objects zero_addr g' == objs)
#pop-options

/// ===========================================================================
/// Section 4: Termination and Emptiness
/// ===========================================================================

/// Empty gray set implies no gray objects in the heap
val empty_gray_set_implies_no_gray :
  (g: heap) -> (gs: gray_set) ->
  Lemma (requires gray_set_inv g gs /\ gs == empty_gray_set)
        (ensures no_gray_objects g)

let empty_gray_set_implies_no_gray g gs =
  let aux (obj: obj_addr) : Lemma
    (requires Seq.mem obj (objects zero_addr g))
    (ensures not (is_gray obj g))
  = assert (not (mem_gray_set obj empty_gray_set))
  in
  forall_intro (move_requires aux)

/// ===========================================================================
/// Section 5: Blue-Gray Exclusion
/// ===========================================================================

/// Blue objects are never in the gray set (given the invariant)
val blue_not_in_gray_set :
  (g: heap) -> (gs: gray_set) -> (h: obj_addr) ->
  Lemma (requires gray_set_inv g gs /\
                  is_blue h g /\
                  Seq.mem h (objects zero_addr g))
        (ensures not (mem_gray_set h gs))

let blue_not_in_gray_set g gs h =
  colors_exclusive_4 h g;
  assert (not (is_gray h g && is_blue h g));
  assert (is_blue h g);
  assert (not (is_gray h g))

/// Black objects are never in the gray set (given the invariant)
val black_not_in_gray_set :
  (g: heap) -> (gs: gray_set) -> (h: obj_addr) ->
  Lemma (requires gray_set_inv g gs /\
                  is_black h g /\
                  Seq.mem h (objects zero_addr g))
        (ensures not (mem_gray_set h gs))

let black_not_in_gray_set g gs h =
  colors_exhaustive_and_exclusive h g;
  assert (not (is_gray h g));
  assert (not (mem_gray_set h gs))

/// ===========================================================================
/// Section 6: makeBlue Preserves Gray Set Invariant
/// ===========================================================================

/// Making a truly-white object blue preserves the gray set invariant.
/// Blue is not gray, and no existing gray objects change color.
val make_blue_preserves_gray_set_inv :
  (g: heap) -> (gs: gray_set) -> (w: obj_addr) ->
  Lemma (requires well_formed_heap g /\
                  gray_set_inv g gs /\
                  is_truly_white w g /\
                  Seq.mem w (objects zero_addr g))
        (ensures gray_set_inv (makeBlue w g) gs)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1 --split_queries always"
let make_blue_preserves_gray_set_inv g gs w =
  makeBlue_preserves_objects w g;
  let g' = makeBlue w g in
  let objs = objects zero_addr g in
  let aux (obj: obj_addr) : Lemma
    (requires Seq.mem obj objs)
    (ensures mem_gray_set obj gs <==> is_gray obj g')
  = if obj = w then begin
      // is_truly_white w g ==> is_white w g && not (is_blue w g)
      // is_white w g ==> not (is_gray w g) by exclusiveness
      assert (is_white w g);
      colors_exhaustive_and_exclusive w g;
      assert (not (is_white w g && is_gray w g));
      assert (not (is_gray w g));
      // After makeBlue, w is blue, not gray (by exclusiveness)
      makeBlue_is_blue w g;
      colors_exclusive_4 w g'
    end else begin
      makeBlue_preserves_other_color w obj g;
      is_gray_iff obj g;
      is_gray_iff obj g'
    end
  in
  forall_intro (move_requires aux);
  assert (objects zero_addr g' == objs)
#pop-options

/// Resetting a blue object to white preserves the gray set invariant.
/// Blue was not gray, and white is not gray.
val reset_blue_preserves_gray_set_inv :
  (g: heap) -> (gs: gray_set) -> (b: obj_addr) ->
  Lemma (requires well_formed_heap g /\
                  gray_set_inv g gs /\
                  is_blue b g /\
                  Seq.mem b (objects zero_addr g))
        (ensures gray_set_inv (resetBlue b g) gs)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1 --split_queries always"
let reset_blue_preserves_gray_set_inv g gs b =
  // resetBlue = makeWhite
  makeWhite_eq b g;
  color_change_preserves_objects g b Header.White;
  let g' = resetBlue b g in
  let objs = objects zero_addr g in
  let aux (obj: obj_addr) : Lemma
    (requires Seq.mem obj objs)
    (ensures mem_gray_set obj gs <==> is_gray obj g')
  = if obj = b then begin
      // b is blue, so not gray (by exclusiveness)
      colors_exclusive_4 b g;
      assert (not (is_gray b g));
      // After resetBlue, b is white, not gray
      makeWhite_is_white b g;
      colors_exhaustive_and_exclusive b g'
    end else begin
      color_change_preserves_other_color b obj g Header.White;
      is_gray_iff obj g;
      is_gray_iff obj g';
      assert (is_gray obj g' == is_gray obj g)
    end
  in
  forall_intro (move_requires aux);
  assert (objects zero_addr g' == objs)
#pop-options
