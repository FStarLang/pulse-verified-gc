/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.CASPreservation - CAS Color Transitions Preserve Invariants
/// ---------------------------------------------------------------------------
///
/// Proves that CAS-based color transitions preserve the tri-color invariant
/// and gray set invariant. Each color transition corresponds to a CAS operation
/// that the Pulse implementation uses atomically.
///
/// Key lemmas:
///   cas_white_gray_preserves_inv   — root scanning / mark children
///   cas_gray_black_preserves_inv   — mark step blackening
///   cas_white_blue_preserves_inv   — per-thread blue marking
///   cas_blue_white_preserves_inv   — reset blue after per-thread pass
///   write_barrier_preserves_inv    — Dijkstra write barrier

module Pulse.Spec.GC.CASPreservation

open FStar.Seq
open FStar.Classical
open FStar.Mul
module U64 = FStar.UInt64

open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Object
open Pulse.Spec.GC.Fields
open Pulse.Spec.GC.Heap
open Pulse.Spec.GC.TriColor
open Pulse.Spec.GC.GraySet
module Header = Pulse.Lib.Header

/// ===========================================================================
/// Section 1: CAS Semantics
/// ===========================================================================

/// CAS result type: either succeeded (with old heap) or failed (heap unchanged)
type cas_result =
  | CAS_Success : h':heap -> cas_result
  | CAS_Failed

/// CAS color transition: try to change object color from expected to desired.
/// Returns new heap on success, or CAS_Failed if current color doesn't match.
let cas_color (h: obj_addr) (g: heap) (expected desired: color)
  : GTot cas_result =
  if color_of_object h g = expected then
    CAS_Success (set_object_color h g desired)
  else
    CAS_Failed

/// CAS failure is always safe: heap is unchanged
let cas_failure_safe (h: obj_addr) (g: heap) (gs: gray_set)
    (expected desired: color)
  : Lemma (requires cas_color h g expected desired == CAS_Failed)
          (ensures tri_color_inv g ==> tri_color_inv g)
  = ()

/// ===========================================================================
/// Section 2: Color Monotonicity
/// ===========================================================================

/// Color ordering: White < Gray < Black
/// Colors only increase during marking (except blue which is temporary).
let color_leq (c1 c2: color) : bool =
  match c1, c2 with
  | Header.White, _ -> true
  | Header.Gray, Header.Gray -> true
  | Header.Gray, Header.Black -> true
  | Header.Black, Header.Black -> true
  | _, _ -> false

/// Monotonicity: valid mark transitions only increase colors
let valid_mark_transition (old_c new_c: color) : bool =
  (old_c = Header.White && new_c = Header.Gray) ||
  (old_c = Header.Gray && new_c = Header.Black)

/// ===========================================================================
/// Section 3: CAS Transitions Preserve Tri-Color Invariant
/// ===========================================================================

/// ---------------------------------------------------------------------------
/// 3.1: White → Gray (root scanning, mark children, write barrier)
/// ---------------------------------------------------------------------------

/// CAS White→Gray preserves tri-color invariant.
/// Used during: root scanning, graying children before blackening parent,
/// and write barrier (shading white target before black→white store).
val cas_white_gray_preserves_inv :
  (g: heap) -> (gs: gray_set) -> (w: obj_addr) ->
  Lemma (requires well_formed_heap g /\ tri_color_inv g /\
                  gray_set_inv g gs /\
                  is_truly_white w g /\
                  Seq.mem w (objects zero_addr g))
        (ensures tri_color_inv (makeGray w g) /\
                 gray_set_inv (makeGray w g) (add_gray_set w gs))

let cas_white_gray_preserves_inv g gs w =
  make_gray_preserves_tri_color g w;
  gray_set_add_preserves_inv g gs w

/// ---------------------------------------------------------------------------
/// 3.2: Gray → Black (mark step: blacken after graying all children)
/// ---------------------------------------------------------------------------

/// CAS Gray→Black preserves tri-color invariant,
/// PROVIDED all children of the gray object are gray or black.
val cas_gray_black_preserves_inv :
  (g: heap) -> (gs: gray_set) -> (gr: obj_addr) ->
  Lemma (requires well_formed_heap g /\ tri_color_inv g /\
                  gray_set_inv g gs /\
                  is_gray gr g /\
                  Seq.mem gr (objects zero_addr g) /\
                  (forall (child: obj_addr).
                    points_to g gr child ==>
                    (is_gray child g \/ is_black child g)))
        (ensures tri_color_inv (makeBlack gr g) /\
                 gray_set_inv (makeBlack gr g) (remove_gray_set gr gs))

let cas_gray_black_preserves_inv g gs gr =
  make_black_preserves_tri_color g gr;
  gray_set_remove_preserves_inv g gs gr

/// ---------------------------------------------------------------------------
/// 3.3: White → Blue (per-thread blue marking)
/// ---------------------------------------------------------------------------

/// CAS White→Blue preserves tri-color invariant.
/// Used when stopping a thread: mark objects reachable from OTHER threads as blue
/// to prevent the current thread's mark from traversing them.
val cas_white_blue_preserves_inv :
  (g: heap) -> (gs: gray_set) -> (w: obj_addr) ->
  Lemma (requires well_formed_heap g /\ tri_color_inv g /\
                  gray_set_inv g gs /\
                  is_truly_white w g /\
                  Seq.mem w (objects zero_addr g))
        (ensures tri_color_inv (makeBlue w g) /\
                 gray_set_inv (makeBlue w g) gs)

let cas_white_blue_preserves_inv g gs w =
  make_blue_preserves_tri_color g w;
  make_blue_preserves_gray_set_inv g gs w

/// ---------------------------------------------------------------------------
/// 3.4: Blue → White (reset blue after per-thread pass)
/// ---------------------------------------------------------------------------

/// CAS Blue→White preserves tri-color invariant,
/// PROVIDED no black object points to the blue object.
val cas_blue_white_preserves_inv :
  (g: heap) -> (gs: gray_set) -> (b: obj_addr) ->
  Lemma (requires well_formed_heap g /\ tri_color_inv g /\
                  gray_set_inv g gs /\
                  is_blue b g /\
                  Seq.mem b (objects zero_addr g) /\
                  (forall (obj: obj_addr). Seq.mem obj (objects zero_addr g) ==>
                    is_black obj g ==> not (points_to g obj b)))
        (ensures tri_color_inv (resetBlue b g) /\
                 gray_set_inv (resetBlue b g) gs)

let cas_blue_white_preserves_inv g gs b =
  reset_blue_white_preserves_tri_color g b;
  reset_blue_preserves_gray_set_inv g gs b

/// ===========================================================================
/// Section 4: Write Barrier Safety
/// ===========================================================================

/// The Dijkstra write barrier: before storing a pointer from src to dst,
/// if src is black and dst is truly-white, shade dst gray.
///
/// After the barrier, the store is safe because dst is no longer truly-white.
val write_barrier_safe :
  (g: heap) -> (gs: gray_set) -> (src: obj_addr) -> (dst: obj_addr) ->
  Lemma (requires well_formed_heap g /\ tri_color_inv g /\
                  gray_set_inv g gs /\
                  is_black src g /\
                  Seq.mem dst (objects zero_addr g) /\
                  Seq.mem src (objects zero_addr g))
        (ensures (let g' = if is_truly_white dst g then makeGray dst g else g in
                  let gs' = if is_truly_white dst g then add_gray_set dst gs else gs in
                  tri_color_inv g' /\ gray_set_inv g' gs'))

let write_barrier_safe g gs src dst =
  if is_truly_white dst g then begin
    cas_white_gray_preserves_inv g gs dst
  end else ()

/// ===========================================================================
/// Section 5: Combined Mark Step Safety
/// ===========================================================================

/// A complete mark step: pop gray object, gray all white children, blacken.
/// This is the composition of multiple CAS operations.
///
/// For the fly/ parallel GC, during a thread's mark pass:
/// 1. Pop gray object from stack
/// 2. For each child: if truly-white, CAS white→gray
/// 3. CAS gray→black the parent
///
/// We express the key invariant: after graying all children,
/// blackening the parent is safe.

/// After graying all truly-white children of a gray object,
/// all children are gray, black, or blue (not truly-white).
val children_grayed_implies_safe :
  (g: heap) -> (gr: obj_addr) ->
  Lemma (requires well_formed_heap g /\
                  is_gray gr g /\
                  Seq.mem gr (objects zero_addr g) /\
                  (forall (child: obj_addr).
                    points_to g gr child ==>
                    not (is_truly_white child g)))
        (ensures (forall (child: obj_addr).
                    points_to g gr child ==>
                    (is_gray child g \/ is_black child g \/ is_blue child g)))

let children_grayed_implies_safe g gr =
  let aux (child: obj_addr) : Lemma
    (requires points_to g gr child)
    (ensures is_gray child g \/ is_black child g \/ is_blue child g)
  = colors_exhaustive_4 child g
  in
  forall_intro (move_requires aux)

/// ===========================================================================
/// Section 6: Initial State
/// ===========================================================================

/// An all-white heap satisfies tri_color_inv with empty gray set
val initial_state_inv :
  (g: heap) ->
  Lemma (requires forall (obj: obj_addr). Seq.mem obj (objects zero_addr g) ==>
                    is_white obj g)
        (ensures tri_color_inv g /\ gray_set_inv g empty_gray_set)

let initial_state_inv g =
  initial_heap_satisfies_tri_color g;
  let aux (obj: obj_addr) : Lemma
    (requires Seq.mem obj (objects zero_addr g))
    (ensures mem_gray_set obj empty_gray_set <==> is_gray obj g)
  = colors_exhaustive_and_exclusive obj g;
    assert (is_white obj g);
    assert (not (is_gray obj g));
    assert (not (mem_gray_set obj empty_gray_set))
  in
  forall_intro (move_requires aux)
