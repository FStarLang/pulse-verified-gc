/// ---------------------------------------------------------------------------
/// GC.Spec.MarkBoundedInv - Abstract bounded mark loop invariant
/// ---------------------------------------------------------------------------
///
/// Wraps well_formed_heap + bounded_stack_props (no gray_objects_on_stack)
/// into an abstract predicate for use in Pulse postconditions.
///
/// Analogous to GC.Spec.MarkInv but for the bounded mark stack variant.

module GC.Spec.MarkBoundedInv

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Mark
open GC.Spec.MarkBounded

module U64 = FStar.UInt64
module SweepInv = GC.Spec.SweepInv

/// ---------------------------------------------------------------------------
/// Introduction
/// ---------------------------------------------------------------------------

let bounded_mark_inv_intro (g: heap) (st: seq obj_addr) (cap: nat)
  = ()
/// ---------------------------------------------------------------------------
/// Elimination
/// ---------------------------------------------------------------------------

let bounded_mark_inv_elim_wfh (g: heap) (st: seq obj_addr) (cap: nat)
  = ()

let bounded_mark_inv_elim_bsp (g: heap) (st: seq obj_addr) (cap: nat)
  = ()

let bounded_mark_inv_elim_objects (g: heap) (st: seq obj_addr) (cap: nat)
  = ()

let bounded_mark_inv_elim_density (g: heap) (st: seq obj_addr) (cap: nat)
  = ()

let bounded_mark_inv_elim_cap (g: heap) (st: seq obj_addr) (cap: nat)
  = ()

/// Stack head is gray and valid
let bounded_mark_inv_head_gray (g: heap) (st: seq obj_addr) (cap: nat)
  = bounded_stack_head_is_gray g st

/// ---------------------------------------------------------------------------
/// Step preservation
/// ---------------------------------------------------------------------------

/// Step preserves full invariant (including density, objects non-empty)
#push-options "--z3rlimit 12"
let bounded_mark_inv_step_full (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  = mark_step_bounded_preserves_bsp g st cap;
    mark_step_bounded_preserves_objects g st cap;
    mark_step_bounded_preserves_density g st cap;
    let obj = Seq.head st in
    let ws = wosize_of_object obj g in
    let g1 = makeBlack obj g in
    if is_no_scan obj g then begin
      // st' = Seq.tail st, length = length st - 1 <= cap - 1 < cap
      ()
    end else begin
      // st' comes from push_children_bounded g1 st_tail obj 1UL ws cap
      push_children_bounded_cap g1 (Seq.tail st) obj 1UL ws cap
      // length st_tail <= cap - 1 < cap, so max(length st_tail, cap) = cap
      // hence length st' <= cap
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Objects preservation
/// ---------------------------------------------------------------------------

/// ---------------------------------------------------------------------------
/// Termination: count_non_black strictly decreases
/// ---------------------------------------------------------------------------

/// ---------------------------------------------------------------------------
/// Rescan
/// ---------------------------------------------------------------------------
