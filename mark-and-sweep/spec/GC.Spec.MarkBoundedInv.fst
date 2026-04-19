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

/// Abstract bounded mark invariant
let bounded_mark_inv (g: heap) (st: seq obj_addr) (cap: nat) : prop =
  well_formed_heap g /\ bounded_stack_props g st /\
  Seq.length (objects 0UL g) > 0 /\
  SweepInv.heap_objects_dense g /\
  Seq.length st <= cap /\
  cap > 0

/// ---------------------------------------------------------------------------
/// Introduction
/// ---------------------------------------------------------------------------

let bounded_mark_inv_intro (g: heap) (st: seq obj_addr) (cap: nat)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                   Seq.length (objects 0UL g) > 0 /\
                   SweepInv.heap_objects_dense g /\
                   Seq.length st <= cap /\ cap > 0)
          (ensures bounded_mark_inv g st cap)
  = ()

/// From full mark_inv to bounded (stronger → weaker)
let bounded_mark_inv_from_full (g: heap) (st: seq obj_addr) (cap: nat)
  : Lemma (requires well_formed_heap g /\ stack_props g st /\
                   Seq.length (objects 0UL g) > 0 /\
                   SweepInv.heap_objects_dense g /\
                   Seq.length st <= cap /\ cap > 0)
          (ensures bounded_mark_inv g st cap)
  = bounded_from_full g st

/// ---------------------------------------------------------------------------
/// Elimination
/// ---------------------------------------------------------------------------

let bounded_mark_inv_elim_wfh (g: heap) (st: seq obj_addr) (cap: nat)
  : Lemma (requires bounded_mark_inv g st cap)
          (ensures well_formed_heap g)
  = ()

let bounded_mark_inv_elim_bsp (g: heap) (st: seq obj_addr) (cap: nat)
  : Lemma (requires bounded_mark_inv g st cap)
          (ensures bounded_stack_props g st)
  = ()

let bounded_mark_inv_elim_objects (g: heap) (st: seq obj_addr) (cap: nat)
  : Lemma (requires bounded_mark_inv g st cap)
          (ensures Seq.length (objects 0UL g) > 0)
  = ()

let bounded_mark_inv_elim_density (g: heap) (st: seq obj_addr) (cap: nat)
  : Lemma (requires bounded_mark_inv g st cap)
          (ensures SweepInv.heap_objects_dense g)
  = ()

let bounded_mark_inv_elim_cap (g: heap) (st: seq obj_addr) (cap: nat)
  : Lemma (requires bounded_mark_inv g st cap)
          (ensures Seq.length st <= cap /\ cap > 0)
  = ()

/// Stack head is gray and valid
let bounded_mark_inv_head_gray (g: heap) (st: seq obj_addr) (cap: nat)
  : Lemma (requires bounded_mark_inv g st cap /\ Seq.length st > 0)
          (ensures is_gray (Seq.head st) g /\
                   Seq.mem (Seq.head st) (objects 0UL g))
  = bounded_stack_head_is_gray g st

/// ---------------------------------------------------------------------------
/// Step preservation
/// ---------------------------------------------------------------------------

let bounded_mark_inv_step (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  : Lemma (requires bounded_mark_inv g st cap)
          (ensures (let (g', st') = mark_step_bounded g st cap in
                    well_formed_heap g' /\ bounded_stack_props g' st'))
  = mark_step_bounded_preserves_bsp g st cap

/// Step preserves full invariant (including density, objects non-empty)
#push-options "--z3rlimit 50"
let bounded_mark_inv_step_full (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  : Lemma (requires bounded_mark_inv g st cap)
          (ensures (let (g', st') = mark_step_bounded g st cap in
                    bounded_mark_inv g' st' cap))
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

let bounded_mark_inv_step_preserves_objects
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  : Lemma (requires bounded_mark_inv g st cap)
          (ensures objects 0UL (fst (mark_step_bounded g st cap)) == objects 0UL g)
  = mark_step_bounded_preserves_objects g st cap

/// ---------------------------------------------------------------------------
/// Termination: count_non_black strictly decreases
/// ---------------------------------------------------------------------------

let bounded_mark_inv_step_decreases (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  : Lemma (requires bounded_mark_inv g st cap)
          (ensures count_non_black (fst (mark_step_bounded g st cap)) < count_non_black g)
  = mark_step_bounded_decreases_non_black g st cap

/// ---------------------------------------------------------------------------
/// Rescan
/// ---------------------------------------------------------------------------

let bounded_mark_inv_rescan (g: heap) (cap: nat)
  : Lemma (requires well_formed_heap g /\
                   Seq.length (objects 0UL g) > 0 /\
                   SweepInv.heap_objects_dense g /\ cap > 0)
          (ensures (let st = rescan_heap g (objects 0UL g) Seq.empty cap in
                    bounded_mark_inv g st cap))
  = rescan_heap_bounded_stack_props g (objects 0UL g) cap;
    rescan_heap_cap_bound g (objects 0UL g) Seq.empty cap

/// If rescan returns empty, no gray objects remain
let bounded_mark_inv_rescan_complete (g: heap) (cap: nat)
  : Lemma (requires cap > 0)
          (ensures (let st = rescan_heap g (objects 0UL g) Seq.empty cap in
                    Seq.length st = 0 ==> SweepInv.no_gray_objects g))
  = rescan_complete g cap;
    let st = rescan_heap g (objects 0UL g) Seq.empty cap in
    if Seq.length st = 0 then
      SweepInv.no_gray_intro g
    else ()
