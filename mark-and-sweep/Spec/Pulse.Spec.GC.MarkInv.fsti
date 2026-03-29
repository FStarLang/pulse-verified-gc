/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.MarkInv - Abstract Mark Loop Invariant
/// ---------------------------------------------------------------------------
///
/// Wraps well_formed_heap and stack_props into an abstract predicate
/// for use in Pulse postconditions without quantifier explosion.
///
/// Also provides non-quantified extraction lemmas that Pulse code can
/// use to derive specific facts (head is gray, addresses valid, etc.)

module Pulse.Spec.GC.MarkInv

open FStar.Seq
open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Heap
open Pulse.Spec.GC.Object
open Pulse.Spec.GC.Fields
open Pulse.Spec.GC.Mark

module U64 = FStar.UInt64
module SweepInv = Pulse.Spec.GC.SweepInv

/// Abstract mark invariant: well_formed_heap + stack_props
val mark_inv (g: heap) (st: seq obj_addr) : prop

/// ---------------------------------------------------------------------------
/// Introduction
/// ---------------------------------------------------------------------------

val mark_inv_intro : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\
                  Seq.length (objects 0UL g) > 0 /\ SweepInv.heap_objects_dense g)
        (ensures mark_inv g st)

/// ---------------------------------------------------------------------------
/// Elimination (well_formed_heap)
/// ---------------------------------------------------------------------------

val mark_inv_elim_wfh : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires mark_inv g st)
        (ensures well_formed_heap g)

/// Elimination (stack_elements_valid)
val mark_inv_elim_sev : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires mark_inv g st)
        (ensures stack_elements_valid g st)

/// Elimination (stack_props)
val mark_inv_elim_sp : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires mark_inv g st)
        (ensures stack_props g st)

/// ---------------------------------------------------------------------------
/// Non-quantified extraction lemmas for Pulse use
/// ---------------------------------------------------------------------------

/// Elimination: objects 0UL is non-empty
val mark_inv_elim_objects : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires mark_inv g st)
        (ensures Seq.length (objects 0UL g) > 0)

/// Stack head is gray and a valid object
val mark_inv_head_gray : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires mark_inv g st /\ Seq.length st > 0)
        (ensures is_gray (Seq.head st) g /\
                 Seq.mem (Seq.head st) (objects 0UL g))

/// Object in objects list has hd_address + (1+wosize)*mword <= heap_size
val mark_inv_obj_fields_bound : (g: heap) -> (obj: obj_addr) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g))
        (ensures U64.v (hd_address obj) + U64.v mword +
                 FStar.Mul.(U64.v (wosize_of_object obj g) * U64.v mword) <= heap_size)

/// ---------------------------------------------------------------------------
/// Preservation through mark_step
/// ---------------------------------------------------------------------------

val mark_inv_step : (g: heap) -> (st: seq obj_addr{Seq.length st > 0 /\ stack_elements_valid g st}) ->
  Lemma (requires mark_inv g st)
        (ensures mark_inv (fst (mark_step g st)) (snd (mark_step g st)))

/// When head is no_scan, mark_step just blackens and pops
val mark_inv_step_no_scan : (g: heap) -> (obj: obj_addr) -> (tl: seq obj_addr) ->
  Lemma (requires mark_inv g (Seq.cons obj tl) /\ is_no_scan obj g)
        (ensures mark_inv (makeBlack obj g) tl)

/// When head is scannable, mark_step blackens + push_children
val mark_inv_step_scan : (g: heap) -> (obj: obj_addr) -> (tl: seq obj_addr) ->
  Lemma (requires mark_inv g (Seq.cons obj tl) /\ not (is_no_scan obj g))
        (ensures (let g' = makeBlack obj g in
                  let wz = wosize_of_object obj g in
                  mark_inv (fst (push_children g' tl obj 1UL wz))
                           (snd (push_children g' tl obj 1UL wz))))

/// ---------------------------------------------------------------------------
/// Objects preservation through mark_step
/// ---------------------------------------------------------------------------

val mark_inv_step_preserves_objects : (g: heap) -> (st: seq obj_addr{Seq.length st > 0 /\ stack_elements_valid g st}) ->
  Lemma (requires mark_inv g st)
        (ensures objects 0UL (fst (mark_step g st)) == objects 0UL g)

/// ---------------------------------------------------------------------------
/// Density elimination and preservation
/// ---------------------------------------------------------------------------

val mark_inv_elim_density : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires mark_inv g st)
        (ensures SweepInv.heap_objects_dense g)

/// ---------------------------------------------------------------------------
/// Stack length bound (proof gap — provable from stack_no_dups + stack_elements_valid)
/// ---------------------------------------------------------------------------

/// The gray stack length is bounded by the number of heap objects.
/// Proof: stack_no_dups + stack_elements_valid imply the stack is a
/// duplicate-free subsequence of (objects 0UL g), hence no longer.
/// Combined with objects_count * mword <= heap_size, this gives
/// Seq.length st <= heap_size / mword < heap_size.
val mark_inv_stack_bound : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires mark_inv g st)
        (ensures Seq.length st < heap_size)

/// push_children result has bounded stack length
val mark_inv_push_children_bound : (g: heap) -> (obj: obj_addr) -> (tl: seq obj_addr) ->
  Lemma (requires mark_inv g (Seq.cons obj tl) /\ not (is_no_scan obj g))
        (ensures (let g' = makeBlack obj g in
                  let wz = wosize_of_object obj g in
                  Seq.length (snd (push_children g' tl obj 1UL wz)) < heap_size))

/// push_children only grows the stack
val push_children_stack_monotone : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) ->
  Lemma (ensures Seq.length st <= Seq.length (snd (push_children g st obj i ws)))

val mark_inv_no_gray : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires mark_inv g st /\ Seq.length st = 0)
        (ensures SweepInv.no_gray_objects g)
