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
open Pulse.Spec.GC.Object
open Pulse.Spec.GC.Fields
open Pulse.Spec.GC.Mark

module U64 = FStar.UInt64

/// Abstract mark invariant: well_formed_heap + stack_props
val mark_inv (g: heap) (st: seq obj_addr) : prop

/// ---------------------------------------------------------------------------
/// Introduction
/// ---------------------------------------------------------------------------

val mark_inv_intro : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st)
        (ensures mark_inv g st)

/// ---------------------------------------------------------------------------
/// Elimination (well_formed_heap)
/// ---------------------------------------------------------------------------

val mark_inv_elim_wfh : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires mark_inv g st)
        (ensures well_formed_heap g)

/// ---------------------------------------------------------------------------
/// Non-quantified extraction lemmas for Pulse use
/// ---------------------------------------------------------------------------

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

val mark_inv_step : (g: heap) -> (st: seq obj_addr{Seq.length st > 0}) ->
  Lemma (requires mark_inv g st)
        (ensures mark_inv (fst (mark_step g st)) (snd (mark_step g st)))
