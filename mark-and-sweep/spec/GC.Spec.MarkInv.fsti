/// ---------------------------------------------------------------------------
/// GC.Spec.MarkInv - Abstract Mark Loop Invariant
/// ---------------------------------------------------------------------------
///
/// Wraps well_formed_heap and stack_props into an abstract predicate
/// for use in Pulse postconditions without quantifier explosion.
///
/// Also provides non-quantified extraction lemmas that Pulse code can
/// use to derive specific facts (head is gray, addresses valid, etc.)

module GC.Spec.MarkInv

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Mark

module U64 = FStar.UInt64
module SweepInv = GC.Spec.SweepInv

/// Abstract mark invariant: well_formed_heap + stack_props
val mark_inv (g: heap) (st: seq obj_addr) : prop

/// ---------------------------------------------------------------------------
/// Introduction
/// ---------------------------------------------------------------------------

/// ---------------------------------------------------------------------------
/// Elimination (well_formed_heap)
/// ---------------------------------------------------------------------------

val mark_inv_elim_wfh : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires mark_inv g st)
        (ensures well_formed_heap g)
/// Elimination (stack_props)
val mark_inv_elim_sp : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires mark_inv g st)
        (ensures stack_props g st)

/// ---------------------------------------------------------------------------
/// Non-quantified extraction lemmas for Pulse use
/// ---------------------------------------------------------------------------

/// Elimination: objects zero_addr is non-empty
val mark_inv_elim_objects : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires mark_inv g st)
        (ensures Seq.length (objects zero_addr g) > 0)
/// ---------------------------------------------------------------------------
/// Preservation through mark_step
/// ---------------------------------------------------------------------------

/// ---------------------------------------------------------------------------
/// Objects preservation through mark_step
/// ---------------------------------------------------------------------------

/// ---------------------------------------------------------------------------
/// Density elimination and preservation
/// ---------------------------------------------------------------------------

val mark_inv_elim_density : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires mark_inv g st)
        (ensures SweepInv.heap_objects_dense g)

/// ---------------------------------------------------------------------------
/// Stack length bound (proof gap — provable from stack_no_dups + stack_elements_valid)
/// ---------------------------------------------------------------------------
