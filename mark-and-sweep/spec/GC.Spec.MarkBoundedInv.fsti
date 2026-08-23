/// ---------------------------------------------------------------------------
/// GC.Spec.MarkBoundedInv — Interface
/// ---------------------------------------------------------------------------

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

/// Abstract bounded mark invariant (exposed for unfolding)
let bounded_mark_inv (g: heap) (st: seq obj_addr) (cap: nat) : prop =
  well_formed_heap g /\ bounded_stack_props g st /\
  Seq.length (objects zero_addr g) > 0 /\
  SweepInv.heap_objects_dense g /\
  Seq.length st <= cap /\
  cap > 0

/// Introduction
val bounded_mark_inv_intro (g: heap) (st: seq obj_addr) (cap: nat)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                   Seq.length (objects zero_addr g) > 0 /\
                   SweepInv.heap_objects_dense g /\
                   Seq.length st <= cap /\ cap > 0)
          (ensures bounded_mark_inv g st cap)

/// Elimination
val bounded_mark_inv_elim_wfh (g: heap) (st: seq obj_addr) (cap: nat)
  : Lemma (requires bounded_mark_inv g st cap)
          (ensures well_formed_heap g)

val bounded_mark_inv_elim_bsp (g: heap) (st: seq obj_addr) (cap: nat)
  : Lemma (requires bounded_mark_inv g st cap)
          (ensures bounded_stack_props g st)

val bounded_mark_inv_elim_objects (g: heap) (st: seq obj_addr) (cap: nat)
  : Lemma (requires bounded_mark_inv g st cap)
          (ensures Seq.length (objects zero_addr g) > 0)

val bounded_mark_inv_elim_density (g: heap) (st: seq obj_addr) (cap: nat)
  : Lemma (requires bounded_mark_inv g st cap)
          (ensures SweepInv.heap_objects_dense g)

val bounded_mark_inv_elim_cap (g: heap) (st: seq obj_addr) (cap: nat)
  : Lemma (requires bounded_mark_inv g st cap)
          (ensures Seq.length st <= cap /\ cap > 0)

/// Stack head is gray and valid
val bounded_mark_inv_head_gray (g: heap) (st: seq obj_addr) (cap: nat)
  : Lemma (requires bounded_mark_inv g st cap /\ Seq.length st > 0)
          (ensures is_gray (Seq.head st) g /\
                   Seq.mem (Seq.head st) (objects zero_addr g))
val bounded_mark_inv_step_full (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  : Lemma (requires bounded_mark_inv g st cap)
          (ensures (let (g', st') = mark_step_bounded g st cap in
                    bounded_mark_inv g' st' cap))
