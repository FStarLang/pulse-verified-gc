/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.MarkInv - Implementation
/// ---------------------------------------------------------------------------

module Pulse.Spec.GC.MarkInv

open FStar.Seq
open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Object
open Pulse.Spec.GC.Fields
open Pulse.Spec.GC.Mark

module U64 = FStar.UInt64
module SweepInv = Pulse.Spec.GC.SweepInv

let mark_inv (g: heap) (st: seq obj_addr) : prop =
  well_formed_heap g /\ stack_props g st /\
  Seq.length (objects 0UL g) > 0 /\ SweepInv.heap_objects_dense g

let mark_inv_intro g st = ()

let mark_inv_elim_wfh g st = ()

let mark_inv_elim_sev g st = ()

let mark_inv_elim_sp g st = ()

let mark_inv_elim_objects g st = ()

let mark_inv_head_gray g st =
  stack_head_is_gray g st

let mark_inv_obj_fields_bound g obj = ()

let mark_inv_step g st =
  mark_step_preserves_wf g st;
  mark_step_preserves_stack_props g st;
  mark_step_preserves_objects g st;
  mark_step_preserves_density g st

#push-options "--z3rlimit 50 --fuel 2"
let mark_inv_step_no_scan g obj tl =
  let st = Seq.cons obj tl in
  Seq.lemma_tl obj tl;
  mark_inv_step g st

let mark_inv_step_scan g obj tl =
  let st = Seq.cons obj tl in
  Seq.lemma_tl obj tl;
  mark_inv_step g st
#pop-options

let mark_inv_step_preserves_objects g st =
  mark_step_preserves_objects g st

let mark_inv_elim_density g st = ()

(* PROOF GAP: stack_length_bound
   The proof requires showing:
   1. stack_no_dups st /\ stack_elements_valid g st ==> Seq.length st <= Seq.length (objects 0UL g)
      (a no-dup subset of a list is no longer than the list)
   2. well_formed_heap g ==> Seq.length (objects 0UL g) * mword <= heap_size
      (each object occupies at least mword bytes)
   3. mword >= 2 ==> Seq.length (objects 0UL g) < heap_size
   Together: Seq.length st < heap_size *)
let mark_inv_stack_bound g st = admit ()

let mark_inv_no_gray g st =
  empty_stack_no_grey g st;
  SweepInv.no_gray_intro g
