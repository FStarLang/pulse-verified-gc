/// ---------------------------------------------------------------------------
/// GC.Spec.MarkInv - Implementation
/// ---------------------------------------------------------------------------

module GC.Spec.MarkInv

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Mark

module U64 = FStar.UInt64
module SweepInv = GC.Spec.SweepInv

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

let mark_inv_stack_bound g st =
  // Step 1: stack is no longer than object list (no-dup subset bound)
  stack_length_bound g st;
  // Step 2: object count bounded by heap_size / 8
  object_count_bound g
  // Step 3: Z3 closes: heap_size >= 8 (pos + %8==0) => heap_size/8 < heap_size

let mark_inv_push_children_bound g obj tl =
  mark_inv_step_scan g obj tl;
  let g' = GC.Spec.Object.makeBlack obj g in
  let wz = GC.Spec.Object.wosize_of_object obj g in
  mark_inv_stack_bound (fst (push_children g' tl obj 1UL wz))
                       (snd (push_children g' tl obj 1UL wz))

let push_children_stack_monotone g st obj i ws =
  push_children_stack_monotone g st obj i ws

let mark_inv_no_gray g st =
  empty_stack_no_grey g st;
  SweepInv.no_gray_intro g
