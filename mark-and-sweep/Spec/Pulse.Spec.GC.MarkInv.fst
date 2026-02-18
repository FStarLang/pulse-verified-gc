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

let mark_inv (g: heap) (st: seq obj_addr) : prop =
  well_formed_heap g /\ stack_props g st

let mark_inv_intro g st = ()

let mark_inv_elim_wfh g st = ()

let mark_inv_elim_sev g st = ()

let mark_inv_head_gray g st =
  stack_head_is_gray g st

let mark_inv_obj_fields_bound g obj = ()

let mark_inv_step g st =
  mark_step_preserves_wf g st;
  mark_step_preserves_stack_props g st
