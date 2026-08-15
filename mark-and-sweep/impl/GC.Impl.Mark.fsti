(*
   Pulse GC - Mark Module Interface

   Exports the mark_loop entry point for the mark phase.
*)

module GC.Impl.Mark

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
open GC.Impl.Stack
module U64 = FStar.UInt64
module Seq = FStar.Seq
module SpecMark = GC.Spec.Mark
module SpecMarkInv = GC.Spec.MarkInv
module SpecFields = GC.Spec.Fields

/// Mark loop: process gray stack until empty.
/// Postcondition: mark_inv preserved, stack empty, spec equality.
fn mark_loop (heap: heap_t) (st: gray_stack)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (SpecMarkInv.mark_inv 's 'st /\ stack_capacity st >= heap_size)
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
          pure (SpecMarkInv.mark_inv s2 st2 /\ Seq.length st2 == 0 /\
                SpecFields.objects zero_addr s2 == SpecFields.objects zero_addr 's /\
                s2 == SpecMark.mark 's 'st)
