(*
   Pulse GC - Bounded Mark Module Interface

   Exports the bounded mark loop entry point. Uses a configurable-size mark
   stack with overflow handling: when the stack is full during push_children,
   children are grayed but not pushed; a linear heap rescan rediscovers them.
*)

module GC.Impl.MarkBounded

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
open GC.Impl.Stack
module U64 = FStar.UInt64
module Seq = FStar.Seq
module SpecMarkBounded = GC.Spec.MarkBounded
module SpecMarkBoundedInv = GC.Spec.MarkBoundedInv
module SpecFields = GC.Spec.Fields
module SweepInv = GC.Spec.SweepInv

/// Bounded mark loop: process gray objects with overflow handling.
/// The outer loop alternates between draining the stack and rescanning
/// the heap for remaining gray objects until none remain.
///
/// Postcondition: well_formed_heap preserved, no gray objects, objects preserved.
fn mark_loop_bounded (heap: heap_t) (st: gray_stack)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (SpecMarkBoundedInv.bounded_mark_inv 's 'st (stack_capacity st))
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
          pure (SpecFields.well_formed_heap s2 /\
                SweepInv.no_gray_objects s2 /\
                SpecFields.objects zero_addr s2 == SpecFields.objects zero_addr 's)
