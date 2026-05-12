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
module SpecMark = GC.Spec.Mark
module SpecMarkBounded = GC.Spec.MarkBounded
module SpecMarkBoundedInv = GC.Spec.MarkBoundedInv
module SpecMarkBoundedCorr = GC.Spec.MarkBoundedCorrectness
module SpecFields = GC.Spec.Fields
module SweepInv = GC.Spec.SweepInv
module SpecHeap = GC.Spec.Heap
module SpecObject = GC.Spec.Object
open GC.Spec.Base

/// Spec function: what darken_if_white_bounded computes
let darken_if_white_bounded_spec (g: heap_state) (st: Seq.seq obj_addr)
    (h_addr: hp_addr) (cap: nat)
  : GTot (heap_state & Seq.seq obj_addr)
  = if U64.v h_addr + U64.v mword < heap_size then
      let obj = SpecHeap.f_address h_addr in
      if SpecObject.is_white obj g then
        let g' = SpecObject.makeGray obj g in
        if Seq.length st < cap then (g', Seq.cons obj st)
        else (g', st)
      else (g, st)
    else (g, st)

/// Spec function: what check_and_darken_bounded computes
let check_and_darken_bounded_spec (g: heap_state) (st: Seq.seq obj_addr) (v: U64.t) (cap: nat)
  : GTot (heap_state & Seq.seq obj_addr)
  = if U64.v v > 0 && U64.v v < heap_size && U64.v v % U64.v mword = 0 then
      darken_if_white_bounded_spec g st (U64.sub v mword) cap
    else (g, st)

/// Bounded mark loop: process gray objects with overflow handling.
/// The outer loop alternates between draining the stack and rescanning
/// the heap for remaining gray objects until none remain.
///
/// Postcondition: well_formed_heap preserved, no gray objects, objects preserved,
/// mark_color_inv, gray_black_reachable, and gray_stays.
/// Check if object at h_addr is white. If so, gray it and push to stack
/// (if stack has capacity). Used by the bridge for root darkening.
fn darken_if_white_bounded (heap: heap_t) (st: gray_stack) (h_addr: hp_addr) (cap: Ghost.erased nat)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (U64.v h_addr + U64.v mword < heap_size /\
                 Seq.length 'st <= cap /\
                 stack_capacity st == cap)
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
    pure ((s2, st2) == darken_if_white_bounded_spec 's 'st h_addr cap)

/// Check if value is a pointer; if so, darken its target with bounded push.
fn check_and_darken_bounded (heap: heap_t) (st: gray_stack) (v: U64.t) (cap: Ghost.erased nat)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (Seq.length 'st <= cap /\ stack_capacity st == cap)
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
    pure ((s2, st2) == check_and_darken_bounded_spec 's 'st v cap)

/// Bounded mark loop: process gray objects with overflow handling.
/// The outer loop alternates between draining the stack and rescanning
/// the heap for remaining gray objects until none remain.
///
/// Postcondition: well_formed_heap preserved, no gray objects, objects preserved,
/// mark_color_inv, gray_black_reachable, and gray_stays.
fn mark_loop_bounded (heap: heap_t) (st: gray_stack)
                     (roots: Ghost.erased (Seq.seq GC.Spec.Base.obj_addr))
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (SpecMarkBoundedInv.bounded_mark_inv 's 'st (stack_capacity st) /\
                 SpecMark.no_black_objects 's /\
                 SpecMark.no_pointer_to_blue 's /\
                 SpecMark.root_props 's roots /\
                 (forall (x:GC.Spec.Base.obj_addr). Seq.mem x (SpecFields.objects GC.Spec.Base.zero_addr 's) /\
                   (GC.Spec.Object.is_gray x 's \/ GC.Spec.Object.is_black x 's) ==> Seq.mem x roots) /\
                 (let graph = GC.Spec.HeapModel.create_graph 's in
                  let roots' = GC.Spec.HeapGraph.coerce_to_vertex_list roots in
                  GC.Spec.Graph.graph_wf graph /\ GC.Spec.Graph.is_vertex_set roots' /\
                  GC.Spec.Graph.subset_vertices roots' graph.vertices))
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
          pure (SpecFields.well_formed_heap s2 /\
                SweepInv.no_gray_objects s2 /\
                SpecFields.objects GC.Spec.Base.zero_addr s2 == SpecFields.objects GC.Spec.Base.zero_addr 's /\
                SpecMarkBoundedCorr.mark_color_inv 's s2 /\
                SpecMarkBoundedCorr.gray_black_reachable 's s2 roots /\
                SpecMarkBoundedCorr.gray_stays 's s2)
