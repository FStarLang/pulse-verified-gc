module GC.SPOT.CallFull

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Impl.MinorHeap
open GC.Gen.Impl
open GC.Impl.Heap
open GC.Impl.Stack

module Preconditions = GC.SPOT.Preconditions
module CheneyImpl = GC.Gen.Impl.Cheney
module CheneySpec = GC.Gen.Cheney
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module MinorFwd = GC.Gen.MinorCollectForwarding
module RBridge = GC.Gen.ReachabilityBridge
module GenInv = GC.Gen.HeapInvariant

fn call_gen_gc_spot
  (gh: gen_heap_t)
  (roots: array U64.t) (nroots: SZ.t)
  (fwd_arr: array U64.t)
  (queue: larray U64.t CheneyImpl.queue_size)
  (slots: array U64.t) (nslots: SZ.t)
  (st: gray_stack)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           pts_to slots 'sl **
           is_gray_stack st 'st **
           pure (SZ.v nroots == Seq.length 'rs /\
                 Preconditions.gen_gc_pre
                   ({ data = 'd; bump = 'b } <: minor_state) 's 'fp
                   'rs 'farr 'sl (SZ.v nslots) 'st (stack_capacity st))
  returns res: (U64.t & bool)
  ensures exists* d2 b2 s2 rs2 farr2 qv2 st2.
    is_gen_heap gh d2 b2 s2 (fst res) **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pts_to slots 'sl **
    is_gray_stack st st2 **
    pure (
      gen_gc_roots_post
        ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs
        rs2 'st (stack_capacity st) /\
      gen_gc_heap_shape_post d2 b2 s2 /\
      gen_gc_reachable_subgraph_isomorphism_post
        ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs
        (snd res) s2 rs2 'st (stack_capacity st) /\
      gen_gc_unreachable_final_blue_post
        ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs
        s2 'st (stack_capacity st))
{
  Preconditions.gen_gc_pre_elim
    ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs 'farr 'sl
    (SZ.v nslots) 'st (stack_capacity st);
  Preconditions.minor_collect_full_pre_elim
    ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs 'farr 'sl
    (SZ.v nslots);
  gen_gc gh roots nroots fwd_arr queue slots nslots st
}
