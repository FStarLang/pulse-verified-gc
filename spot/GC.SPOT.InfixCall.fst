module GC.SPOT.InfixCall

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

module CheneyImpl = GC.Gen.Impl.Cheney
module GenInv = GC.Gen.HeapInvariant
module InfixMajor = GC.SPOT.InfixMajor
module InfixPre = GC.SPOT.InfixPre

/// Running the real collector on a heap that contains a genuine OCaml interior
/// pointer.
///
/// The precondition is discharged entirely by `GC.SPOT.InfixPre`, so calling
/// this function is a machine-checked demonstration that `gen_gc` *accepts* an
/// infix-pointing heap.  The postcondition records what comes back:
///
///   * the collection succeeded (`snd res == true`);
///   * `GC.Gen.HeapInvariant.collection_heap_shape` -- the very predicate the
///     precondition demands -- holds again of the returned state, so the heap
///     is ready for the next cycle;
///   * the nursery handed back is the reset one;
///   * `Q`, the object holding the interior pointer, is still an enumerated
///     object of the post-collection major heap.
fn call_gen_gc_infix
  (r: (r:unit{InfixMajor.spot_infix_room}))
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
                 ({ data = 'd; bump = 'b } <: minor_state) ==
                   InfixPre.spot_infix_minor /\
                 's == InfixMajor.spot_infix_heap r /\
                 'fp == InfixMajor.spot_infix_fp r /\
                 'rs == InfixPre.spot_infix_roots r /\
                 'farr == InfixPre.spot_infix_fwd_array /\
                 'sl == InfixPre.spot_infix_slots /\
                 SZ.v nslots == 0 /\
                 'st == Seq.empty /\
                 stack_capacity st >= 1)
  returns res: (U64.t & bool)
  ensures exists* d2 b2 s2 rs2 farr2 qv2 st2.
    is_gen_heap gh d2 b2 s2 (fst res) **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pts_to slots 'sl **
    is_gray_stack st st2 **
    pure (
      snd res == true /\
      ({ data = d2; bump = b2 } <: minor_state) == InfixPre.spot_infix_minor /\
      GenInv.collection_heap_shape
        InfixPre.spot_infix_minor s2 (fst res) /\
      gen_gc_heap_shape_post d2 b2 s2 /\
      Seq.mem (InfixMajor.spot_q r <: U64.t) rs2 /\
      Seq.mem (InfixMajor.spot_q r) (GC.Spec.Fields.objects zero_addr s2))
{
  InfixPre.spot_infix_gen_gc_pre r (stack_capacity st);
  GC.SPOT.Preconditions.gen_gc_pre_elim
    InfixPre.spot_infix_minor 's 'fp 'rs 'farr 'sl
    (SZ.v nslots) 'st (stack_capacity st);
  GC.SPOT.Preconditions.minor_collect_full_pre_elim
    InfixPre.spot_infix_minor 's 'fp 'rs 'farr 'sl (SZ.v nslots);
  let res = gen_gc gh roots nroots fwd_arr queue slots nslots st;
  with d2 b2 s2 rs2. assert (is_gen_heap gh d2 b2 s2 (fst res) ** pts_to roots rs2);
  GC.SPOT.InfixPost.spot_infix_ok r (snd res);
  GC.SPOT.InfixPost.spot_infix_q_survives r rs2 s2 'st (stack_capacity st);
  InfixPre.spot_infix_minor_is_reset ({ data = 'd; bump = 'b } <: minor_state);
  gen_gc_heap_shape_post_intro d2 b2 s2 (fst res);
  res
}
