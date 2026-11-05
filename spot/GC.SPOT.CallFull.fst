module GC.SPOT.CallFull

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Phase
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

module FA = GC.Gen.ForwardingArray
fn full_gc_from_shape
  (gh: gen_heap_t)
  (roots: array U64.t) (nroots: SZ.t)
  (fwd_arr: array U64.t)
  (queue: larray U64.t FA.queue_size)
  (slots: array U64.t) (nslots: SZ.t)
  (st: gray_stack)
  requires gen_phase gh 's GC.Spec.Phase.Idle ** mark_state gh 's GC.Spec.Phase.Idle ** is_gen_heap gh 'd 'b 's 'fp **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           pts_to slots 'sl **
           is_gray_stack st 'st **
           pure (GC.Gen.HeapInvariant.collection_heap_shape
                   ({ data = 'd; bump = 'b } <: minor_state) 's 'fp /\
                 gen_gc_stack_budget 'rs 'st (stack_capacity st) /\
                 SZ.v nroots == Seq.length 'rs /\
                 Seq.length 'farr == FA.fwd_array_size /\
                 (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\
                 GC.Gen.RefTable.ref_table_sound 's 'sl (SZ.v nslots) /\
                 GC.Gen.RefTable.ref_table_covers_minor_ptrs 's 'sl (SZ.v nslots) /\
                 GC.Gen.MinorCollectForwarding.remembered_targets_in_roots 's 'rs 'sl (SZ.v nslots) /\
                 GC.Gen.MinorCollectForwarding.roots_valid_for_minor_collection
                   ({ data = 'd; bump = 'b } <: minor_state) 's 'rs)
  returns res: (U64.t & bool)
  ensures exists* d2 b2 s2 rs2 farr2 qv2 st2.
    gen_phase gh s2 GC.Spec.Phase.Idle ** mark_state gh s2 GC.Spec.Phase.Idle ** is_gen_heap gh d2 b2 s2 (fst res) **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pts_to slots 'sl **
    is_gray_stack st st2 **
    pure (
      let minor_st : minor_state = { data = 'd; bump = 'b } in
      let minor_st_out : minor_state = { data = d2; bump = b2 } in
      let ok = snd res in
      (not ok ==> GC.Gen.CheneyBFS.cheney_oom Idle minor_st 's 'fp 'rs) /\
      gen_gc_roots_post minor_st 's 'fp 'rs rs2 ok 'st (stack_capacity st) /\
      minor_st_out == minor_reset minor_st /\
      GC.Gen.HeapInvariant.collection_heap_shape minor_st_out s2 (fst res) /\
      gen_gc_reachable_subgraph_isomorphism_post
        minor_st 's 'fp 'rs ok s2 rs2 'st (stack_capacity st) /\
      gen_gc_unreachable_final_blue_post
        minor_st 's 'fp 'rs ok s2 'st (stack_capacity st))
{
  GC.Gen.Incremental.phase_shape_idle ({ data = 'd; bump = 'b } <: minor_state) 's 'fp;
  fold (gc_state gh 'd 'b 's 'fp GC.Spec.Phase.Idle);
  let ok = full_gc gh roots nroots fwd_arr queue slots nslots st;
  with d2 b2 s2 fp2. assert (gc_state gh d2 b2 s2 fp2 GC.Spec.Phase.Idle);
  unfold gc_state;
  unfold is_gen_heap;
  let fp = Pulse.Lib.Reference.op_Bang gh.fp_ref;
  fold (is_gen_heap gh d2 b2 s2 fp);
  (fp, ok)
}

fn call_gen_gc_spot
  (gh: gen_heap_t)
  (roots: array U64.t) (nroots: SZ.t)
  (fwd_arr: array U64.t)
  (queue: larray U64.t FA.queue_size)
  (slots: array U64.t) (nslots: SZ.t)
  (st: gray_stack)
  requires gen_phase gh 's GC.Spec.Phase.Idle ** mark_state gh 's GC.Spec.Phase.Idle ** is_gen_heap gh 'd 'b 's 'fp **
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
    gen_phase gh s2 GC.Spec.Phase.Idle ** mark_state gh s2 GC.Spec.Phase.Idle ** is_gen_heap gh d2 b2 s2 (fst res) **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pts_to slots 'sl **
    is_gray_stack st st2 **
    pure (
      gen_gc_roots_post
        ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs
        rs2 (snd res) 'st (stack_capacity st) /\
      gen_gc_heap_shape_post d2 b2 s2 /\
      gen_gc_reachable_subgraph_isomorphism_post
        ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs
        (snd res) s2 rs2 'st (stack_capacity st) /\
      gen_gc_unreachable_final_blue_post
        ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs
        (snd res) s2 'st (stack_capacity st))
{
  Preconditions.gen_gc_pre_elim
    ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs 'farr 'sl
    (SZ.v nslots) 'st (stack_capacity st);
  Preconditions.minor_collect_full_pre_elim
    ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs 'farr 'sl
    (SZ.v nslots);
  let res = full_gc_from_shape gh roots nroots fwd_arr queue slots nslots st;
  // `full_gc` promises the invariant itself; the colour-only projection this
  // wrapper advertises is derived from it here rather than restated there.
  with d2 b2 s2. assert (is_gen_heap gh d2 b2 s2 (fst res));
  gen_gc_heap_shape_post_intro d2 b2 s2 (fst res);
  res
}
