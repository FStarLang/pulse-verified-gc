module GC.SPOT.ConcreteCallFull

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
module CheneySpec = GC.Gen.Cheney
module CheneyBFS = GC.Gen.CheneyBFS
module GenImpl = GC.Gen.Impl
module Layout = GC.SPOT.Layout
module ConcreteMinor = GC.SPOT.ConcreteMinor
module ConcreteMajor = GC.SPOT.ConcreteMajor
module ConcreteScenarios = GC.SPOT.ConcreteScenarios
module ConcreteForwarding = GC.SPOT.ConcreteForwarding
module ConcreteFull = GC.SPOT.ConcreteFull
module Postconditions = GC.SPOT.Postconditions
module ThreeObjects = GC.SPOT.ThreeObjects
module CallFull = GC.SPOT.CallFull

let spot_gen_gc_success_post_from_gen_gc_post
  (r: unit{ConcreteMajor.spot_major_room})
  (d2: minor_heap) (b2: U64.t)
  (roots_out: Seq.seq U64.t) (ok: bool) (final_major: heap)
  (st: Seq.seq obj_addr) (cap: nat)
  : Lemma
      (requires (
        let result =
          CheneySpec.cheney_collect_spec
            ConcreteMinor.spot_minor2
            (ConcreteMajor.spot_major_heap r)
            (ConcreteMajor.spot_major_fp r)
            (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) in
        ok ==>
          GenImpl.gen_gc_roots_post
            ConcreteMinor.spot_minor2
            (ConcreteMajor.spot_major_heap r)
            (ConcreteMajor.spot_major_fp r)
            (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
            roots_out st cap /\
          GenImpl.gen_gc_heap_shape_post d2 b2 final_major /\
          GenImpl.gen_gc_reachable_subgraph_isomorphism_post
           ConcreteMinor.spot_minor2
           (ConcreteMajor.spot_major_heap r)
           (ConcreteMajor.spot_major_fp r)
           (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
           ok final_major roots_out st cap))
      (ensures spot_gen_gc_success_post r ok final_major)
  =
  if ok then begin
    ConcreteForwarding.spot_concrete_no_oom r;
    ConcreteFull.spot_concrete_c_field_final_points_to_a_prime
      r d2 b2 roots_out ok final_major st cap
  end

fn call_concrete_gen_gc_spot
  (r: unit{ConcreteMajor.spot_major_room})
  (gh: gen_heap_t)
  (roots: array U64.t) (nroots: SZ.t)
  (fwd_arr: array U64.t)
  (queue: larray U64.t CheneyImpl.queue_size)
  (slots: array U64.t) (nslots: SZ.t)
  (st: gray_stack)
  requires is_gen_heap gh ConcreteMinor.spot_minor2.data ConcreteMinor.spot_minor2.bump
             (ConcreteMajor.spot_major_heap r) (ConcreteMajor.spot_major_fp r) **
           pts_to roots (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) **
           pts_to fwd_arr ConcreteScenarios.spot_fwd_array **
           pts_to queue 'qv **
           pts_to slots (ThreeObjects.spot_slots (ConcreteMajor.spot_c r)) **
           is_gray_stack st Seq.empty **
           pure (
             SZ.v nroots == 2 /\
             SZ.v nslots == 1 /\
             stack_capacity st >= 2)
  returns res: (U64.t & bool)
  ensures exists* d2 b2 final_major roots_out farr_out qv_out st_out.
    is_gen_heap gh d2 b2 final_major (fst res) **
    pts_to roots roots_out **
    pts_to fwd_arr farr_out **
    pts_to queue qv_out **
    pts_to slots (ThreeObjects.spot_slots (ConcreteMajor.spot_c r)) **
    is_gray_stack st st_out **
    pure (
      let result =
        CheneySpec.cheney_collect_spec
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) in
      let ok = snd res in
      GenImpl.gen_gc_roots_post
        ConcreteMinor.spot_minor2
        (ConcreteMajor.spot_major_heap r)
        (ConcreteMajor.spot_major_fp r)
        (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
        roots_out Seq.empty (stack_capacity st) /\
      GenImpl.gen_gc_heap_shape_post d2 b2 final_major /\
      GenImpl.gen_gc_reachable_subgraph_isomorphism_post
        ConcreteMinor.spot_minor2
        (ConcreteMajor.spot_major_heap r)
        (ConcreteMajor.spot_major_fp r)
        (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
        ok final_major roots_out Seq.empty (stack_capacity st) /\
      GenImpl.gen_gc_unreachable_final_blue_post
        ConcreteMinor.spot_minor2
        (ConcreteMajor.spot_major_heap r)
        (ConcreteMajor.spot_major_fp r)
        (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
        final_major Seq.empty (stack_capacity st) /\
      Postconditions.minor_not_promoted
        ConcreteMinor.spot_minor2
        (ConcreteMajor.spot_major_heap r)
        (ConcreteMajor.spot_major_fp r)
        (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
        Layout.b_minor /\
      spot_gen_gc_success_post r ok final_major)
{
  let c = ConcreteMajor.spot_c r;
  ConcreteForwarding.spot_concrete_no_oom r;
  ThreeObjects.spot_roots_len c;
  ThreeObjects.spot_slots_len c;
  assert (pure (
    SZ.v nroots == Seq.length (ThreeObjects.spot_roots c) /\
    SZ.v nslots == 1));
  ConcreteScenarios.spot_concrete_gen_gc_pre_empty_stack
    r (stack_capacity st);
  let res = CallFull.call_gen_gc_spot
    gh roots nroots fwd_arr queue slots nslots st;
  with d2 b2 final_major roots_out farr_out qv_out st_out. _;
  let ok = snd res;
  ConcreteScenarios.spot_concrete_b_not_promoted r;
  assert (pure (Postconditions.minor_not_promoted
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    (ThreeObjects.spot_roots c)
    Layout.b_minor));
  spot_gen_gc_success_post_from_gen_gc_post
    r d2 b2 roots_out ok final_major Seq.empty (stack_capacity st);
  res
}
