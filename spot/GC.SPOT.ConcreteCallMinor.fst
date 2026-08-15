module GC.SPOT.ConcreteCallMinor

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

module CheneyImpl = GC.Gen.Impl.Cheney
module CheneySpec = GC.Gen.Cheney
module PromoteSpec = GC.Gen.Promote
module MinorFwd = GC.Gen.MinorCollectForwarding
module Layout = GC.SPOT.Layout
module ConcreteMinor = GC.SPOT.ConcreteMinor
module ConcreteMajor = GC.SPOT.ConcreteMajor
module ConcreteScenarios = GC.SPOT.ConcreteScenarios
module ConcreteForwarding = GC.SPOT.ConcreteForwarding
module Postconditions = GC.SPOT.Postconditions
module ThreeObjects = GC.SPOT.ThreeObjects
module Preconditions = GC.SPOT.Preconditions
module SpecHeap = GC.Spec.Heap
module ConcreteSetup = GC.SPOT.ConcreteSetup

let spot_minor_collect_full_success_post_from_call_post
  (r: unit{ConcreteMajor.spot_major_room})
  (post_major: heap)
  : Lemma
      (requires
        post_major ==
          (CheneySpec.cheney_collect_spec
            ConcreteMinor.spot_minor2
            (ConcreteMajor.spot_major_heap r)
            (ConcreteMajor.spot_major_fp r)
            (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))).mc_major)
      (ensures spot_minor_collect_full_success_post r post_major)
  =
  ConcreteForwarding.spot_concrete_no_oom r;
  ConcreteScenarios.spot_concrete_a_promoted_from_no_oom r;
  ConcreteScenarios.spot_concrete_c_field_rewritten_from_no_oom r;
  ConcreteScenarios.spot_concrete_b_not_promoted r

divergent
fn call_concrete_minor_collect_full_spot_borrowed
  (r: unit{ConcreteMajor.spot_major_room})
  (gh: gen_heap_t)
  (roots: array U64.t) (nroots: SZ.t)
  (fwd_arr: array U64.t)
  (queue: larray U64.t CheneyImpl.queue_size)
  (slots: array U64.t) (nslots: SZ.t)
  requires is_gen_heap gh ConcreteMinor.spot_minor2.data ConcreteMinor.spot_minor2.bump
             (ConcreteMajor.spot_major_heap r) (ConcreteMajor.spot_major_fp r) **
           pts_to roots (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) **
           pts_to fwd_arr ConcreteScenarios.spot_fwd_array **
           pts_to queue 'qv **
           pts_to slots (ThreeObjects.spot_slots (ConcreteMajor.spot_c r)) **
           pure (
             SZ.v nroots == 2 /\
             SZ.v nslots == 1)
  returns ok: bool
  ensures exists* d2 b2 post_major fp2 roots_out farr_out qv_out.
    is_gen_heap gh d2 b2 post_major fp2 **
    pts_to roots roots_out **
    pts_to fwd_arr farr_out **
    pts_to queue qv_out **
    pts_to slots (ThreeObjects.spot_slots (ConcreteMajor.spot_c r)) **
    pure (
      U64.v b2 == 0 /\
      Postconditions.minor_collect_full_post
        ConcreteMinor.spot_minor2
        (ConcreteMajor.spot_major_heap r)
        (ConcreteMajor.spot_major_fp r)
        (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
        ok post_major roots_out /\
      spot_minor_collect_full_success_post r post_major)
{
  let c = ConcreteMajor.spot_c r;
  ConcreteForwarding.spot_concrete_no_oom r;
  ThreeObjects.spot_roots_len c;
  ThreeObjects.spot_slots_len c;
  assert (pure (
    SZ.v nroots == Seq.length (ThreeObjects.spot_roots c) /\
    SZ.v nslots == 1));
  ConcreteScenarios.spot_concrete_minor_collect_full_pre r;
  Preconditions.minor_collect_full_pre_elim
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    (ThreeObjects.spot_roots c)
    ConcreteScenarios.spot_fwd_array
    (ThreeObjects.spot_slots c)
    1;
  let ok = minor_collect_full gh roots nroots fwd_arr queue slots nslots;
  with d2 b2 post_major fp2 roots_out farr_out qv_out. _;
  assert (pure (post_major ==
    (CheneySpec.cheney_collect_spec
      ConcreteMinor.spot_minor2
      (ConcreteMajor.spot_major_heap r)
      (ConcreteMajor.spot_major_fp r)
      (ThreeObjects.spot_roots c)).mc_major));
  assert (pure (roots_out ==
    PromoteSpec.rewrite_roots (ThreeObjects.spot_roots c)
      (CheneySpec.cheney_promote
        ConcreteMinor.spot_minor2
        (ConcreteMajor.spot_major_heap r)
        (ConcreteMajor.spot_major_fp r)
        (ThreeObjects.spot_roots c)).fwd_map));
  assert (pure (roots_out ==
    (CheneySpec.cheney_collect_spec
      ConcreteMinor.spot_minor2
      (ConcreteMajor.spot_major_heap r)
      (ConcreteMajor.spot_major_fp r)
      (ThreeObjects.spot_roots c)).mc_roots));
  assert (pure (ok ==> MinorFwd.normal_result_reachable_subgraph_isomorphism_prop
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    (ThreeObjects.spot_roots c)
    post_major roots_out));
  assert (pure (ok ==> MinorFwd.normal_result_non_pointer_fields_preserved_prop
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    (ThreeObjects.spot_roots c)
    post_major));
  Postconditions.minor_collect_full_post_intro
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    (ThreeObjects.spot_roots c)
    ok post_major roots_out;
  spot_minor_collect_full_success_post_from_call_post r post_major;
  ok
}

#push-options "--warn_error -288"
divergent
fn call_concrete_minor_collect_full_spot
  (r: unit{ConcreteMajor.spot_major_room})
  (gh: gen_heap_t)
  requires is_gen_heap gh ConcreteMinor.spot_minor2.data ConcreteMinor.spot_minor2.bump
             (ConcreteMajor.spot_major_heap r) (ConcreteMajor.spot_major_fp r)
  returns ok: bool
  ensures exists* d2 b2 post_major fp2.
    is_gen_heap gh d2 b2 post_major fp2 **
    pure (
      U64.v b2 == 0 /\
      spot_minor_collect_full_success_post r post_major)
{
  let c = ConcreteMajor.spot_c r;
  let roots = alloc (c <: U64.t) 2sz;
  roots.(1sz) <- Layout.a_minor;
  with roots_init. assert (pts_to roots roots_init);
  ConcreteSetup.spot_roots_alloc_seq c;
  rewrite (pts_to roots roots_init) as
          (pts_to roots (ThreeObjects.spot_roots c));

  let fwd_arr = alloc 0UL CheneyImpl.queue_size_sz;
  with fwd_init. assert (pts_to fwd_arr fwd_init);
  ConcreteSetup.spot_fwd_alloc_seq ();
  rewrite (pts_to fwd_arr fwd_init) as
          (pts_to fwd_arr ConcreteScenarios.spot_fwd_array);

  let queue = alloc 0UL CheneyImpl.queue_size_sz;

  let slots = alloc ((ThreeObjects.spot_c_to_a_slot c) <: U64.t) 1sz;
  with slots_init. assert (pts_to slots slots_init);
  ConcreteSetup.spot_slots_alloc_seq c;
  rewrite (pts_to slots slots_init) as
          (pts_to slots (ThreeObjects.spot_slots c));

  let ok = call_concrete_minor_collect_full_spot_borrowed
    r gh roots 2sz fwd_arr queue slots 1sz;
  with d2 b2 post_major fp2 roots_out farr_out qv_out. _;
  assert (pure (
    U64.v b2 == 0 /\
    spot_minor_collect_full_success_post r post_major));
  free roots;
  free fwd_arr;
  free queue;
  free slots;
  ok
}
#pop-options
