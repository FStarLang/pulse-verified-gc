module GC.SPOT.CallMinor

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

module Preconditions = GC.SPOT.Preconditions
module Postconditions = GC.SPOT.Postconditions
module CheneyImpl = GC.Gen.Impl.Cheney
module CheneySpec = GC.Gen.Cheney
module PromoteSpec = GC.Gen.Promote
module MinorFwd = GC.Gen.MinorCollectForwarding
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module RBridge = GC.Gen.ReachabilityBridge
module GenInv = GC.Gen.HeapInvariant

module FA = GC.Gen.ForwardingArray
fn call_minor_collect_full_spot
  (gh: gen_heap_t)
  (roots: array U64.t) (nroots: SZ.t)
  (fwd_arr: array U64.t)
  (queue: larray U64.t FA.queue_size)
  (slots: array U64.t) (nslots: SZ.t)
  requires gen_phase gh 's GC.Spec.Phase.Idle ** is_gen_heap gh 'd 'b 's 'fp **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           pts_to slots 'sl **
           pure (SZ.v nroots == Seq.length 'rs /\
                 Preconditions.minor_collect_full_pre
                   ({ data = 'd; bump = 'b } <: minor_state) 's 'fp
                   'rs 'farr 'sl (SZ.v nslots))
  returns ok: bool
  ensures exists* d2 b2 s2 fp2 rs2 farr2 qv2.
    gen_phase gh s2 GC.Spec.Phase.Idle ** is_gen_heap gh d2 b2 s2 fp2 **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pts_to slots 'sl **
    pure (
      U64.v b2 == 0 /\
      Postconditions.minor_collect_full_post
        ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs ok s2 rs2)
{
  Preconditions.minor_collect_full_pre_elim
    ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs 'farr 'sl (SZ.v nslots);
  minor_collect_idle_pre ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs 'farr 'sl
    (SZ.v nslots);
  // The minor-collection entry point, idle: `gc_state` at `Idle` is the
  // stop-the-world shape, and the phase's definition of free is `free_stw`.
  GC.Gen.Incremental.phase_free_idle ();
  GC.Gen.Incremental.phase_shape_idle ({ data = 'd; bump = 'b } <: minor_state) 's 'fp;
  fold (gc_state gh 'd 'b 's 'fp GC.Spec.Phase.Idle);
  let ok = minor_collect gh roots nroots fwd_arr queue slots nslots;
  with d2 b2 s2 fp2 rs2 farr2 qv2. _;
  unfold gc_state;
  minor_collect_idle_post ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs 'farr 'sl
    (SZ.v nslots) ok d2 b2 s2 fp2 rs2;
  assert (pure (s2 ==
    (CheneySpec.cheney_collect_spec ({ data = 'd; bump = 'b } <: minor_state)
      's 'fp 'rs).mc_major));
  assert (pure (rs2 ==
    PromoteSpec.rewrite_roots 'rs
      (CheneySpec.cheney_promote Idle ({ data = 'd; bump = 'b } <: minor_state)
        's 'fp 'rs).fwd_map));
  assert (pure (rs2 ==
    (CheneySpec.cheney_collect_spec ({ data = 'd; bump = 'b } <: minor_state)
      's 'fp 'rs).mc_roots));
  assert (pure (ok ==> MinorFwd.normal_result_reachable_subgraph_isomorphism_prop Idle
    ({ data = 'd; bump = 'b } <: minor_state) 's 'fp GC.Spec.Fields.free_stw 'rs s2
    (MCFH.resolve_roots s2 rs2)));
  assert (pure (ok ==> MinorFwd.normal_result_non_pointer_fields_preserved_prop Idle
    ({ data = 'd; bump = 'b } <: minor_state) 's 'fp GC.Spec.Fields.free_stw 'rs s2));
  assert (pure (U64.v b2 == 0));
  assert (pure (ok ==> MinorFwd.normal_result_reachable_subgraph_isomorphism_prop Idle
    ({ data = 'd; bump = 'b } <: minor_state) 's 'fp GC.Spec.Fields.free_stw 'rs s2
    (MCFH.resolve_roots s2 rs2) /\
    MinorFwd.normal_result_non_pointer_fields_preserved_prop Idle
      ({ data = 'd; bump = 'b } <: minor_state) 's 'fp GC.Spec.Fields.free_stw 'rs s2));
  Postconditions.minor_collect_full_post_intro
    ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs ok s2 rs2;
  assert (pure (Postconditions.minor_collect_full_post
    ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs ok s2 rs2));
  ok
}
