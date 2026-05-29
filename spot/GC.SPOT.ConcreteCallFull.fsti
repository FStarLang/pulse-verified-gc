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
module GenInv = GC.Gen.HeapInvariant
module SpecFields = GC.Spec.Fields
module SpecHeap = GC.Spec.Heap
module Layout = GC.SPOT.Layout
module ConcreteMinor = GC.SPOT.ConcreteMinor
module ConcreteMajor = GC.SPOT.ConcreteMajor
module ConcreteScenarios = GC.SPOT.ConcreteScenarios
module Postconditions = GC.SPOT.Postconditions
module ThreeObjects = GC.SPOT.ThreeObjects

let spot_gen_gc_stack_pre
  (r: unit{ConcreteMajor.spot_major_room})
  (st: Seq.seq obj_addr) (cap: nat) : prop =
  let result =
    CheneySpec.cheney_collect_spec
      ConcreteMinor.spot_minor2
      (ConcreteMajor.spot_major_heap r)
      (ConcreteMajor.spot_major_fp r)
      (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) in
  GenInv.major_stack_shape result.mc_major st cap /\
  GenImpl.roots_match_stack result.mc_roots st

let spot_gen_gc_success_post
  (r: unit{ConcreteMajor.spot_major_room})
  (ok: bool) (final_major: heap) : prop =
  let prom =
    CheneySpec.cheney_promote
      ConcreteMinor.spot_minor2
      (ConcreteMajor.spot_major_heap r)
      (ConcreteMajor.spot_major_fp r)
      (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) in
  ok ==>
    Seq.mem (ConcreteMajor.spot_c r)
      (SpecFields.objects zero_addr final_major) /\
    exists (a_prime: obj_addr).
      a_prime == prom.fwd_map Layout.a_minor /\
      Seq.mem a_prime (SpecFields.objects zero_addr final_major) /\
      SpecHeap.read_word final_major (ConcreteMajor.spot_c_field1 r) == a_prime

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
           is_gray_stack st 'st **
           pure (
             SZ.v nroots == 2 /\
             SZ.v nslots == 1 /\
             CheneyBFS.cheney_no_oom
               ConcreteMinor.spot_minor2
               (ConcreteMajor.spot_major_heap r)
               (ConcreteMajor.spot_major_fp r)
               (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) /\
             spot_gen_gc_stack_pre r 'st (stack_capacity st))
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
        roots_out 'st /\
      GenImpl.gen_gc_heap_shape_post
        d2 b2 result.mc_major final_major result.mc_fp 'st (stack_capacity st) /\
      GenImpl.gen_gc_reachable_subgraph_isomorphism_post
        ConcreteMinor.spot_minor2
        (ConcreteMajor.spot_major_heap r)
        (ConcreteMajor.spot_major_fp r)
        (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
        ok final_major roots_out 'st /\
      GenImpl.gen_gc_unreachable_final_blue_post
        ConcreteMinor.spot_minor2
        (ConcreteMajor.spot_major_heap r)
        (ConcreteMajor.spot_major_fp r)
        (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
        final_major 'st /\
      Postconditions.minor_not_promoted
        ConcreteMinor.spot_minor2
        (ConcreteMajor.spot_major_heap r)
        (ConcreteMajor.spot_major_fp r)
        (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
        Layout.b_minor /\
      spot_gen_gc_success_post r ok final_major)

