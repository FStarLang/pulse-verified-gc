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
module SpecFields = GC.Spec.Fields
module SpecHeap = GC.Spec.Heap
module Layout = GC.SPOT.Layout
module ConcreteMinor = GC.SPOT.ConcreteMinor
module ConcreteMajor = GC.SPOT.ConcreteMajor
module ConcreteScenarios = GC.SPOT.ConcreteScenarios
module Postconditions = GC.SPOT.Postconditions
module ThreeObjects = GC.SPOT.ThreeObjects

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
  requires is_gen_heap gh ConcreteMinor.spot_minor2.data ConcreteMinor.spot_minor2.bump
            (ConcreteMajor.spot_major_heap r) (ConcreteMajor.spot_major_fp r)
  returns res: (U64.t & bool)
  ensures exists* d2 b2 final_major.
    is_gen_heap gh d2 b2 final_major (fst res) **
    pure (
      let ok = snd res in
      GenImpl.gen_gc_heap_shape_post d2 b2 final_major /\
      Postconditions.minor_not_promoted
        ConcreteMinor.spot_minor2
        (ConcreteMajor.spot_major_heap r)
        (ConcreteMajor.spot_major_fp r)
        (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
        Layout.b_minor /\
      spot_gen_gc_success_post r ok final_major)
