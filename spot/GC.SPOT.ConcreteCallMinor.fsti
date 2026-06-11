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
module Layout = GC.SPOT.Layout
module ConcreteMinor = GC.SPOT.ConcreteMinor
module ConcreteMajor = GC.SPOT.ConcreteMajor
module ConcreteScenarios = GC.SPOT.ConcreteScenarios
module Postconditions = GC.SPOT.Postconditions
module ThreeObjects = GC.SPOT.ThreeObjects
module SpecHeap = GC.Spec.Heap

let spot_minor_collect_full_success_post
  (r: unit{ConcreteMajor.spot_major_room})
  (post_major: heap) : prop =
  let roots = ThreeObjects.spot_roots (ConcreteMajor.spot_c r) in
  let prom =
    CheneySpec.cheney_promote
      ConcreteMinor.spot_minor2
      (ConcreteMajor.spot_major_heap r)
      (ConcreteMajor.spot_major_fp r)
      roots in
  let result =
    CheneySpec.cheney_collect_spec
      ConcreteMinor.spot_minor2
      (ConcreteMajor.spot_major_heap r)
      (ConcreteMajor.spot_major_fp r)
      roots in
  post_major == result.mc_major /\
  Postconditions.promoted_image
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    roots
    Layout.a_minor
    (prom.fwd_map Layout.a_minor) /\
  SpecHeap.read_word post_major (ConcreteMajor.spot_c_field1 r) ==
    prom.fwd_map Layout.a_minor /\
  Postconditions.minor_not_promoted
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    roots
    Layout.b_minor

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
