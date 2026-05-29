module GC.SPOT.ConcreteForwarding

module U64 = FStar.UInt64
module Seq = FStar.Seq

open FStar.Seq
open GC.Spec.Base

module Cheney = GC.Gen.Cheney
module ConcreteMajor = GC.SPOT.ConcreteMajor

val spot_concrete_b_forwarding_zero
  : r:unit{ConcreteMajor.spot_major_room} ->
    Lemma (ensures
      (Cheney.cheney_promote
        GC.SPOT.ConcreteMinor.spot_minor2
        (ConcreteMajor.spot_major_heap r)
        (ConcreteMajor.spot_major_fp r)
        (GC.SPOT.ThreeObjects.spot_roots (ConcreteMajor.spot_c r))).fwd_map
        GC.SPOT.Layout.b_minor == 0UL)
