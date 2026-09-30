module GC.SPOT.ConcreteForwarding

module U64 = FStar.UInt64
module Seq = FStar.Seq

open FStar.Seq
open GC.Spec.Base

module Cheney = GC.Gen.Cheney
module CheneyBFS = GC.Gen.CheneyBFS
module ConcreteMajor = GC.SPOT.ConcreteMajor

val spot_concrete_no_oom
  : r:unit{ConcreteMajor.spot_major_room} ->
    Lemma (ensures
      CheneyBFS.cheney_no_oom
        GC.SPOT.ConcreteMinor.spot_minor2
        (ConcreteMajor.spot_major_heap r)
        (ConcreteMajor.spot_major_fp r)
        (GC.SPOT.ThreeObjects.spot_roots (ConcreteMajor.spot_c r)))

val spot_concrete_b_forwarding_zero
  : r:unit{ConcreteMajor.spot_major_room} ->
    Lemma (ensures
      (Cheney.cheney_promote
        GC.SPOT.ConcreteMinor.spot_minor2
        (ConcreteMajor.spot_major_heap r)
        (ConcreteMajor.spot_major_fp r)
        (GC.SPOT.ThreeObjects.spot_roots (ConcreteMajor.spot_c r))).fwd_map
        GC.SPOT.Layout.b_minor == 0UL)

val spot_concrete_a_forwarding_free_obj
  : r:unit{ConcreteMajor.spot_major_room} ->
    Lemma (ensures
      U64.v ((Cheney.cheney_promote
        GC.SPOT.ConcreteMinor.spot_minor2
        (ConcreteMajor.spot_major_heap r)
        (ConcreteMajor.spot_major_fp r)
        (GC.SPOT.ThreeObjects.spot_roots (ConcreteMajor.spot_c r))).fwd_map
        GC.SPOT.Layout.a_minor) ==
      // Right-justified: `a` lands at the TOP of the free block, not at its
      // bottom -- the block keeps its own address, as the remainder.  Stated
      // on the integers so the statement itself carries no side condition.
      U64.v (ConcreteMajor.spot_free_obj r)
        + (ConcreteMajor.spot_free_wosize r - 1) * 8)
