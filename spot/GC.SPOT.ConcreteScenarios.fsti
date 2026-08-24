module GC.SPOT.ConcreteScenarios

module U64 = FStar.UInt64
module Seq = FStar.Seq

open FStar.Seq
open GC.Spec.Base
open GC.Gen.Base

module Cheney = GC.Gen.Cheney
module GenImpl = GC.Gen.Impl
module GenInv = GC.Gen.HeapInvariant
module MinorFwd = GC.Gen.MinorCollectForwarding
module Preconditions = GC.SPOT.Preconditions
module ThreeObjects = GC.SPOT.ThreeObjects
module ConcreteMajor = GC.SPOT.ConcreteMajor
module ConcreteMinor = GC.SPOT.ConcreteMinor
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs

val spot_fwd_array : seq U64.t

val spot_fwd_array_zero : unit ->
  Lemma (ensures Preconditions.zero_forwarding_array spot_fwd_array)

val spot_c_slot_is_field1
  : r:unit{ConcreteMajor.spot_major_room} ->
    Lemma (ensures
      ThreeObjects.spot_c_to_a_slot (ConcreteMajor.spot_c r) ==
      ConcreteMajor.spot_c_field1 r)

/// The concrete scenario's pre-minor shape and root validity, which the
/// `gen_gc` entry contract is stated against.
val spot_collection_heap_shape
  : r:unit{ConcreteMajor.spot_major_room} ->
    Lemma (GenInv.collection_heap_shape
             ConcreteMinor.spot_minor2
             (ConcreteMajor.spot_major_heap r)
             (ConcreteMajor.spot_major_fp r))

val spot_roots_valid_for_minor_collection
  : r:unit{ConcreteMajor.spot_major_room} ->
    Lemma (MinorFwd.roots_valid_for_minor_collection
             ConcreteMinor.spot_minor2
             (ConcreteMajor.spot_major_heap r)
             (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)))

val spot_concrete_minor_collect_full_pre
  : r:unit{ConcreteMajor.spot_major_room} ->
    Lemma (ensures
      Preconditions.minor_collect_full_pre
        ConcreteMinor.spot_minor2
        (ConcreteMajor.spot_major_heap r)
        (ConcreteMajor.spot_major_fp r)
        (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
        spot_fwd_array
        (ThreeObjects.spot_slots (ConcreteMajor.spot_c r))
        1)

val spot_concrete_minor_scenario_pre_from_no_oom
  : r:unit{ConcreteMajor.spot_major_room} ->
    Lemma
      (ensures
        ThreeObjects.spot_minor_scenario_pre
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ConcreteMajor.spot_c r)
          spot_fwd_array)

val spot_concrete_gen_gc_pre_from_stack
  : r:unit{ConcreteMajor.spot_major_room} ->
    st:seq obj_addr -> cap:nat ->
    Lemma
      (requires
        Seq.length st <= cap /\
        GenImpl.gen_gc_major_precondition
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
          st cap)
      (ensures
        Preconditions.gen_gc_pre
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
          spot_fwd_array
          (ThreeObjects.spot_slots (ConcreteMajor.spot_c r))
          1 st cap)

val spot_concrete_gen_gc_pre_empty_stack
  : r:unit{ConcreteMajor.spot_major_room} ->
    cap:nat{cap >= 2} ->
    Lemma
      (ensures
        Preconditions.gen_gc_pre
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
          spot_fwd_array
          (ThreeObjects.spot_slots (ConcreteMajor.spot_c r))
          1 Seq.empty cap)

val spot_concrete_a_promoted_from_no_oom
  : r:unit{ConcreteMajor.spot_major_room} ->
    Lemma
      (ensures (
        let prom =
          Cheney.cheney_promote
            ConcreteMinor.spot_minor2
            (ConcreteMajor.spot_major_heap r)
            (ConcreteMajor.spot_major_fp r)
            (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) in
        GC.SPOT.Postconditions.promoted_image
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
          GC.SPOT.Layout.a_minor
          (prom.fwd_map GC.SPOT.Layout.a_minor)))

val spot_concrete_c_field_rewritten_from_no_oom
  : r:unit{ConcreteMajor.spot_major_room} ->
    Lemma
      (ensures (
        let prom =
          Cheney.cheney_promote
            ConcreteMinor.spot_minor2
            (ConcreteMajor.spot_major_heap r)
            (ConcreteMajor.spot_major_fp r)
            (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) in
        let res =
          Cheney.cheney_collect_spec
            ConcreteMinor.spot_minor2
            (ConcreteMajor.spot_major_heap r)
            (ConcreteMajor.spot_major_fp r)
            (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) in
        GC.SPOT.Postconditions.promoted_image
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
          GC.SPOT.Layout.a_minor
          (prom.fwd_map GC.SPOT.Layout.a_minor) /\
        GC.Spec.Heap.read_word res.mc_major (ConcreteMajor.spot_c_field1 r) ==
          prom.fwd_map GC.SPOT.Layout.a_minor))

val spot_concrete_b_not_promoted
  : r:unit{ConcreteMajor.spot_major_room} ->
    Lemma (ensures
      GC.SPOT.Postconditions.minor_not_promoted
        ConcreteMinor.spot_minor2
        (ConcreteMajor.spot_major_heap r)
        (ConcreteMajor.spot_major_fp r)
        (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
        GC.SPOT.Layout.b_minor)
