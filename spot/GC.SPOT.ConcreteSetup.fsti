module GC.SPOT.ConcreteSetup

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base

module CheneyImpl = GC.Gen.Impl.Cheney
module Layout = GC.SPOT.Layout
module ConcreteScenarios = GC.SPOT.ConcreteScenarios
module ThreeObjects = GC.SPOT.ThreeObjects

val spot_roots_alloc_seq
  : c:obj_addr ->
    Lemma (Seq.upd (Seq.create 2 (c <: U64.t)) 1 Layout.a_minor ==
           ThreeObjects.spot_roots c)

val spot_slots_alloc_seq
  : c:obj_addr{U64.v c + Layout.c_to_a_field_index * 8 + 8 <= heap_size} ->
    Lemma (Seq.create 1 ((ThreeObjects.spot_c_to_a_slot c) <: U64.t) ==
           ThreeObjects.spot_slots c)

val spot_fwd_alloc_seq
  : unit ->
    Lemma (Seq.create (FStar.SizeT.v CheneyImpl.queue_size_sz) 0UL ==
           ConcreteScenarios.spot_fwd_array)
