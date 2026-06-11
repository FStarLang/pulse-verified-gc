module GC.SPOT.ConcreteFull

module U64 = FStar.UInt64
module Seq = FStar.Seq

open FStar.Seq
open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

module Cheney = GC.Gen.Cheney
module GenImpl = GC.Gen.Impl
module ConcreteMajor = GC.SPOT.ConcreteMajor
module ConcreteMinor = GC.SPOT.ConcreteMinor
module ThreeObjects = GC.SPOT.ThreeObjects

val spot_concrete_c_final_survives
  : r:unit{ConcreteMajor.spot_major_room} ->
    d2:minor_heap -> b2:U64.t ->
    roots_out:seq U64.t -> ok:bool -> final_major:heap ->
    st:seq obj_addr -> cap:nat ->
    Lemma
      (requires (
        let result =
          Cheney.cheney_collect_spec
            ConcreteMinor.spot_minor2
            (ConcreteMajor.spot_major_heap r)
            (ConcreteMajor.spot_major_fp r)
            (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) in
        ok /\
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
      (ensures Seq.mem (ConcreteMajor.spot_c r)
        (GC.Spec.Fields.objects zero_addr final_major))

val spot_concrete_a_prime_final_survives
  : r:unit{ConcreteMajor.spot_major_room} ->
    d2:minor_heap -> b2:U64.t ->
    roots_out:seq U64.t -> ok:bool -> final_major:heap ->
    st:seq obj_addr -> cap:nat ->
    Lemma
      (requires (
        let result =
          Cheney.cheney_collect_spec
            ConcreteMinor.spot_minor2
            (ConcreteMajor.spot_major_heap r)
            (ConcreteMajor.spot_major_fp r)
            (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) in
        ok /\
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
      (ensures (
        let prom =
          Cheney.cheney_promote
            ConcreteMinor.spot_minor2
            (ConcreteMajor.spot_major_heap r)
            (ConcreteMajor.spot_major_fp r)
            (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) in
        exists (a_prime:obj_addr).
          a_prime == prom.fwd_map GC.SPOT.Layout.a_minor /\
          Seq.mem a_prime (GC.Spec.Fields.objects zero_addr final_major))
      )

val spot_concrete_c_field_final_points_to_a_prime
  : r:unit{ConcreteMajor.spot_major_room} ->
    d2:minor_heap -> b2:U64.t ->
    roots_out:seq U64.t -> ok:bool -> final_major:heap ->
    st:seq obj_addr -> cap:nat ->
    Lemma
      (requires (
        let result =
          Cheney.cheney_collect_spec
            ConcreteMinor.spot_minor2
            (ConcreteMajor.spot_major_heap r)
            (ConcreteMajor.spot_major_fp r)
            (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) in
        ok /\
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
      (ensures (
        let prom =
          Cheney.cheney_promote
            ConcreteMinor.spot_minor2
            (ConcreteMajor.spot_major_heap r)
            (ConcreteMajor.spot_major_fp r)
            (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) in
        Seq.mem (ConcreteMajor.spot_c r)
          (GC.Spec.Fields.objects zero_addr final_major) /\
        exists (a_prime:obj_addr).
          a_prime == prom.fwd_map GC.SPOT.Layout.a_minor /\
          Seq.mem a_prime (GC.Spec.Fields.objects zero_addr final_major) /\
          GC.Spec.Heap.read_word final_major (ConcreteMajor.spot_c_field1 r) ==
            a_prime))
