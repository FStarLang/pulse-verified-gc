module GC.SPOT.ThreeObjects

open FStar.Seq
module Seq = FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

val spot_roots : c:obj_addr -> Tot (seq U64.t)

val spot_c_to_a_slot
  : c:obj_addr{U64.v c + GC.SPOT.Layout.c_to_a_field_index * 8 + 8 <= heap_size} ->
    Tot hp_addr

val spot_c_to_a_slot_spec
  : c:obj_addr{U64.v c + GC.SPOT.Layout.c_to_a_field_index * 8 + 8 <= heap_size} ->
    Lemma (ensures
      U64.v (spot_c_to_a_slot c) ==
        U64.v c + GC.SPOT.Layout.c_to_a_field_index * 8 /\
      U64.v (spot_c_to_a_slot c) == U64.v c + 8)

val spot_slots
  : c:obj_addr{U64.v c + GC.SPOT.Layout.c_to_a_field_index * 8 + 8 <= heap_size} ->
    Tot (seq U64.t)

val spot_slots_len
  : c:obj_addr{U64.v c + GC.SPOT.Layout.c_to_a_field_index * 8 + 8 <= heap_size} ->
    Lemma (ensures Seq.length (spot_slots c) == 1)

val spot_slots_index
  : c:obj_addr{U64.v c + GC.SPOT.Layout.c_to_a_field_index * 8 + 8 <= heap_size} ->
    i:nat{i < Seq.length (spot_slots c)} ->
    Lemma (requires i < 1)
          (ensures Seq.index (spot_slots c) i == spot_c_to_a_slot c)

val spot_roots_mem_c
  : c:obj_addr -> Lemma (Seq.mem (c <: U64.t) (spot_roots c))

val spot_roots_mem_a
  : c:obj_addr -> Lemma (Seq.mem GC.SPOT.Layout.a_minor (spot_roots c))

val spot_roots_len
  : c:obj_addr -> Lemma (Seq.length (spot_roots c) == 2)

val spot_roots_index_c
  : c:obj_addr -> Lemma (requires Seq.length (spot_roots c) > 0)
                          (ensures Seq.index (spot_roots c) 0 == (c <: U64.t))

val spot_roots_index_a
  : c:obj_addr -> Lemma (requires Seq.length (spot_roots c) > 1)
                          (ensures Seq.index (spot_roots c) 1 == GC.SPOT.Layout.a_minor)

val spot_roots_cases
  : c:obj_addr -> root:U64.t ->
    Lemma (requires Seq.mem root (spot_roots c))
          (ensures root == (c <: U64.t) \/ root == GC.SPOT.Layout.a_minor)

val spot_slots_singleton_distinct
  : c:obj_addr{U64.v c + GC.SPOT.Layout.c_to_a_field_index * 8 + 8 <= heap_size} ->
    Lemma (GC.Gen.Impl.UpdatePtrs.slots_pairwise_distinct (spot_slots c) 1)

val spot_minor_scenario_pre
  : minor:minor_state -> major:heap -> fp:U64.t ->
    c:obj_addr{U64.v c + GC.SPOT.Layout.c_to_a_field_index * 8 + 8 <= heap_size} ->
    farr:seq U64.t -> Tot prop

val spot_minor_scenario_pre_intro_from_c_to_a
  : minor:minor_state -> major:heap -> fp:U64.t ->
    c:obj_addr{U64.v c + GC.SPOT.Layout.c_to_a_field_index * 8 + 8 <= heap_size} ->
    farr:seq U64.t ->
    Lemma
      (requires
        GC.SPOT.Preconditions.minor_collect_full_pre
          minor major fp (spot_roots c) farr (spot_slots c) 1 /\
        ~(GC.Gen.Promote.is_minor_pointer (c <: U64.t)) /\
        Seq.mem c (GC.Spec.Fields.objects zero_addr major) /\
        ~(GC.Spec.Object.is_no_scan c major) /\
        U64.v (GC.Spec.Object.wosize_of_object c major) >
          GC.SPOT.Layout.c_to_a_field_index /\
        U64.v c + GC.SPOT.Layout.c_to_a_field_index * 8 + 8 <= heap_size /\
        GC.Spec.Heap.read_word major (spot_c_to_a_slot c) ==
          GC.SPOT.Layout.a_minor /\
        Seq.mem GC.SPOT.Layout.a_minor (minor_objects minor) /\
        Seq.mem GC.SPOT.Layout.b_minor (minor_objects minor) /\
        minor_wosize minor GC.SPOT.Layout.a_minor > 0 /\
        minor_wosize minor GC.SPOT.Layout.b_minor > 0 /\
        GC.Gen.CheneyBFS.cheney_no_oom minor major fp (spot_roots c))
      (ensures spot_minor_scenario_pre minor major fp c farr)

val spot_full_scenario_pre
  : minor:minor_state -> major:heap -> fp:U64.t ->
    c:obj_addr{U64.v c + GC.SPOT.Layout.c_to_a_field_index * 8 + 8 <= heap_size} ->
    farr:seq U64.t -> st:seq obj_addr -> cap:nat -> Tot prop

val spot_c_reachable_root
  : minor:minor_state -> major:heap -> fp:U64.t ->
    c:obj_addr{U64.v c + GC.SPOT.Layout.c_to_a_field_index * 8 + 8 <= heap_size} ->
    farr:seq U64.t ->
    Lemma
      (requires spot_minor_scenario_pre minor major fp c farr)
      (ensures (
        let cg = GC.Gen.CombinedGraph.build_combined_graph minor major in
        GC.Gen.CombinedGraph.combined_reachable
          cg (GC.Gen.CombinedGraph.classify_roots minor (spot_roots c))
          (GC.Gen.CombinedGraph.MajorV c)))

val spot_a_reachable_root
  : minor:minor_state -> major:heap -> fp:U64.t ->
    c:obj_addr{U64.v c + GC.SPOT.Layout.c_to_a_field_index * 8 + 8 <= heap_size} ->
    farr:seq U64.t ->
    Lemma
      (requires spot_minor_scenario_pre minor major fp c farr)
      (ensures (
        let cg = GC.Gen.CombinedGraph.build_combined_graph minor major in
        GC.Gen.CombinedGraph.combined_reachable
          cg (GC.Gen.CombinedGraph.classify_roots minor (spot_roots c))
          (GC.Gen.CombinedGraph.MinorV GC.SPOT.Layout.a_minor)))

val spot_a_promoted
  : minor:minor_state -> major:heap -> fp:U64.t ->
    c:obj_addr{U64.v c + GC.SPOT.Layout.c_to_a_field_index * 8 + 8 <= heap_size} ->
    farr:seq U64.t ->
    Lemma
      (requires spot_minor_scenario_pre minor major fp c farr)
      (ensures (
        let prom = GC.Gen.Cheney.cheney_promote minor major fp (spot_roots c) in
        GC.SPOT.Postconditions.promoted_image
          minor major fp (spot_roots c) GC.SPOT.Layout.a_minor
          (prom.fwd_map GC.SPOT.Layout.a_minor)))

val spot_c_field_rewritten_to_a_prime
  : minor:minor_state -> major:heap -> fp:U64.t ->
    c:obj_addr{U64.v c + GC.SPOT.Layout.c_to_a_field_index * 8 + 8 <= heap_size} ->
    farr:seq U64.t ->
    Lemma
      (requires spot_minor_scenario_pre minor major fp c farr)
      (ensures (
        let prom = GC.Gen.Cheney.cheney_promote minor major fp (spot_roots c) in
        let res = GC.Gen.Cheney.cheney_collect_spec minor major fp (spot_roots c) in
        GC.SPOT.Postconditions.promoted_image
          minor major fp (spot_roots c) GC.SPOT.Layout.a_minor
          (prom.fwd_map GC.SPOT.Layout.a_minor) /\
        GC.Spec.Heap.read_word res.mc_major (spot_c_to_a_slot c) ==
          prom.fwd_map GC.SPOT.Layout.a_minor))

val spot_b_not_promoted_from_forwarding_zero
  : minor:minor_state -> major:heap -> fp:U64.t -> c:obj_addr ->
    Lemma
      (requires
        (GC.Gen.Cheney.cheney_promote minor major fp (spot_roots c)).fwd_map
          GC.SPOT.Layout.b_minor == 0UL)
      (ensures
        GC.SPOT.Postconditions.minor_not_promoted
          minor major fp (spot_roots c) GC.SPOT.Layout.b_minor)

val spot_final_survives_from_gen_gc_post
  : minor:minor_state -> major:heap -> fp:U64.t ->
    c:obj_addr{U64.v c + GC.SPOT.Layout.c_to_a_field_index * 8 + 8 <= heap_size} ->
    roots_out:seq U64.t -> ok:bool -> final_major:heap -> st:seq obj_addr ->
    cap:nat -> x:obj_addr ->
    Lemma
      (requires
        ok /\
        GC.Gen.Impl.gen_gc_reachable_subgraph_isomorphism_post
          minor major fp (spot_roots c) ok final_major roots_out st cap /\
        GC.Spec.Correctness.heap_reachable
          (GC.Gen.Impl.gen_gc_prepared_major minor major fp (spot_roots c) st cap)
          (GC.Gen.Impl.gen_gc_prepared_roots minor major fp (spot_roots c) st cap)
          x)
      (ensures Seq.mem x (GC.Spec.Fields.objects zero_addr final_major))
