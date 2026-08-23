module GC.SPOT.Postconditions

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

val minor_collect_full_post
  : minor_state -> heap -> U64.t -> seq U64.t -> bool -> heap -> seq U64.t -> prop

val promoted_image
  : minor_state -> heap -> U64.t -> seq U64.t -> U64.t -> U64.t -> prop

val minor_not_promoted
  : minor_state -> heap -> U64.t -> seq U64.t -> U64.t -> prop

val minor_collect_full_post_intro
  : minor:minor_state -> major:heap -> fp:U64.t -> roots:seq U64.t ->
    ok:bool -> post_major:heap -> post_roots:seq U64.t ->
    Lemma
      (requires (
        let res = GC.Gen.Cheney.cheney_collect_spec minor major fp roots in
        post_major == res.mc_major /\
        post_roots == res.mc_roots /\
        (ok ==> GC.Gen.MinorCollectForwarding.normal_result_reachable_subgraph_isomorphism_prop
                   minor major fp roots post_major post_roots /\
                 GC.Gen.MinorCollectForwarding.normal_result_non_pointer_fields_preserved_prop
                   minor major fp roots post_major)))
      (ensures minor_collect_full_post minor major fp roots ok post_major post_roots)

val promoted_image_from_forwarding
  : minor:minor_state -> major:heap -> fp:U64.t -> roots:seq U64.t ->
    old:U64.t -> img:U64.t ->
    Lemma (requires (GC.Gen.Cheney.cheney_promote minor major fp roots).fwd_map old == img /\
                    img <> 0UL)
          (ensures promoted_image minor major fp roots old img)

val promoted_image_elim
  : minor:minor_state -> major:heap -> fp:U64.t -> roots:seq U64.t ->
    old:U64.t -> img:U64.t ->
    Lemma (requires promoted_image minor major fp roots old img)
          (ensures img <> 0UL /\
                   (GC.Gen.Cheney.cheney_promote minor major fp roots).fwd_map old == img)

val not_promoted_from_zero_forwarding
  : minor:minor_state -> major:heap -> fp:U64.t -> roots:seq U64.t -> old:U64.t ->
    Lemma (requires (GC.Gen.Cheney.cheney_promote minor major fp roots).fwd_map old == 0UL)
          (ensures minor_not_promoted minor major fp roots old)

val major_minor_field_rewritten
  : minor:minor_state -> major:heap -> fp:U64.t ->
    roots:seq U64.t -> slots:seq U64.t -> n:nat ->
    src:obj_addr -> dst:U64.t -> i:nat ->
    Lemma
      (requires
        GC.Gen.HeapInvariant.collection_heap_shape minor major fp /\
        GC.Gen.ReachabilityBridge.major_field_zero_covered minor major roots /\
        GC.Gen.Impl.UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
        GC.Gen.MinorCollectForwarding.remembered_targets_in_roots major roots slots n /\
        GC.Spec.Mark.no_pointer_to_blue major /\
        GC.Gen.ReachabilityBridge.minor_no_pointer_to_blue minor major /\
        GC.Gen.ReachabilityBridge.roots_valid_nonblue roots major /\
        GC.Gen.CheneyBFS.cheney_no_oom minor major fp roots /\
        (let cg = GC.Gen.CombinedGraph.build_combined_graph minor major in
         let combined_roots = GC.Gen.CombinedGraph.classify_roots roots in
         GC.Gen.CombinedGraph.combined_reachable cg combined_roots
           (GC.Gen.CombinedGraph.MajorV src) /\
         GC.Gen.CombinedGraph.combined_reachable cg combined_roots
           (GC.Gen.CombinedGraph.MinorV dst)) /\
        ~(GC.Spec.Object.is_no_scan src major) /\
        i < U64.v (GC.Spec.Object.wosize_of_object src major) /\
        U64.v src + i * 8 + 8 <= heap_size /\
        (U64.v src + i * 8) % 8 == 0 /\
        GC.Gen.CombinedGraph.classify_major_field minor major
          (GC.Spec.Heap.read_word major (U64.uint_to_t (U64.v src + i * 8))) ==
          Some (GC.Gen.CombinedGraph.MinorV dst) /\
        GC.Gen.MinorHeap.minor_wosize minor dst > 0)
      (ensures (
        let prom = GC.Gen.Cheney.cheney_promote minor major fp roots in
        let res = GC.Gen.Cheney.cheney_collect_spec minor major fp roots in
        promoted_image minor major fp roots dst (prom.fwd_map dst) /\
        GC.Spec.Heap.read_word res.mc_major
          (U64.uint_to_t (U64.v src + i * 8)) == prom.fwd_map dst))

val final_major_survives_from_gen_gc_post
  : minor:minor_state -> major:heap -> fp:U64.t ->
    roots:seq U64.t -> roots_out:seq U64.t ->
    ok:bool -> final_major:heap -> st:seq obj_addr -> cap:nat -> x:obj_addr ->
    Lemma
      (requires
        ok /\
        GC.Gen.Impl.gen_gc_reachable_subgraph_isomorphism_post
          minor major fp roots ok final_major roots_out st cap /\
        GC.Spec.Correctness.heap_reachable
          (GC.Gen.Impl.gen_gc_prepared_major minor major fp roots st cap)
          (GC.Gen.Impl.gen_gc_prepared_roots minor major fp roots st cap)
          x)
      (ensures Seq.mem x (GC.Spec.Fields.objects zero_addr final_major))
