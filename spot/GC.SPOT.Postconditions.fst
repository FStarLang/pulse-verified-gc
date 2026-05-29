module GC.SPOT.Postconditions

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

module SpecHeap = GC.Spec.Heap
module SpecObj = GC.Spec.Object
module SpecFields = GC.Spec.Fields
module SpecMark = GC.Spec.Mark
module SpecCorrectness = GC.Spec.Correctness
module Cheney = GC.Gen.Cheney
module CheneyBFS = GC.Gen.CheneyBFS
module MinorFwd = GC.Gen.MinorCollectForwarding
module RBridge = GC.Gen.ReachabilityBridge
module GenInv = GC.Gen.HeapInvariant
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module CG = GC.Gen.CombinedGraph
module GenImpl = GC.Gen.Impl

let minor_collect_full_post
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (ok: bool) (post_major: heap) (post_roots: seq U64.t) : prop =
  let res = Cheney.cheney_collect_spec minor major fp roots in
  post_major == res.mc_major /\
  post_roots == res.mc_roots /\
  (ok ==> MinorFwd.normal_result_reachable_subgraph_isomorphism_prop
             minor major fp roots post_major post_roots /\
           MinorFwd.normal_result_non_pointer_fields_preserved_prop
             minor major fp roots post_major)

let promoted_image
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (old img: U64.t) : prop =
  img <> 0UL /\
  (Cheney.cheney_promote minor major fp roots).fwd_map old == img

let minor_not_promoted
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (old: U64.t) : prop =
  (Cheney.cheney_promote minor major fp roots).fwd_map old == 0UL

let minor_collect_full_post_intro
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (ok: bool) (post_major: heap) (post_roots: seq U64.t)
  : Lemma
      (requires (
        let res = Cheney.cheney_collect_spec minor major fp roots in
        post_major == res.mc_major /\
        post_roots == res.mc_roots /\
        (ok ==> MinorFwd.normal_result_reachable_subgraph_isomorphism_prop
                   minor major fp roots post_major post_roots /\
                 MinorFwd.normal_result_non_pointer_fields_preserved_prop
                   minor major fp roots post_major)))
      (ensures minor_collect_full_post minor major fp roots ok post_major post_roots)
  = ()

let promoted_image_from_forwarding
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (old img: U64.t)
  : Lemma (requires (Cheney.cheney_promote minor major fp roots).fwd_map old == img /\
                    img <> 0UL)
          (ensures promoted_image minor major fp roots old img)
  = ()

let not_promoted_from_zero_forwarding
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) (old: U64.t)
  : Lemma (requires (Cheney.cheney_promote minor major fp roots).fwd_map old == 0UL)
          (ensures minor_not_promoted minor major fp roots old)
  = ()

let major_minor_field_rewritten
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (src: obj_addr) (dst: U64.t) (i: nat)
  : Lemma
      (requires
        GenInv.collection_heap_shape minor major fp /\
        RBridge.major_field_zero_no_minor minor major /\
        UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
        MinorFwd.remembered_targets_in_roots major roots slots n /\
        SpecMark.no_pointer_to_blue major /\
        RBridge.minor_no_pointer_to_blue minor major /\
        RBridge.roots_valid_nonblue roots major /\
        CheneyBFS.cheney_no_oom minor major fp roots /\
        (let cg = CG.build_combined_graph minor major in
         let combined_roots = CG.classify_roots roots in
         CG.combined_reachable cg combined_roots (CG.MajorV src) /\
         CG.combined_reachable cg combined_roots (CG.MinorV dst)) /\
        ~(SpecObj.is_no_scan src major) /\
        i < U64.v (SpecObj.wosize_of_object src major) /\
        U64.v src + i * 8 + 8 <= heap_size /\
        (U64.v src + i * 8) % 8 == 0 /\
        CG.classify_major_field minor major
          (SpecHeap.read_word major (U64.uint_to_t (U64.v src + i * 8))) ==
          Some (CG.MinorV dst) /\
        minor_wosize minor dst > 0)
      (ensures (
        let prom = Cheney.cheney_promote minor major fp roots in
        let res = Cheney.cheney_collect_spec minor major fp roots in
        promoted_image minor major fp roots dst (prom.fwd_map dst) /\
        SpecHeap.read_word res.mc_major
          (U64.uint_to_t (U64.v src + i * 8)) == prom.fwd_map dst))
  =
  MinorFwd.combined_major_minor_field_forwarded
    minor major fp roots slots n src dst i;
  promoted_image_from_forwarding minor major fp roots dst
    ((Cheney.cheney_promote minor major fp roots).fwd_map dst)

let final_major_survives_from_gen_gc_post
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots roots_out: seq U64.t) (ok: bool) (final_major: heap)
  (st: seq obj_addr) (x: obj_addr)
  : Lemma
      (requires
        ok /\
        GenImpl.gen_gc_reachable_subgraph_isomorphism_post
          minor major fp roots ok final_major roots_out st /\
        SpecCorrectness.heap_reachable
          (Cheney.cheney_collect_spec minor major fp roots).mc_major st x)
      (ensures Seq.mem x (SpecFields.objects zero_addr final_major))
  =
  assert (SpecCorrectness.major_gc_live_subgraph_isomorphism
    (Cheney.cheney_collect_spec minor major fp roots).mc_major final_major st);
  assert (Seq.mem x (SpecFields.objects zero_addr final_major))
