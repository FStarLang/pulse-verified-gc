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
  = ()

let minor_collect_full_post_elim
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (ok: bool) (post_major: heap) (post_roots: seq U64.t)
  = ()

let promoted_image_from_forwarding
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (old img: U64.t)
  = ()

let promoted_image_elim
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (old img: U64.t)
  = ()

let not_promoted_from_zero_forwarding
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) (old: U64.t)
  = ()

let major_minor_field_rewritten
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (src: obj_addr) (dst: U64.t) (i: nat)
  =
  MinorFwd.combined_major_minor_field_forwarded
    minor major fp roots slots n src dst i;
  promoted_image_from_forwarding minor major fp roots dst
    ((Cheney.cheney_promote minor major fp roots).fwd_map dst)

let final_major_survives_from_gen_gc_post
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots roots_out: seq U64.t) (ok: bool) (final_major: heap)
  (st: seq obj_addr) (cap: nat) (x: obj_addr)
  =
  assert (SpecCorrectness.major_gc_live_subgraph_isomorphism
    (GenImpl.gen_gc_prepared_major minor major fp roots st cap)
    final_major
    (GenImpl.gen_gc_prepared_roots minor major fp roots st cap));
  assert (Seq.mem x (SpecFields.objects zero_addr final_major))
