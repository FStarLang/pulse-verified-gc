/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyDischarge — Implementation of bridge lemmas
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyDischarge

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Spec.HeapModel
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.CombinedGraph
open GC.Gen.Cheney
open GC.Gen.Correctness

module AllocLemmas = GC.Spec.Allocator.Lemmas
module CheneyInj = GC.Gen.CheneyInjectivity
module PromUpdate = GC.Gen.PromoteUpdate

/// ---------------------------------------------------------------------------
/// allocated_objects_avoid_chain from chain_objects_blue
/// ---------------------------------------------------------------------------

/// chain_objects_blue and allocated_objects_avoid_chain are definitionally
/// identical (same quantifier body). chain_objects_blue is opaque_to_smt,
/// so we must normalize to reveal its definition.
let chain_blue_implies_alloc_avoids (major: heap) (fp: U64.t)
  : Lemma (requires chain_objects_blue major fp)
          (ensures allocated_objects_avoid_chain major fp)
  = norm_spec [delta_only [`%chain_objects_blue]] (chain_objects_blue major fp)

/// ---------------------------------------------------------------------------
/// Fwd targets in mc_major: bridges promote-phase validity to post-collect
/// ---------------------------------------------------------------------------

/// All nonzero forwarding targets are valid objects in the post-collection
/// major heap (mc_major). Combines:
///   - cheney_promote_fwd_targets_valid (targets in prom.major_final)
///   - update_major_pointers_preserves_objects (objects unchanged by update)
let cheney_fwd_targets_in_mc_major
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec minor major fp roots in
      forall (a: U64.t). prom.fwd_map a <> 0UL ==>
        (U64.v (prom.fwd_map a) >= U64.v mword /\
         U64.v (prom.fwd_map a) < heap_size /\
         U64.v (prom.fwd_map a) % U64.v mword == 0 /\
         Seq.mem ((prom.fwd_map a) <: obj_addr) (objects zero_addr res.mc_major))))
  = CheneyInj.cheney_promote_fwd_targets_valid minor major fp roots;
    let prom = cheney_promote minor major fp roots in
    cheney_promote_preserves_wfh_part1 minor major fp roots;
    PromUpdate.update_major_pointers_preserves_objects prom.major_final prom.fwd_map
