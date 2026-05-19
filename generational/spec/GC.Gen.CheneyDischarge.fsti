/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyDischarge — Proven Cheney BFS bridge lemmas
/// ---------------------------------------------------------------------------
///
/// Utility lemmas that bridge Cheney BFS properties into forms needed
/// by the isomorphism proof (MinorCollectIso):
///
///   - chain_blue_implies_alloc_avoids: chain_objects_blue → allocated_objects_avoid_chain
///   - cheney_fwd_targets_in_mc_major: fwd targets are valid objects in mc_major

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
open GC.Gen.Remembered
open GC.Gen.CombinedGraph
open GC.Gen.Cheney
open GC.Gen.Correctness

module AllocLemmas = GC.Spec.Allocator.Lemmas

/// ---------------------------------------------------------------------------
/// allocated_objects_avoid_chain derived from chain_objects_blue
/// ---------------------------------------------------------------------------

/// chain_objects_blue and allocated_objects_avoid_chain are definitionally
/// identical. This lemma bridges between the opaque predicate and the
/// transparent one.
val chain_blue_implies_alloc_avoids (major: heap) (fp: U64.t)
  : Lemma (requires chain_objects_blue major fp)
          (ensures allocated_objects_avoid_chain major fp)

/// ---------------------------------------------------------------------------
/// Fwd targets in mc_major
/// ---------------------------------------------------------------------------

/// All nonzero forwarding targets are valid object addresses in mc_major
/// (the post-collection major heap).
val cheney_fwd_targets_in_mc_major
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
