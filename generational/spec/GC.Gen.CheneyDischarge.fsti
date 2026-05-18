/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyDischarge — Partial discharge of iso_structural_preconditions
/// ---------------------------------------------------------------------------
///
/// Assembles proven Cheney BFS properties (injectivity, disjointness) and
/// reachability bridge to eliminate 4 out of 8 conjuncts from
/// iso_structural_preconditions.
///
/// Proven internally (no caller obligation):
///   - Fwd injectivity: cheney_promote produces injective fwd_map
///     (from CheneyInjectivity.cheney_promote_fwd_injective)
///   - Promoted disjoint from non-blue: fwd targets ≠ allocated major objects
///     (from CheneyDisjoint.cheney_promote_fwd_disjoint_nonblue)
///   - Reachability bridge: combined-reachable MinorV → live_set
///     (from ReachabilityBridge.reachability_bridge)
///   - Reachable major valid/non-blue: MajorV reachable → in objects, non-blue
///     (from ReachabilityBridge.reachable_major_valid_nonblue)
///
/// Remaining (still required from caller):
///   - Root correspondence
///   - Fwd nonzero on live_set
///   - Field correspondence
///   - Morphism image preservation

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
module Iso = GC.Gen.CombinedGraph.Isomorphism
module TopLevel = GC.Gen.CombinedGraph.Isomorphism.TopLevel
module CheneyDisj = GC.Gen.CheneyDisjoint
module Mark = GC.Spec.Mark
module RBridge = GC.Gen.ReachabilityBridge

/// ---------------------------------------------------------------------------
/// Reduced precondition: iso_structural without injectivity and disjoint
/// ---------------------------------------------------------------------------

/// The remaining 4 conjuncts of iso_structural_preconditions that are
/// NOT yet proven internally. Conjuncts (3), (5), (6), (7) are now discharged.
let iso_remaining_preconditions
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (combined_roots: seq combined_vertex)
  (major_stack: seq obj_addr) : prop =
  let cg = build_combined_graph minor major in
  let prom = cheney_promote minor major fp roots in
  let res = cheney_collect_spec minor major fp roots in
  let g_mc = create_graph res.mc_major in
  // (1) Root correspondence
  (forall (r: obj_addr). Seq.mem r major_stack <==>
    Seq.mem (MajorV r) combined_roots \/
    (exists (m: U64.t). Seq.mem (MinorV m) combined_roots /\
      prom.fwd_map m == r)) /\
  // (2) Fwd nonzero on live_set
  (let live_set = live_set_of minor major roots in
   forall (v: U64.t). Seq.mem v live_set ==> prom.fwd_map v <> 0UL) /\
  // (4) Field correspondence
  (field_correspondence minor major res.mc_major prom.fwd_map roots) /\
  // (8) Morphism image preservation
  (forall (v: combined_vertex).
    combined_reachable cg combined_roots v ==>
    (let w = Iso.fwd_morphism prom.fwd_map v in
     U64.v w >= U64.v mword /\ U64.v w < heap_size /\ U64.v w % U64.v mword == 0 /\
     mem_graph_vertex g_mc (w <: obj_addr) /\
     (exists (r: obj_addr). Seq.mem r major_stack /\
                            mem_graph_vertex g_mc r /\
                            reachable g_mc r (w <: obj_addr))))

/// ---------------------------------------------------------------------------
/// Phase A: allocated_objects_avoid_chain derived from chain_objects_blue
/// ---------------------------------------------------------------------------

/// chain_objects_blue (conjunct 5 of gen_gc_iso preconditions) is definitionally
/// identical to allocated_objects_avoid_chain (conjunct 16). This lemma
/// eliminates (16) as a redundant precondition.
val chain_blue_implies_alloc_avoids (major: heap) (fp: U64.t)
  : Lemma (requires chain_objects_blue major fp)
          (ensures allocated_objects_avoid_chain major fp)

/// ---------------------------------------------------------------------------
/// Fwd targets in mc_major
/// ---------------------------------------------------------------------------

/// All nonzero forwarding targets are valid object addresses in mc_major
/// (the post-collection major heap). Useful for morphism image preservation.
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

/// ---------------------------------------------------------------------------
/// Main discharge lemma
/// ---------------------------------------------------------------------------

/// Derives the full iso_structural_preconditions from:
///   - Standard GC preconditions (well_formed_heap, fl_valid, chain_objects_blue)
///   - Reachability preconditions (no_pointer_to_blue, roots_valid_nonblue, etc.)
///   - The reduced preconditions (4 remaining conjuncts)
///
/// The injectivity, disjoint, reachability bridge, and major non-blue conjuncts
/// are discharged internally by calling CheneyInjectivity, CheneyDisjoint, and
/// ReachabilityBridge.
val discharge_structural_preconditions
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (combined_roots: seq combined_vertex)
  (major_stack: seq obj_addr)
  : Lemma
    (requires
      // Standard GC preconditions needed by Cheney theorems
      well_formed_heap major /\
      minor_wf minor /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp /\
      CheneyDisj.nonblue_wosize_positive major /\
      // Root classification link
      combined_roots == classify_roots roots /\
      // Reachability preconditions (for conjuncts 5 and 7)
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      RBridge.major_field_one_plus_in_remembered minor major /\
      RBridge.major_field_zero_no_minor minor major /\
      // Reduced preconditions (the remaining 4 conjuncts)
      iso_remaining_preconditions minor major fp roots combined_roots major_stack)
    (ensures
      TopLevel.iso_structural_preconditions minor major fp roots combined_roots major_stack)
