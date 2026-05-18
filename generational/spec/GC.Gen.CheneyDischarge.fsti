/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyDischarge — Partial discharge of iso_structural_preconditions
/// ---------------------------------------------------------------------------
///
/// Assembles proven Cheney BFS properties (injectivity, disjointness) to
/// eliminate 2 out of 8 conjuncts from iso_structural_preconditions.
///
/// Proven internally (no caller obligation):
///   - Fwd injectivity: cheney_promote produces injective fwd_map
///     (from CheneyInjectivity.cheney_promote_fwd_injective)
///   - Promoted disjoint from non-blue: fwd targets ≠ allocated major objects
///     (from CheneyDisjoint.cheney_promote_fwd_disjoint_nonblue)
///
/// Remaining (still required from caller):
///   - Root correspondence
///   - Fwd nonzero on live_set
///   - Field correspondence
///   - Reachability bridge
///   - Reachable major vertices valid/non-blue
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

/// ---------------------------------------------------------------------------
/// Reduced precondition: iso_structural without injectivity and disjoint
/// ---------------------------------------------------------------------------

/// The remaining 6 conjuncts of iso_structural_preconditions that are
/// NOT yet proven internally. Once field_correspondence, surjectivity,
/// and the remaining properties are proven, this predicate will shrink further.
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
  // (5) Reachability bridge
  (forall (v: U64.t).
    combined_reachable cg combined_roots (MinorV v) ==>
    Seq.mem v (live_set_of minor major roots)) /\
  // (7) Reachable major vertices valid and non-blue
  (forall (v: U64.t).
    combined_reachable cg combined_roots (MajorV v) ==>
    U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
    Seq.mem (v <: obj_addr) (objects zero_addr major) /\
    ~(is_blue (v <: obj_addr) major)) /\
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
/// Main discharge lemma
/// ---------------------------------------------------------------------------

/// Derives the full iso_structural_preconditions from:
///   - Standard GC preconditions (well_formed_heap, fl_valid, chain_objects_blue)
///   - The reduced preconditions (6 remaining conjuncts)
///
/// The injectivity and disjoint conjuncts are discharged by calling
/// CheneyInjectivity and CheneyDisjoint internally.
val discharge_structural_preconditions
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (combined_roots: seq combined_vertex)
  (major_stack: seq obj_addr)
  : Lemma
    (requires
      // Standard GC preconditions needed by Cheney theorems
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp /\
      // Reduced preconditions (the remaining 6 conjuncts)
      iso_remaining_preconditions minor major fp roots combined_roots major_stack)
    (ensures
      TopLevel.iso_structural_preconditions minor major fp roots combined_roots major_stack)
