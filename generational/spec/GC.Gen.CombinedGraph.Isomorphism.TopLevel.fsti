/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph.Isomorphism.TopLevel
/// ---------------------------------------------------------------------------
///
/// States the isomorphism theorem at the same level as GC.Gen.Impl.fsti,
/// using cheney_collect_spec (matching the Pulse implementation's postcondition).
///
/// This module provides:
///   1. A predicate `isomorphism_postcondition` that can be added to gen_gc's ensures
///   2. A lemma `gen_gc_isomorphism` that derives it from gen_gc's existing
///      postcondition plus structural/bridge assumptions
///
/// The bridge assumptions are stated at the mc_major level (easier to prove)
/// and composed with MarkSweepFrame internally via the Discharge module.

module GC.Gen.CombinedGraph.Isomorphism.TopLevel

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

module HeapGraph = GC.Spec.HeapGraph
module AllocLemmas = GC.Spec.Allocator.Lemmas
module Mark = GC.Spec.Mark
module Sweep = GC.Spec.Sweep
module DFS = GC.Spec.DFS
module Iso = GC.Gen.CombinedGraph.Isomorphism
module Discharge = GC.Gen.CombinedGraph.Isomorphism.Discharge


/// ---------------------------------------------------------------------------
/// The isomorphism postcondition (can be conjoined to gen_gc's ensures)
/// ---------------------------------------------------------------------------

/// States that the reachable subgraph of the pre-GC combined graph is
/// isomorphic to the reachable subgraph of the post-GC major graph.
///
/// The isomorphism is witnessed by fwd_morphism:
///   MinorV v ↦ fwd(v)   (promoted copy in major heap)
///   MajorV v ↦ v        (identity on major objects)
let isomorphism_postcondition
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (combined_roots: seq combined_vertex)
  (major_stack: seq obj_addr) (major_fp: U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  let fwd = prom.fwd_map in
  let res = cheney_collect_spec minor major fp roots in
  let h_final = fst (Sweep.sweep (Mark.mark res.mc_major major_stack) major_fp) in
  // All reachable minor vertices were successfully forwarded
  Iso.reachable_implies_forwarded
    (build_combined_graph minor major)
    combined_roots fwd /\
  // The reachable subgraphs are isomorphic
  Iso.reachable_subgraph_isomorphism minor major fwd
    combined_roots h_final major_stack


/// ---------------------------------------------------------------------------
/// Preconditions for the isomorphism (on top of gen_gc's preconditions)
/// ---------------------------------------------------------------------------

/// Structural connection between the combined graph and the post-minor heap.
/// These are semantic properties of the forwarding map and combined graph
/// that must be established externally (from Cheney BFS correctness).
let iso_structural_preconditions
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (combined_roots: seq combined_vertex)
  (major_stack: seq obj_addr) : prop =
  let cg = build_combined_graph minor major in
  let prom = cheney_promote minor major fp roots in
  let res = cheney_collect_spec minor major fp roots in
  let g_mc = create_graph res.mc_major in
  // Root correspondence: major_stack roots correspond to combined_roots
  (forall (r: obj_addr). Seq.mem r major_stack <==>
    Seq.mem (MajorV r) combined_roots \/
    (exists (m: U64.t). Seq.mem (MinorV m) combined_roots /\
      prom.fwd_map m == r)) /\
  // Fwd injectivity
  (let live_set = live_set_of minor major roots in
   forall (i j: nat). i < Seq.length live_set /\ j < Seq.length live_set /\ i <> j ==>
     (let oi = Seq.index live_set i in
      let oj = Seq.index live_set j in
      prom.fwd_map oi <> 0UL /\ prom.fwd_map oj <> 0UL ==>
      prom.fwd_map oi <> prom.fwd_map oj)) /\
  // Field correspondence
  (field_correspondence minor major res.mc_major prom.fwd_map roots) /\
  // Reachability bridge: combined-reachable minor → live set
  (forall (v: U64.t).
    combined_reachable cg combined_roots (MinorV v) ==>
    Seq.mem v (live_set_of minor major roots)) /\
  // Promoted disjoint from non-blue major
  (let live_set = live_set_of minor major roots in
   forall (v: U64.t) (obj: obj_addr).
     Seq.mem v live_set /\ prom.fwd_map v <> 0UL /\
     Seq.mem obj (objects zero_addr major) /\ ~(is_blue obj major) ==>
     prom.fwd_map v <> obj) /\
  // Reachable major vertices valid and non-blue
  (forall (v: U64.t).
    combined_reachable cg combined_roots (MajorV v) ==>
    U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
    Seq.mem (v <: obj_addr) (objects zero_addr major) /\
    ~(is_blue (v <: obj_addr) major)) /\
  // Morphism image preservation
  (forall (v: combined_vertex).
    combined_reachable cg combined_roots v ==>
    (let w = Iso.fwd_morphism prom.fwd_map v in
     U64.v w >= U64.v mword /\ U64.v w < heap_size /\ U64.v w % U64.v mword == 0 /\
     mem_graph_vertex g_mc (w <: obj_addr) /\
     (exists (r: obj_addr). Seq.mem r major_stack /\
                            mem_graph_vertex g_mc r /\
                            reachable g_mc r (w <: obj_addr))))

/// Edge bridge forward: combined edge → mc_major edge
let iso_edge_bridge_forward
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (combined_roots: seq combined_vertex)
  (major_stack: seq obj_addr) : prop =
  let cg = build_combined_graph minor major in
  let prom = cheney_promote minor major fp roots in
  let res = cheney_collect_spec minor major fp roots in
  let g_mc = create_graph res.mc_major in
  forall (u v: combined_vertex).
    combined_reachable cg combined_roots u /\
    combined_reachable cg combined_roots v /\
    mem_ce (u, v) cg ==>
    (let fu = Iso.fwd_morphism prom.fwd_map u in
     let fv = Iso.fwd_morphism prom.fwd_map v in
     U64.v fu >= U64.v mword /\ U64.v fu < heap_size /\ U64.v fu % U64.v mword == 0 /\
     U64.v fv >= U64.v mword /\ U64.v fv < heap_size /\ U64.v fv % U64.v mword == 0 /\
     Seq.mem ((fu <: hp_addr), (fv <: hp_addr)) g_mc.edges)

/// Surjectivity at mc_major level: mc-reachable → has combined pre-image
let iso_surjectivity
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (combined_roots: seq combined_vertex)
  (major_stack: seq obj_addr) : prop =
  let cg = build_combined_graph minor major in
  let prom = cheney_promote minor major fp roots in
  let res = cheney_collect_spec minor major fp roots in
  let g_mc = create_graph res.mc_major in
  let mc_roots_v = HeapGraph.coerce_to_vertex_list major_stack in
  graph_wf g_mc /\ is_vertex_set mc_roots_v /\
  subset_vertices mc_roots_v g_mc.vertices /\
  (forall (w: obj_addr).
    mem_graph_vertex g_mc w /\
    Seq.mem w (DFS.reachable_set g_mc mc_roots_v) ==>
    (exists (v: combined_vertex).
      combined_reachable cg combined_roots v /\
      Iso.fwd_morphism prom.fwd_map v == (w <: U64.t)))

/// Edge backward at mc_major: mc edge between images → combined edge
let iso_edge_backward
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (combined_roots: seq combined_vertex) : prop =
  let cg = build_combined_graph minor major in
  let prom = cheney_promote minor major fp roots in
  let res = cheney_collect_spec minor major fp roots in
  let g_mc = create_graph res.mc_major in
  forall (u v: combined_vertex).
    combined_reachable cg combined_roots u /\
    combined_reachable cg combined_roots v /\
    (let fu = Iso.fwd_morphism prom.fwd_map u in
     let fv = Iso.fwd_morphism prom.fwd_map v in
     U64.v fu < heap_size /\ U64.v fu % U64.v mword == 0 /\
     U64.v fv < heap_size /\ U64.v fv % U64.v mword == 0 /\
     Seq.mem ((fu <: hp_addr), (fv <: hp_addr)) g_mc.edges) ==>
    mem_ce (u, v) cg


/// ---------------------------------------------------------------------------
/// Main lemma: derive isomorphism from gen_gc postcondition + assumptions
/// ---------------------------------------------------------------------------

/// Given:
///   - The standard preconditions of gen_gc (minor well-formedness, allocator,
///     major GC preconditions on post-minor heap)
///   - Structural preconditions connecting the combined graph to the forwarding map
///   - The 3 bridge assumptions (edge forward, surjectivity, edge backward)
///
/// Derives: the full reachable-subgraph isomorphism.
///
/// This is the theorem a Pulse wrapper would call as a ghost step after gen_gc.
val gen_gc_isomorphism
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (combined_roots: seq combined_vertex)
  (major_stack: seq obj_addr) (major_fp: U64.t)
  : Lemma
    (requires
      // --- Standard gen_gc preconditions ---
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp /\
      Mark.no_black_objects major /\
      minor_wf minor /\
      // Post-Cheney preconditions
      (let res = cheney_collect_spec minor major fp roots in
       well_formed_heap res.mc_major /\
       Mark.no_pointer_to_blue res.mc_major /\
       Mark.stack_props res.mc_major major_stack /\
       Mark.root_props res.mc_major major_stack /\
       Sweep.fp_in_heap major_fp res.mc_major /\
       Mark.no_black_objects res.mc_major /\
       no_scan_invariant res.mc_major /\
       (let g = create_graph res.mc_major in
        let rs = HeapGraph.coerce_to_vertex_list major_stack in
        graph_wf g /\ is_vertex_set rs /\ subset_vertices rs g.vertices)) /\
      // --- Isomorphism-specific assumptions ---
      iso_structural_preconditions minor major fp roots combined_roots major_stack /\
      iso_edge_bridge_forward minor major fp roots combined_roots major_stack /\
      iso_surjectivity minor major fp roots combined_roots major_stack /\
      iso_edge_backward minor major fp roots combined_roots)
    (ensures
      isomorphism_postcondition minor major fp roots combined_roots major_stack major_fp)
