/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph.Isomorphism.Discharge
/// ---------------------------------------------------------------------------
///
/// Top-level composition: derives the isomorphism from standard GC
/// preconditions plus 3 bridge assumptions stated at the mc_major level.
///
/// The key contribution:
///   - The main theorem (Isomorphism.fsti) requires surjectivity and
///     edge-backward stated over g_final (the post-mark/sweep graph).
///   - This module takes those assumptions at the mc_major level
///     (easier to prove from the GC infrastructure) and bridges
///     them to g_final using MarkSweepFrame lemmas.
///
/// Architecture:
///   Caller proves:
///     1. Edge bridge forward:  combined edge → mc_major edge
///     2. Surjectivity at mc:   mc-reachable → has combined pre-image
///     3. Edge backward at mc:  mc edge between images → combined edge
///
///   This module derives (using MarkSweepFrame):
///     1. (pass-through)
///     2. g_final-reachable → has pre-image   (via black ↔ reachable)
///     3. g_final edge → combined edge         (via successor preservation)
///
///   Then calls generational_gc_isomorphism to get the full isomorphism.

module GC.Gen.CombinedGraph.Isomorphism.Discharge

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
open GC.Gen.Reachability
open GC.Gen.Remembered
open GC.Gen.Promote
open GC.Gen.CombinedGraph
open GC.Gen.Correctness
open GC.Gen.Allocator

module HeapGraph = GC.Spec.HeapGraph
module AllocLemmas = GC.Spec.Allocator.Lemmas
module Mark = GC.Spec.Mark
module Sweep = GC.Spec.Sweep
module DFS = GC.Spec.DFS
module MSFrame = GC.Gen.CombinedGraph.MarkSweepFrame
module Iso = GC.Gen.CombinedGraph.Isomorphism


/// The standard GC preconditions shared by all lemmas in this module.
let standard_gc_preconditions
  (gs: gen_state) (roots: seq U64.t) (fp: U64.t)
  (major_roots: seq obj_addr) (major_stack: seq obj_addr) (major_fp: U64.t)
  = gen_wf gs /\
    well_formed_heap gs.gs_major /\
    AllocLemmas.fl_valid gs.gs_major fp (heap_size / U64.v mword) /\
    AllocLemmas.fl_chain_terminates gs.gs_major fp (heap_size / U64.v mword) /\
    minor_fields_well_formed gs.gs_minor gs.gs_major roots /\
    all_promotions_succeed gs.gs_minor gs.gs_major fp roots /\
    allocated_objects_avoid_chain gs.gs_major fp /\
    post_promote_pointer_closure gs.gs_minor gs.gs_major fp roots /\
    live_set_no_infix gs.gs_minor (live_set_of gs.gs_minor gs.gs_major roots) /\
    no_scan_invariant gs.gs_major /\
    minor_no_scan_invariant gs.gs_minor /\
    (let live_set = live_set_of gs.gs_minor gs.gs_major roots in
     forall (v: U64.t). Seq.mem v live_set ==> minor_wosize gs.gs_minor v > 0) /\
    (let mc = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
     well_formed_heap mc.mc_major /\
     Mark.stack_props mc.mc_major major_stack /\
     Mark.root_props mc.mc_major major_roots /\
     Sweep.fp_in_heap major_fp mc.mc_major /\
     Mark.no_black_objects mc.mc_major /\
     Mark.no_pointer_to_blue mc.mc_major /\
     (forall (r: obj_addr). Seq.mem r major_roots <==> Seq.mem r major_stack) /\
     (let g_mc = create_graph mc.mc_major in
      let mc_roots = HeapGraph.coerce_to_vertex_list major_roots in
      graph_wf g_mc /\ is_vertex_set mc_roots /\ subset_vertices mc_roots g_mc.vertices))

/// The structural preconditions that connect combined graph to mc_major.
let structural_preconditions
  (gs: gen_state) (roots: seq U64.t) (fp: U64.t)
  (combined_roots: seq combined_vertex)
  (major_roots: seq obj_addr)
  = // Root correspondence
    (forall (r: obj_addr). Seq.mem r major_roots <==>
      Seq.mem (MajorV r) combined_roots \/
      (exists (m: U64.t). Seq.mem (MinorV m) combined_roots /\
        (let live_set = live_set_of gs.gs_minor gs.gs_major roots in
         let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
         prom_res.fwd_map m == r))) /\
    // Fwd injectivity on live set
    (let live_set = live_set_of gs.gs_minor gs.gs_major roots in
     let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
     forall (i j: nat). i < Seq.length live_set /\ j < Seq.length live_set /\ i <> j ==>
       (let oi = Seq.index live_set i in
        let oj = Seq.index live_set j in
        prom_res.fwd_map oi <> 0UL /\ prom_res.fwd_map oj <> 0UL ==>
        prom_res.fwd_map oi <> prom_res.fwd_map oj)) /\
    // Field correspondence
    (let live_set = live_set_of gs.gs_minor gs.gs_major roots in
     let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
     let mc = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
     field_correspondence gs.gs_minor gs.gs_major mc.mc_major prom_res.fwd_map roots) /\
    // Reachability bridge
    (let cg = build_combined_graph gs.gs_minor gs.gs_major in
     let live_set = live_set_of gs.gs_minor gs.gs_major roots in
     forall (v: U64.t).
       combined_reachable cg combined_roots (MinorV v) ==> Seq.mem v live_set) /\
    // Promoted disjoint from non-blue major
    (let live_set = live_set_of gs.gs_minor gs.gs_major roots in
     let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
     forall (v: U64.t) (obj: obj_addr).
       Seq.mem v live_set /\ prom_res.fwd_map v <> 0UL /\
       Seq.mem obj (objects zero_addr gs.gs_major) /\ ~(is_blue obj gs.gs_major) ==>
       prom_res.fwd_map v <> obj) /\
    // Reachable major vertices valid non-blue
    (let cg = build_combined_graph gs.gs_minor gs.gs_major in
     forall (v: U64.t).
       combined_reachable cg combined_roots (MajorV v) ==>
       U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
       Seq.mem (v <: obj_addr) (objects zero_addr gs.gs_major) /\
       ~(is_blue (v <: obj_addr) gs.gs_major)) /\
    // Morphism image preservation (forward)
    (let cg = build_combined_graph gs.gs_minor gs.gs_major in
     let live_set = live_set_of gs.gs_minor gs.gs_major roots in
     let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
     let mc = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
     let g_mc = create_graph mc.mc_major in
     forall (v: combined_vertex).
       combined_reachable cg combined_roots v ==>
       (let w = Iso.fwd_morphism prom_res.fwd_map v in
        U64.v w >= U64.v mword /\ U64.v w < heap_size /\ U64.v w % U64.v mword == 0 /\
        mem_graph_vertex g_mc (w <: obj_addr) /\
        (exists (r: obj_addr). Seq.mem r major_roots /\
                               mem_graph_vertex g_mc r /\
                               reachable g_mc r (w <: obj_addr))))


/// ---------------------------------------------------------------------------
/// The 3 bridge assumptions, stated at the mc_major level
/// ---------------------------------------------------------------------------

/// (1) Edge bridge forward: combined edge → mc_major edge.
/// Already at mc_major level — passes through to the main theorem.
let edge_bridge_forward_at_mc
  (gs: gen_state) (roots: seq U64.t) (fp: U64.t)
  (combined_roots: seq combined_vertex)
  = let cg = build_combined_graph gs.gs_minor gs.gs_major in
    let live_set = live_set_of gs.gs_minor gs.gs_major roots in
    let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
    let mc = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
    let g_mc = create_graph mc.mc_major in
    forall (u v: combined_vertex).
      combined_reachable cg combined_roots u /\
      combined_reachable cg combined_roots v /\
      mem_ce (u, v) cg ==>
      (let fu = Iso.fwd_morphism prom_res.fwd_map u in
       let fv = Iso.fwd_morphism prom_res.fwd_map v in
       U64.v fu >= U64.v mword /\ U64.v fu < heap_size /\ U64.v fu % U64.v mword == 0 /\
       U64.v fv >= U64.v mword /\ U64.v fv < heap_size /\ U64.v fv % U64.v mword == 0 /\
       Seq.mem ((fu <: hp_addr), (fv <: hp_addr)) g_mc.edges)

/// (2) Surjectivity at mc_major level:
/// mc-reachable from major_roots → has a combined-reachable pre-image.
let surjectivity_at_mc
  (gs: gen_state) (roots: seq U64.t) (fp: U64.t)
  (combined_roots: seq combined_vertex) (major_roots: seq obj_addr)
  (major_stack: seq obj_addr) (major_fp: U64.t)
  = let cg = build_combined_graph gs.gs_minor gs.gs_major in
    let live_set = live_set_of gs.gs_minor gs.gs_major roots in
    let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
    let mc = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
    let g_mc = create_graph mc.mc_major in
    let mc_roots_v = HeapGraph.coerce_to_vertex_list major_roots in
    graph_wf g_mc /\ is_vertex_set mc_roots_v /\ subset_vertices mc_roots_v g_mc.vertices /\
    (forall (w: obj_addr).
      mem_graph_vertex g_mc w /\
      Seq.mem w (DFS.reachable_set g_mc mc_roots_v) ==>
      (exists (v: combined_vertex).
        combined_reachable cg combined_roots v /\
        Iso.fwd_morphism prom_res.fwd_map v == (w <: U64.t)))

/// (3) Edge backward at mc_major level:
/// mc_major edge between morphism images → combined edge.
let edge_backward_at_mc
  (gs: gen_state) (roots: seq U64.t) (fp: U64.t)
  (combined_roots: seq combined_vertex)
  = let cg = build_combined_graph gs.gs_minor gs.gs_major in
    let live_set = live_set_of gs.gs_minor gs.gs_major roots in
    let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
    let mc = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
    let g_mc = create_graph mc.mc_major in
    forall (u v: combined_vertex).
      combined_reachable cg combined_roots u /\
      combined_reachable cg combined_roots v /\
      (let fu = Iso.fwd_morphism prom_res.fwd_map u in
       let fv = Iso.fwd_morphism prom_res.fwd_map v in
       U64.v fu < heap_size /\ U64.v fu % U64.v mword == 0 /\
       U64.v fv < heap_size /\ U64.v fv % U64.v mword == 0 /\
       Seq.mem ((fu <: hp_addr), (fv <: hp_addr)) g_mc.edges) ==>
      mem_ce (u, v) cg


/// ---------------------------------------------------------------------------
/// Top-level composition lemma
/// ---------------------------------------------------------------------------

/// Derives the full isomorphism from:
///   - Standard GC + structural preconditions
///   - 3 bridge assumptions at mc_major level
///
/// The proof bridges mc_major to g_final using MarkSweepFrame, then
/// calls generational_gc_isomorphism.
val isomorphism_from_gc
  (gs: gen_state) (roots: seq U64.t) (fp: U64.t)
  (combined_roots: seq combined_vertex)
  (major_roots: seq obj_addr) (major_stack: seq obj_addr) (major_fp: U64.t)
  : Lemma
    (requires
      standard_gc_preconditions gs roots fp major_roots major_stack major_fp /\
      structural_preconditions gs roots fp combined_roots major_roots /\
      edge_bridge_forward_at_mc gs roots fp combined_roots /\
      surjectivity_at_mc gs roots fp combined_roots major_roots major_stack major_fp /\
      edge_backward_at_mc gs roots fp combined_roots)
    (ensures
      (let live_set = live_set_of gs.gs_minor gs.gs_major roots in
       let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
       let fwd = prom_res.fwd_map in
       let h_final = Iso.post_gc_heap gs.gs_minor gs.gs_major fp roots major_stack major_fp in
       Iso.reachable_implies_forwarded (Iso.pre_gc_graph gs.gs_minor gs.gs_major)
                                       combined_roots fwd /\
       Iso.reachable_subgraph_isomorphism gs.gs_minor gs.gs_major fwd
                                          combined_roots h_final major_roots))
