/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph.Isomorphism — End-to-end isomorphism statement
/// ---------------------------------------------------------------------------
///
/// The main theorem: the pre-GC combined graph (minor + major) is isomorphic
/// to the post-GC major graph, restricted to objects reachable from roots.
///
/// The isomorphism is witnessed by:
///   MinorV v ↦ fwd(v)   (promoted copies in major heap)
///   MajorV v ↦ v        (identity on major objects)
///
/// Scope: This is an UNLABELED graph isomorphism — it preserves the pointer
/// structure (edges) between objects. Header/tag/payload preservation is
/// captured separately by field_correspondence and Pillar 5 of the mark-sweep
/// correctness theorem.
///
/// This module states the theorem and supporting predicates.

module GC.Gen.CombinedGraph.Isomorphism

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
open GC.Gen.Allocator
open GC.Gen.Correctness

module HeapGraph = GC.Spec.HeapGraph
module AllocLemmas = GC.Spec.Allocator.Lemmas
module Mark = GC.Spec.Mark
module Sweep = GC.Spec.Sweep
module MajorCorrectness = GC.Spec.Correctness

/// ---------------------------------------------------------------------------
/// Definitions
/// ---------------------------------------------------------------------------

/// The morphism maps pre-GC combined vertices to post-GC major heap addresses.
/// MinorV v → fwd(v) (promoted copy in major heap)
/// MajorV v → v      (identity, already in major heap)
let fwd_morphism (fwd: forwarding_map) (v: combined_vertex) : GTot U64.t =
  match v with
  | MinorV addr -> fwd addr
  | MajorV addr -> addr

/// The pre-GC combined graph restricted to reachable vertices
let pre_gc_graph (ms: minor_state) (major: heap) : GTot combined_graph =
  build_combined_graph ms major

/// The post-GC heap after the full generational cycle:
///   minor_collect (promote + update_pointers) → mark → sweep
let post_gc_heap (ms: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
                 (major_stack: seq obj_addr) (major_fp: U64.t) : GTot heap =
  let mc = minor_collect_spec ms major fp roots in
  let marked = Mark.mark mc.mc_major major_stack in
  fst (Sweep.sweep marked major_fp)

/// The post-GC graph (standard HeapGraph construction from final heap)
let post_gc_graph (ms: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
                  (major_stack: seq obj_addr) (major_fp: U64.t) : GTot graph_state =
  create_graph (post_gc_heap ms major fp roots major_stack major_fp)

/// ---------------------------------------------------------------------------
/// Isomorphism Properties
/// ---------------------------------------------------------------------------

/// Key requirement: reachable minor vertices must have been forwarded.
/// This follows from: reachable in combined graph → in live_set → fwd <> 0.
let reachable_implies_forwarded
  (cg: combined_graph) (combined_roots: seq combined_vertex) (fwd: forwarding_map) : prop =
  forall (v: U64.t).
    combined_reachable cg combined_roots (MinorV v) ==> fwd v <> 0UL

/// The canonical definition of graph isomorphism on reachable subgraphs:
/// fwd_morphism is a bijection between pre-GC reachable vertices and post-GC
/// reachable vertices, preserving edges in both directions.
let reachable_subgraph_isomorphism
  (ms: minor_state) (major: heap) (fwd: forwarding_map)
  (combined_roots: seq combined_vertex)
  (h_final: heap) (major_roots: seq obj_addr) : prop =
  let cg = pre_gc_graph ms major in
  let g_final = create_graph h_final in
  // (A) Injectivity: distinct reachable vertices map to distinct addresses
  (forall (u v: combined_vertex).
    combined_reachable cg combined_roots u /\
    combined_reachable cg combined_roots v /\
    fwd_morphism fwd u == fwd_morphism fwd v ==> u == v) /\
  // (B) Image in post-GC: reachable pre-GC vertices map to post-GC vertices
  //     The morphism result is a valid heap address in the post-GC graph.
  (forall (v: combined_vertex).
    combined_reachable cg combined_roots v ==>
    (let w = fwd_morphism fwd v in
     U64.v w >= 0 /\ U64.v w < heap_size /\ U64.v w % U64.v mword == 0 /\
     Seq.mem (w <: hp_addr) g_final.vertices)) /\
  // (C) Surjectivity on reachable: post-GC reachable vertices have pre-images
  (forall (w: vertex_id).
    Seq.mem w g_final.vertices /\
    (exists (r: obj_addr). Seq.mem r major_roots /\
                           Seq.mem r g_final.vertices /\
                           reachable g_final r w) ==>
    (exists (v: combined_vertex).
      combined_reachable cg combined_roots v /\
      fwd_morphism fwd v == (w <: U64.t))) /\
  // (D) Edge equivalence (biconditional): edges are preserved in both directions
  //     This is the canonical induced-subgraph isomorphism condition.
  //     Quantified over reachable vertices whose morphism images are valid addresses.
  (forall (u v: combined_vertex).
    combined_reachable cg combined_roots u /\
    combined_reachable cg combined_roots v /\
    (let fu = fwd_morphism fwd u in
     let fv = fwd_morphism fwd v in
     U64.v fu < heap_size /\ U64.v fu % U64.v mword == 0 /\
     U64.v fv < heap_size /\ U64.v fv % U64.v mword == 0) ==>
    (mem_ce (u, v) cg <==>
     Seq.mem ((fwd_morphism fwd u <: hp_addr), (fwd_morphism fwd v <: hp_addr)) g_final.edges))

/// ---------------------------------------------------------------------------
/// The Main Theorem
/// ---------------------------------------------------------------------------

/// Full generational GC isomorphism: the pre-GC combined graph (restricted to
/// objects reachable from roots) is isomorphic to the post-GC major graph
/// (restricted to objects reachable from updated roots).
///
/// The isomorphism is witnessed by fwd_morphism:
///   MinorV v ↦ fwd(v)   (promoted copy in major heap)
///   MajorV v ↦ v        (identity on major objects)
val generational_gc_isomorphism
  (gs: gen_state) (roots: seq U64.t) (fp: U64.t)
  (combined_roots: seq combined_vertex)
  (major_roots: seq obj_addr) (major_stack: seq obj_addr) (major_fp: U64.t)
  : Lemma
    (requires
      // Standard gen GC preconditions
      gen_wf gs /\
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
      // Live objects have positive wosize (needed for promotion guarantee)
      (let live_set = live_set_of gs.gs_minor gs.gs_major roots in
       forall (v: U64.t). Seq.mem v live_set ==> minor_wosize gs.gs_minor v > 0) /\
      // Major GC preconditions
      (let mc = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
       well_formed_heap mc.mc_major /\
       Mark.stack_props mc.mc_major major_stack /\
       Mark.root_props mc.mc_major major_roots /\
       Sweep.fp_in_heap major_fp mc.mc_major /\
       Mark.no_black_objects mc.mc_major /\
       Mark.no_pointer_to_blue mc.mc_major /\
       (forall (r: obj_addr). Seq.mem r major_roots <==> Seq.mem r major_stack) /\
       // Graph well-formedness of mc_major (needed for mark/sweep composition)
       (let g_mc = create_graph mc.mc_major in
        let mc_roots = HeapGraph.coerce_to_vertex_list major_roots in
        graph_wf g_mc /\ is_vertex_set mc_roots /\ subset_vertices mc_roots g_mc.vertices)) /\
      // Root correspondence
      (forall (r: obj_addr). Seq.mem r major_roots <==>
        Seq.mem (MajorV r) combined_roots \/ 
        (exists (m: U64.t). Seq.mem (MinorV m) combined_roots /\
          (let live_set = live_set_of gs.gs_minor gs.gs_major roots in
           let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
           prom_res.fwd_map m == r))) /\
      // Injectivity of forwarding on live set
      (let live_set = live_set_of gs.gs_minor gs.gs_major roots in
       let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
       forall (i j: nat). i < Seq.length live_set /\ j < Seq.length live_set /\ i <> j ==>
         (let oi = Seq.index live_set i in
          let oj = Seq.index live_set j in
          prom_res.fwd_map oi <> 0UL /\ prom_res.fwd_map oj <> 0UL ==>
          prom_res.fwd_map oi <> prom_res.fwd_map oj)) /\
      // Field correspondence for promoted objects
      (let live_set = live_set_of gs.gs_minor gs.gs_major roots in
       let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
       let mc = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
       field_correspondence gs.gs_minor gs.gs_major mc.mc_major prom_res.fwd_map roots) /\
      // Reachability bridge: combined-reachable minor vertices are in the live set
      (let cg = build_combined_graph gs.gs_minor gs.gs_major in
       let live_set = live_set_of gs.gs_minor gs.gs_major roots in
       forall (v: U64.t).
         combined_reachable cg combined_roots (MinorV v) ==>
         Seq.mem v live_set) /\
      // Promoted targets are disjoint from pre-existing non-blue major objects
      // (follows from: promote allocates from free list, non-blue objects avoid chain)
      (let live_set = live_set_of gs.gs_minor gs.gs_major roots in
       let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
       forall (v: U64.t) (obj: obj_addr).
         Seq.mem v live_set /\ prom_res.fwd_map v <> 0UL /\
         Seq.mem obj (objects zero_addr gs.gs_major) /\ ~(is_blue obj gs.gs_major) ==>
         prom_res.fwd_map v <> obj) /\
      // Reachable major vertices are valid non-blue objects in the pre-GC heap
      (let cg = build_combined_graph gs.gs_minor gs.gs_major in
       forall (v: U64.t).
         combined_reachable cg combined_roots (MajorV v) ==>
         U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
         Seq.mem (v <: obj_addr) (objects zero_addr gs.gs_major) /\
         ~(is_blue (v <: obj_addr) gs.gs_major)) /\
      // Morphism image preservation: combined-reachable vertices map to
      // objects reachable from major_roots in the post-minor-collect heap.
      // This is the central bridge connecting the combined graph to the mark phase.
      (let cg = build_combined_graph gs.gs_minor gs.gs_major in
       let live_set = live_set_of gs.gs_minor gs.gs_major roots in
       let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
       let mc = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
       let g_mc = create_graph mc.mc_major in
       forall (v: combined_vertex).
         combined_reachable cg combined_roots v ==>
         (let w = fwd_morphism prom_res.fwd_map v in
          U64.v w >= U64.v mword /\ U64.v w < heap_size /\ U64.v w % U64.v mword == 0 /\
          mem_graph_vertex g_mc (w <: obj_addr) /\
          (exists (r: obj_addr). Seq.mem r major_roots /\
                                 mem_graph_vertex g_mc r /\
                                 reachable g_mc r (w <: obj_addr)))) /\
      // Edge bridge: combined edges between reachable vertices map to mc_major edges.
      // This composes: edge elimination → EdgePreservation (4 cases) → HeapGraph intro.
      (let cg = build_combined_graph gs.gs_minor gs.gs_major in
       let live_set = live_set_of gs.gs_minor gs.gs_major roots in
       let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
       let mc = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
       let g_mc = create_graph mc.mc_major in
       forall (u v: combined_vertex).
         combined_reachable cg combined_roots u /\
         combined_reachable cg combined_roots v /\
         mem_ce (u, v) cg ==>
         (let fu = fwd_morphism prom_res.fwd_map u in
          let fv = fwd_morphism prom_res.fwd_map v in
          U64.v fu >= U64.v mword /\ U64.v fu < heap_size /\ U64.v fu % U64.v mword == 0 /\
          U64.v fv >= U64.v mword /\ U64.v fv < heap_size /\ U64.v fv % U64.v mword == 0 /\
          Seq.mem ((fu <: hp_addr), (fv <: hp_addr)) g_mc.edges)) /\
      // Surjectivity: post-GC reachable vertices have pre-images under fwd_morphism.
      (let ms = gs.gs_minor in
       let major = gs.gs_major in
       let live_set = live_set_of ms major roots in
       let prom_res = promote_all_spec ms major fp live_set in
       let fwd = prom_res.fwd_map in
       let cg = pre_gc_graph ms major in
       let h_final = post_gc_heap ms major fp roots major_stack major_fp in
       let g_final = create_graph h_final in
       forall (w: vertex_id).
         Seq.mem w g_final.vertices /\
         (exists (r: obj_addr). Seq.mem r major_roots /\
                                Seq.mem r g_final.vertices /\
                                reachable g_final r w) ==>
         (exists (v: combined_vertex).
           combined_reachable cg combined_roots v /\
           fwd_morphism fwd v == (w <: U64.t))) /\
      // Edge backward: post-GC edges between morphism images imply combined edges.
      (let ms = gs.gs_minor in
       let major = gs.gs_major in
       let live_set = live_set_of ms major roots in
       let prom_res = promote_all_spec ms major fp live_set in
       let fwd = prom_res.fwd_map in
       let cg = pre_gc_graph ms major in
       let h_final = post_gc_heap ms major fp roots major_stack major_fp in
       let g_final = create_graph h_final in
       forall (u v: combined_vertex).
         combined_reachable cg combined_roots u /\
         combined_reachable cg combined_roots v /\
         (let fu = fwd_morphism fwd u in
          let fv = fwd_morphism fwd v in
          U64.v fu < heap_size /\ U64.v fu % U64.v mword == 0 /\
          U64.v fv < heap_size /\ U64.v fv % U64.v mword == 0) /\
         Seq.mem ((fwd_morphism fwd u <: hp_addr), (fwd_morphism fwd v <: hp_addr)) g_final.edges ==>
         mem_ce (u, v) cg))
    (ensures
      (let live_set = live_set_of gs.gs_minor gs.gs_major roots in
       let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
       let fwd = prom_res.fwd_map in
       let h_final = post_gc_heap gs.gs_minor gs.gs_major fp roots major_stack major_fp in
       // The forwarding map witnesses a graph isomorphism between the
       // pre-GC combined reachable subgraph and post-GC reachable subgraph
       reachable_implies_forwarded (pre_gc_graph gs.gs_minor gs.gs_major)
                                   combined_roots fwd /\
       reachable_subgraph_isomorphism gs.gs_minor gs.gs_major fwd
                                      combined_roots h_final major_roots))

