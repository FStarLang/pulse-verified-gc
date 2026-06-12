module GC.Gen.CheneyGraphReadiness

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Reachability
open GC.Gen.Promote
open GC.Gen.Cheney

module MH = GC.Spec.MajorHeap
module SpecMajorAlloc = GC.Spec.MajorAllocator
module PromotionDemand = GC.Gen.PromotionDemand
module ChunkedCheney = GC.Gen.ChunkedCheney
module GenInv = GC.Gen.HeapInvariant
module CG = GC.Gen.CombinedGraph
module CC = GC.Gen.CheneyCorrectness
module RBridge = GC.Gen.ReachabilityBridge
module CReach = GC.Gen.ChunkedReachabilityBridge
module CRem = GC.Gen.ChunkedRemembered

/// Heap-level separation fact needed to discharge major-target update stability
/// from graph-edge membership: every active major object address lies outside
/// the minor range.  This is intentionally separate from `major_heap`'s pure
/// well-formedness, which only records chunk disjointness.
let chunked_major_objects_above_minor (major: MH.major_heap) : prop =
  forall (obj: obj_addr).
    Seq.mem obj (MH.major_objects major) ==> U64.v obj >= minor_heap_size

/// Stronger range fact used when a proof must relate chunked active-major
/// classification back to the legacy heap-pointer predicate.
let chunked_major_objects_are_pointer_fields (major: MH.major_heap) : prop =
  forall (obj: obj_addr).
    Seq.mem obj (MH.major_objects major) ==>
    GC.Spec.Fields.is_pointer_field obj

let chunked_major_chunks_above_minor (major: MH.major_heap) : prop =
  forall (i: nat).
    i < Seq.length major ==> U64.v (Seq.index major i).base >= minor_heap_size

let chunked_major_chunks_above_zero_addr (major: MH.major_heap) : prop =
  forall (i: nat).
    i < Seq.length major ==> U64.v (Seq.index major i).base >= U64.v zero_addr

val chunked_major_chunks_above_minor_objects_above_minor
  (major: MH.major_heap)
  : Lemma
    (requires chunked_major_chunks_above_minor major)
    (ensures chunked_major_objects_above_minor major)

val chunked_major_chunks_above_minor_single_chunk
  (g: heap)
  : Lemma
    (ensures chunked_major_chunks_above_minor (MH.single_chunk_major_heap g))

val chunked_major_objects_above_minor_single_chunk
  (g: heap)
  : Lemma
    (ensures chunked_major_objects_above_minor (MH.single_chunk_major_heap g))

val chunked_major_objects_above_minor_expand_major_heap
  (major: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
    (requires
      chunked_major_objects_above_minor major /\
      U64.v fresh.base >= minor_heap_size)
    (ensures
      chunked_major_objects_above_minor
        (SpecMajorAlloc.expand_major_heap major fresh fp).major_out)

val chunked_major_objects_above_minor_ensure_head_capacity
  (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (needed: nat{needed > 0}) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      chunked_major_objects_above_minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp < needed ==>
       U64.v fresh.base >= U64.v zero_addr))
    (ensures
      (let r =
         SpecMajorAlloc.ensure_major_head_capacity_spec
           major fp fuel needed fresh in
       chunked_major_objects_above_minor r.capacity_major_out))

val chunked_major_chunks_above_zero_addr_objects_are_pointer_fields
  (major: MH.major_heap)
  : Lemma
    (requires chunked_major_chunks_above_zero_addr major)
    (ensures chunked_major_objects_are_pointer_fields major)

val chunked_major_chunks_above_zero_addr_single_chunk
  (g: heap)
  : Lemma
    (ensures chunked_major_chunks_above_zero_addr (MH.single_chunk_major_heap g))

val chunked_major_chunks_above_zero_addr_expand_major_heap
  (major: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
    (requires
      chunked_major_chunks_above_zero_addr major /\
      U64.v fresh.base >= U64.v zero_addr)
    (ensures
      chunked_major_chunks_above_zero_addr
        (SpecMajorAlloc.expand_major_heap major fresh fp).major_out)

val chunked_major_chunks_above_zero_addr_ensure_head_capacity
  (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (needed: nat{needed > 0}) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      chunked_major_chunks_above_zero_addr major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp < needed ==>
       U64.v fresh.base >= U64.v zero_addr))
    (ensures
      (let r =
         SpecMajorAlloc.ensure_major_head_capacity_spec
           major fp fuel needed fresh in
       chunked_major_chunks_above_zero_addr r.capacity_major_out))

val chunked_major_chunks_above_zero_addr_chunks_above_minor
  (major: MH.major_heap)
  : Lemma
    (requires chunked_major_chunks_above_zero_addr major)
    (ensures chunked_major_chunks_above_minor major)

val chunked_major_chunks_above_zero_addr_objects_above_minor
  (major: MH.major_heap)
  : Lemma
    (requires chunked_major_chunks_above_zero_addr major)
    (ensures chunked_major_objects_above_minor major)

val chunked_major_objects_are_pointer_fields_single_chunk
  (g: heap)
  : Lemma
    (ensures
      chunked_major_objects_are_pointer_fields (MH.single_chunk_major_heap g))

val chunked_major_objects_are_pointer_fields_expand_major_heap
  (major: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
    (requires
      chunked_major_objects_are_pointer_fields major /\
      U64.v fresh.base >= U64.v zero_addr)
    (ensures
      chunked_major_objects_are_pointer_fields
        (SpecMajorAlloc.expand_major_heap major fresh fp).major_out)

val chunked_major_objects_are_pointer_fields_ensure_head_capacity
  (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (needed: nat{needed > 0}) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      chunked_major_objects_are_pointer_fields major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp < needed ==>
       U64.v fresh.base >= U64.v zero_addr))
    (ensures
      (let r =
         SpecMajorAlloc.ensure_major_head_capacity_spec
           major fp fuel needed fresh in
       chunked_major_objects_are_pointer_fields r.capacity_major_out))

/// Edge readiness variant that derives major-target witnesses from the graph
/// edge itself.  Major target branches no longer mention the target address:
/// `CG.mem_ce` plus `chunked_major_objects_above_minor` recovers the active
/// target object and proves it is outside the minor range.
let chunked_graph_edge_maps_to_major_edge_targets_ready
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex) : GTot prop =
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      major fp alloc_fuel needed fresh in
  let collect =
    ChunkedCheney.chunked_cheney_collect_spec
      minor r.capacity_major_out r.capacity_fp_out roots
      r.capacity_fuel_out in
  match u, v with
  | CG.MinorV src, CG.MinorV dst ->
    Seq.mem src (minor_reachable minor roots) /\
    minor_tag minor src < U64.v GC.Spec.Object.no_scan_tag /\
    minor_wosize minor dst > 0
  | CG.MinorV src, CG.MajorV dst ->
    Seq.mem src (minor_reachable minor roots) /\
    minor_tag minor src < U64.v GC.Spec.Object.no_scan_tag
  | CG.MajorV src, CG.MajorV dst ->
    exists (src_obj: obj_addr).
      src_obj == src /\
      Seq.mem src_obj (MH.major_objects major) /\
      ~(GenInv.chunked_is_blue major src_obj)
  | CG.MajorV src, CG.MinorV dst ->
    (exists (src_obj: obj_addr).
      src_obj == src /\
      Seq.mem src_obj (MH.major_objects major) /\
      ~(GenInv.chunked_is_blue major src_obj)) /\
    collect.cmc_fwd dst <> 0UL
  | _, _ -> False

val chunked_graph_edge_maps_to_major_edge_targets_ready_implies_nonblue_sources_above_minor_targets_ready
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      chunked_major_objects_above_minor major /\
      CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
      chunked_graph_edge_maps_to_major_edge_targets_ready
        minor major fp roots alloc_fuel fresh u v)
    (ensures
      CC.chunked_graph_edge_maps_to_major_nonblue_sources_above_minor_targets_ready
        minor major fp roots alloc_fuel fresh u v)

val chunked_cheney_gc_correct_after_preflight_graph_edge_edge_targets_maps_to_major_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_objects_above_minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0) /\
      CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
      chunked_graph_edge_maps_to_major_edge_targets_ready
        minor major fp roots alloc_fuel fresh u v)
    (ensures
      (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
       let r =
       SpecMajorAlloc.ensure_major_head_capacity_spec
         major fp alloc_fuel needed fresh in
       let collect =
       ChunkedCheney.chunked_cheney_collect_spec
         minor r.capacity_major_out r.capacity_fp_out roots
         r.capacity_fuel_out in
       CG.mem_ce
        (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u),
         CG.MajorV (CG.fwd_morphism collect.cmc_fwd v))
        (CG.build_chunked_combined_graph
         collect.cmc_minor collect.cmc_major)))

let chunked_graph_edges_edge_targets_map_to_major_edges_prop
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk) : prop =
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      major fp alloc_fuel needed fresh in
  let collect =
    ChunkedCheney.chunked_cheney_collect_spec
      minor r.capacity_major_out r.capacity_fp_out roots
      r.capacity_fuel_out in
  forall (u v: CG.combined_vertex).
    CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
    chunked_graph_edge_maps_to_major_edge_targets_ready
      minor major fp roots alloc_fuel fresh u v ==>
    CG.mem_ce
      (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u),
       CG.MajorV (CG.fwd_morphism collect.cmc_fwd v))
      (CG.build_chunked_combined_graph
        collect.cmc_minor collect.cmc_major)

val chunked_cheney_gc_correct_after_preflight_graph_edges_edge_targets_map_to_major_edges
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_objects_above_minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_graph_edges_edge_targets_map_to_major_edges_prop
        minor major fp roots alloc_fuel fresh)

/// Readiness variant for client-selected live edges.  Compared with
/// `chunked_graph_edge_maps_to_major_edge_targets_ready`, this derives
/// `MinorV -> MinorV` target positivity from the edge itself, and replaces the
/// final forwarding-map side condition for `MajorV -> MinorV` edges by the
/// source-level fact that the minor target is reachable and positive.
let chunked_graph_edge_maps_to_major_reachable_targets_ready
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex) : GTot prop =
  match u, v with
  | CG.MinorV src, CG.MinorV dst ->
    Seq.mem src (minor_reachable minor roots) /\
    minor_tag minor src < U64.v GC.Spec.Object.no_scan_tag
  | CG.MinorV src, CG.MajorV dst ->
    Seq.mem src (minor_reachable minor roots) /\
    minor_tag minor src < U64.v GC.Spec.Object.no_scan_tag
  | CG.MajorV src, CG.MajorV dst ->
    exists (src_obj: obj_addr).
      src_obj == src /\
      Seq.mem src_obj (MH.major_objects major) /\
      ~(GenInv.chunked_is_blue major src_obj)
  | CG.MajorV src, CG.MinorV dst ->
    (exists (src_obj: obj_addr).
      src_obj == src /\
      Seq.mem src_obj (MH.major_objects major) /\
      ~(GenInv.chunked_is_blue major src_obj)) /\
    Seq.mem dst (minor_reachable minor roots) /\
    minor_wosize minor dst > 0
  | _, _ -> False

val chunked_graph_edge_maps_to_major_reachable_targets_ready_implies_edge_targets_ready
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_objects_above_minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0) /\
      CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
      chunked_graph_edge_maps_to_major_reachable_targets_ready
        minor major fp roots alloc_fuel fresh u v)
    (ensures
      chunked_graph_edge_maps_to_major_edge_targets_ready
        minor major fp roots alloc_fuel fresh u v)

val chunked_cheney_gc_correct_after_preflight_graph_edge_reachable_targets_maps_to_major_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_objects_above_minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0) /\
      CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
      chunked_graph_edge_maps_to_major_reachable_targets_ready
        minor major fp roots alloc_fuel fresh u v)
    (ensures
      (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
       let r =
       SpecMajorAlloc.ensure_major_head_capacity_spec
         major fp alloc_fuel needed fresh in
       let collect =
       ChunkedCheney.chunked_cheney_collect_spec
         minor r.capacity_major_out r.capacity_fp_out roots
         r.capacity_fuel_out in
       CG.mem_ce
        (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u),
         CG.MajorV (CG.fwd_morphism collect.cmc_fwd v))
        (CG.build_chunked_combined_graph
         collect.cmc_minor collect.cmc_major)))

let chunked_graph_edges_reachable_targets_map_to_major_edges_prop
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk) : prop =
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      major fp alloc_fuel needed fresh in
  let collect =
    ChunkedCheney.chunked_cheney_collect_spec
      minor r.capacity_major_out r.capacity_fp_out roots
      r.capacity_fuel_out in
  forall (u v: CG.combined_vertex).
    CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
    chunked_graph_edge_maps_to_major_reachable_targets_ready
      minor major fp roots alloc_fuel fresh u v ==>
    CG.mem_ce
      (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u),
       CG.MajorV (CG.fwd_morphism collect.cmc_fwd v))
      (CG.build_chunked_combined_graph
        collect.cmc_minor collect.cmc_major)

val chunked_cheney_gc_correct_after_preflight_graph_edges_reachable_targets_map_to_major_edges
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_objects_above_minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_graph_edges_reachable_targets_map_to_major_edges_prop
        minor major fp roots alloc_fuel fresh)

/// Vertex readiness variant that relies on graph vertex membership to recover
/// the active-major-object witness.  Clients only need to provide
/// reachability/positivity for minor vertices.
let chunked_graph_vertex_maps_to_major_membership_ready
  (minor: minor_state) (roots: seq U64.t)
  (u: CG.combined_vertex) : GTot prop =
  match u with
  | CG.MinorV src ->
    Seq.mem src (minor_reachable minor roots) /\
    minor_wosize minor src > 0
  | CG.MajorV _ -> True
  | _ -> False

val chunked_graph_vertex_maps_to_major_membership_ready_implies_ready
  (minor: minor_state) (major: MH.major_heap) (roots: seq U64.t)
  (u: CG.combined_vertex)
  : Lemma
    (requires
      CG.mem_cv u (CG.build_chunked_combined_graph minor major) /\
      chunked_graph_vertex_maps_to_major_membership_ready minor roots u)
    (ensures
      CC.chunked_graph_vertex_maps_to_major_ready minor major roots u)

val chunked_cheney_gc_correct_after_preflight_graph_vertex_membership_ready_maps_to_major_vertex
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u: CG.combined_vertex)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0) /\
      CG.mem_cv u (CG.build_chunked_combined_graph minor major) /\
      chunked_graph_vertex_maps_to_major_membership_ready minor roots u)
    (ensures
      (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
       let r =
       SpecMajorAlloc.ensure_major_head_capacity_spec
         major fp alloc_fuel needed fresh in
       let collect =
       ChunkedCheney.chunked_cheney_collect_spec
         minor r.capacity_major_out r.capacity_fp_out roots
         r.capacity_fuel_out in
       CG.mem_cv (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u))
        (CG.build_chunked_combined_graph collect.cmc_minor collect.cmc_major)))

let chunked_graph_vertices_membership_ready_map_to_major_vertices_prop
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk) : prop =
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      major fp alloc_fuel needed fresh in
  let collect =
    ChunkedCheney.chunked_cheney_collect_spec
      minor r.capacity_major_out r.capacity_fp_out roots
      r.capacity_fuel_out in
  forall (u: CG.combined_vertex).
    CG.mem_cv u (CG.build_chunked_combined_graph minor major) /\
    chunked_graph_vertex_maps_to_major_membership_ready minor roots u ==>
    CG.mem_cv (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u))
      (CG.build_chunked_combined_graph collect.cmc_minor collect.cmc_major)

val chunked_cheney_gc_correct_after_preflight_graph_vertices_membership_ready_map_to_major_vertices
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_graph_vertices_membership_ready_map_to_major_vertices_prop
        minor major fp roots alloc_fuel fresh)

let chunked_graph_membership_ready_maps_to_major_graph_prop
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk) : prop =
  chunked_graph_vertices_membership_ready_map_to_major_vertices_prop
    minor major fp roots alloc_fuel fresh /\
  chunked_graph_edges_reachable_targets_map_to_major_edges_prop
    minor major fp roots alloc_fuel fresh

val chunked_cheney_gc_correct_after_preflight_graph_membership_ready_maps_to_major_graph
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_objects_above_minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_graph_membership_ready_maps_to_major_graph_prop
        minor major fp roots alloc_fuel fresh)

/// Edge readiness phrased over a selected source/target view:
/// minor sources must be selected and scannable, major sources must be active
/// non-blue objects, and major-to-minor edges require a selected minor target.
let chunked_graph_edge_maps_to_major_selected_ready
  (minor: minor_state) (major: MH.major_heap) (roots: seq U64.t)
  (u v: CG.combined_vertex) : GTot prop =
  match u, v with
  | CG.MinorV src, CG.MinorV _ ->
    chunked_graph_vertex_maps_to_major_membership_ready minor roots u /\
    minor_tag minor src < U64.v GC.Spec.Object.no_scan_tag
  | CG.MinorV src, CG.MajorV _ ->
    chunked_graph_vertex_maps_to_major_membership_ready minor roots u /\
    minor_tag minor src < U64.v GC.Spec.Object.no_scan_tag
  | CG.MajorV src, CG.MajorV _ ->
    exists (src_obj: obj_addr).
      src_obj == src /\
      Seq.mem src_obj (MH.major_objects major) /\
      ~(GenInv.chunked_is_blue major src_obj)
  | CG.MajorV src, CG.MinorV _ ->
    (exists (src_obj: obj_addr).
      src_obj == src /\
      Seq.mem src_obj (MH.major_objects major) /\
      ~(GenInv.chunked_is_blue major src_obj)) /\
    chunked_graph_vertex_maps_to_major_membership_ready minor roots v
  | _, _ -> False

val chunked_minor_source_edge_not_no_scan
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (src: U64.t) (dst: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.chunked_collection_heap_shape minor major fp fuel /\
      chunked_major_objects_are_pointer_fields major /\
      CG.mem_ce (CG.MinorV src, dst)
        (CG.build_chunked_combined_graph minor major))
    (ensures
      minor_tag minor src < U64.v GC.Spec.Object.no_scan_tag)

/// Live-selected edge readiness: clients select minor vertices and active
/// non-blue major sources; minor-source scannability is derived from the graph
/// edge and chunked collection shape.
let chunked_graph_edge_maps_to_major_live_selected_ready
  (minor: minor_state) (major: MH.major_heap) (roots: seq U64.t)
  (u v: CG.combined_vertex) : GTot prop =
  match u, v with
  | CG.MinorV _, CG.MinorV _ ->
    chunked_graph_vertex_maps_to_major_membership_ready minor roots u
  | CG.MinorV _, CG.MajorV _ ->
    chunked_graph_vertex_maps_to_major_membership_ready minor roots u
  | CG.MajorV src, CG.MajorV _ ->
    exists (src_obj: obj_addr).
      src_obj == src /\
      Seq.mem src_obj (MH.major_objects major) /\
      ~(GenInv.chunked_is_blue major src_obj)
  | CG.MajorV src, CG.MinorV _ ->
    (exists (src_obj: obj_addr).
      src_obj == src /\
      Seq.mem src_obj (MH.major_objects major) /\
      ~(GenInv.chunked_is_blue major src_obj)) /\
    chunked_graph_vertex_maps_to_major_membership_ready minor roots v
  | _, _ -> False

let chunked_live_selected_graph_vertex
  (minor: minor_state) (major: MH.major_heap) (roots: seq U64.t)
  (u: CG.combined_vertex) : GTot prop =
  CG.mem_cv u (CG.build_chunked_combined_graph minor major) /\
  (match u with
  | CG.MinorV _ ->
    chunked_graph_vertex_maps_to_major_membership_ready minor roots u
  | CG.MajorV src ->
    exists (src_obj: obj_addr).
      src_obj == src /\
      Seq.mem src_obj (MH.major_objects major) /\
      ~(GenInv.chunked_is_blue major src_obj)
  | _ -> False)

val chunked_reachable_major_vertex_live_selected
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: seq U64.t) (v: U64.t)
  : Lemma
   (requires
     GenInv.chunked_collection_heap_shape minor major fp fuel /\
     CReach.chunked_roots_valid_nonblue roots major /\
     chunked_major_objects_are_pointer_fields major /\
     CG.combined_reachable
       (CG.build_chunked_combined_graph minor major)
       (CG.classify_roots roots)
       (CG.MajorV v))
   (ensures
     chunked_live_selected_graph_vertex minor major roots (CG.MajorV v))

val chunked_reachable_major_vertex_live_selected_from_chunk_bases
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: seq U64.t) (v: U64.t)
  : Lemma
   (requires
     GenInv.chunked_collection_heap_shape minor major fp fuel /\
     CReach.chunked_roots_valid_nonblue roots major /\
     chunked_major_chunks_above_zero_addr major /\
     CG.combined_reachable
       (CG.build_chunked_combined_graph minor major)
       (CG.classify_roots roots)
       (CG.MajorV v))
   (ensures
     chunked_live_selected_graph_vertex minor major roots (CG.MajorV v))

val chunked_reachable_positive_minor_vertex_live_selected
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: seq U64.t) (v: U64.t)
  : Lemma
   (requires
     GenInv.chunked_collection_heap_shape minor major fp fuel /\
     CReach.chunked_roots_valid_nonblue roots major /\
     chunked_major_objects_are_pointer_fields major /\
     CReach.chunked_major_field_zero_no_minor minor major /\
     CReach.chunked_remembered_minor_edges_in_roots minor major roots /\
     CG.combined_reachable
       (CG.build_chunked_combined_graph minor major)
       (CG.classify_roots roots)
       (CG.MinorV v) /\
     minor_wosize minor v > 0)
   (ensures
     chunked_live_selected_graph_vertex minor major roots (CG.MinorV v))

val chunked_reachable_positive_minor_vertex_live_selected_from_chunk_bases
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: seq U64.t) (v: U64.t)
  : Lemma
   (requires
     GenInv.chunked_collection_heap_shape minor major fp fuel /\
     CReach.chunked_roots_valid_nonblue roots major /\
     chunked_major_chunks_above_zero_addr major /\
     CReach.chunked_major_field_zero_no_minor minor major /\
     CReach.chunked_remembered_minor_edges_in_roots minor major roots /\
     CG.combined_reachable
       (CG.build_chunked_combined_graph minor major)
       (CG.classify_roots roots)
       (CG.MinorV v) /\
     minor_wosize minor v > 0)
   (ensures
     chunked_live_selected_graph_vertex minor major roots (CG.MinorV v))

let chunked_live_selected_graph_edge
  (minor: minor_state) (major: MH.major_heap) (roots: seq U64.t)
  (u v: CG.combined_vertex) : GTot prop =
  match u, v with
  | CG.MinorV _, CG.MinorV _ ->
    CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
    chunked_live_selected_graph_vertex minor major roots u /\
    chunked_live_selected_graph_vertex minor major roots v
  | CG.MinorV _, CG.MajorV _ ->
    CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
    chunked_live_selected_graph_vertex minor major roots u
  | CG.MajorV _, CG.MajorV _ ->
    CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
    chunked_live_selected_graph_vertex minor major roots u
  | CG.MajorV _, CG.MinorV _ ->
    CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
    chunked_live_selected_graph_vertex minor major roots u /\
    chunked_live_selected_graph_vertex minor major roots v
  | _, _ -> False

val chunked_live_selected_graph_edge_implies_live_selected_ready
  (minor: minor_state) (major: MH.major_heap) (roots: seq U64.t)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      chunked_live_selected_graph_edge minor major roots u v)
    (ensures
      chunked_graph_edge_maps_to_major_live_selected_ready
        minor major roots u v)

val chunked_graph_edge_maps_to_major_live_selected_ready_implies_selected_ready
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: seq U64.t) (u v: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.chunked_collection_heap_shape minor major fp fuel /\
      chunked_major_objects_are_pointer_fields major /\
      CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
      chunked_graph_edge_maps_to_major_live_selected_ready
        minor major roots u v)
    (ensures
      chunked_graph_edge_maps_to_major_selected_ready minor major roots u v)

val chunked_graph_edge_maps_to_major_selected_ready_implies_reachable_targets_ready
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      chunked_graph_edge_maps_to_major_selected_ready minor major roots u v)
    (ensures
      chunked_graph_edge_maps_to_major_reachable_targets_ready
        minor major fp roots alloc_fuel fresh u v)

val chunked_cheney_gc_correct_after_preflight_graph_edge_selected_maps_to_major_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_objects_above_minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0) /\
      CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
      chunked_graph_edge_maps_to_major_selected_ready
        minor major roots u v)
    (ensures
      (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
       let r =
       SpecMajorAlloc.ensure_major_head_capacity_spec
         major fp alloc_fuel needed fresh in
       let collect =
       ChunkedCheney.chunked_cheney_collect_spec
         minor r.capacity_major_out r.capacity_fp_out roots
         r.capacity_fuel_out in
       CG.mem_ce
        (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u),
         CG.MajorV (CG.fwd_morphism collect.cmc_fwd v))
        (CG.build_chunked_combined_graph
         collect.cmc_minor collect.cmc_major)))

val chunked_cheney_gc_correct_after_preflight_graph_edge_live_selected_maps_to_major_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_objects_above_minor major /\
      chunked_major_objects_are_pointer_fields major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0) /\
      CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
      chunked_graph_edge_maps_to_major_live_selected_ready
        minor major roots u v)
    (ensures
      (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
       let r =
        SpecMajorAlloc.ensure_major_head_capacity_spec
          major fp alloc_fuel needed fresh in
       let collect =
        ChunkedCheney.chunked_cheney_collect_spec
          minor r.capacity_major_out r.capacity_fp_out roots
          r.capacity_fuel_out in
       CG.mem_ce
        (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u),
         CG.MajorV (CG.fwd_morphism collect.cmc_fwd v))
        (CG.build_chunked_combined_graph
          collect.cmc_minor collect.cmc_major)))

let chunked_live_selected_graph_maps_to_major_graph_prop
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk) : prop =
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      major fp alloc_fuel needed fresh in
  let collect =
    ChunkedCheney.chunked_cheney_collect_spec
      minor r.capacity_major_out r.capacity_fp_out roots
      r.capacity_fuel_out in
  (forall (u: CG.combined_vertex).
    chunked_live_selected_graph_vertex minor major roots u ==>
    CG.mem_cv (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u))
      (CG.build_chunked_combined_graph collect.cmc_minor collect.cmc_major)) /\
  (forall (u v: CG.combined_vertex).
    chunked_live_selected_graph_edge minor major roots u v ==>
    CG.mem_ce
      (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u),
       CG.MajorV (CG.fwd_morphism collect.cmc_fwd v))
      (CG.build_chunked_combined_graph
        collect.cmc_minor collect.cmc_major))

val chunked_cheney_gc_correct_after_preflight_live_selected_graph_maps_to_major_graph
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_objects_above_minor major /\
      chunked_major_objects_are_pointer_fields major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_live_selected_graph_maps_to_major_graph_prop
        minor major fp roots alloc_fuel fresh)

val chunked_cheney_gc_correct_after_preflight_live_selected_graph_maps_to_major_graph_from_chunk_bases
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_chunks_above_zero_addr major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_live_selected_graph_maps_to_major_graph_prop
        minor major fp roots alloc_fuel fresh)

let chunked_reachable_live_graph_vertex
  (minor: minor_state) (major: MH.major_heap) (roots: seq U64.t)
  (u: CG.combined_vertex) : GTot prop =
  CG.combined_reachable
    (CG.build_chunked_combined_graph minor major)
    (CG.classify_roots roots)
    u /\
  (match u with
  | CG.MinorV v -> minor_wosize minor v > 0
  | CG.MajorV _ -> True
  | _ -> False)

let chunked_reachable_live_graph_edge
  (minor: minor_state) (major: MH.major_heap) (roots: seq U64.t)
  (u v: CG.combined_vertex) : GTot prop =
  CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
  chunked_reachable_live_graph_vertex minor major roots u /\
  chunked_reachable_live_graph_vertex minor major roots v

val chunked_reachable_live_graph_vertex_implies_live_selected_from_chunk_bases
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: seq U64.t) (u: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.chunked_collection_heap_shape minor major fp fuel /\
      CReach.chunked_roots_valid_nonblue roots major /\
      chunked_major_chunks_above_zero_addr major /\
      CReach.chunked_major_field_zero_no_minor minor major /\
      CReach.chunked_remembered_minor_edges_in_roots minor major roots /\
      chunked_reachable_live_graph_vertex minor major roots u)
    (ensures
      chunked_live_selected_graph_vertex minor major roots u)

val chunked_reachable_live_graph_edge_implies_live_selected_from_chunk_bases
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: seq U64.t) (u v: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.chunked_collection_heap_shape minor major fp fuel /\
      CReach.chunked_roots_valid_nonblue roots major /\
      chunked_major_chunks_above_zero_addr major /\
      CReach.chunked_major_field_zero_no_minor minor major /\
      CReach.chunked_remembered_minor_edges_in_roots minor major roots /\
      chunked_reachable_live_graph_edge minor major roots u v)
    (ensures
      chunked_live_selected_graph_edge minor major roots u v)

let chunked_reachable_live_graph_maps_to_major_graph_prop
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk) : prop =
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      major fp alloc_fuel needed fresh in
  let collect =
    ChunkedCheney.chunked_cheney_collect_spec
      minor r.capacity_major_out r.capacity_fp_out roots
      r.capacity_fuel_out in
  (forall (u: CG.combined_vertex).
    chunked_reachable_live_graph_vertex minor major roots u ==>
    CG.mem_cv (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u))
      (CG.build_chunked_combined_graph collect.cmc_minor collect.cmc_major)) /\
  (forall (u v: CG.combined_vertex).
    chunked_reachable_live_graph_edge minor major roots u v ==>
    CG.mem_ce
      (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u),
       CG.MajorV (CG.fwd_morphism collect.cmc_fwd v))
      (CG.build_chunked_combined_graph
        collect.cmc_minor collect.cmc_major))

val chunked_cheney_gc_correct_after_preflight_reachable_live_graph_maps_to_major_graph_from_chunk_bases
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      CReach.chunked_roots_valid_nonblue roots major /\
      chunked_major_chunks_above_zero_addr major /\
      CReach.chunked_major_field_zero_no_minor minor major /\
      CReach.chunked_remembered_minor_edges_in_roots minor major roots /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_reachable_live_graph_maps_to_major_graph_prop
        minor major fp roots alloc_fuel fresh)

let chunked_graph_edges_selected_map_to_major_edges_prop
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk) : prop =
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      major fp alloc_fuel needed fresh in
  let collect =
    ChunkedCheney.chunked_cheney_collect_spec
      minor r.capacity_major_out r.capacity_fp_out roots
      r.capacity_fuel_out in
  forall (u v: CG.combined_vertex).
    CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
    chunked_graph_edge_maps_to_major_selected_ready minor major roots u v ==>
    CG.mem_ce
      (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u),
       CG.MajorV (CG.fwd_morphism collect.cmc_fwd v))
      (CG.build_chunked_combined_graph
        collect.cmc_minor collect.cmc_major)

val chunked_cheney_gc_correct_after_preflight_graph_edges_selected_map_to_major_edges
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_objects_above_minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_graph_edges_selected_map_to_major_edges_prop
        minor major fp roots alloc_fuel fresh)

let chunked_graph_selected_ready_maps_to_major_graph_prop
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk) : prop =
  chunked_graph_vertices_membership_ready_map_to_major_vertices_prop
    minor major fp roots alloc_fuel fresh /\
  chunked_graph_edges_selected_map_to_major_edges_prop
    minor major fp roots alloc_fuel fresh

val chunked_cheney_gc_correct_after_preflight_graph_selected_ready_maps_to_major_graph
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_objects_above_minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_graph_selected_ready_maps_to_major_graph_prop
        minor major fp roots alloc_fuel fresh)

let chunked_selected_graph_vertex
  (minor: minor_state) (major: MH.major_heap) (roots: seq U64.t)
  (u: CG.combined_vertex) : GTot prop =
  CG.mem_cv u (CG.build_chunked_combined_graph minor major) /\
  chunked_graph_vertex_maps_to_major_membership_ready minor roots u

let chunked_selected_graph_edge
  (minor: minor_state) (major: MH.major_heap) (roots: seq U64.t)
  (u v: CG.combined_vertex) : GTot prop =
  CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
  chunked_graph_edge_maps_to_major_selected_ready minor major roots u v

let chunked_selected_graph_maps_to_major_graph_prop
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk) : prop =
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      major fp alloc_fuel needed fresh in
  let collect =
    ChunkedCheney.chunked_cheney_collect_spec
      minor r.capacity_major_out r.capacity_fp_out roots
      r.capacity_fuel_out in
  (forall (u: CG.combined_vertex).
    chunked_selected_graph_vertex minor major roots u ==>
    CG.mem_cv (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u))
      (CG.build_chunked_combined_graph collect.cmc_minor collect.cmc_major)) /\
  (forall (u v: CG.combined_vertex).
    chunked_selected_graph_edge minor major roots u v ==>
    CG.mem_ce
      (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u),
       CG.MajorV (CG.fwd_morphism collect.cmc_fwd v))
      (CG.build_chunked_combined_graph
        collect.cmc_minor collect.cmc_major))

val chunked_cheney_gc_correct_after_preflight_selected_graph_maps_to_major_graph
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_objects_above_minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_selected_graph_maps_to_major_graph_prop
        minor major fp roots alloc_fuel fresh)

val chunked_cheney_gc_correct_after_preflight_reachable_live_graph_maps_to_major_graph_from_chunk_bases_and_scan
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      CReach.chunked_roots_valid_nonblue roots major /\
      chunked_major_chunks_above_zero_addr major /\
      CReach.chunked_major_field_zero_no_minor minor major /\
      CRem.chunked_minor_roots_in_roots minor major roots /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_reachable_live_graph_maps_to_major_graph_prop
        minor major fp roots alloc_fuel fresh)

val chunked_cheney_gc_correct_after_preflight_reachable_live_graph_maps_to_major_graph_from_chunk_bases_and_scanned_roots
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (base_roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      CReach.chunked_roots_valid_nonblue
        (CRem.chunked_minor_collection_roots minor major base_roots) major /\
      chunked_major_chunks_above_zero_addr major /\
      CReach.chunked_major_field_zero_no_minor minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_reachable_live_graph_maps_to_major_graph_prop
        minor major fp
        (CRem.chunked_minor_collection_roots minor major base_roots)
        alloc_fuel fresh)

let chunked_reachable_live_graph_image_vertex
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (w: U64.t) : GTot prop =
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      major fp alloc_fuel needed fresh in
  let collect =
    ChunkedCheney.chunked_cheney_collect_spec
      minor r.capacity_major_out r.capacity_fp_out roots
      r.capacity_fuel_out in
  exists (u: CG.combined_vertex).
    chunked_reachable_live_graph_vertex minor major roots u /\
    CG.fwd_morphism collect.cmc_fwd u == w

let chunked_reachable_live_graph_image_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (x y: U64.t) : GTot prop =
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      major fp alloc_fuel needed fresh in
  let collect =
    ChunkedCheney.chunked_cheney_collect_spec
      minor r.capacity_major_out r.capacity_fp_out roots
      r.capacity_fuel_out in
  exists (u v: CG.combined_vertex).
    chunked_reachable_live_graph_edge minor major roots u v /\
    CG.fwd_morphism collect.cmc_fwd u == x /\
    CG.fwd_morphism collect.cmc_fwd v == y

let chunked_reachable_live_graph_image_subgraph_of_post_major_graph_prop
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk) : prop =
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      major fp alloc_fuel needed fresh in
  let collect =
    ChunkedCheney.chunked_cheney_collect_spec
      minor r.capacity_major_out r.capacity_fp_out roots
      r.capacity_fuel_out in
  let post_g =
    CG.build_chunked_combined_graph collect.cmc_minor collect.cmc_major in
  (forall (w: U64.t).
    chunked_reachable_live_graph_image_vertex
      minor major fp roots alloc_fuel fresh w ==>
    CG.mem_cv (CG.MajorV w) post_g) /\
  (forall (x y: U64.t).
    chunked_reachable_live_graph_image_edge
      minor major fp roots alloc_fuel fresh x y ==>
    CG.mem_ce (CG.MajorV x, CG.MajorV y) post_g)

let chunked_reachable_live_graph_root_images_in_post_roots_prop
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk) : prop =
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      major fp alloc_fuel needed fresh in
  let collect =
    ChunkedCheney.chunked_cheney_collect_spec
      minor r.capacity_major_out r.capacity_fp_out roots
      r.capacity_fuel_out in
  let pre_g = CG.build_chunked_combined_graph minor major in
  forall (u: CG.combined_vertex).
    Seq.mem u (CG.classify_roots roots) /\
    CG.mem_cv u pre_g /\
    (match u with
     | CG.MinorV v -> minor_wosize minor v > 0
     | CG.MajorV _ -> True
     | _ -> False) ==>
    Seq.mem (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u))
      (CG.classify_roots collect.cmc_roots)

let chunked_reachable_live_graph_image_reachable_in_post_major_graph_prop
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk) : prop =
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      major fp alloc_fuel needed fresh in
  let collect =
    ChunkedCheney.chunked_cheney_collect_spec
      minor r.capacity_major_out r.capacity_fp_out roots
      r.capacity_fuel_out in
  let post_g =
    CG.build_chunked_combined_graph collect.cmc_minor collect.cmc_major in
  forall (w: U64.t).
    chunked_reachable_live_graph_image_vertex
      minor major fp roots alloc_fuel fresh w ==>
    CG.combined_reachable post_g (CG.classify_roots collect.cmc_roots)
      (CG.MajorV w)

let chunked_reachable_live_graph_post_reachable_image_vertex
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (w: U64.t) : prop =
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      major fp alloc_fuel needed fresh in
  let collect =
    ChunkedCheney.chunked_cheney_collect_spec
      minor r.capacity_major_out r.capacity_fp_out roots
      r.capacity_fuel_out in
  let post_g =
    CG.build_chunked_combined_graph collect.cmc_minor collect.cmc_major in
  chunked_reachable_live_graph_image_vertex
    minor major fp roots alloc_fuel fresh w /\
  CG.combined_reachable post_g (CG.classify_roots collect.cmc_roots)
    (CG.MajorV w)

let chunked_reachable_live_graph_post_reachable_image_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (x y: U64.t) : prop =
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      major fp alloc_fuel needed fresh in
  let collect =
    ChunkedCheney.chunked_cheney_collect_spec
      minor r.capacity_major_out r.capacity_fp_out roots
      r.capacity_fuel_out in
  let post_g =
    CG.build_chunked_combined_graph collect.cmc_minor collect.cmc_major in
  chunked_reachable_live_graph_image_edge
    minor major fp roots alloc_fuel fresh x y /\
  CG.mem_ce (CG.MajorV x, CG.MajorV y) post_g

let chunked_reachable_live_graph_post_reachable_image_isomorphism_prop
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk) : prop =
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      major fp alloc_fuel needed fresh in
  let collect =
    ChunkedCheney.chunked_cheney_collect_spec
      minor r.capacity_major_out r.capacity_fp_out roots
      r.capacity_fuel_out in
  CG.reachable_subgraph_isomorphism
    (chunked_reachable_live_graph_vertex minor major roots)
    (chunked_reachable_live_graph_post_reachable_image_vertex
      minor major fp roots alloc_fuel fresh)
    (chunked_reachable_live_graph_edge minor major roots)
    (chunked_reachable_live_graph_post_reachable_image_edge
      minor major fp roots alloc_fuel fresh)
    collect.cmc_fwd

let chunked_reachable_live_graph_injective_prop
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk) : prop =
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      major fp alloc_fuel needed fresh in
  let collect =
    ChunkedCheney.chunked_cheney_collect_spec
      minor r.capacity_major_out r.capacity_fp_out roots
      r.capacity_fuel_out in
  forall (u v: CG.combined_vertex).
    chunked_reachable_live_graph_vertex minor major roots u /\
    chunked_reachable_live_graph_vertex minor major roots v /\
    CG.fwd_morphism collect.cmc_fwd u == CG.fwd_morphism collect.cmc_fwd v ==>
    u == v

let chunked_reachable_live_graph_image_isomorphism_prop
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk) : prop =
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      major fp alloc_fuel needed fresh in
  let collect =
    ChunkedCheney.chunked_cheney_collect_spec
      minor r.capacity_major_out r.capacity_fp_out roots
      r.capacity_fuel_out in
  CG.reachable_subgraph_isomorphism
    (chunked_reachable_live_graph_vertex minor major roots)
    (chunked_reachable_live_graph_image_vertex
      minor major fp roots alloc_fuel fresh)
    (chunked_reachable_live_graph_edge minor major roots)
    (chunked_reachable_live_graph_image_edge
      minor major fp roots alloc_fuel fresh)
    collect.cmc_fwd

let chunked_reachable_live_minor_images_injective_prop
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk) : prop =
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      major fp alloc_fuel needed fresh in
  let collect =
    ChunkedCheney.chunked_cheney_collect_spec
      minor r.capacity_major_out r.capacity_fp_out roots
      r.capacity_fuel_out in
  forall (x y: U64.t).
    chunked_reachable_live_graph_vertex minor major roots (CG.MinorV x) /\
    chunked_reachable_live_graph_vertex minor major roots (CG.MinorV y) /\
    collect.cmc_fwd x == collect.cmc_fwd y ==>
    x == y

val chunked_cheney_gc_correct_after_preflight_reachable_live_minor_images_injective_from_chunk_bases_and_scan
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      CReach.chunked_roots_valid_nonblue roots major /\
      chunked_major_chunks_above_zero_addr major /\
      CReach.chunked_major_field_zero_no_minor minor major /\
      CRem.chunked_minor_roots_in_roots minor major roots /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_reachable_live_minor_images_injective_prop
        minor major fp roots alloc_fuel fresh)

let chunked_reachable_live_minor_images_disjoint_from_major_prop
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk) : prop =
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      major fp alloc_fuel needed fresh in
  let collect =
    ChunkedCheney.chunked_cheney_collect_spec
      minor r.capacity_major_out r.capacity_fp_out roots
      r.capacity_fuel_out in
  forall (x y: U64.t).
    chunked_reachable_live_graph_vertex minor major roots (CG.MinorV x) /\
    chunked_reachable_live_graph_vertex minor major roots (CG.MajorV y) ==>
    collect.cmc_fwd x <> y

val chunked_cheney_gc_correct_after_preflight_reachable_live_minor_images_disjoint_from_major_from_chunk_bases_and_scan
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      CReach.chunked_roots_valid_nonblue roots major /\
      chunked_major_chunks_above_zero_addr major /\
      CReach.chunked_major_field_zero_no_minor minor major /\
      CRem.chunked_minor_roots_in_roots minor major roots /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_reachable_live_minor_images_disjoint_from_major_prop
        minor major fp roots alloc_fuel fresh)

val chunked_reachable_live_graph_injective_from_minor_image_facts
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      chunked_reachable_live_minor_images_injective_prop
        minor major fp roots alloc_fuel fresh /\
      chunked_reachable_live_minor_images_disjoint_from_major_prop
        minor major fp roots alloc_fuel fresh)
    (ensures
      chunked_reachable_live_graph_injective_prop
        minor major fp roots alloc_fuel fresh)

val chunked_reachable_live_graph_image_isomorphism_from_injective
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      chunked_reachable_live_graph_injective_prop
        minor major fp roots alloc_fuel fresh)
    (ensures
      chunked_reachable_live_graph_image_isomorphism_prop
        minor major fp roots alloc_fuel fresh)

val chunked_reachable_live_graph_image_subgraph_of_post_major_graph_from_maps
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      chunked_reachable_live_graph_maps_to_major_graph_prop
        minor major fp roots alloc_fuel fresh)
    (ensures
      chunked_reachable_live_graph_image_subgraph_of_post_major_graph_prop
        minor major fp roots alloc_fuel fresh)

val chunked_cheney_gc_correct_after_preflight_reachable_live_graph_injective_from_chunk_bases_and_scan
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      CReach.chunked_roots_valid_nonblue roots major /\
      chunked_major_chunks_above_zero_addr major /\
      CReach.chunked_major_field_zero_no_minor minor major /\
      CRem.chunked_minor_roots_in_roots minor major roots /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_reachable_live_graph_injective_prop
        minor major fp roots alloc_fuel fresh)

val chunked_cheney_gc_correct_after_preflight_reachable_live_graph_image_isomorphism_from_chunk_bases_and_scan
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      CReach.chunked_roots_valid_nonblue roots major /\
      chunked_major_chunks_above_zero_addr major /\
      CReach.chunked_major_field_zero_no_minor minor major /\
      CRem.chunked_minor_roots_in_roots minor major roots /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_reachable_live_graph_image_isomorphism_prop
        minor major fp roots alloc_fuel fresh)

val chunked_cheney_gc_correct_after_preflight_reachable_live_graph_image_subgraph_of_post_major_graph_from_chunk_bases_and_scan
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      CReach.chunked_roots_valid_nonblue roots major /\
      chunked_major_chunks_above_zero_addr major /\
      CReach.chunked_major_field_zero_no_minor minor major /\
      CRem.chunked_minor_roots_in_roots minor major roots /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_reachable_live_graph_image_subgraph_of_post_major_graph_prop
        minor major fp roots alloc_fuel fresh)

val chunked_cheney_gc_correct_after_preflight_reachable_live_graph_root_images_in_post_roots
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_reachable_live_graph_root_images_in_post_roots_prop
        minor major fp roots alloc_fuel fresh)

val chunked_reachable_live_graph_image_reachable_in_post_major_graph_from_roots_and_subgraph
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      chunked_reachable_live_graph_root_images_in_post_roots_prop
        minor major fp roots alloc_fuel fresh /\
      chunked_reachable_live_graph_image_subgraph_of_post_major_graph_prop
        minor major fp roots alloc_fuel fresh)
    (ensures
      chunked_reachable_live_graph_image_reachable_in_post_major_graph_prop
        minor major fp roots alloc_fuel fresh)

val chunked_reachable_live_graph_post_reachable_image_isomorphism_from_image_facts
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      chunked_reachable_live_graph_image_isomorphism_prop
        minor major fp roots alloc_fuel fresh /\
      chunked_reachable_live_graph_image_subgraph_of_post_major_graph_prop
        minor major fp roots alloc_fuel fresh /\
      chunked_reachable_live_graph_image_reachable_in_post_major_graph_prop
        minor major fp roots alloc_fuel fresh)
    (ensures
      chunked_reachable_live_graph_post_reachable_image_isomorphism_prop
        minor major fp roots alloc_fuel fresh)

val chunked_cheney_gc_correct_after_preflight_reachable_live_graph_image_reachable_in_post_major_graph_from_chunk_bases_and_scan
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      CReach.chunked_roots_valid_nonblue roots major /\
      chunked_major_chunks_above_zero_addr major /\
      CReach.chunked_major_field_zero_no_minor minor major /\
      CRem.chunked_minor_roots_in_roots minor major roots /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_reachable_live_graph_image_reachable_in_post_major_graph_prop
        minor major fp roots alloc_fuel fresh)

val chunked_cheney_gc_correct_after_preflight_reachable_live_graph_post_reachable_image_isomorphism_from_chunk_bases_and_scan
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      CReach.chunked_roots_valid_nonblue roots major /\
      chunked_major_chunks_above_zero_addr major /\
      CReach.chunked_major_field_zero_no_minor minor major /\
      CRem.chunked_minor_roots_in_roots minor major roots /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_reachable_live_graph_post_reachable_image_isomorphism_prop
        minor major fp roots alloc_fuel fresh)

val chunked_cheney_gc_correct_after_preflight_reachable_live_graph_post_reachable_image_isomorphism_from_chunk_bases_and_scanned_roots
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (base_roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      CReach.chunked_roots_valid_nonblue
        (CRem.chunked_minor_collection_roots minor major base_roots) major /\
      chunked_major_chunks_above_zero_addr major /\
      CReach.chunked_major_field_zero_no_minor minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_reachable_live_graph_post_reachable_image_isomorphism_prop
        minor major fp
        (CRem.chunked_minor_collection_roots minor major base_roots)
        alloc_fuel fresh)

val chunked_cheney_gc_correct_after_preflight_reachable_live_graph_post_reachable_image_isomorphism_from_chunk_bases_and_base_roots
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (base_roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      CReach.chunked_roots_valid_nonblue base_roots major /\
      chunked_major_chunks_above_zero_addr major /\
      CReach.chunked_major_field_zero_no_minor minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_reachable_live_graph_post_reachable_image_isomorphism_prop
        minor major fp
        (CRem.chunked_minor_collection_roots minor major base_roots)
        alloc_fuel fresh)

val chunked_cheney_gc_correct_after_preflight_policy_and_post_reachable_image_from_base_roots
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (base_roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      CReach.chunked_roots_valid_nonblue base_roots major /\
      chunked_major_chunks_above_zero_addr major /\
      CReach.chunked_major_field_zero_no_minor minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_reachable_live_graph_post_reachable_image_isomorphism_prop
        minor major fp
        (CRem.chunked_minor_collection_roots minor major base_roots)
        alloc_fuel fresh /\
      (let r =
        SpecMajorAlloc.ensure_major_head_capacity_spec
          major fp alloc_fuel (PromotionDemand.minor_promotion_demand minor + 1)
          fresh in
       chunked_major_chunks_above_zero_addr r.capacity_major_out /\
       chunked_major_objects_are_pointer_fields r.capacity_major_out /\
       CReach.chunked_major_field_zero_no_minor
         minor r.capacity_major_out))

val chunked_cheney_gc_correct_after_preflight_full_policy_and_post_reachable_image_from_base_roots
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (base_roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      CReach.chunked_roots_valid_nonblue base_roots major /\
      chunked_major_chunks_above_zero_addr major /\
      CReach.chunked_major_field_zero_no_minor minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       CReach.chunked_roots_disjoint_from_chunk base_roots fresh /\
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_reachable_live_graph_post_reachable_image_isomorphism_prop
        minor major fp
        (CRem.chunked_minor_collection_roots minor major base_roots)
        alloc_fuel fresh /\
      (let r =
        SpecMajorAlloc.ensure_major_head_capacity_spec
          major fp alloc_fuel (PromotionDemand.minor_promotion_demand minor + 1)
          fresh in
       CReach.chunked_roots_valid_nonblue base_roots r.capacity_major_out /\
        CReach.chunked_roots_valid_nonblue
          (CRem.chunked_minor_collection_roots minor major base_roots)
          r.capacity_major_out /\
        (SpecMajorAlloc.major_fl_head_wosize major fp <
         PromotionDemand.minor_promotion_demand minor + 1 ==>
         CReach.chunked_roots_disjoint_from_chunk
           (CRem.chunked_minor_collection_roots minor major base_roots)
           fresh) /\
        chunked_major_chunks_above_zero_addr r.capacity_major_out /\
        chunked_major_objects_are_pointer_fields r.capacity_major_out /\
        CReach.chunked_major_field_zero_no_minor
         minor r.capacity_major_out))

val chunked_cheney_gc_correct_after_preflight_full_policy_and_post_reachable_image_from_base_roots_value_safety
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (base_roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      CReach.chunked_roots_valid_nonblue base_roots major /\
      chunked_major_chunks_above_zero_addr major /\
      CReach.chunked_major_field_zero_no_minor minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       CReach.chunked_roots_disjoint_from_chunk base_roots fresh /\
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       (forall (obj:obj_addr).
        Seq.mem obj (MH.major_objects major) ==>
          CG.chunked_major_field_values_miss_fresh
            major fresh obj (CG.chunked_wosize_nat_of_object major obj) 0)))
    (ensures
      chunked_reachable_live_graph_post_reachable_image_isomorphism_prop
        minor major fp
        (CRem.chunked_minor_collection_roots minor major base_roots)
        alloc_fuel fresh /\
      (let r =
        SpecMajorAlloc.ensure_major_head_capacity_spec
          major fp alloc_fuel (PromotionDemand.minor_promotion_demand minor + 1)
          fresh in
       CReach.chunked_roots_valid_nonblue base_roots r.capacity_major_out /\
        CReach.chunked_roots_valid_nonblue
          (CRem.chunked_minor_collection_roots minor major base_roots)
          r.capacity_major_out /\
        (SpecMajorAlloc.major_fl_head_wosize major fp <
         PromotionDemand.minor_promotion_demand minor + 1 ==>
         CReach.chunked_roots_disjoint_from_chunk
           (CRem.chunked_minor_collection_roots minor major base_roots)
           fresh) /\
        chunked_major_chunks_above_zero_addr r.capacity_major_out /\
        chunked_major_objects_are_pointer_fields r.capacity_major_out /\
        CReach.chunked_major_field_zero_no_minor
         minor r.capacity_major_out))

let chunked_preflight_base_policy
  (minor: minor_state) (major: MH.major_heap) (base_roots: seq U64.t)
  : prop =
  CReach.chunked_roots_valid_nonblue base_roots major /\
  chunked_major_chunks_above_zero_addr major /\
  CReach.chunked_major_field_zero_no_minor minor major

let chunked_preflight_expansion_value_policy
  (major: MH.major_heap) (fp: U64.t) (base_roots: seq U64.t)
  (needed: nat) (fresh: MH.heap_chunk)
  : prop =
  CReach.chunked_roots_disjoint_from_chunk base_roots fresh /\
  MH.chunk_disjoint_from_all fresh major /\
  fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
  U64.v fresh.base >= U64.v zero_addr /\
  SpecMajorAlloc.fresh_chunk_wosize fresh >= needed /\
  (forall (obj:obj_addr).
    Seq.mem obj (MH.major_objects major) ==>
      CG.chunked_major_field_values_miss_fresh
        major fresh obj (CG.chunked_wosize_nat_of_object major obj) 0)

let chunked_minor_preflight_value_policy
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (base_roots: seq U64.t) (fresh: MH.heap_chunk)
  : prop =
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  chunked_preflight_base_policy minor major base_roots /\
  (SpecMajorAlloc.major_fl_head_wosize major fp < needed ==>
   chunked_preflight_expansion_value_policy
     major fp base_roots needed fresh)

val chunked_minor_preflight_value_policy_core_expansion_safety
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (base_roots: seq U64.t) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      chunked_minor_preflight_value_policy
        minor major fp base_roots fresh)
    (ensures
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
         PromotionDemand.minor_promotion_demand minor + 1 /\
       (forall (obj:obj_addr).
         Seq.mem obj (MH.major_objects major) ==>
           CG.chunked_major_field_values_miss_fresh
             major fresh obj (CG.chunked_wosize_nat_of_object major obj) 0)))

val chunked_cheney_gc_correct_after_preflight_full_policy_and_post_reachable_image_from_preflight_value_policy
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (base_roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_minor_preflight_value_policy
        minor major fp base_roots fresh)
    (ensures
      chunked_reachable_live_graph_post_reachable_image_isomorphism_prop
        minor major fp
        (CRem.chunked_minor_collection_roots minor major base_roots)
        alloc_fuel fresh /\
      (let r =
        SpecMajorAlloc.ensure_major_head_capacity_spec
          major fp alloc_fuel (PromotionDemand.minor_promotion_demand minor + 1)
          fresh in
       CReach.chunked_roots_valid_nonblue base_roots r.capacity_major_out /\
        CReach.chunked_roots_valid_nonblue
          (CRem.chunked_minor_collection_roots minor major base_roots)
          r.capacity_major_out /\
        (SpecMajorAlloc.major_fl_head_wosize major fp <
         PromotionDemand.minor_promotion_demand minor + 1 ==>
         CReach.chunked_roots_disjoint_from_chunk
           (CRem.chunked_minor_collection_roots minor major base_roots)
           fresh) /\
        chunked_major_chunks_above_zero_addr r.capacity_major_out /\
        chunked_major_objects_are_pointer_fields r.capacity_major_out /\
        CReach.chunked_major_field_zero_no_minor
         minor r.capacity_major_out))

val chunked_minor_preflight_value_policy_single_chunk_from_dense
  (minor: minor_state) (major: heap) (fp: U64.t)
  (base_roots: seq U64.t) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      RBridge.roots_valid_nonblue base_roots major /\
      RBridge.major_field_zero_no_minor minor major /\
      (let chunked_major = MH.single_chunk_major_heap major in
       let needed = PromotionDemand.minor_promotion_demand minor + 1 in
       SpecMajorAlloc.major_fl_head_wosize chunked_major fp < needed ==>
       CReach.chunked_roots_disjoint_from_chunk base_roots fresh /\
       MH.chunk_disjoint_from_all fresh chunked_major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >= needed /\
       (forall (obj:obj_addr).
        Seq.mem obj (MH.major_objects chunked_major) ==>
          CG.chunked_major_field_values_miss_fresh
            chunked_major fresh obj
            (CG.chunked_wosize_nat_of_object chunked_major obj) 0)))
    (ensures
      chunked_minor_preflight_value_policy
        minor (MH.single_chunk_major_heap major) fp base_roots fresh)

val chunked_minor_preflight_value_policy_core_expansion_safety_single_chunk_from_dense
  (minor: minor_state) (major: heap) (fp: U64.t)
  (base_roots: seq U64.t) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      RBridge.roots_valid_nonblue base_roots major /\
      RBridge.major_field_zero_no_minor minor major /\
      (let chunked_major = MH.single_chunk_major_heap major in
       let needed = PromotionDemand.minor_promotion_demand minor + 1 in
       SpecMajorAlloc.major_fl_head_wosize chunked_major fp < needed ==>
       CReach.chunked_roots_disjoint_from_chunk base_roots fresh /\
       MH.chunk_disjoint_from_all fresh chunked_major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >= needed /\
       (forall (obj:obj_addr).
        Seq.mem obj (MH.major_objects chunked_major) ==>
          CG.chunked_major_field_values_miss_fresh
            chunked_major fresh obj
            (CG.chunked_wosize_nat_of_object chunked_major obj) 0)))
    (ensures
      (let chunked_major = MH.single_chunk_major_heap major in
       SpecMajorAlloc.major_fl_head_wosize chunked_major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh chunked_major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
         PromotionDemand.minor_promotion_demand minor + 1 /\
       (forall (obj:obj_addr).
         Seq.mem obj (MH.major_objects chunked_major) ==>
           CG.chunked_major_field_values_miss_fresh
             chunked_major fresh obj
             (CG.chunked_wosize_nat_of_object chunked_major obj) 0)))

val chunked_cheney_gc_correct_after_preflight_policy_and_post_reachable_image_single_chunk_from_dense_roots
  (minor: minor_state) (major: heap) (fp: U64.t)
  (base_roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape
        minor (MH.single_chunk_major_heap major) fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates
        (MH.single_chunk_major_heap major) fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue
        (MH.single_chunk_major_heap major) fp alloc_fuel /\
      RBridge.roots_valid_nonblue base_roots major /\
      RBridge.major_field_zero_no_minor minor major /\
      (SpecMajorAlloc.major_fl_head_wosize
        (MH.single_chunk_major_heap major) fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh (MH.single_chunk_major_heap major) /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       (MH.single_chunk_major_heap major) fresh
       (MH.major_objects (MH.single_chunk_major_heap major)) 0))
    (ensures
      chunked_reachable_live_graph_post_reachable_image_isomorphism_prop
        minor (MH.single_chunk_major_heap major) fp
        (CRem.chunked_minor_collection_roots
          minor (MH.single_chunk_major_heap major) base_roots)
        alloc_fuel fresh /\
      (let r =
        SpecMajorAlloc.ensure_major_head_capacity_spec
          (MH.single_chunk_major_heap major) fp alloc_fuel
          (PromotionDemand.minor_promotion_demand minor + 1) fresh in
       chunked_major_chunks_above_zero_addr r.capacity_major_out /\
       chunked_major_objects_are_pointer_fields r.capacity_major_out /\
       CReach.chunked_major_field_zero_no_minor
         minor r.capacity_major_out))
