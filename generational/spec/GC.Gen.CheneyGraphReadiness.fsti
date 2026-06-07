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

/// Heap-level separation fact needed to discharge major-target update stability
/// from graph-edge membership: every active major object address lies outside
/// the minor range.  This is intentionally separate from `major_heap`'s pure
/// well-formedness, which only records chunk disjointness.
let chunked_major_objects_above_minor (major: MH.major_heap) : prop =
  forall (obj: obj_addr).
    Seq.mem obj (MH.major_objects major) ==> U64.v obj >= minor_heap_size

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
