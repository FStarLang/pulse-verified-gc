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

#push-options "--split_queries always --z3rlimit 5 --fuel 1 --ifuel 0"
private let minor_major_edge_target_above_minor_witness
  (minor: minor_state) (major: MH.major_heap)
  (src: U64.t) (dst: U64.t)
  : Lemma
    (requires
      chunked_major_objects_above_minor major /\
      CG.mem_ce (CG.MinorV src, CG.MajorV dst)
        (CG.build_chunked_combined_graph minor major))
    (ensures
      exists (dst_obj: obj_addr).
        dst_obj == dst /\ U64.v dst_obj >= minor_heap_size)
  =
  CG.chunked_minor_edge_elim minor major src (CG.MajorV dst);
  let i =
    FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun i ->
        i < minor_wosize minor src /\
        CG.chunked_classify_minor_field
          minor major (minor_read_field minor src i) == Some (CG.MajorV dst)) in
  let field_v = minor_read_field minor src i in
  assert (CG.chunked_classify_minor_field minor major field_v ==
          Some (CG.MajorV dst));
  CG.chunked_classify_minor_field_inv_major minor major field_v dst;
  let dst_obj = (field_v <: obj_addr) in
  assert (dst_obj == dst);
  assert (Seq.mem dst_obj (MH.major_objects major));
  assert (U64.v dst_obj >= minor_heap_size)

private let major_major_edge_target_above_minor_witness
  (minor: minor_state) (major: MH.major_heap)
  (src: obj_addr) (dst: U64.t)
  : Lemma
    (requires
      chunked_major_objects_above_minor major /\
      CG.mem_ce (CG.MajorV src, CG.MajorV dst)
        (CG.build_chunked_combined_graph minor major))
    (ensures
      exists (dst_obj: obj_addr).
        dst_obj == dst /\ U64.v dst_obj >= minor_heap_size)
  =
  CG.chunked_major_edge_elim minor major src (CG.MajorV dst);
  let i =
    FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun i ->
        exists (field_addr: hp_addr).
        exists (v: U64.t).
          i < CG.chunked_wosize_nat_of_object major src /\
          CG.chunked_major_field_slot src i == Some field_addr /\
          MH.read_word_in_major major field_addr == Some v /\
          CG.chunked_classify_major_field minor major v == Some (CG.MajorV dst)) in
  let field_addr =
    FStar.IndefiniteDescription.indefinite_description_ghost hp_addr
      (fun field_addr ->
        exists (v: U64.t).
          i < CG.chunked_wosize_nat_of_object major src /\
          CG.chunked_major_field_slot src i == Some field_addr /\
          MH.read_word_in_major major field_addr == Some v /\
          CG.chunked_classify_major_field minor major v == Some (CG.MajorV dst)) in
  let field_v =
    FStar.IndefiniteDescription.indefinite_description_ghost U64.t
      (fun v ->
        i < CG.chunked_wosize_nat_of_object major src /\
        CG.chunked_major_field_slot src i == Some field_addr /\
        MH.read_word_in_major major field_addr == Some v /\
        CG.chunked_classify_major_field minor major v == Some (CG.MajorV dst)) in
  assert (CG.chunked_classify_major_field minor major field_v ==
          Some (CG.MajorV dst));
  CG.chunked_classify_major_field_inv_major minor major field_v dst;
  let dst_obj = (field_v <: obj_addr) in
  assert (dst_obj == dst);
  assert (Seq.mem dst_obj (MH.major_objects major));
  assert (U64.v dst_obj >= minor_heap_size)
#pop-options

#push-options "--split_queries always --z3rlimit 5 --fuel 1 --ifuel 0"
let chunked_graph_edge_maps_to_major_edge_targets_ready_implies_nonblue_sources_above_minor_targets_ready
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
  =
  match u, v with
  | CG.MinorV src, CG.MinorV dst -> ()
  | CG.MinorV src, CG.MajorV dst ->
    minor_major_edge_target_above_minor_witness minor major src dst
  | CG.MajorV src, CG.MajorV dst ->
    let src_obj =
      FStar.IndefiniteDescription.indefinite_description_ghost obj_addr
        (fun src_obj ->
          src_obj == src /\
          Seq.mem src_obj (MH.major_objects major) /\
          ~(GenInv.chunked_is_blue major src_obj)) in
    assert (src_obj == src);
    assert (CG.mem_ce (CG.MajorV src_obj, CG.MajorV dst)
              (CG.build_chunked_combined_graph minor major));
    major_major_edge_target_above_minor_witness minor major src_obj dst
  | CG.MajorV src, CG.MinorV dst -> ()
  | _, _ -> assert False
#pop-options

#push-options "--split_queries always --z3rlimit 5 --fuel 1 --ifuel 0"
let chunked_cheney_gc_correct_after_preflight_graph_edge_edge_targets_maps_to_major_edge
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
  =
  chunked_graph_edge_maps_to_major_edge_targets_ready_implies_nonblue_sources_above_minor_targets_ready
    minor major fp roots alloc_fuel fresh u v;
  CC.chunked_cheney_gc_correct_after_preflight_graph_edge_nonblue_sources_above_minor_targets_maps_to_major_edge
    minor major fp roots alloc_fuel fresh u v
#pop-options

#push-options "--split_queries always --z3rlimit 5 --fuel 1 --ifuel 0"
let chunked_cheney_gc_correct_after_preflight_graph_edges_edge_targets_map_to_major_edges
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
  =
  let prove_for_u (u: CG.combined_vertex)
    : Lemma
      (ensures
        forall (v: CG.combined_vertex).
          CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
          chunked_graph_edge_maps_to_major_edge_targets_ready
            minor major fp roots alloc_fuel fresh u v ==>
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
    =
    let prove_for_v (v: CG.combined_vertex)
      : Lemma
        (requires
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
      =
      chunked_cheney_gc_correct_after_preflight_graph_edge_edge_targets_maps_to_major_edge
        minor major fp roots alloc_fuel fresh u v
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires prove_for_v)
  in
  FStar.Classical.forall_intro prove_for_u
#pop-options
