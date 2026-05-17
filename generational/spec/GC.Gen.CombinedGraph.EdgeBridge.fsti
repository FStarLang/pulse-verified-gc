/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph.EdgeBridge — Combined edge → mc_major edge
/// ---------------------------------------------------------------------------
///
/// Proves the "bridge" assumption in the isomorphism theorem:
/// for each combined edge (u, v) where both endpoints are reachable,
/// the morphism image (φ(u), φ(v)) is an edge in create_graph mc.mc_major.
///
/// Decomposes into 4 cases by source/target constructor:
///   Case 4 (MajorV→MajorV): field preserved through promotion (unchanged)
///   Case 3 (MajorV→MinorV): field rewritten to fwd(dst)
///   Case 1 (MinorV→MinorV): promoted field becomes fwd(dst)
///   Case 2 (MinorV→MajorV): promoted field preserved as dst
///
/// Each case chains:
///   1. CombinedGraph edge elimination → field index + classification
///   2. EdgePreservation → field value in mc_major
///   3. HeapGraph.pointer_field_is_graph_edge → graph edge

module GC.Gen.CombinedGraph.EdgeBridge

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

open GC.Spec.HeapGraph
module HeapGraph = GC.Spec.HeapGraph
module AllocLemmas = GC.Spec.Allocator.Lemmas

/// ---------------------------------------------------------------------------
/// 0-based → 1-based field index bridge
/// ---------------------------------------------------------------------------

/// Converts CombinedGraph's 0-based field index to HeapGraph's 1-based index.
/// CombinedGraph reads field i at address (obj + i*8).
/// HeapGraph reads field j at address (obj + (j-1)*8) via get_field.
/// So j = i + 1.
val field_index_bridge (h: heap) (obj: obj_addr) (i: nat)
  : Lemma (requires i < U64.v (wosize_of_object obj h) /\
                    object_fits_in_heap obj h /\
                    i + 1 < pow2 54)
          (ensures (let j = U64.uint_to_t (i + 1) in
                    U64.v j >= 1 /\
                    U64.v j <= U64.v (wosize_of_object obj h) /\
                    U64.v obj + i * 8 + 8 <= heap_size /\
                    (U64.v obj + i * 8) % 8 == 0 /\
                    get_field h obj j == read_word h (U64.uint_to_t (U64.v obj + i * 8))))

/// ---------------------------------------------------------------------------
/// Case 4: Major→Major (field unchanged through promotion)
/// ---------------------------------------------------------------------------

/// When a major-heap edge (MajorV src, MajorV dst) exists in the combined graph,
/// and both endpoints are reachable, the edge (src, dst) exists in create_graph mc_major.
///
/// Since fwd_morphism is identity on major vertices, φ(MajorV src) = src and
/// φ(MajorV dst) = dst, so this directly gives the required mc_major edge.
val bridge_case_major_major
  (ms: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src dst: obj_addr)
  : Lemma
    (requires
      // src→dst is a major→major edge in the combined graph
      mem_ce (MajorV src, MajorV dst) (build_combined_graph ms major) /\
      // src is a non-blue allocated object that avoids the free list
      Seq.mem src (objects zero_addr major) /\
      ~(is_blue src major) /\
      // Allocator + well-formedness
      well_formed_heap major /\
      no_scan_invariant major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      AllocLemmas.chain_avoids major fp src (heap_size / U64.v mword) = true /\
      // Live set / promotion context
      (let live_set = live_set_of ms major roots in
       let prom_res = promote_all_spec ms major fp live_set in
       // src survives promotion (preserved in major_final)
       Seq.mem src (objects zero_addr prom_res.major_final) /\
       wosize_of_object src prom_res.major_final == wosize_of_object src major /\
       is_blue src prom_res.major_final = false /\
       is_no_scan src prom_res.major_final = false /\
       // mc_major graph well-formedness
       (let mc = minor_collect_spec ms major fp roots in
        well_formed_heap mc.mc_major /\
        graph_wf (create_graph mc.mc_major))))
    (ensures
      (let mc = minor_collect_spec ms major fp roots in
       Seq.mem (src, dst) (create_graph mc.mc_major).edges))

/// ---------------------------------------------------------------------------
/// Case 3: Major→Minor (field forwarded by update_major_pointers)
/// ---------------------------------------------------------------------------

/// When a major-heap object `src` has a field pointing to a minor object `dst`,
/// and dst is promoted (fwd dst ≠ 0), the mc_major heap has field = fwd(dst).
/// Since fwd_morphism(MinorV dst) = fwd(dst), this gives an edge (src, fwd(dst))
/// in create_graph mc_major.
val bridge_case_major_minor
  (ms: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: obj_addr) (dst: U64.t)
  : Lemma
    (requires
      // src→MinorV dst is a major→minor edge in the combined graph
      mem_ce (MajorV src, MinorV dst) (build_combined_graph ms major) /\
      // src is a non-blue allocated object that avoids the free list
      Seq.mem src (objects zero_addr major) /\
      ~(is_blue src major) /\
      // Allocator + well-formedness
      well_formed_heap major /\
      no_scan_invariant major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      AllocLemmas.chain_avoids major fp src (heap_size / U64.v mword) = true /\
      // Live set / promotion context
      (let live_set = live_set_of ms major roots in
       let prom_res = promote_all_spec ms major fp live_set in
       // dst is promoted
       Seq.mem dst live_set /\ prom_res.fwd_map dst <> 0UL /\
       // src survives promotion
       Seq.mem src (objects zero_addr prom_res.major_final) /\
       wosize_of_object src prom_res.major_final == wosize_of_object src major /\
       is_blue src prom_res.major_final = false /\
       is_no_scan src prom_res.major_final = false /\
       // fwd(dst) is a valid object in mc_major
       (let mc = minor_collect_spec ms major fp roots in
        let fwd_dst : U64.t = prom_res.fwd_map dst in
        U64.v fwd_dst >= U64.v mword /\ U64.v fwd_dst < heap_size /\
        U64.v fwd_dst % U64.v mword == 0 /\
        Seq.mem (fwd_dst <: obj_addr) (objects zero_addr mc.mc_major) /\
        well_formed_heap mc.mc_major /\
        graph_wf (create_graph mc.mc_major))))
    (ensures
      (let live_set = live_set_of ms major roots in
       let prom_res = promote_all_spec ms major fp live_set in
       let mc = minor_collect_spec ms major fp roots in
       let fwd_dst : hp_addr = prom_res.fwd_map dst in
       Seq.mem ((src <: hp_addr), fwd_dst) (create_graph mc.mc_major).edges))

/// ---------------------------------------------------------------------------
/// Cases 1 & 2: Minor→Minor and Minor→Major (promoted copy fields)
/// ---------------------------------------------------------------------------

/// When a promoted minor object's field points to another minor object (Case 1)
/// or a major object (Case 2), the promoted copy's field in mc_major has the
/// correct value (fwd(dst) for Case 1, dst for Case 2), giving a HeapGraph edge.
///
/// This uses field_correspondence (from GC.Gen.Correctness) + field_index_bridge.
val bridge_case_minor
  (ms: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: U64.t) (dst: combined_vertex)
  : Lemma
    (requires
      // MinorV src → dst is an edge in the combined graph
      mem_ce (MinorV src, dst) (build_combined_graph ms major) /\
      // src is in the live set and gets promoted
      (let live_set = live_set_of ms major roots in
       let prom_res = promote_all_spec ms major fp live_set in
       let mc = minor_collect_spec ms major fp roots in
       Seq.mem src live_set /\ prom_res.fwd_map src <> 0UL /\
       // field_correspondence holds
       GC.Gen.Correctness.field_correspondence ms major mc.mc_major prom_res.fwd_map roots /\
       // fwd(src) is a valid object in mc_major
       (let fwd_src : U64.t = prom_res.fwd_map src in
        U64.v fwd_src >= U64.v mword /\ U64.v fwd_src < heap_size /\
        U64.v fwd_src % U64.v mword == 0 /\
        Seq.mem (fwd_src <: obj_addr) (objects zero_addr mc.mc_major) /\
        object_fits_in_heap (fwd_src <: obj_addr) mc.mc_major /\
        // wosize of promoted copy matches minor wosize
        U64.v (wosize_of_object (fwd_src <: obj_addr) mc.mc_major) == minor_wosize ms src) /\
       // dst target info
       (match dst with
        | MinorV d -> Seq.mem d live_set /\ prom_res.fwd_map d <> 0UL /\
                      U64.v (prom_res.fwd_map d) >= U64.v mword /\
                      U64.v (prom_res.fwd_map d) < heap_size /\
                      U64.v (prom_res.fwd_map d) % U64.v mword == 0 /\
                      Seq.mem (prom_res.fwd_map d <: obj_addr) (objects zero_addr mc.mc_major)
        | MajorV d -> U64.v d >= U64.v mword /\ U64.v d < heap_size /\
                      U64.v d % U64.v mword == 0 /\
                      Seq.mem (d <: obj_addr) (objects zero_addr mc.mc_major)) /\
       well_formed_heap mc.mc_major /\
       graph_wf (create_graph mc.mc_major)))
    (ensures
      (let live_set = live_set_of ms major roots in
       let prom_res = promote_all_spec ms major fp live_set in
       let mc = minor_collect_spec ms major fp roots in
       let fwd_src : hp_addr = prom_res.fwd_map src in
       let fwd_dst : hp_addr = (match dst with
                                | MinorV d -> prom_res.fwd_map d
                                | MajorV d -> d) in
       Seq.mem (fwd_src, fwd_dst) (create_graph mc.mc_major).edges))
