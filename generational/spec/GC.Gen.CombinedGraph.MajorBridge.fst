/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph.MajorBridge — Implementation
/// ---------------------------------------------------------------------------

module GC.Gen.CombinedGraph.MajorBridge

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

module HeapGraph = GC.Spec.HeapGraph

/// ---------------------------------------------------------------------------
/// Disjointness lemmas
/// ---------------------------------------------------------------------------

/// Major objects have addresses > zero_addr > minor_heap_size,
/// so they cannot satisfy is_minor_pointer.
let major_object_not_minor_pointer (major: heap) (v: obj_addr)
  : Lemma (requires Seq.mem v (objects zero_addr major))
          (ensures ~(is_minor_pointer v))
  = major_starts_after_minor ();
    objects_addresses_gt_start zero_addr major v
    // v > zero_addr >= minor_heap_size, so v >= minor_heap_size
    // is_minor_pointer v requires v < minor_heap_size → contradiction

/// Pointer fields (from HeapGraph) have v >= zero_addr + mword.
/// With major_starts_after_minor, this gives v >= minor_heap_size + mword > minor_heap_size.
let pointer_field_not_minor (v: U64.t)
  : Lemma (requires HeapGraph.is_pointer_field v)
          (ensures ~(is_minor_pointer v))
  = major_starts_after_minor ()
    // is_pointer_field v gives v >= zero_addr + mword >= minor_heap_size + 8
    // is_minor_pointer v requires v < minor_heap_size → contradiction

/// ---------------------------------------------------------------------------
/// Forward bridge: HeapGraph edge → CombinedGraph edge
/// ---------------------------------------------------------------------------

/// Helper: if (src, dst) is a HeapGraph edge, then dst is a major object
/// and classify_major_field returns Some (MajorV dst).
private let heapgraph_edge_classify
  (ms: minor_state) (major: heap) (src dst: obj_addr)
  : Lemma (requires
      well_formed_heap major /\
      graph_wf (create_graph major) /\
      Seq.mem (src, dst) (create_graph major).edges)
    (ensures
      is_val_addr dst /\
      Seq.mem dst (objects zero_addr major) /\
      ~(is_minor_pointer dst /\ Seq.mem dst (minor_objects ms)) /\
      classify_major_field ms major dst == Some (MajorV dst))
  = // From graph_wf: edge endpoints are vertices
    let g = create_graph major in
    // graph_wf says: edge ∈ g.edges ==> fst/snd ∈ g.vertices
    assert (Seq.mem dst g.vertices);
    graph_vertices_mem major dst;
    // dst ∈ objects zero_addr major
    // is_val_addr follows from being an object
    objects_addresses_gt_start zero_addr major dst;
    is_val_addr_spec dst;
    // dst is not a minor pointer (disjointness)
    major_object_not_minor_pointer major dst;
    // Therefore classify_major_field returns MajorV dst
    classify_major_field_major ms major dst

/// The main forward bridge, but we first need to decompose the edge into
/// a field read. HeapGraph edges come from object_edges which come from
/// get_pointer_fields. We need a reverse lemma: edge ∈ all_edges →
/// ∃ i. get_field g src i = dst.
///
/// For now, we prove this under an additional assumption that provides
/// the field index directly. The full proof requires a reverse lemma
/// in HeapGraph (all_edges_mem_rev), which is infrastructure we'd add
/// to common/.
let heapgraph_edge_implies_combined
  (ms: minor_state) (major: heap) (src dst: obj_addr)
  : Lemma (requires
      well_formed_heap major /\
      minor_wf ms /\
      graph_wf (create_graph major) /\
      Seq.mem (src, dst) (create_graph major).edges)
    (ensures
      mem_ce (MajorV src, MajorV dst) (build_combined_graph ms major))
  = let g = create_graph major in
    // src and dst are both vertices (graph_wf)
    graph_vertices_mem major src;
    graph_vertices_mem major dst;
    // Classify dst as MajorV
    heapgraph_edge_classify ms major src dst;
    // Get field index from HeapGraph infrastructure
    objects_is_vertex_set major;
    // From well_formed_heap + membership, get object_fits_in_heap
    wf_object_size_bound major src;
    HeapGraph.object_fits_in_heap_intro src major;
    // Get edge in object_edges via source membership
    HeapGraph.all_edges_source_membership major (objects zero_addr major) src dst;
    // (src,dst) ∈ object_edges major src implies get_pointer_fields is non-empty
    // which implies ~(is_no_scan src major)
    HeapGraph.object_edges_dst_in_pointer_fields major src dst;
    // get_pointer_fields_aux_mem_rev gives us the existential field index
    let ws = wosize_of_object src major in
    HeapGraph.get_pointer_fields_aux_mem_rev major src 1UL ws dst;
    // Now we have: ∃ j >= 1. j <= wosize ∧ get_field major src j == dst ∧ is_pointer_field dst
    // Extract the witness using indefinite_description_ghost
    let p = fun (j: U64.t) -> U64.v j >= 1 /\ U64.v j <= U64.v ws /\
                               HeapGraph.get_field major src j == dst /\
                               HeapGraph.is_pointer_field dst in
    let j = FStar.IndefiniteDescription.indefinite_description_ghost U64.t p in
    // Convert to 0-indexed: i = U64.v j - 1
    let i = U64.v j - 1 in
    // Use get_field_addr_eq to connect get_field (1-indexed) to read_word (0-indexed)
    HeapGraph.get_field_addr_eq major src j;
    // get_field_addr_eq gives: get_field major src j == read_word major (src + (j-1)*8)
    // So read_word major (src + i*8) == dst
    // Now invoke major_field_edge_intro
    major_field_edge_intro ms major src i (MajorV dst)

/// ---------------------------------------------------------------------------
/// Reachability bridge
/// ---------------------------------------------------------------------------

/// HeapGraph reachability → combined reachability (by induction on reach witness)
let rec heapgraph_reach_implies_combined_aux
  (ms: minor_state) (major: heap)
  (roots: seq combined_vertex)
  (major_root: obj_addr{mem_graph_vertex (create_graph major) major_root})
  (dst: obj_addr{mem_graph_vertex (create_graph major) dst})
  (r: reach (create_graph major) major_root dst)
  : Lemma (requires
      well_formed_heap major /\
      minor_wf ms /\
      graph_wf (create_graph major) /\
      Seq.mem (MajorV major_root) roots /\
      Seq.mem major_root (objects zero_addr major))
    (ensures
      combined_reachable (build_combined_graph ms major) roots (MajorV dst))
    (decreases r)
  = let g = create_graph major in
    let cg = build_combined_graph ms major in
    match r with
    | ReachRefl _ ->
      // dst = major_root, which is in roots
      major_vertex_char ms major major_root;
      combined_reachable_root cg roots (MajorV major_root)
    | ReachTrans _ mid _ r_to_mid ->
      // mid has type vertex_id with mem_graph_vertex refinement
      // Prove it satisfies obj_addr (>= mword) via coerce_mem_is_obj_addr
      HeapGraph.coerce_mem_is_obj_addr (objects zero_addr major) mid;
      HeapGraph.coerce_mem_is_obj_addr (objects zero_addr major) dst;
      let mid_o : obj_addr = mid in
      let dst_o : obj_addr = dst in
      // mid_o ∈ objects (from graph_vertices_mem reverse direction)
      graph_vertices_mem major mid_o;
      graph_vertices_mem major dst_o;
      // By IH: combined_reachable cg roots (MajorV mid_o)
      heapgraph_reach_implies_combined_aux ms major roots major_root mid_o r_to_mid;
      // edge (mid_o, dst_o) in create_graph → combined edge
      heapgraph_edge_implies_combined ms major mid_o dst_o;
      // combined_reachable step
      combined_reachable_step cg roots (MajorV mid_o) (MajorV dst_o)

/// HeapGraph reachability → combined reachability (by induction on reach)
let heapgraph_reachable_implies_combined
  (ms: minor_state) (major: heap)
  (roots: seq combined_vertex)
  (major_root: obj_addr) (dst: obj_addr)
  : Lemma (requires
      well_formed_heap major /\
      minor_wf ms /\
      graph_wf (create_graph major) /\
      Seq.mem (MajorV major_root) roots /\
      Seq.mem major_root (objects zero_addr major) /\
      mem_graph_vertex (create_graph major) major_root /\
      mem_graph_vertex (create_graph major) dst /\
      reachable (create_graph major) major_root dst)
    (ensures
      combined_reachable (build_combined_graph ms major) roots (MajorV dst))
  = // Extract the reach witness from the existential
    let g = create_graph major in
    let p = fun (r: reach g major_root dst) -> True in
    let r = FStar.IndefiniteDescription.indefinite_description_ghost (reach g major_root dst) p in
    heapgraph_reach_implies_combined_aux ms major roots major_root dst r
