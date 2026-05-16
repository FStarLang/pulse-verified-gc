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
    // Now we need to show the edge exists in the combined graph.
    // We know: src ∈ objects zero_addr major, dst ∈ objects zero_addr major,
    // classify_major_field ms major dst == Some (MajorV dst),
    // and (src, dst) is a HeapGraph edge (meaning dst is a pointer field of src).
    //
    // From the HeapGraph edge, there exists field index i such that:
    //   get_field major src i = dst (where i is 1-indexed, 1..wosize)
    //   is_pointer_field dst = true
    //
    // The combined graph uses 0-indexed fields:
    //   read_word major (src + j*8) for j = 0..wosize-1
    //
    // The connection: get_field major src (j+1) = read_word major (src + j*8)
    //   (this is get_field_addr_eq from HeapGraph)
    //
    // We need major_field_edge_intro with:
    //   - src ∈ objects zero_addr major ✓
    //   - j < wosize ✓ (from i <= wosize, j = i-1)
    //   - ~(is_no_scan src major) — follows from having pointer fields
    //   - classify_major_field ms major (read_word major ...) == Some (MajorV dst) ✓
    //
    // The gap is extracting the field index from the HeapGraph edge.
    // HeapGraph doesn't export a reverse lemma (edge → field index).
    // We use admit here and note this requires adding all_edges_mem_rev to HeapGraph.
    admit ()

/// ---------------------------------------------------------------------------
/// Reachability bridge
/// ---------------------------------------------------------------------------

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
  = // Induction on reachability
    // Base case: dst = major_root → combined_reachable_root
    // Step case: reachable major_root u, edge (u, dst) →
    //   heapgraph_edge_implies_combined gives combined edge,
    //   combined_reachable_step gives combined reachability
    //
    // This requires reachable_ind from HeapGraph, which uses
    // the graph's reach relation. We use admit pending the
    // heapgraph_edge_implies_combined proof above.
    admit ()
