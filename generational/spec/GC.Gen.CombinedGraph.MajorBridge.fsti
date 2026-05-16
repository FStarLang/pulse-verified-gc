/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph.MajorBridge — HeapGraph ↔ CombinedGraph correspondence
/// ---------------------------------------------------------------------------
///
/// Bridge between HeapGraph edges (create_graph major) and CombinedGraph edges
/// (build_combined_graph ms major) for major objects.
///
/// Key insight: with major_starts_after_minor, pointer fields in the major
/// heap (satisfying is_pointer_field) cannot be minor pointers. So:
///   - HeapGraph edges from major objects → only major→major
///   - CombinedGraph also has major→minor edges (via classify_major_field)
///   - HeapGraph edges ⊆ CombinedGraph major edges (forward direction)
///
/// The backward direction (combined major→major edge → HeapGraph edge)
/// also holds because both use the same field reads.

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

/// Major objects are not minor pointers (uses major_starts_after_minor axiom).
/// This is the key disjointness fact bridging the two graph constructions.
val major_object_not_minor_pointer (major: heap) (v: obj_addr)
  : Lemma (requires Seq.mem v (objects zero_addr major))
          (ensures ~(is_minor_pointer v))

/// HeapGraph pointer fields from major objects are not minor pointers.
/// Consequence: HeapGraph edges from major objects always point to major objects.
val pointer_field_not_minor (v: U64.t)
  : Lemma (requires HeapGraph.is_pointer_field v)
          (ensures ~(is_minor_pointer v))

/// Forward bridge: if (src, dst) is an edge in create_graph major,
/// then (MajorV src, MajorV dst) is an edge in build_combined_graph ms major.
val heapgraph_edge_implies_combined
  (ms: minor_state) (major: heap) (src dst: obj_addr)
  : Lemma (requires
      well_formed_heap major /\
      minor_wf ms /\
      graph_wf (create_graph major) /\
      Seq.mem (src, dst) (create_graph major).edges)
    (ensures
      mem_ce (MajorV src, MajorV dst) (build_combined_graph ms major))

/// Every HeapGraph-reachable vertex from major roots is combined-reachable.
val heapgraph_reachable_implies_combined
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
