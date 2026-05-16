/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph — Combined minor+major heap graph for isomorphism proof
/// ---------------------------------------------------------------------------
///
/// Defines a graph over both minor-heap and major-heap objects, with edges
/// representing all pointer relationships (intra-minor, intra-major, and
/// cross-generational). This is the "pre-GC" graph whose reachable subgraph
/// must be isomorphic to the "post-GC" graph after minor collection.
///
/// Design: Vertices are TAGGED (MinorV / MajorV) because minor and major
/// address spaces can overlap (zero_addr is abstract, and minor addresses
/// in [8, minor_heap_size) may coincide numerically with major addresses).
/// A raw U64.t cannot distinguish generations.

module GC.Gen.CombinedGraph

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Reachability
open GC.Gen.Remembered
open GC.Gen.Promote

/// ---------------------------------------------------------------------------
/// Tagged Vertex Type
/// ---------------------------------------------------------------------------

/// A vertex is either a minor-heap object or a major-heap object.
/// The tag disambiguates overlapping address ranges.
type combined_vertex =
  | MinorV : addr:U64.t -> combined_vertex
  | MajorV : addr:U64.t -> combined_vertex

/// Decidable equality (needed for membership predicates)
let cv_eq (a b: combined_vertex) : bool =
  match a, b with
  | MinorV x, MinorV y -> x = y
  | MajorV x, MajorV y -> x = y
  | _, _ -> false

/// cv_eq is correct
val cv_eq_correct (a b: combined_vertex)
  : Lemma (cv_eq a b <==> a == b)

/// ---------------------------------------------------------------------------
/// Combined Graph Type
/// ---------------------------------------------------------------------------

type combined_edge = combined_vertex & combined_vertex

noeq type combined_graph = {
  cg_vertices : seq combined_vertex;
  cg_edges    : seq combined_edge;
}

/// Vertex membership
let mem_cv (v: combined_vertex) (g: combined_graph) : bool =
  Seq.mem v g.cg_vertices

/// Edge membership
let mem_ce (e: combined_edge) (g: combined_graph) : bool =
  Seq.mem e g.cg_edges

/// Well-formedness: all edge endpoints are vertices
let combined_graph_wf (g: combined_graph) : prop =
  forall (e: combined_edge). mem_ce e g ==>
    (mem_cv (fst e) g /\ mem_cv (snd e) g)

/// No duplicate vertices
let combined_vertices_distinct (g: combined_graph) : prop =
  forall (i j: nat). i < Seq.length g.cg_vertices /\ j < Seq.length g.cg_vertices /\ i <> j ==>
    Seq.index g.cg_vertices i <> Seq.index g.cg_vertices j

/// ---------------------------------------------------------------------------
/// Graph Construction
/// ---------------------------------------------------------------------------

/// Classify a field value from a minor-heap object.
/// Returns the target vertex if the field is a pointer.
val classify_minor_field (ms: minor_state) (major: heap) (v: U64.t)
  : GTot (option combined_vertex)

/// Classify a field value from a major-heap object.
/// Returns the target vertex if the field is a pointer.
val classify_major_field (ms: minor_state) (major: heap) (v: U64.t)
  : GTot (option combined_vertex)

/// Build edges from a single minor-heap object
val minor_object_edges (ms: minor_state) (major: heap) (obj: U64.t)
  : GTot (seq combined_edge)

/// Build edges from a single major-heap object
val major_object_edges (ms: minor_state) (major: heap) (obj: obj_addr)
  : GTot (seq combined_edge)

/// Construct the combined graph from a generational state.
/// Vertices: all objects in minor live set + all objects in major heap.
/// Edges: pointer fields from both generations.
val build_combined_graph (ms: minor_state) (major: heap) (roots: seq U64.t)
  : GTot combined_graph

/// ---------------------------------------------------------------------------
/// Well-Formedness of Construction
/// ---------------------------------------------------------------------------

/// The constructed graph is well-formed (all edge endpoints are vertices)
val build_combined_graph_wf (ms: minor_state) (major: heap) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\ minor_wf ms)
          (ensures combined_graph_wf (build_combined_graph ms major roots))

/// The constructed graph has distinct vertices
val build_combined_graph_distinct (ms: minor_state) (major: heap) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\ minor_wf ms)
          (ensures combined_vertices_distinct (build_combined_graph ms major roots))

/// ---------------------------------------------------------------------------
/// Vertex Membership Characterization
/// ---------------------------------------------------------------------------

/// A MinorV is a vertex iff it's in the live set
val minor_vertex_mem (ms: minor_state) (major: heap) (roots: seq U64.t) (a: U64.t)
  : Lemma (ensures
      mem_cv (MinorV a) (build_combined_graph ms major roots) <==>
      Seq.mem a (minor_reachable ms (Seq.append roots (minor_roots_from_major major))))

/// A MajorV is a vertex iff it's an allocated major object
val major_vertex_mem (ms: minor_state) (major: heap) (roots: seq U64.t) (a: U64.t)
  : Lemma (requires well_formed_heap major)
          (ensures
            mem_cv (MajorV a) (build_combined_graph ms major roots) <==>
            Seq.mem (a <: obj_addr) (objects zero_addr major))

/// ---------------------------------------------------------------------------
/// GC Morphism (forwarding map as graph homomorphism)
/// ---------------------------------------------------------------------------

/// The morphism sends minor objects to their forwarded major addresses
/// and leaves major objects unchanged.
let gc_morphism (fwd: forwarding_map) (v: combined_vertex) : GTot combined_vertex =
  match v with
  | MinorV a -> if fwd a <> 0UL then MajorV (fwd a) else MinorV a
  | MajorV a -> MajorV a

/// ---------------------------------------------------------------------------
/// Reachability in Combined Graph
/// ---------------------------------------------------------------------------

/// A vertex is reachable from a set of root vertices via edges
val combined_reachable (g: combined_graph) (roots: seq combined_vertex) (v: combined_vertex)
  : GTot prop

/// Roots are reachable
val combined_reachable_root (g: combined_graph) (roots: seq combined_vertex) (v: combined_vertex)
  : Lemma (requires Seq.mem v roots /\ mem_cv v g)
          (ensures combined_reachable g roots v)

/// Successor closure
val combined_reachable_step (g: combined_graph) (roots: seq combined_vertex)
                            (u v: combined_vertex)
  : Lemma (requires combined_reachable g roots u /\ mem_ce (u, v) g)
          (ensures combined_reachable g roots v)

/// ---------------------------------------------------------------------------
/// Bridge: combined reachability ≡ minor_reachable ∪ major reachable
/// ---------------------------------------------------------------------------

/// Classify program roots as combined vertices
let classify_root (ms: minor_state) (r: U64.t) : GTot combined_vertex =
  if is_minor_pointer r then MinorV r else MajorV r

/// Classify a sequence of roots
val classify_roots (ms: minor_state) (roots: seq U64.t)
  : GTot (seq combined_vertex)

/// Every minor-reachable object is reachable in the combined graph
val minor_reachable_implies_combined
  (ms: minor_state) (major: heap) (roots: seq U64.t) (a: U64.t)
  : Lemma (requires
      well_formed_heap major /\ minor_wf ms /\
      Seq.mem a (minor_reachable ms (Seq.append roots (minor_roots_from_major major))))
    (ensures
      combined_reachable (build_combined_graph ms major roots)
                         (classify_roots ms roots) (MinorV a))

/// Every major-heap object reachable in the major graph is reachable in the combined graph
val major_reachable_implies_combined
  (ms: minor_state) (major: heap) (roots: seq U64.t) (a: obj_addr)
  : Lemma (requires
      well_formed_heap major /\ minor_wf ms /\
      (exists (r: obj_addr). Seq.mem r (objects zero_addr major) /\
        (* r is a root or reachable from a root through major-only paths *)
        True (* placeholder — full characterization in .fst *)))
    (ensures
      combined_reachable (build_combined_graph ms major roots)
                         (classify_roots ms roots) (MajorV a))
