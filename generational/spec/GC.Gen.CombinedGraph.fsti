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

/// cv_eq is decidable (F* derives this for inductive types, but we state it
/// explicitly for use in Seq.mem which requires eqtype)
val cv_eqtype : squash (hasEq combined_vertex)

/// ---------------------------------------------------------------------------
/// Combined Graph Type
/// ---------------------------------------------------------------------------

type combined_edge = combined_vertex & combined_vertex

noeq type combined_graph = {
  cg_vertices : seq combined_vertex;
  cg_edges    : seq combined_edge;
}

/// Vertex membership
let mem_cv (v: combined_vertex) (g: combined_graph) : GTot bool =
  Seq.mem v g.cg_vertices

/// Edge membership
let mem_ce (e: combined_edge) (g: combined_graph) : GTot bool =
  Seq.mem e g.cg_edges

/// Well-formedness: all edge endpoints are vertices
let combined_graph_wf (g: combined_graph) : prop =
  forall (e: combined_edge). mem_ce e g ==>
    (mem_cv (fst e) g /\ mem_cv (snd e) g)

/// ---------------------------------------------------------------------------
/// Field Classification
/// ---------------------------------------------------------------------------

/// Classify a field value read from a minor-heap object.
/// A field is a pointer if it refers to another minor object or a major object.
val classify_minor_field (ms: minor_state) (major: heap) (v: U64.t)
  : GTot (option combined_vertex)

/// Characterization: classify_minor_field returns MinorV v when v is a minor object
val classify_minor_field_minor (ms: minor_state) (major: heap) (v: U64.t)
  : Lemma (requires is_minor_addr v /\ Seq.mem v (minor_objects ms))
          (ensures classify_minor_field ms major v == Some (MinorV v))

/// Classify a field value read from a major-heap object.
/// A field is a pointer if it refers to a major object or a minor object.
val classify_major_field (ms: minor_state) (major: heap) (v: U64.t)
  : GTot (option combined_vertex)

/// Characterization: classify_major_field returns MajorV v when v is a major object
/// and not a minor pointer
val classify_major_field_major (ms: minor_state) (major: heap) (v: U64.t)
  : Lemma (requires is_val_addr v /\ Seq.mem v (objects zero_addr major) /\
                    ~(is_minor_pointer v /\ Seq.mem v (minor_objects ms)))
          (ensures classify_major_field ms major v == Some (MajorV v))

/// ---------------------------------------------------------------------------
/// Classification Inversion Lemmas
/// ---------------------------------------------------------------------------

/// Inversion: classify_minor_field == Some (MinorV x) implies v == x and v is minor
val classify_minor_field_inv_minor (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  : Lemma (requires classify_minor_field ms major v == Some (MinorV x))
          (ensures v == x /\ is_minor_addr v /\ Seq.mem v (minor_objects ms))

/// Inversion: classify_minor_field == Some (MajorV x) implies v == x and v is major
val classify_minor_field_inv_major (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  : Lemma (requires classify_minor_field ms major v == Some (MajorV x))
          (ensures v == x /\ is_val_addr v /\ Seq.mem (v <: obj_addr) (objects zero_addr major) /\
                   ~(is_minor_addr v /\ Seq.mem v (minor_objects ms)))

/// Inversion: classify_major_field == Some (MinorV x) implies v == x and v is minor
val classify_major_field_inv_minor (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  : Lemma (requires classify_major_field ms major v == Some (MinorV x))
          (ensures v == x /\ is_minor_pointer v /\ Seq.mem v (minor_objects ms))

/// Inversion: classify_major_field == Some (MajorV x) implies v == x and v is major
val classify_major_field_inv_major (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  : Lemma (requires classify_major_field ms major v == Some (MajorV x))
          (ensures v == x /\ is_val_addr v /\ Seq.mem (v <: obj_addr) (objects zero_addr major) /\
                   ~(is_minor_pointer v /\ Seq.mem v (minor_objects ms)))

/// ---------------------------------------------------------------------------
/// Graph Construction
/// ---------------------------------------------------------------------------

/// Build the combined graph from a generational state.
/// Vertices: all minor objects + all major objects.
/// Edges: pointer fields from both generations, classified by source.
///
/// NOTE: Uses ALL minor objects (not just reachable ones) as vertices.
/// The reachability analysis happens at a higher level via combined_reachable.
val build_combined_graph (ms: minor_state) (major: heap)
  : GTot combined_graph

/// ---------------------------------------------------------------------------
/// Vertex Membership Characterization
/// ---------------------------------------------------------------------------

/// A MinorV is a vertex iff it's a valid minor object
val minor_vertex_char (ms: minor_state) (major: heap) (a: U64.t)
  : Lemma (ensures
      mem_cv (MinorV a) (build_combined_graph ms major) <==>
      Seq.mem a (minor_objects ms))

/// A MajorV is a vertex iff it's an allocated major object
val major_vertex_char (ms: minor_state) (major: heap) (a: obj_addr)
  : Lemma (ensures
      mem_cv (MajorV a) (build_combined_graph ms major) <==>
      Seq.mem a (objects zero_addr major))

/// ---------------------------------------------------------------------------
/// Well-Formedness of Construction
/// ---------------------------------------------------------------------------

/// The constructed graph is well-formed (all edge endpoints are vertices)
val build_combined_graph_wf (ms: minor_state) (major: heap)
  : Lemma (requires well_formed_heap major /\ minor_wf ms)
          (ensures combined_graph_wf (build_combined_graph ms major))

/// ---------------------------------------------------------------------------
/// Edge Introduction Lemmas
/// ---------------------------------------------------------------------------

/// If a field of minor object src is classified as a pointer, the
/// corresponding edge exists in the combined graph.
val minor_field_edge_intro (ms: minor_state) (major: heap)
  (src: U64.t) (i: nat) (dst: combined_vertex)
  : Lemma (requires Seq.mem src (minor_objects ms) /\
                    i < minor_wosize ms src /\
                    classify_minor_field ms major (minor_read_field ms src i) == Some dst)
          (ensures mem_ce (MinorV src, dst) (build_combined_graph ms major))

/// If a field of major object src is classified as a pointer, the
/// corresponding edge exists in the combined graph.
val major_field_edge_intro (ms: minor_state) (major: heap)
  (src: obj_addr) (i: nat) (dst: combined_vertex)
  : Lemma (requires Seq.mem src (objects zero_addr major) /\
                    i < U64.v (wosize_of_object src major) /\
                    ~(is_no_scan src major) /\
                    U64.v src + i * 8 + 8 <= heap_size /\
                    (U64.v src + i * 8) % 8 == 0 /\
                    classify_major_field ms major
                      (read_word major (U64.uint_to_t (U64.v src + i * 8))) == Some dst)
          (ensures mem_ce (MajorV src, dst) (build_combined_graph ms major))

/// ---------------------------------------------------------------------------
/// Edge Elimination Lemmas
/// ---------------------------------------------------------------------------

/// Source decomposition: every edge comes from a minor or major source.
/// Combined with well-formedness, this classifies every edge into one of two cases.
val edge_source_decomposition (ms: minor_state) (major: heap)
  (e: combined_edge)
  : Lemma (requires mem_ce e (build_combined_graph ms major))
          (ensures
            (match fst e with
             | MinorV src -> Seq.mem src (minor_objects ms)
             | MajorV src ->
               U64.v src >= U64.v mword /\ U64.v src < heap_size /\ U64.v src % U64.v mword == 0 /\
               Seq.mem (src <: obj_addr) (objects zero_addr major)))

/// Minor edge elimination: every edge from a minor source has a witness field.
val minor_edge_elim (ms: minor_state) (major: heap)
  (src: U64.t) (dst: combined_vertex)
  : Lemma (requires mem_ce (MinorV src, dst) (build_combined_graph ms major))
          (ensures Seq.mem src (minor_objects ms) /\
                   (exists (i: nat). i < minor_wosize ms src /\
                     classify_minor_field ms major (minor_read_field ms src i) == Some dst))

/// Major edge elimination: every edge from a major source has a witness field.
val major_edge_elim (ms: minor_state) (major: heap)
  (src: obj_addr) (dst: combined_vertex)
  : Lemma (requires mem_ce (MajorV src, dst) (build_combined_graph ms major))
          (ensures Seq.mem src (objects zero_addr major) /\
                   ~(is_no_scan src major) /\
                   (exists (i: nat). i < U64.v (wosize_of_object src major) /\
                     U64.v src + i * 8 + 8 <= heap_size /\
                     (U64.v src + i * 8) % 8 == 0 /\
                     classify_major_field ms major
                       (read_word major (U64.uint_to_t (U64.v src + i * 8))) == Some dst))

/// ---------------------------------------------------------------------------
/// GC Morphism (forwarding map as graph homomorphism)
/// ---------------------------------------------------------------------------

/// The morphism sends minor objects to their forwarded major addresses
/// and leaves major objects unchanged.
val gc_morphism (fwd: forwarding_map) (v: combined_vertex) : GTot combined_vertex

/// Characterization: minor vertex with non-zero forwarding
val gc_morphism_minor_fwd (fwd: forwarding_map) (v: U64.t)
  : Lemma (requires fwd v <> 0UL)
          (ensures gc_morphism fwd (MinorV v) == MajorV (fwd v))

/// Characterization: minor vertex with zero forwarding (stays)
val gc_morphism_minor_stay (fwd: forwarding_map) (v: U64.t)
  : Lemma (requires fwd v == 0UL)
          (ensures gc_morphism fwd (MinorV v) == MinorV v)

/// Characterization: major vertex (identity)
val gc_morphism_major (fwd: forwarding_map) (v: U64.t)
  : Lemma (ensures gc_morphism fwd (MajorV v) == MajorV v)

/// ---------------------------------------------------------------------------
/// Reachability (inductive)
/// ---------------------------------------------------------------------------

/// A vertex is reachable from roots if it's a root vertex, or reachable
/// from a reachable vertex via an edge.
val combined_reachable (g: combined_graph) (roots: seq combined_vertex)
                       (v: combined_vertex)
  : GTot prop

/// Roots are reachable
val combined_reachable_root (g: combined_graph) (roots: seq combined_vertex)
                            (v: combined_vertex)
  : Lemma (requires Seq.mem v roots /\ mem_cv v g)
          (ensures combined_reachable g roots v)

/// Successor closure
val combined_reachable_step (g: combined_graph) (roots: seq combined_vertex)
                            (u v: combined_vertex)
  : Lemma (requires combined_reachable g roots u /\ mem_ce (u, v) g)
          (ensures combined_reachable g roots v)

/// Induction principle: any predicate closed under roots and edges
/// holds for all reachable vertices
val combined_reachable_ind (g: combined_graph) (roots: seq combined_vertex)
                           (p: combined_vertex -> prop) (v: combined_vertex)
  : Lemma (requires
      combined_reachable g roots v /\
      (forall r. Seq.mem r roots /\ mem_cv r g ==> p r) /\
      (forall u w. p u /\ mem_ce (u, w) g ==> p w))
    (ensures p v)

/// ---------------------------------------------------------------------------
/// Root Classification
/// ---------------------------------------------------------------------------

/// Classify a program root as a combined vertex
let classify_root (r: U64.t) : GTot combined_vertex =
  if is_minor_pointer r then MinorV r else MajorV r

/// Classify a sequence of roots
let rec classify_roots (roots: seq U64.t)
  : GTot (seq combined_vertex) (decreases Seq.length roots) =
  if Seq.length roots = 0 then Seq.empty
  else Seq.cons (classify_root (Seq.head roots)) (classify_roots (Seq.tail roots))

/// Membership in classify_roots: if r ∈ roots and is_minor_pointer r,
/// then MinorV r ∈ classify_roots roots.
val classify_roots_minor_mem (roots: seq U64.t) (r: U64.t)
  : Lemma (requires Seq.mem r roots /\ is_minor_pointer r)
          (ensures Seq.mem (MinorV r) (classify_roots roots))

/// Membership in classify_roots: if r ∈ roots and ¬(is_minor_pointer r),
/// then MajorV r ∈ classify_roots roots.
val classify_roots_major_mem (roots: seq U64.t) (r: U64.t)
  : Lemma (requires Seq.mem r roots /\ ~(is_minor_pointer r))
          (ensures Seq.mem (MajorV r) (classify_roots roots))
