/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph -- Combined minor+major heap graph for isomorphism proof
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
/// Minor targets are normalized with `to_minor_offset` and then resolved;
/// major targets use the raw value.
val classify_minor_field (ms: minor_state) (major: heap) (v: U64.t)
  : GTot (option combined_vertex)

/// Characterization: classify_minor_field returns
/// `MinorV (resolve_minor ms (to_minor_offset v))` when the resolved value is
/// a minor object.
val classify_minor_field_minor (ms: minor_state) (major: heap) (v: U64.t)
  : Lemma (requires (
             let vr = resolve_minor ms (to_minor_offset v) in
             is_minor_addr vr /\ Seq.mem vr (minor_objects ms)))
          (ensures classify_minor_field ms major v
                     == Some (MinorV (resolve_minor ms (to_minor_offset v))))

/// Characterization specialized to non-interior nursery targets, where
/// resolution is the identity.
val classify_minor_field_minor_raw (ms: minor_state) (major: heap) (v: U64.t)
  : Lemma (requires (
             let vo = to_minor_offset v in
             ~(is_infix_in_minor ms vo) /\
             is_minor_addr vo /\ Seq.mem vo (minor_objects ms)))
          (ensures classify_minor_field ms major v == Some (MinorV (to_minor_offset v)))

/// Characterization: classify_minor_field returns MajorV v when v is a major object
/// and not a minor object (used by edge backward proofs).
///
/// Unlike `classify_major_field`, the *major* branch of this classifier is still
/// raw: a minor object's field holding an interior pointer into a major closure
/// is ruled out by `GC.Gen.HeapInvariant.minor_major_fields_no_blue`, which
/// requires every pointer-valued minor field to name an enumerated major object
/// outright.
val classify_minor_field_major (ms: minor_state) (major: heap) (v: U64.t)
  : Lemma (requires is_val_addr v /\ Seq.mem v (objects zero_addr major) /\
                    (let vr = resolve_minor ms (to_minor_offset v) in
                     ~(is_minor_addr vr /\ Seq.mem vr (minor_objects ms))))
          (ensures classify_minor_field ms major v == Some (MajorV v))

/// Classify a field value read from a major-heap object.
/// Minor targets are normalized with `to_minor_offset`, matching the
/// remembered-set scan and pointer-update semantics.
val classify_major_field (ms: minor_state) (major: heap) (v: U64.t)
  : GTot (option combined_vertex)

/// Characterization: classify_major_field returns `MajorV (resolve_object v major)`
/// when the *resolved* value is a major object and v is not a minor pointer.
val classify_major_field_major (ms: minor_state) (major: heap) (v: U64.t)
  : Lemma (requires is_val_addr v /\ is_pointer_field v /\
                    Seq.mem (resolve_object v major) (objects zero_addr major) /\
                    (let vr = resolve_minor ms (to_minor_offset v) in
                     ~(is_minor_pointer (to_minor_offset v) /\ Seq.mem vr (minor_objects ms))))
          (ensures classify_major_field ms major v
                     == Some (MajorV (resolve_object v major)))

/// Characterization: classify_major_field returns
/// `MinorV (resolve_minor ms (to_minor_offset v))` when the resolved value is a
/// minor object.  A major-heap field may hold an interior pointer into a
/// nursery closure: `caml_modify` (`runtime/memory.c:617`) files any young
/// block pointer in the remembered set without an infix special case, and
/// `caml_oldify_one` (`runtime/minor_gc.c:231`) then resolves it.
val classify_major_field_is_minor (ms: minor_state) (major: heap) (v: U64.t)
  : Lemma (requires (
             let vr = resolve_minor ms (to_minor_offset v) in
             is_minor_pointer (to_minor_offset v) /\ Seq.mem vr (minor_objects ms)))
          (ensures classify_major_field ms major v
                     == Some (MinorV (resolve_minor ms (to_minor_offset v))))

/// Characterization specialized to non-interior nursery targets.
val classify_major_field_is_minor_raw (ms: minor_state) (major: heap) (v: U64.t)
  : Lemma (requires (
             let vo = to_minor_offset v in
             ~(is_infix_in_minor ms vo) /\
             is_minor_pointer vo /\ Seq.mem vo (minor_objects ms)))
          (ensures classify_major_field ms major v == Some (MinorV (to_minor_offset v)))

/// ---------------------------------------------------------------------------
/// Classification Inversion Lemmas
/// ---------------------------------------------------------------------------

/// Inversion: classify_minor_field == Some (MinorV x) implies x is the resolved
/// form of the normalized value, and x is minor.  Note `to_minor_offset v == x`
/// only when the target is not interior; use `classify_minor_field_inv_minor_raw`
/// when that is known.
val classify_minor_field_inv_minor (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  : Lemma (requires classify_minor_field ms major v == Some (MinorV x))
          (ensures resolve_minor ms (to_minor_offset v) == x /\
                   is_minor_addr x /\ Seq.mem x (minor_objects ms))

/// Inversion specialized to non-interior targets, where resolution is the
/// identity and the pre-resolution conclusion is recovered verbatim.
val classify_minor_field_inv_minor_raw (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  : Lemma (requires classify_minor_field ms major v == Some (MinorV x) /\
                    ~(is_infix_in_minor ms (to_minor_offset v)))
          (ensures to_minor_offset v == x /\ is_minor_addr x /\ Seq.mem x (minor_objects ms))

/// Inversion: classify_minor_field == Some (MajorV x) implies v == x and v is major
val classify_minor_field_inv_major (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  : Lemma (requires classify_minor_field ms major v == Some (MajorV x))
          (ensures v == x /\ is_val_addr v /\ Seq.mem (v <: obj_addr) (objects zero_addr major) /\
                   (let vr = resolve_minor ms (to_minor_offset v) in
                    ~(is_minor_addr vr /\ Seq.mem vr (minor_objects ms))))

/// Inversion: classify_major_field == Some (MinorV x) implies x is the resolved
/// form of the normalized field value, and x is minor.
val classify_major_field_inv_minor (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  : Lemma (requires classify_major_field ms major v == Some (MinorV x))
          (ensures resolve_minor ms (to_minor_offset v) == x /\
                   is_minor_pointer (to_minor_offset v) /\
                   is_minor_pointer x /\ Seq.mem x (minor_objects ms))

/// Inversion specialized to non-interior targets.
val classify_major_field_inv_minor_raw (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  : Lemma (requires classify_major_field ms major v == Some (MinorV x) /\
                    ~(is_infix_in_minor ms (to_minor_offset v)))
          (ensures to_minor_offset v == x /\ is_minor_pointer x /\ Seq.mem x (minor_objects ms))

/// Inversion: classify_major_field == Some (MajorV x) implies x is the resolved
/// form of v, and x is a major object.  Note x == v only when v is not interior;
/// use `classify_major_field_inv_major_raw` when that is known.
val classify_major_field_inv_major (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  : Lemma (requires classify_major_field ms major v == Some (MajorV x))
          (ensures is_val_addr v /\ is_pointer_field v /\ x == resolve_object v major /\
                   Seq.mem (x <: obj_addr) (objects zero_addr major) /\
                   (let vr = resolve_minor ms (to_minor_offset v) in
                    ~(is_minor_pointer (to_minor_offset v) /\ Seq.mem vr (minor_objects ms))))

/// Inversion specialized to non-interior targets, where resolution is the
/// identity and the pre-resolution conclusion `v == x` is recovered verbatim.
val classify_major_field_inv_major_raw (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  : Lemma (requires classify_major_field ms major v == Some (MajorV x) /\
                    is_val_addr v /\ ~(is_infix (v <: obj_addr) major))
          (ensures v == x /\ Seq.mem (v <: obj_addr) (objects zero_addr major) /\
                   (let vr = resolve_minor ms (to_minor_offset v) in
                    ~(is_minor_pointer (to_minor_offset v) /\ Seq.mem vr (minor_objects ms))))

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

/// Validity from vertex membership: if MajorV v is a vertex, then v satisfies
/// the obj_addr refinement (>= mword, < heap_size, word-aligned).
val major_vertex_valid (ms: minor_state) (major: heap) (v: U64.t)
  : Lemma (requires mem_cv (MajorV v) (build_combined_graph ms major))
          (ensures U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
                   Seq.mem (v <: obj_addr) (objects zero_addr major))

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

/// Induction principle that exposes reachability of the edge source in the
/// step case.  This is useful when edge preservation needs global facts about
/// reachable sources, not just the induction predicate.
val combined_reachable_ind_with_reach
  (g: combined_graph) (roots: seq combined_vertex)
  (p: combined_vertex -> prop) (v: combined_vertex)
  : Lemma (requires
      combined_reachable g roots v /\
      (forall r. Seq.mem r roots /\ mem_cv r g ==> p r) /\
      (forall u w. combined_reachable g roots u /\ p u /\ mem_ce (u, w) g ==> p w))
    (ensures p v)

/// ---------------------------------------------------------------------------
/// Root Classification
/// ---------------------------------------------------------------------------

/// Classify a program root as a combined vertex.
///
/// Nursery roots are *resolved*, exactly as the field classifiers are.  A root
/// may be an interior (infix) pointer: OCaml pushes the entry point of a
/// non-first function of a mutually recursive group directly
/// (`runtime/interp.c:601`), and the byte-code root scanner walks such stack
/// slots verbatim (`runtime/roots_byt.c:39`).  Since the group is allocated in
/// the nursery, that is an interior pointer into a young block.
///
/// Resolving here puts the *enclosing closure* --- a genuine vertex of the
/// combined graph --- into the root set.  Leaving it raw would yield
/// `MinorV <interior>`, which is not a vertex at all.  It also makes this
/// agree with `Reachability.minor_reachable_roots`, which resolves; the two
/// root notions previously coincided only because interior roots were
/// excluded outright.
///
/// Note the *hypotheses* of the reachability theorems have not caught up:
/// `MinorCollectForwarding.roots_valid_for_minor_collection` still places
/// every nursery root in `minor_objects`, so an interior root cannot occur
/// under them and the resolution is provably the identity there
/// (`roots_not_infix_in_minor`).  Relaxing that predicate is Phase D2 step 5
/// of `docs/minor-infix-support-plan.md`.
///
/// The major branch is still raw, mirroring `classify_minor_field`: a root
/// pointing into the middle of a *major* closure is excluded by
/// `roots_valid_nonblue`, which requires every root to name an enumerated
/// major object outright.
let classify_root (ms: minor_state) (r: U64.t) : GTot combined_vertex =
  if is_minor_pointer r then MinorV (resolve_minor ms r) else MajorV r

/// Classify a sequence of roots
let rec classify_roots (ms: minor_state) (roots: seq U64.t)
  : GTot (seq combined_vertex) (decreases Seq.length roots) =
  if Seq.length roots = 0 then Seq.empty
  else Seq.cons (classify_root ms (Seq.head roots)) (classify_roots ms (Seq.tail roots))

/// Membership in classify_roots: if r is in roots and is_minor_pointer r,
/// then MinorV (resolve_minor ms r) is in classify_roots ms roots.
val classify_roots_minor_mem (ms: minor_state) (roots: seq U64.t) (r: U64.t)
  : Lemma (requires Seq.mem r roots /\ is_minor_pointer r)
          (ensures Seq.mem (MinorV (resolve_minor ms r)) (classify_roots ms roots))

/// Specialization to non-interior roots, where resolution is the identity and
/// the pre-resolution conclusion is recovered verbatim.
val classify_roots_minor_mem_raw (ms: minor_state) (roots: seq U64.t) (r: U64.t)
  : Lemma (requires Seq.mem r roots /\ is_minor_pointer r /\ ~(is_infix_in_minor ms r))
          (ensures Seq.mem (MinorV r) (classify_roots ms roots))

/// Membership in classify_roots: if r is in roots and not (is_minor_pointer r),
/// then MajorV r is in classify_roots ms roots.
val classify_roots_major_mem (ms: minor_state) (roots: seq U64.t) (r: U64.t)
  : Lemma (requires Seq.mem r roots /\ ~(is_minor_pointer r))
          (ensures Seq.mem (MajorV r) (classify_roots ms roots))

/// Inversion: if MinorV v is in classify_roots ms roots, then *some* root
/// resolves to v.  The root itself need not equal v --- it may be an interior
/// pointer into the closure v names.
val classify_roots_inv_minor (ms: minor_state) (roots: seq U64.t) (v: U64.t)
  : Lemma (requires Seq.mem (MinorV v) (classify_roots ms roots))
          (ensures exists (r: U64.t).
                     Seq.mem r roots /\ is_minor_pointer r /\ resolve_minor ms r == v)

/// Inversion: if MajorV v is in classify_roots ms roots, then v is in roots and
/// not (is_minor_pointer v).
val classify_roots_inv_major (ms: minor_state) (roots: seq U64.t) (v: U64.t)
  : Lemma (requires Seq.mem (MajorV v) (classify_roots ms roots))
          (ensures Seq.mem v roots /\ ~(is_minor_pointer v))

/// The raw-address morphism used by the post-minor heap graph: minor vertices
/// are mapped through the forwarding map, while existing major vertices keep
/// their address.
let fwd_morphism (fwd: forwarding_map) (v: combined_vertex) : GTot U64.t =
  match v with
  | MinorV addr -> fwd addr
  | MajorV addr -> addr

/// Generic shape of a true reachable-subgraph graph isomorphism.
let reachable_subgraph_isomorphism
  (src_reachable: combined_vertex -> prop)
  (dst_reachable: U64.t -> prop)
  (src_edge: combined_vertex -> combined_vertex -> prop)
  (dst_edge: U64.t -> U64.t -> prop)
  (fwd: forwarding_map) : prop =
  (forall (u: combined_vertex). src_reachable u ==>
    dst_reachable (fwd_morphism fwd u)) /\
  (forall (u v: combined_vertex). src_reachable u /\ src_reachable v /\
    fwd_morphism fwd u == fwd_morphism fwd v ==> u == v) /\
  (forall (w: U64.t). dst_reachable w ==>
    exists (u: combined_vertex). src_reachable u /\ fwd_morphism fwd u == w) /\
  (forall (u v: combined_vertex). src_reachable u /\ src_reachable v ==>
    (src_edge u v <==>
     dst_edge (fwd_morphism fwd u) (fwd_morphism fwd v)))
