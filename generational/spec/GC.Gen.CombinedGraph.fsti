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

module MH = GC.Spec.MajorHeap
module SpecMajorAlloc = GC.Spec.MajorAllocator

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
/// Minor targets are normalized with `to_minor_offset`; major targets use the
/// raw value.
val classify_minor_field (ms: minor_state) (major: heap) (v: U64.t)
  : GTot (option combined_vertex)

/// Characterization: classify_minor_field returns `MinorV (to_minor_offset v)`
/// when the normalized value is a minor object.
val classify_minor_field_minor (ms: minor_state) (major: heap) (v: U64.t)
  : Lemma (requires (
             let vo = to_minor_offset v in
             is_minor_addr vo /\ Seq.mem vo (minor_objects ms)))
          (ensures classify_minor_field ms major v == Some (MinorV (to_minor_offset v)))

/// Characterization: classify_minor_field returns MajorV v when v is a major object
/// and not a minor object (used by edge backward proofs)
val classify_minor_field_major (ms: minor_state) (major: heap) (v: U64.t)
  : Lemma (requires is_val_addr v /\ Seq.mem v (objects zero_addr major) /\
                    (let vo = to_minor_offset v in
                     ~(is_minor_addr vo /\ Seq.mem vo (minor_objects ms))))
          (ensures classify_minor_field ms major v == Some (MajorV v))

/// Classify a field value read from a major-heap object.
/// Minor targets are normalized with `to_minor_offset`, matching the
/// remembered-set scan and pointer-update semantics.
val classify_major_field (ms: minor_state) (major: heap) (v: U64.t)
  : GTot (option combined_vertex)

/// Characterization: classify_major_field returns MajorV v when v is a major object
/// and not a minor pointer
val classify_major_field_major (ms: minor_state) (major: heap) (v: U64.t)
  : Lemma (requires is_val_addr v /\ Seq.mem v (objects zero_addr major) /\
                    (let vo = to_minor_offset v in
                     ~(is_minor_pointer vo /\ Seq.mem vo (minor_objects ms))))
          (ensures classify_major_field ms major v == Some (MajorV v))

/// Characterization: classify_major_field returns MinorV (to_minor_offset v)
/// when the normalized value is a minor pointer in the minor objects set.
val classify_major_field_is_minor (ms: minor_state) (major: heap) (v: U64.t)
  : Lemma (requires (
             let vo = to_minor_offset v in
             is_minor_pointer vo /\ Seq.mem vo (minor_objects ms)))
          (ensures classify_major_field ms major v == Some (MinorV (to_minor_offset v)))

/// Chunked-major analogue of `classify_minor_field`, used while porting the
/// generational graph/shape proof from dense `heap` to expandable `major_heap`.
val chunked_classify_minor_field (ms: minor_state) (mh: MH.major_heap) (v: U64.t)
  : GTot (option combined_vertex)

/// Chunked-major analogue of `classify_major_field`.
val chunked_classify_major_field (ms: minor_state) (mh: MH.major_heap) (v: U64.t)
  : GTot (option combined_vertex)

/// Fresh expansion preserves membership for an old value that cannot point into
/// the newly registered chunk. This is the classification-side obligation that
/// prevents registering a fresh chunk from turning old raw field data into a
/// new major pointer.
val chunked_major_member_preserved_by_expansion
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t -> v:obj_addr ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.pointer_in_chunk fresh v))
      (ensures
        Seq.mem v
          (MH.major_objects
            (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out) ==
        Seq.mem v (MH.major_objects mh))

val chunked_classify_minor_field_preserved_by_expansion
  : ms:minor_state -> mh:MH.major_heap -> fresh:MH.heap_chunk ->
    fp:U64.t -> v:U64.t ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.pointer_in_chunk fresh v))
      (ensures
        chunked_classify_minor_field ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out v ==
        chunked_classify_minor_field ms mh v)

val chunked_classify_major_field_preserved_by_expansion
  : ms:minor_state -> mh:MH.major_heap -> fresh:MH.heap_chunk ->
    fp:U64.t -> v:U64.t ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.pointer_in_chunk fresh v))
      (ensures
        chunked_classify_major_field ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out v ==
        chunked_classify_major_field ms mh v)

/// Checked major field slot address used by chunked edge construction.
val chunked_major_field_slot (src: obj_addr) (i: nat)
  : GTot (option hp_addr)

/// Build field edges for a major object in a chunked major heap.
val chunked_major_field_edges
  : ms:minor_state -> mh:MH.major_heap -> src:obj_addr -> wz:nat -> i:nat ->
    GTot (seq combined_edge)

/// The old major field slots from `i` onward, and any old field values read
/// there, do not point into the newly registered chunk.
val chunked_major_field_expansion_safe
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> src:obj_addr -> wz:nat -> i:nat ->
    Tot prop

val chunked_major_field_expansion_safe_intro
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> src:obj_addr -> wz:nat -> i:nat ->
    Lemma
      (requires
        (forall (j:nat) (field_addr:hp_addr).
          i <= j /\ j < wz /\
          chunked_major_field_slot src j == Some field_addr ==>
            ~(MH.chunk_contains_addr fresh field_addr)) /\
        (forall (j:nat) (field_addr:hp_addr) (v:U64.t).
          i <= j /\ j < wz /\
          chunked_major_field_slot src j == Some field_addr /\
          MH.read_word_in_major mh field_addr == Some v ==>
            ~(MH.pointer_in_chunk fresh v)))
      (ensures chunked_major_field_expansion_safe mh fresh src wz i)

val chunked_major_field_expansion_safe_at
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> src:obj_addr ->
    wz:nat -> i:nat -> j:nat -> field_addr:hp_addr -> v:U64.t ->
    Lemma
      (requires chunked_major_field_expansion_safe mh fresh src wz i /\
                i <= j /\ j < wz /\
                chunked_major_field_slot src j == Some field_addr)
      (ensures
        ~(MH.chunk_contains_addr fresh field_addr) /\
        (MH.read_word_in_major mh field_addr == Some v ==>
         ~(MH.pointer_in_chunk fresh v)))

val chunked_major_field_expansion_safe_tail
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> src:obj_addr -> wz:nat -> i:nat ->
    Lemma
      (requires i < wz /\
                chunked_major_field_expansion_safe mh fresh src wz i)
      (ensures chunked_major_field_expansion_safe mh fresh src wz (i + 1))

val chunked_major_field_edges_preserved_by_expansion
  : ms:minor_state -> mh:MH.major_heap -> fresh:MH.heap_chunk ->
    fp:U64.t -> src:obj_addr -> wz:nat -> i:nat ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                chunked_major_field_expansion_safe mh fresh src wz i)
      (ensures
        chunked_major_field_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out src wz i ==
        chunked_major_field_edges ms mh src wz i)

/// Collect chunked major field edges from an explicit old-object sequence. The
/// `wz_of` parameter lets future clients instantiate this with header-derived
/// old sizes after proving those headers are preserved by expansion.
val chunked_all_major_field_edges
  : ms:minor_state -> mh:MH.major_heap -> objs:seq obj_addr ->
    wz_of:(obj_addr -> GTot nat) -> idx:nat -> GTot (seq combined_edge)

val chunked_all_major_field_expansion_safe
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> objs:seq obj_addr ->
    wz_of:(obj_addr -> GTot nat) -> idx:nat -> Tot prop

val chunked_all_major_field_expansion_safe_at
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> objs:seq obj_addr ->
    wz_of:(obj_addr -> GTot nat) -> idx:nat -> k:nat ->
    Lemma
      (requires chunked_all_major_field_expansion_safe mh fresh objs wz_of idx /\
                idx <= k /\ k < Seq.length objs)
      (ensures
        chunked_major_field_expansion_safe
          mh fresh (Seq.index objs k) (wz_of (Seq.index objs k)) 0)

val chunked_all_major_field_expansion_safe_tail
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> objs:seq obj_addr ->
    wz_of:(obj_addr -> GTot nat) -> idx:nat ->
    Lemma
      (requires idx < Seq.length objs /\
                chunked_all_major_field_expansion_safe mh fresh objs wz_of idx)
      (ensures
        chunked_all_major_field_expansion_safe mh fresh objs wz_of (idx + 1))

val chunked_all_major_field_edges_preserved_by_expansion
  : ms:minor_state -> mh:MH.major_heap -> fresh:MH.heap_chunk ->
    fp:U64.t -> objs:seq obj_addr -> wz_of:(obj_addr -> GTot nat) -> idx:nat ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                chunked_all_major_field_expansion_safe mh fresh objs wz_of idx)
      (ensures
        chunked_all_major_field_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out objs wz_of idx ==
        chunked_all_major_field_edges ms mh objs wz_of idx)

/// ---------------------------------------------------------------------------
/// Classification Inversion Lemmas
/// ---------------------------------------------------------------------------

/// Inversion: classify_minor_field == Some (MinorV x) implies the normalized
/// value is x and x is minor.
val classify_minor_field_inv_minor (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  : Lemma (requires classify_minor_field ms major v == Some (MinorV x))
          (ensures to_minor_offset v == x /\ is_minor_addr x /\ Seq.mem x (minor_objects ms))

/// Inversion: classify_minor_field == Some (MajorV x) implies v == x and v is major
val classify_minor_field_inv_major (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  : Lemma (requires classify_minor_field ms major v == Some (MajorV x))
          (ensures v == x /\ is_val_addr v /\ Seq.mem (v <: obj_addr) (objects zero_addr major) /\
                   (let vo = to_minor_offset v in
                    ~(is_minor_addr vo /\ Seq.mem vo (minor_objects ms))))

/// Inversion: classify_major_field == Some (MinorV x) implies the normalized
/// field value is x and x is minor.
val classify_major_field_inv_minor (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  : Lemma (requires classify_major_field ms major v == Some (MinorV x))
          (ensures to_minor_offset v == x /\ is_minor_pointer x /\ Seq.mem x (minor_objects ms))

/// Inversion: classify_major_field == Some (MajorV x) implies v == x and v is major
val classify_major_field_inv_major (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  : Lemma (requires classify_major_field ms major v == Some (MajorV x))
          (ensures v == x /\ is_val_addr v /\ Seq.mem (v <: obj_addr) (objects zero_addr major) /\
                   (let vo = to_minor_offset v in
                    ~(is_minor_pointer vo /\ Seq.mem vo (minor_objects ms))))

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

/// Classify a program root as a combined vertex
let classify_root (r: U64.t) : GTot combined_vertex =
  if is_minor_pointer r then MinorV r else MajorV r

/// Classify a sequence of roots
let rec classify_roots (roots: seq U64.t)
  : GTot (seq combined_vertex) (decreases Seq.length roots) =
  if Seq.length roots = 0 then Seq.empty
  else Seq.cons (classify_root (Seq.head roots)) (classify_roots (Seq.tail roots))

/// Membership in classify_roots: if r is in roots and is_minor_pointer r,
/// then MinorV r is in classify_roots roots.
val classify_roots_minor_mem (roots: seq U64.t) (r: U64.t)
  : Lemma (requires Seq.mem r roots /\ is_minor_pointer r)
          (ensures Seq.mem (MinorV r) (classify_roots roots))

/// Membership in classify_roots: if r is in roots and not (is_minor_pointer r),
/// then MajorV r is in classify_roots roots.
val classify_roots_major_mem (roots: seq U64.t) (r: U64.t)
  : Lemma (requires Seq.mem r roots /\ ~(is_minor_pointer r))
          (ensures Seq.mem (MajorV r) (classify_roots roots))

/// Inversion: if MinorV v is in classify_roots roots, then v is in roots and is_minor_pointer v.
val classify_roots_inv_minor (roots: seq U64.t) (v: U64.t)
  : Lemma (requires Seq.mem (MinorV v) (classify_roots roots))
          (ensures Seq.mem v roots /\ is_minor_pointer v)

/// Inversion: if MajorV v is in classify_roots roots, then v is in roots and not (is_minor_pointer v).
val classify_roots_inv_major (roots: seq U64.t) (v: U64.t)
  : Lemma (requires Seq.mem (MajorV v) (classify_roots roots))
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
