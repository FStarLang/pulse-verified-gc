/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectForwarding -- Minor-collection forwarding kernel
/// ---------------------------------------------------------------------------
///
/// This module captures the reusable forwarding kernel of the upstream
/// minor-collection isomorphism proof, specialized to the current
/// `minor_collect_full` path.
///
/// The property is intentionally stated over `cheney_collect_spec`, since the
/// Pulse implementation proves its concrete two-pass update equals that spec.
/// The source roots are the program roots plus the remembered-set slot targets;
/// when those remembered targets are represented in the root array and the
/// collector returns `ok`, the forwarding map is an injective morphism for
/// reachable minor objects and all images are valid post-minor addresses
/// (ordinary objects or infix interior pointers).  This is NOT, by itself, a
/// graph isomorphism: the full reachable-subgraph isomorphism additionally
/// proves surjectivity onto the post-minor reachable subgraph and edge
/// preservation/reflection.  The result-indexed wrapper states that theorem
/// directly over the heap and roots returned by `minor_collect_full`.

module GC.Gen.MinorCollectForwarding

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Remembered
open GC.Gen.Reachability
open GC.Gen.Cheney

module AllocLemmas = GC.Spec.Allocator.Lemmas
module Mark = GC.Spec.Mark
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module PromUpdate = GC.Gen.PromoteUpdate
module Cheney = GC.Gen.Cheney
module CheneyBFS = GC.Gen.CheneyBFS
module CheneyCorr = GC.Gen.CheneyCorrectness
module CheneyPres = GC.Gen.CheneyPreservation
module CG = GC.Gen.CombinedGraph
module RBridge = GC.Gen.ReachabilityBridge
module GenInv = GC.Gen.HeapInvariant
module HeapGraph = GC.Spec.HeapGraph
module HeapModel = GC.Spec.HeapModel
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module MCFE = GC.Gen.MinorCollectForwarding.Edges
module MCFNE = GC.Gen.MinorCollectForwarding.NormalEdges
module MCFNP = GC.Gen.MinorCollectForwarding.NonPointerFields
let remembered_targets_in_roots
  (major: heap) (roots slots: seq U64.t) (n: nat) : prop =
  MCFH.remembered_targets_in_roots major roots slots n

#push-options "--z3rlimit 10"
/// Root validity needed to make the target be all concrete post-reachable
/// vertices: a minor-shaped root must be a real live minor object, while a
/// non-minor root must be an allocated major object.
let roots_valid_for_minor_collection
  (minor: minor_state) (major: heap) (roots: seq U64.t) : prop =
  MCFH.roots_valid_for_minor_collection minor major roots
#pop-options

/// Raw-address view of graph-edge membership, useful when the endpoint is a
/// forwarding-map image whose `hp_addr` refinement is proved by preconditions.
let mem_graph_edge_at (g: graph_state) (src dst: U64.t) : prop =
  MCFH.mem_graph_edge_at g src dst

let mem_graph_vertex_at (g: graph_state) (w: U64.t) : prop =
  MCFH.mem_graph_vertex_at g w

let post_minor_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (w: U64.t) : prop =
  MCFH.post_minor_reachable minor major fp roots w

let post_minor_edge
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (x y: U64.t) : prop =
  MCFH.post_minor_edge minor major fp roots x y

/// Result-indexed post-minor reachability: unlike `post_minor_reachable`, this
/// names the concrete heap and rewritten roots exposed by an implementation
/// postcondition.
let result_post_reachable
  (post_major: heap) (post_roots: seq U64.t) (w: U64.t) : prop =
  MCFH.result_post_reachable post_major post_roots w

let result_post_edge (post_major: heap) (x y: U64.t) : prop =
  MCFH.result_post_edge post_major x y

val post_minor_reachable_refl_from_root
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (w: U64.t)
  : Lemma
    (requires (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec minor major fp roots in
      Seq.mem w (rewrite_roots roots prom.fwd_map) /\
      mem_graph_vertex_at (HeapModel.create_graph res.mc_major) w))
    (ensures post_minor_reachable minor major fp roots w)

/// Bridge the implementation-facing ref-table coverage predicate to the
/// scan-root coverage predicate used by the combined-graph reachability bridge.
val remembered_roots_in_roots_from_slots
  (major: heap) (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n)
    (ensures RBridge.remembered_roots_in_roots major roots)
val heap_graph_edge_to_field_read
  (g: heap) (src dst: obj_addr)
  : Lemma
    (requires mem_graph_edge (HeapModel.create_graph g) src dst)
    (ensures
      Seq.mem src (objects zero_addr g) /\
      is_no_scan src g = false /\
      HeapGraph.is_pointer_field dst /\
      (exists (j: nat).
        j < U64.v (wosize_of_object src g) /\
        U64.v src + j * 8 + 8 <= heap_size /\
        (U64.v src + j * 8) % 8 == 0 /\
        read_word g (U64.uint_to_t (U64.v src + j * 8)) == dst))

/// Cheney promotion preserves the header-derived facts and body field of a
/// pre-existing non-blue major object.
val cheney_promote_preserves_old_major_field_context
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: obj_addr) (j: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Seq.mem src (objects zero_addr major) /\
      is_blue src major = false /\
      j < U64.v (wosize_of_object src major) /\
      U64.v src + j * 8 + 8 <= heap_size /\
      (U64.v src + j * 8) % 8 == 0)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      Seq.mem src (objects zero_addr prom.major_final) /\
      is_blue src prom.major_final = false /\
      is_no_scan src prom.major_final == is_no_scan src major /\
      wosize_of_object src prom.major_final == wosize_of_object src major /\
      read_word prom.major_final (U64.uint_to_t (U64.v src + j * 8)) ==
      read_word major (U64.uint_to_t (U64.v src + j * 8))))
/// Combined-reachable minor vertices have forwarding images when promotion does
/// not run out of space and scan-derived remembered roots are included in the
/// Cheney roots.
val combined_reachable_minor_has_fwd
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      RBridge.major_field_zero_covered minor major roots /\
      RBridge.remembered_roots_in_roots major roots /\
      well_formed_heap major /\
      minor_wf minor /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures (
      let cg = CG.build_combined_graph minor major in
      let combined_roots = CG.classify_roots roots in
      let fwd = (cheney_promote minor major fp roots).fwd_map in
      forall (v: U64.t).
        CG.combined_reachable cg combined_roots (CG.MinorV v) /\
        minor_wosize minor v > 0 ==> fwd v <> 0UL))

/// Slot-table-facing form of `combined_reachable_minor_has_fwd`.
val combined_reachable_minor_has_fwd_from_slots
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      RBridge.major_field_zero_covered minor major roots /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      well_formed_heap major /\
      minor_wf minor /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures (
      let cg = CG.build_combined_graph minor major in
      let combined_roots = CG.classify_roots roots in
      let fwd = (cheney_promote minor major fp roots).fwd_map in
      forall (v: U64.t).
        CG.combined_reachable cg combined_roots (CG.MinorV v) /\
        minor_wosize minor v > 0 ==> fwd v <> 0UL))

/// Field-level MajorV -> MinorV edge-forwarding lemma: if an old major field
/// points to a reachable positive-size minor object, the post-minor heap stores
/// the target's forwarding address in that field.
val combined_major_minor_field_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (src: obj_addr) (dst: U64.t) (i: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_covered minor major roots /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      (let cg = CG.build_combined_graph minor major in
       let combined_roots = CG.classify_roots roots in
       CG.combined_reachable cg combined_roots (CG.MajorV src) /\
       CG.combined_reachable cg combined_roots (CG.MinorV dst)) /\
      ~(is_no_scan src major) /\
      i < U64.v (wosize_of_object src major) /\
      U64.v src + i * 8 + 8 <= heap_size /\
      (U64.v src + i * 8) % 8 == 0 /\
      CG.classify_major_field minor major
        (read_word major (U64.uint_to_t (U64.v src + i * 8))) == Some (CG.MinorV dst) /\
      minor_wosize minor dst > 0)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec minor major fp roots in
      prom.fwd_map dst <> 0UL /\
      read_word res.mc_major (U64.uint_to_t (U64.v src + i * 8)) == prom.fwd_map dst))

/// Side condition for the normal-object edge-forwarding theorem.  Minor-source
/// cases require the source image to be a normal promoted object; minor-target
/// cases require the target image to be pointer-shaped.
let normal_edge_forward_ready
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (u v: CG.combined_vertex) : prop =
  MCFNE.normal_edge_forward_ready minor major fp roots u v

/// Composed forward-edge theorem for the normal reachable subgraph: any
/// reachable combined edge satisfying `normal_edge_forward_ready` maps to a
/// concrete edge in the post-minor major heap graph.
val combined_reachable_edge_forwarded_normal
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_covered minor major roots /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      (let cg = CG.build_combined_graph minor major in
       let combined_roots = CG.classify_roots roots in
       CG.combined_reachable cg combined_roots u /\
       CG.combined_reachable cg combined_roots v /\
       CG.mem_ce (u, v) cg) /\
      normal_edge_forward_ready minor major fp roots u v)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec minor major fp roots in
      mem_graph_edge_at (HeapModel.create_graph res.mc_major)
        (CG.fwd_morphism prom.fwd_map u)
        (CG.fwd_morphism prom.fwd_map v)))

/// Disjointness assumption needed for cross-generation injectivity: normal
/// forwarding targets are not old non-blue major objects.
let fwd_disjoint_reachable_major
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  MCFNE.fwd_disjoint_reachable_major minor major fp roots

val fwd_disjoint_reachable_major_intro
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major)
    (ensures fwd_disjoint_reachable_major minor major fp roots)

let combined_reachable_normal_injective_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  MCFNE.combined_reachable_normal_injective_prop minor major fp roots

let normal_vertex_ready
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (u: CG.combined_vertex) : prop =
  MCFNE.normal_vertex_ready minor major fp roots u

let normal_src_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (u: CG.combined_vertex) : prop =
  MCFNE.normal_src_reachable minor major fp roots u

val normal_edge_forward_ready_intro
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      normal_src_reachable minor major fp roots u /\
      normal_src_reachable minor major fp roots v /\
      CG.mem_ce (u, v) (CG.build_combined_graph minor major))
    (ensures normal_edge_forward_ready minor major fp roots u v)

val normal_classified_root_image_in_rewrite_roots
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (u: CG.combined_vertex)
  : Lemma
    (requires
      Seq.mem u (CG.classify_roots roots) /\
      normal_vertex_ready minor major fp roots u)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      Seq.mem (CG.fwd_morphism prom.fwd_map u)
        (rewrite_roots roots prom.fwd_map)))

let normal_src_edge
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (u v: CG.combined_vertex) : prop =
  let cg = CG.build_combined_graph minor major in
  normal_src_reachable minor major fp roots u /\
  normal_src_reachable minor major fp roots v /\
  CG.mem_ce (u, v) cg /\
  normal_edge_forward_ready minor major fp roots u v

noeq type ready_src_reach
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : CG.combined_vertex -> Type =
  | ReadyRoot :
      u:CG.combined_vertex ->
      (Seq.mem u (CG.classify_roots roots) /\
       CG.mem_cv u (CG.build_combined_graph minor major) /\
       normal_vertex_ready minor major fp roots u) ->
      ready_src_reach minor major fp roots u
  | ReadyStep :
      u:CG.combined_vertex ->
      v:CG.combined_vertex ->
      ready_src_reach minor major fp roots u ->
      normal_src_edge minor major fp roots u v ->
      ready_src_reach minor major fp roots v

let ready_src_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (u: CG.combined_vertex) : prop =
  exists (_: ready_src_reach minor major fp roots u). True

let ready_image_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (w: U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  exists (u: CG.combined_vertex).
    ready_src_reachable minor major fp roots u /\
    CG.fwd_morphism prom.fwd_map u == w

let normal_image_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (w: U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  exists (u: CG.combined_vertex).
    normal_src_reachable minor major fp roots u /\
    CG.fwd_morphism prom.fwd_map u == w

let normal_image_edge
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (x y: U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  exists (u v: CG.combined_vertex).
    normal_src_edge minor major fp roots u v /\
    CG.fwd_morphism prom.fwd_map u == x /\
    CG.fwd_morphism prom.fwd_map v == y

val normal_image_vertex_is_post_vertex
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (w: U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      normal_image_reachable minor major fp roots w)
    (ensures (
      let res = cheney_collect_spec minor major fp roots in
      mem_graph_vertex_at (HeapModel.create_graph res.mc_major) w))

val normal_classified_root_image_post_reachable
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (u: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Seq.mem u (CG.classify_roots roots) /\
      normal_src_reachable minor major fp roots u)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      post_minor_reachable minor major fp roots
        (CG.fwd_morphism prom.fwd_map u)))

let normal_image_reachable_subgraph_isomorphism_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  CG.reachable_subgraph_isomorphism
    (normal_src_reachable minor major fp roots)
    (normal_image_reachable minor major fp roots)
    (normal_src_edge minor major fp roots)
    (normal_image_edge minor major fp roots)
    prom.fwd_map

val combined_reachable_normal_injective
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      fwd_disjoint_reachable_major minor major fp roots)
    (ensures combined_reachable_normal_injective_prop minor major fp roots)

val normal_image_reachable_subgraph_isomorphism
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      fwd_disjoint_reachable_major minor major fp roots)
    (ensures normal_image_reachable_subgraph_isomorphism_prop minor major fp roots)

val normal_src_edge_preserves_post_minor_reachable
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_covered minor major roots /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      normal_src_edge minor major fp roots u v /\
      (let prom = cheney_promote minor major fp roots in
       post_minor_reachable minor major fp roots
         (CG.fwd_morphism prom.fwd_map u)))
    (ensures (
      let prom = cheney_promote minor major fp roots in
      post_minor_reachable minor major fp roots
        (CG.fwd_morphism prom.fwd_map v)))

val ready_src_reach_image_post_reachable
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (u: CG.combined_vertex)
  (r: ready_src_reach minor major fp roots u)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_covered minor major roots /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      post_minor_reachable minor major fp roots
        (CG.fwd_morphism prom.fwd_map u)))

val ready_image_reachable_is_post_reachable
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (w: U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_covered minor major roots /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      ready_image_reachable minor major fp roots w)
    (ensures post_minor_reachable minor major fp roots w)

val normal_src_reachable_is_ready_src_reachable
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (u: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_covered minor major roots /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      normal_src_reachable minor major fp roots u)
    (ensures ready_src_reachable minor major fp roots u)

let normal_image_reachable_is_post_reachable_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  forall (w: U64.t).
    normal_image_reachable minor major fp roots w ==>
    post_minor_reachable minor major fp roots w

val normal_image_reachable_is_post_reachable
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (w: U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_covered minor major roots /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      normal_image_reachable minor major fp roots w)
    (ensures post_minor_reachable minor major fp roots w)

val normal_image_reachable_is_post_reachable_all
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_covered minor major roots /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures normal_image_reachable_is_post_reachable_prop minor major fp roots)

val post_normal_image_edges_reflect_src
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_covered minor major roots /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      normal_src_reachable minor major fp roots u /\
      normal_src_reachable minor major fp roots v /\
      (let prom = cheney_promote minor major fp roots in
       post_minor_edge minor major fp roots
         (CG.fwd_morphism prom.fwd_map u)
         (CG.fwd_morphism prom.fwd_map v)))
    (ensures normal_src_edge minor major fp roots u v)

let post_minor_reachable_is_normal_image_reachable_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  forall (w: U64.t).
    post_minor_reachable minor major fp roots w ==>
    normal_image_reachable minor major fp roots w

let normal_post_reachable_subgraph_isomorphism_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  CG.reachable_subgraph_isomorphism
    (normal_src_reachable minor major fp roots)
    (post_minor_reachable minor major fp roots)
    (normal_src_edge minor major fp roots)
    (post_minor_edge minor major fp roots)
    prom.fwd_map

let normal_result_reachable_subgraph_isomorphism_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (post_major: heap) (post_roots: seq U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  CG.reachable_subgraph_isomorphism
    (normal_src_reachable minor major fp roots)
    (result_post_reachable post_major post_roots)
    (normal_src_edge minor major fp roots)
    (result_post_edge post_major)
    prom.fwd_map

let normal_post_non_pointer_fields_preserved_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  MCFNP.normal_post_non_pointer_fields_preserved_prop minor major fp roots

let normal_result_non_pointer_fields_preserved_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (post_major: heap) : prop =
  MCFNP.normal_result_non_pointer_fields_preserved_prop
    minor major fp roots post_major
val post_minor_reachable_is_normal_image_reachable_all
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_covered minor major roots /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      roots_valid_for_minor_collection minor major roots /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures post_minor_reachable_is_normal_image_reachable_prop minor major fp roots)

val normal_post_reachable_subgraph_isomorphism
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_covered minor major roots /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      roots_valid_for_minor_collection minor major roots /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures normal_post_reachable_subgraph_isomorphism_prop minor major fp roots)

val normal_post_reachable_subgraph_isomorphism_to_result
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (post_major: heap) (post_roots: seq U64.t)
  : Lemma
    (requires
      post_major == (cheney_collect_spec minor major fp roots).mc_major /\
      post_roots == rewrite_roots roots (cheney_promote minor major fp roots).fwd_map /\
      normal_post_reachable_subgraph_isomorphism_prop minor major fp roots)
    (ensures
      normal_result_reachable_subgraph_isomorphism_prop
        minor major fp roots post_major post_roots)

val normal_post_non_pointer_fields_preserved
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_covered minor major roots /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      roots_valid_for_minor_collection minor major roots /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures normal_post_non_pointer_fields_preserved_prop minor major fp roots)

val normal_post_non_pointer_fields_preserved_to_result
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (post_major: heap)
  : Lemma
    (requires
      post_major == (cheney_collect_spec minor major fp roots).mc_major /\
      normal_post_non_pointer_fields_preserved_prop minor major fp roots)
    (ensures
      normal_result_non_pointer_fields_preserved_prop
        minor major fp roots post_major)
