/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectForwarding -- Minor-collection forwarding kernel
/// ---------------------------------------------------------------------------
///
/// This module captures the reusable forwarding kernel of the upstream
/// minor-collection isomorphism proof, specialized to the current
/// `minor_collect_full` path.
///
/// The property is stated over `cheney_collect_spec_with` for a definition
/// `free` of what counts as free in the major heap (`free_stw` gives the
/// stop-the-world `cheney_collect_spec`), since the Pulse implementation
/// proves its concrete two-pass update equals that spec.  The graphs give a
/// free block no outgoing edges, and every reachable block is not free: the roots are,
/// and a non-free block points only to non-free blocks.
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
open GC.Gen.Reachability
open GC.Gen.Cheney

module AllocLemmas = GC.Spec.Allocator.Lemmas
module Mark = GC.Spec.Mark
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
module RT = GC.Gen.RefTable
module CE = GC.Gen.CheneyGeneric
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

/// The same, with the non-minor roots not free.
let roots_valid_with
  (free: free_def) (minor: minor_state) (major: heap) (roots: seq U64.t) : prop =
  MCFH.roots_valid_with free minor major roots

/// Raw-address view of graph-edge membership, useful when the endpoint is a
/// forwarding-map image whose `hp_addr` refinement is proved by preconditions.
let mem_graph_edge_at (g: graph_state) (src dst: U64.t) : prop =
  MCFH.mem_graph_edge_at g src dst

/// The image of a classified root is named by a rewritten root --- either
/// directly, or, when the root is an interior nursery pointer, as the
/// *resolution* of one.
///
/// `classify_root` resolves, so the vertex `CG.MinorV w` may have been
/// contributed by an interior root `r` with `resolve_minor minor r == w`
/// rather than by `w` itself.  `rewrite_root` does *not* resolve --- an
/// interior root must keep its offset at run time --- so it maps that `r` to
/// `fwd r`, an interior pointer into the promoted copy of the closure.
/// `MCFH.fwd_image_resolves` says that address resolves to `fwd w`, which is
/// exactly `fwd_morphism fwd u`.
val normal_classified_root_image_in_rewrite_roots
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def)
  (roots: seq U64.t) (u: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_shape_with free minor major fp /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      Seq.mem u (CG.classify_roots minor roots) /\
      MCFH.normal_vertex_ready minor major fp roots u)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec_with free minor major fp roots in
      let img = CG.fwd_morphism prom.fwd_map u in
      Seq.mem img (rewrite_roots roots prom.fwd_map) \/
      (exists (rr: U64.t).
         Seq.mem rr (rewrite_roots roots prom.fwd_map) /\
         HeapGraph.resolve_field res.mc_major rr == img)))

let normal_src_edge
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def) (roots: seq U64.t)
  (u w: CG.combined_vertex) : prop =
  let cg = CG.build_combined_graph minor major free in
  MCFH.normal_src_reachable minor major fp free roots u /\
  MCFH.normal_src_reachable minor major fp free roots w /\
  CG.mem_ce (u, w) cg /\
  MCFNE.normal_edge_forward_ready minor major fp roots u w

noeq type ready_src_reach
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def) (roots: seq U64.t)
  : CG.combined_vertex -> Type =
  | ReadyRoot :
      u:CG.combined_vertex ->
      (Seq.mem u (CG.classify_roots minor roots) /\
       CG.mem_cv u (CG.build_combined_graph minor major free) /\
       MCFH.normal_vertex_ready minor major fp roots u) ->
      ready_src_reach minor major fp free roots u
  | ReadyStep :
      u:CG.combined_vertex ->
      w:CG.combined_vertex ->
      ready_src_reach minor major fp free roots u ->
      normal_src_edge minor major fp free roots u w ->
      ready_src_reach minor major fp free roots w

let ready_src_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def) (roots: seq U64.t)
  (u: CG.combined_vertex) : prop =
  exists (_: ready_src_reach minor major fp free roots u). True

let ready_image_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def) (roots: seq U64.t)
  (w: U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  exists (u: CG.combined_vertex).
    ready_src_reachable minor major fp free roots u /\
    CG.fwd_morphism prom.fwd_map u == w

let normal_image_edge
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def) (roots: seq U64.t)
  (x y: U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  exists (u w: CG.combined_vertex).
    normal_src_edge minor major fp free roots u w /\
    CG.fwd_morphism prom.fwd_map u == x /\
    CG.fwd_morphism prom.fwd_map w == y

val normal_image_vertex_is_post_vertex
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def) (roots: seq U64.t)
  (w: U64.t)
  : Lemma
    (requires
      GenInv.collection_shape_with free minor major fp /\
      MCFH.normal_image_reachable minor major fp free roots w)
    (ensures (
      let res = cheney_collect_spec_with free minor major fp roots in
      MCFH.mem_graph_vertex_at (HeapModel.create_graph_with free res.mc_major) w))

val normal_classified_root_image_post_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def)
  (roots: seq U64.t) (u: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_shape_with free minor major fp /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      Seq.mem u (CG.classify_roots minor roots) /\
      MCFH.normal_src_reachable minor major fp free roots u)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      MCFH.post_minor_reachable minor major fp free roots
        (CG.fwd_morphism prom.fwd_map u)))

let normal_image_reachable_subgraph_isomorphism_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def) (roots: seq U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  CG.reachable_subgraph_isomorphism
    (MCFH.normal_src_reachable minor major fp free roots)
    (MCFH.normal_image_reachable minor major fp free roots)
    (normal_src_edge minor major fp free roots)
    (normal_image_edge minor major fp free roots)
    prom.fwd_map

val normal_image_reachable_subgraph_isomorphism
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_shape_with free minor major fp /\
      RBridge.roots_not_free free roots major /\
      MCFNE.fwd_disjoint_reachable_major minor major fp free roots)
    (ensures normal_image_reachable_subgraph_isomorphism_prop minor major fp free roots)

val normal_src_edge_preserves_post_minor_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def)
  (roots slots: seq U64.t) (n: nat)
  (u w: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_shape_with free minor major fp /\
      RBridge.major_fields_covered minor major free roots /\
      RT.ref_table_covers_with free major slots n /\
      remembered_targets_in_roots major roots slots n /\
      RBridge.roots_not_free free roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      normal_src_edge minor major fp free roots u w /\
      (let prom = cheney_promote minor major fp roots in
       MCFH.post_minor_reachable minor major fp free roots
         (CG.fwd_morphism prom.fwd_map u)))
    (ensures (
      let prom = cheney_promote minor major fp roots in
      MCFH.post_minor_reachable minor major fp free roots
        (CG.fwd_morphism prom.fwd_map w)))

val ready_src_reach_image_post_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def)
  (roots slots: seq U64.t) (n: nat)
  (u: CG.combined_vertex)
  (r: ready_src_reach minor major fp free roots u)
  : Lemma
    (requires
      GenInv.collection_shape_with free minor major fp /\
      RBridge.major_fields_covered minor major free roots /\
      RT.ref_table_covers_with free major slots n /\
      remembered_targets_in_roots major roots slots n /\
      RBridge.roots_not_free free roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      MCFH.post_minor_reachable minor major fp free roots
        (CG.fwd_morphism prom.fwd_map u)))

val ready_image_reachable_is_post_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def)
  (roots slots: seq U64.t) (n: nat)
  (w: U64.t)
  : Lemma
    (requires
      GenInv.collection_shape_with free minor major fp /\
      RBridge.major_fields_covered minor major free roots /\
      RT.ref_table_covers_with free major slots n /\
      remembered_targets_in_roots major roots slots n /\
      RBridge.roots_not_free free roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      ready_image_reachable minor major fp free roots w)
    (ensures MCFH.post_minor_reachable minor major fp free roots w)

val normal_src_reachable_is_ready_src_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def)
  (roots slots: seq U64.t) (n: nat)
  (u: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_shape_with free minor major fp /\
      RBridge.major_fields_covered minor major free roots /\
      RT.ref_table_covers_with free major slots n /\
      remembered_targets_in_roots major roots slots n /\
      RBridge.roots_not_free free roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      MCFH.normal_src_reachable minor major fp free roots u)
    (ensures ready_src_reachable minor major fp free roots u)

let normal_image_reachable_is_post_reachable_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def) (roots: seq U64.t) : prop =
  forall (w: U64.t).
    MCFH.normal_image_reachable minor major fp free roots w ==>
    MCFH.post_minor_reachable minor major fp free roots w

val normal_image_reachable_is_post_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def)
  (roots slots: seq U64.t) (n: nat)
  (w: U64.t)
  : Lemma
    (requires
      GenInv.collection_shape_with free minor major fp /\
      RBridge.major_fields_covered minor major free roots /\
      RT.ref_table_covers_with free major slots n /\
      remembered_targets_in_roots major roots slots n /\
      RBridge.roots_not_free free roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      MCFH.normal_image_reachable minor major fp free roots w)
    (ensures MCFH.post_minor_reachable minor major fp free roots w)

val normal_image_reachable_is_post_reachable_all
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def)
  (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      GenInv.collection_shape_with free minor major fp /\
      RBridge.major_fields_covered minor major free roots /\
      RT.ref_table_covers_with free major slots n /\
      remembered_targets_in_roots major roots slots n /\
      RBridge.roots_not_free free roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures normal_image_reachable_is_post_reachable_prop minor major fp free roots)

val post_normal_image_edges_reflect_src
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def)
  (roots slots: seq U64.t) (n: nat)
  (u w: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_shape_with free minor major fp /\
      RBridge.major_fields_covered minor major free roots /\
      RT.ref_table_covers_with free major slots n /\
      remembered_targets_in_roots major roots slots n /\
      RBridge.roots_not_free free roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      MCFH.normal_src_reachable minor major fp free roots u /\
      MCFH.normal_src_reachable minor major fp free roots w /\
      (let prom = cheney_promote minor major fp roots in
       MCFH.post_minor_edge minor major fp free roots
         (CG.fwd_morphism prom.fwd_map u)
         (CG.fwd_morphism prom.fwd_map w)))
    (ensures normal_src_edge minor major fp free roots u w)

let post_minor_reachable_is_normal_image_reachable_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def) (roots: seq U64.t) : prop =
  forall (w: U64.t).
    MCFH.post_minor_reachable minor major fp free roots w ==>
    MCFH.normal_image_reachable minor major fp free roots w

let normal_post_reachable_subgraph_isomorphism_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def) (roots: seq U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  CG.reachable_subgraph_isomorphism
    (MCFH.normal_src_reachable minor major fp free roots)
    (MCFH.post_minor_reachable minor major fp free roots)
    (normal_src_edge minor major fp free roots)
    (MCFH.post_minor_edge minor major fp free roots)
    prom.fwd_map

let normal_result_reachable_subgraph_isomorphism_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def) (roots: seq U64.t)
  (post_major: heap) (post_roots: seq U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  CG.reachable_subgraph_isomorphism
    (MCFH.normal_src_reachable minor major fp free roots)
    (MCFH.result_post_reachable post_major free post_roots)
    (normal_src_edge minor major fp free roots)
    (MCFH.result_post_edge post_major free)
    prom.fwd_map

let normal_post_non_pointer_fields_preserved_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def) (roots: seq U64.t) : prop =
  MCFNP.normal_post_non_pointer_fields_preserved_prop minor major fp free roots

let normal_result_non_pointer_fields_preserved_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def) (roots: seq U64.t)
  (post_major: heap) : prop =
  MCFNP.normal_result_non_pointer_fields_preserved_prop
    minor major fp free roots post_major
val post_minor_reachable_is_normal_image_reachable_all
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def)
  (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      GenInv.collection_shape_with free minor major fp /\
      RBridge.major_fields_covered minor major free roots /\
      RT.ref_table_covers_with free major slots n /\
      remembered_targets_in_roots major roots slots n /\
      roots_valid_with free minor major roots /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures post_minor_reachable_is_normal_image_reachable_prop minor major fp free roots)

val normal_post_reachable_subgraph_isomorphism
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def)
  (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      GenInv.collection_shape_with free minor major fp /\
      RBridge.major_fields_covered minor major free roots /\
      RT.ref_table_covers_with free major slots n /\
      remembered_targets_in_roots major roots slots n /\
      roots_valid_with free minor major roots /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures normal_post_reachable_subgraph_isomorphism_prop minor major fp free roots)

val normal_post_reachable_subgraph_isomorphism_to_result
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def) (roots: seq U64.t)
  (post_major: heap) (post_roots: seq U64.t)
  : Lemma
    (requires
      post_major == (cheney_collect_spec_with free minor major fp roots).mc_major /\
      post_roots == MCFH.resolve_roots post_major
                      (rewrite_roots roots (cheney_promote minor major fp roots).fwd_map) /\
      normal_post_reachable_subgraph_isomorphism_prop minor major fp free roots)
    (ensures
      normal_result_reachable_subgraph_isomorphism_prop
        minor major fp free roots post_major post_roots)

val normal_post_non_pointer_fields_preserved
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def)
  (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      GenInv.collection_shape_with free minor major fp /\
      RBridge.major_fields_covered minor major free roots /\
      RT.ref_table_covers_with free major slots n /\
      remembered_targets_in_roots major roots slots n /\
      roots_valid_with free minor major roots /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures normal_post_non_pointer_fields_preserved_prop minor major fp free roots)

val normal_post_non_pointer_fields_preserved_to_result
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def) (roots: seq U64.t)
  (post_major: heap)
  : Lemma
    (requires
      post_major == (cheney_collect_spec_with free minor major fp roots).mc_major /\
      normal_post_non_pointer_fields_preserved_prop minor major fp free roots)
    (ensures
      normal_result_non_pointer_fields_preserved_prop
        minor major fp free roots post_major)

/// The stop-the-world context gives the generic one at `free_stw`.  (The
/// collection at `free_stw` is `cheney_collect_spec`:
/// `GC.Gen.CheneyGeneric.cheney_collect_spec_with_stw`.)
val stop_the_world_context
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires GenInv.collection_heap_shape minor major fp)
    (ensures
      GenInv.collection_shape_with free_stw minor major fp /\
      well_formed_heap_with free_stw major /\
      GenInv.minor_major_fields_not_free free_stw minor major /\
      (roots_valid_for_minor_collection minor major roots ==>
       roots_valid_with free_stw minor major roots /\
       RBridge.roots_not_free free_stw roots major))
