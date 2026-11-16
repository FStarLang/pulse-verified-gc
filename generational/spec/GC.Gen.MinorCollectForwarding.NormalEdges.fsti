/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectForwarding.NormalEdges
/// ---------------------------------------------------------------------------
///
/// Normal-object edge readiness and forwarding facts for the
/// minor-collection forwarding kernel.

module GC.Gen.MinorCollectForwarding.NormalEdges

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
module Cheney = GC.Gen.Cheney
module CheneyBFS = GC.Gen.CheneyBFS
module CheneyPres = GC.Gen.CheneyPreservation
module CG = GC.Gen.CombinedGraph
module RBridge = GC.Gen.ReachabilityBridge
module GenInv = GC.Gen.HeapInvariant
module HeapGraph = GC.Spec.HeapGraph
module HeapModel = GC.Spec.HeapModel

module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module RT = GC.Gen.RefTable
module CE = GC.Gen.CheneyGeneric
open GC.Gen.MinorCollectForwarding.Helpers
module MCFE = GC.Gen.MinorCollectForwarding.Edges
open GC.Gen.MinorCollectForwarding.Edges

let normal_edge_forward_ready (ph: gc_phase)
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (u v: CG.combined_vertex) : prop =
  let prom = cheney_promote ph minor major fp roots in
  let normal_minor_source (src: U64.t) =
    let fwd_src = prom.fwd_map src in
    fwd_src <> 0UL /\
    Seq.mem src (minor_objects minor) /\
    is_val_addr fwd_src /\
    is_infix fwd_src prom.major_final = false /\
    Seq.mem (fwd_src <: obj_addr) (objects zero_addr prom.major_final) /\
    is_blue (fwd_src <: obj_addr) prom.major_final = false /\
    is_no_scan (fwd_src <: obj_addr) prom.major_final = false /\
    U64.v (wosize_of_object (fwd_src <: obj_addr) prom.major_final) >=
      minor_wosize minor src /\
    (forall (i:nat). i < minor_wosize minor src ==>
      i < U64.v (wosize_of_object (fwd_src <: obj_addr) prom.major_final) /\
      U64.v fwd_src + i * 8 + 8 <= heap_size /\
      (U64.v fwd_src + i * 8) % 8 == 0)
  in
  match u, v with
  | CG.MajorV _, CG.MajorV _ -> True
  | CG.MajorV _, CG.MinorV dst ->
    minor_wosize minor dst > 0 /\
    HeapGraph.is_pointer_field (prom.fwd_map dst)
  | CG.MinorV src, CG.MajorV dst ->
    normal_minor_source src /\ is_val_addr dst
  | CG.MinorV src, CG.MinorV dst ->
    normal_minor_source src /\
    prom.fwd_map dst <> 0UL /\
    HeapGraph.is_pointer_field (prom.fwd_map dst) /\
    is_minor_pointer dst

val combined_reachable_edge_forwarded_normal (ph: gc_phase)
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def)
  (roots slots: seq U64.t) (n: nat)
  (u w: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_shape_with ph free minor major fp /\
      RBridge.major_fields_covered minor major free roots /\
      RT.ref_table_covers_with free major slots n /\
      remembered_targets_in_roots major roots slots n /\
      RBridge.roots_not_free free roots major /\
      CheneyBFS.cheney_no_oom ph minor major fp roots /\
      (let cg = CG.build_combined_graph minor major free in
       let combined_roots = CG.classify_roots minor roots in
       CG.combined_reachable cg combined_roots u /\
       CG.combined_reachable cg combined_roots w /\
       CG.mem_ce (u, w) cg) /\
      normal_edge_forward_ready ph minor major fp roots u w)
    (ensures (
      let prom = cheney_promote ph minor major fp roots in
      let res = cheney_collect_spec_with ph free minor major fp roots in
      mem_graph_edge_at (HeapModel.create_graph_with free res.mc_major)
        (CG.fwd_morphism prom.fwd_map u)
        (CG.fwd_morphism prom.fwd_map w)))

let fwd_disjoint_reachable_major (ph: gc_phase)
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def) (roots: seq U64.t) : prop =
  let cg = CG.build_combined_graph minor major free in
  let combined_roots = CG.classify_roots minor roots in
  let prom = cheney_promote ph minor major fp roots in
  forall (x y: U64.t).
    CG.combined_reachable cg combined_roots (CG.MinorV x) /\
    CG.combined_reachable cg combined_roots (CG.MajorV y) /\
    prom.fwd_map x <> 0UL /\
    is_val_addr (prom.fwd_map x) /\
    is_infix (prom.fwd_map x) prom.major_final = false ==>
    prom.fwd_map x <> y

val fwd_disjoint_reachable_major_intro (ph: gc_phase)
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_shape_with ph free minor major fp /\
      RBridge.roots_not_free free roots major)
    (ensures fwd_disjoint_reachable_major ph minor major fp free roots)

val minor_source_edge_not_no_scan (ph: gc_phase)
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def)
  (src: U64.t) (dst: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_shape_with ph free minor major fp /\
      CG.mem_ce (CG.MinorV src, dst) (CG.build_combined_graph minor major free))
    (ensures minor_tag minor src < 251)

let combined_reachable_normal_injective_prop (ph: gc_phase)
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def) (roots: seq U64.t) : prop =
  let cg = CG.build_combined_graph minor major free in
  let combined_roots = CG.classify_roots minor roots in
  let prom = cheney_promote ph minor major fp roots in
  forall (u w: CG.combined_vertex).
    CG.combined_reachable cg combined_roots u /\
    CG.combined_reachable cg combined_roots w /\
    (match u with
     | CG.MinorV x ->
       prom.fwd_map x <> 0UL /\
       is_val_addr (prom.fwd_map x) /\
       is_infix (prom.fwd_map x) prom.major_final = false
     | CG.MajorV _ -> True) /\
    (match w with
     | CG.MinorV x ->
       prom.fwd_map x <> 0UL /\
       is_val_addr (prom.fwd_map x) /\
       is_infix (prom.fwd_map x) prom.major_final = false
     | CG.MajorV _ -> True) /\
    CG.fwd_morphism prom.fwd_map u == CG.fwd_morphism prom.fwd_map w ==> u == w

val combined_reachable_normal_injective (ph: gc_phase)
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_shape_with ph free minor major fp /\
      RBridge.roots_not_free free roots major /\
      fwd_disjoint_reachable_major ph minor major fp free roots)
    (ensures combined_reachable_normal_injective_prop ph minor major fp free roots)

val normal_edge_forward_ready_intro (ph: gc_phase)
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def)
  (roots: seq U64.t)
  (u w: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_shape_with ph free minor major fp /\
      RBridge.roots_not_free free roots major /\
      normal_src_reachable ph minor major fp free roots u /\
      normal_src_reachable ph minor major fp free roots w /\
      CG.mem_ce (u, w) (CG.build_combined_graph minor major free))
    (ensures normal_edge_forward_ready ph minor major fp roots u w)

val normal_src_images_injective (ph: gc_phase)
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def)
  (roots: seq U64.t) (u w: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_shape_with ph free minor major fp /\
      RBridge.roots_not_free free roots major /\
      normal_src_reachable ph minor major fp free roots u /\
      normal_src_reachable ph minor major fp free roots w /\
      (let prom = cheney_promote ph minor major fp roots in
       CG.fwd_morphism prom.fwd_map u == CG.fwd_morphism prom.fwd_map w))
    (ensures u == w)
