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
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module Cheney = GC.Gen.Cheney
module CheneyBFS = GC.Gen.CheneyBFS
module CheneyPres = GC.Gen.CheneyPreservation
module CG = GC.Gen.CombinedGraph
module RBridge = GC.Gen.ReachabilityBridge
module GenInv = GC.Gen.HeapInvariant
module HeapGraph = GC.Spec.HeapGraph
module HeapModel = GC.Spec.HeapModel

module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module TPC = GC.Gen.TwoPassEquiv.Collect
module CE = GC.Gen.CheneyExcept
open GC.Gen.MinorCollectForwarding.Helpers
module MCFE = GC.Gen.MinorCollectForwarding.Edges
open GC.Gen.MinorCollectForwarding.Edges

let normal_edge_forward_ready
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (u v: CG.combined_vertex) : prop =
  let prom = cheney_promote minor major fp roots in
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

val combined_reachable_edge_forwarded_normal
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop)
  (roots slots: seq U64.t) (n: nat)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_shape_except minor major fp pf /\
      RBridge.major_fields_covered minor major pf roots /\
      TPC.ref_table_covers_except major pf slots n /\
      remembered_targets_in_roots major roots slots n /\
      RBridge.roots_not_freed roots major pf /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      (let cg = CG.build_combined_graph minor major pf in
       let combined_roots = CG.classify_roots minor roots in
       CG.combined_reachable cg combined_roots u /\
       CG.combined_reachable cg combined_roots v /\
       CG.mem_ce (u, v) cg) /\
      normal_edge_forward_ready minor major fp roots u v)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec_except minor major fp roots pf in
      mem_graph_edge_at (HeapModel.create_graph_except res.mc_major pf)
        (CG.fwd_morphism prom.fwd_map u)
        (CG.fwd_morphism prom.fwd_map v)))

let fwd_disjoint_reachable_major
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t) : prop =
  let cg = CG.build_combined_graph minor major pf in
  let combined_roots = CG.classify_roots minor roots in
  let prom = cheney_promote minor major fp roots in
  forall (x y: U64.t).
    CG.combined_reachable cg combined_roots (CG.MinorV x) /\
    CG.combined_reachable cg combined_roots (CG.MajorV y) /\
    prom.fwd_map x <> 0UL /\
    is_val_addr (prom.fwd_map x) /\
    is_infix (prom.fwd_map x) prom.major_final = false ==>
    prom.fwd_map x <> y

val fwd_disjoint_reachable_major_intro
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_shape_except minor major fp pf /\
      RBridge.roots_not_freed roots major pf)
    (ensures fwd_disjoint_reachable_major minor major fp pf roots)

val minor_source_edge_not_no_scan
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop)
  (src: U64.t) (dst: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_shape_except minor major fp pf /\
      CG.mem_ce (CG.MinorV src, dst) (CG.build_combined_graph minor major pf))
    (ensures minor_tag minor src < 251)

let normal_vertex_ready
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (u: CG.combined_vertex) : prop =
  let prom = cheney_promote minor major fp roots in
  match u with
  | CG.MajorV _ -> True
  | CG.MinorV x ->
    prom.fwd_map x <> 0UL /\
    is_val_addr (prom.fwd_map x) /\
    is_infix (prom.fwd_map x) prom.major_final = false

let normal_src_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t)
  (u: CG.combined_vertex) : prop =
  let cg = CG.build_combined_graph minor major pf in
  let combined_roots = CG.classify_roots minor roots in
  CG.combined_reachable cg combined_roots u /\
  normal_vertex_ready minor major fp roots u

let combined_reachable_normal_injective_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t) : prop =
  let cg = CG.build_combined_graph minor major pf in
  let combined_roots = CG.classify_roots minor roots in
  let prom = cheney_promote minor major fp roots in
  forall (u v: CG.combined_vertex).
    CG.combined_reachable cg combined_roots u /\
    CG.combined_reachable cg combined_roots v /\
    (match u with
     | CG.MinorV x ->
       prom.fwd_map x <> 0UL /\
       is_val_addr (prom.fwd_map x) /\
       is_infix (prom.fwd_map x) prom.major_final = false
     | CG.MajorV _ -> True) /\
    (match v with
     | CG.MinorV x ->
       prom.fwd_map x <> 0UL /\
       is_val_addr (prom.fwd_map x) /\
       is_infix (prom.fwd_map x) prom.major_final = false
     | CG.MajorV _ -> True) /\
    CG.fwd_morphism prom.fwd_map u == CG.fwd_morphism prom.fwd_map v ==> u == v

val combined_reachable_normal_injective
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_shape_except minor major fp pf /\
      RBridge.roots_not_freed roots major pf /\
      fwd_disjoint_reachable_major minor major fp pf roots)
    (ensures combined_reachable_normal_injective_prop minor major fp pf roots)

val normal_edge_forward_ready_intro
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop)
  (roots: seq U64.t)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_shape_except minor major fp pf /\
      RBridge.roots_not_freed roots major pf /\
      normal_src_reachable minor major fp pf roots u /\
      normal_src_reachable minor major fp pf roots v /\
      CG.mem_ce (u, v) (CG.build_combined_graph minor major pf))
    (ensures normal_edge_forward_ready minor major fp roots u v)

val normal_src_images_injective
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop)
  (roots: seq U64.t) (u v: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_shape_except minor major fp pf /\
      RBridge.roots_not_freed roots major pf /\
      normal_src_reachable minor major fp pf roots u /\
      normal_src_reachable minor major fp pf roots v /\
      (let prom = cheney_promote minor major fp roots in
       CG.fwd_morphism prom.fwd_map u == CG.fwd_morphism prom.fwd_map v))
    (ensures u == v)
