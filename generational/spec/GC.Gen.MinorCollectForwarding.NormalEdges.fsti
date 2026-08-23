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
open GC.Gen.Remembered
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
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
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

let fwd_disjoint_reachable_major
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  let cg = CG.build_combined_graph minor major in
  let combined_roots = CG.classify_roots roots in
  let prom = cheney_promote minor major fp roots in
  forall (x y: U64.t).
    CG.combined_reachable cg combined_roots (CG.MinorV x) /\
    CG.combined_reachable cg combined_roots (CG.MajorV y) /\
    prom.fwd_map x <> 0UL /\
    is_val_addr (prom.fwd_map x) /\
    is_infix (prom.fwd_map x) prom.major_final = false ==>
    prom.fwd_map x <> y

val fwd_disjoint_reachable_major_intro
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major)
    (ensures fwd_disjoint_reachable_major minor major fp roots)

val minor_source_edge_not_no_scan
  (minor: minor_state) (major: heap) (fp: U64.t)
  (src: U64.t) (dst: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      CG.mem_ce (CG.MinorV src, dst) (CG.build_combined_graph minor major))
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
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (u: CG.combined_vertex) : prop =
  let cg = CG.build_combined_graph minor major in
  let combined_roots = CG.classify_roots roots in
  CG.combined_reachable cg combined_roots u /\
  normal_vertex_ready minor major fp roots u

let combined_reachable_normal_injective_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  let cg = CG.build_combined_graph minor major in
  let combined_roots = CG.classify_roots roots in
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
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      fwd_disjoint_reachable_major minor major fp roots)
    (ensures combined_reachable_normal_injective_prop minor major fp roots)

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

val normal_src_images_injective
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (u v: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      normal_src_reachable minor major fp roots u /\
      normal_src_reachable minor major fp roots v /\
      (let prom = cheney_promote minor major fp roots in
       CG.fwd_morphism prom.fwd_map u == CG.fwd_morphism prom.fwd_map v))
    (ensures u == v)
