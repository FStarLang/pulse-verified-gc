/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectForwarding.Reflection
/// ---------------------------------------------------------------------------
///
/// Focused post-minor edge reflection lemmas for the forwarding proof.

module GC.Gen.MinorCollectForwarding.Reflection

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

module Mark = GC.Spec.Mark
module CheneyBFS = GC.Gen.CheneyBFS
module CG = GC.Gen.CombinedGraph
module RBridge = GC.Gen.ReachabilityBridge
module GenInv = GC.Gen.HeapInvariant
module HeapModel = GC.Spec.HeapModel
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module RT = GC.Gen.RefTable
module CE = GC.Gen.CheneyView
module MCFNE = GC.Gen.MinorCollectForwarding.NormalEdges

let normal_image_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (v: view) (roots: seq U64.t)
  (w: U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  exists (u: CG.combined_vertex).
    MCFNE.normal_src_reachable minor major fp v roots u /\
    CG.fwd_morphism prom.fwd_map u == w

val post_edge_from_minor_image_reflects_mem_ce
  (minor: minor_state) (major: heap) (fp: U64.t) (v: view)
  (roots slots: seq U64.t) (n: nat)
  (src: U64.t) (w: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_shape_view v minor major fp /\ CE.promotion_in_view v minor major fp roots /\
      RBridge.major_fields_covered minor major v roots /\
      RT.ref_table_covers_view v major slots n /\
      MCFH.remembered_targets_in_roots major roots slots n /\
      RBridge.roots_in_view v roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      MCFNE.normal_src_reachable minor major fp v roots (CG.MinorV src) /\
      MCFNE.normal_src_reachable minor major fp v roots w /\
      (let prom = cheney_promote minor major fp roots in
       MCFH.post_minor_edge minor major fp v roots (prom.fwd_map src)
         (CG.fwd_morphism prom.fwd_map w)))
    (ensures CG.mem_ce (CG.MinorV src, w) (CG.build_combined_graph minor major v))

val post_edge_from_minor_image_reflects_target
  (minor: minor_state) (major: heap) (fp: U64.t) (v: view)
  (roots slots: seq U64.t) (n: nat)
  (src y: U64.t)
  : Lemma
    (requires
      GenInv.collection_shape_view v minor major fp /\ CE.promotion_in_view v minor major fp roots /\
      RBridge.major_fields_covered minor major v roots /\
      RT.ref_table_covers_view v major slots n /\
      MCFH.remembered_targets_in_roots major roots slots n /\
      RBridge.roots_in_view v roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      MCFNE.normal_src_reachable minor major fp v roots (CG.MinorV src) /\
      (let prom = cheney_promote minor major fp roots in
       MCFH.post_minor_edge minor major fp v roots (prom.fwd_map src) y) /\
      (let res = cheney_collect_spec_view v minor major fp roots in
       MCFH.mem_graph_vertex_at (HeapModel.create_graph_view v res.mc_major) y))
    (ensures normal_image_reachable minor major fp v roots y)
