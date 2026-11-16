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
module CE = GC.Gen.CheneyGeneric
module MCFNE = GC.Gen.MinorCollectForwarding.NormalEdges

val post_edge_from_minor_image_reflects_mem_ce (ph: gc_phase)
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def)
  (roots slots: seq U64.t) (n: nat)
  (src: U64.t) (w: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_shape_with ph free minor major fp /\
      RBridge.major_fields_covered minor major free roots /\
      RT.ref_table_covers_with free major slots n /\
      MCFH.remembered_targets_in_roots major roots slots n /\
      RBridge.roots_not_free free roots major /\
      CheneyBFS.cheney_no_oom ph minor major fp roots /\
      MCFH.normal_src_reachable ph minor major fp free roots (CG.MinorV src) /\
      MCFH.normal_src_reachable ph minor major fp free roots w /\
      (let prom = cheney_promote ph minor major fp roots in
       MCFH.post_minor_edge ph minor major fp free roots (prom.fwd_map src)
         (CG.fwd_morphism prom.fwd_map w)))
    (ensures CG.mem_ce (CG.MinorV src, w) (CG.build_combined_graph minor major free))

val post_edge_from_minor_image_reflects_target (ph: gc_phase)
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def)
  (roots slots: seq U64.t) (n: nat)
  (src y: U64.t)
  : Lemma
    (requires
      GenInv.collection_shape_with ph free minor major fp /\
      RBridge.major_fields_covered minor major free roots /\
      RT.ref_table_covers_with free major slots n /\
      MCFH.remembered_targets_in_roots major roots slots n /\
      RBridge.roots_not_free free roots major /\
      CheneyBFS.cheney_no_oom ph minor major fp roots /\
      MCFH.normal_src_reachable ph minor major fp free roots (CG.MinorV src) /\
      (let prom = cheney_promote ph minor major fp roots in
       MCFH.post_minor_edge ph minor major fp free roots (prom.fwd_map src) y) /\
      (let res = cheney_collect_spec_with ph free minor major fp roots in
       MCFH.mem_graph_vertex_at (HeapModel.create_graph_with free res.mc_major) y))
    (ensures MCFH.normal_image_reachable ph minor major fp free roots y)
