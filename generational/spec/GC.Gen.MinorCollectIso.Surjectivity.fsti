/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectIso.Surjectivity — Surjectivity proof
/// ---------------------------------------------------------------------------
///
/// Proves property (H): every mc_major-reachable vertex has a combined-reachable
/// pre-image under fwd_morphism.

module GC.Gen.MinorCollectIso.Surjectivity

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Spec.HeapModel
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Remembered
open GC.Gen.CombinedGraph
open GC.Gen.Cheney
open GC.Gen.Correctness
open GC.Gen.MinorCollectIso

module Iso = GC.Gen.CombinedGraph.Isomorphism

/// (H) Surjectivity: every mc_major-reachable vertex has a combined-reachable pre-image.
val prove_surjectivity
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires minor_collect_iso_preconditions minor major fp roots)
    (ensures (
      let combined_roots = pre_gc_roots roots in
      let cg = build_combined_graph minor major in
      let prom = cheney_promote minor major fp roots in
      let fwd = prom.fwd_map in
      let res = cheney_collect_spec minor major fp roots in
      let g_mc = create_graph res.mc_major in
      let mc_roots = res.mc_roots in
      forall (v: U64.t) (root: U64.t).
        Seq.mem root mc_roots /\
        U64.v root >= U64.v mword /\ U64.v root < heap_size /\ U64.v root % U64.v mword == 0 /\
        Seq.mem (root <: hp_addr) g_mc.vertices /\
        U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
        Seq.mem (v <: hp_addr) g_mc.vertices /\
        reachable g_mc (root <: hp_addr) (v <: hp_addr) ==>
        (exists (cv: combined_vertex).
          combined_reachable cg combined_roots cv /\
          Iso.fwd_morphism fwd cv == v)))
