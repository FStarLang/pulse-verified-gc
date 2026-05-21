/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectIso.EdgeForward — Edge forward + forward reachability proofs
/// ---------------------------------------------------------------------------
///
/// Proves properties (C) and (G) of the isomorphism theorem.
/// Isolated to prevent SMT context pollution from the 2000+ line main file.

module GC.Gen.MinorCollectIso.EdgeForward

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

/// (C) Edge forward: combined edges between reachable vertices are preserved in mc_major.
val prove_edge_forward
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
      forall (u v: combined_vertex).
        combined_reachable cg combined_roots u /\
        combined_reachable cg combined_roots v /\
        mem_ce (u, v) cg ==>
        (let fu = Iso.fwd_morphism fwd u in
         let fv = Iso.fwd_morphism fwd v in
         U64.v fu >= 0 /\ U64.v fu < heap_size /\ U64.v fu % U64.v mword == 0 /\
         U64.v fv >= 0 /\ U64.v fv < heap_size /\ U64.v fv % U64.v mword == 0 /\
         Seq.mem ((fu <: hp_addr), (fv <: hp_addr)) g_mc.edges)))

/// (G) Forward reachability: combined-reachable vertices are reachable from mc_roots in g_mc.
val prove_forward_reachability
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
      forall (v: combined_vertex).
        combined_reachable cg combined_roots v ==>
        (let w = Iso.fwd_morphism fwd v in
         U64.v w >= U64.v mword /\ U64.v w < heap_size /\ U64.v w % U64.v mword == 0 /\
         Seq.mem (w <: hp_addr) g_mc.vertices /\
         (exists (r: U64.t).
           Seq.mem r mc_roots /\
           U64.v r >= U64.v mword /\ U64.v r < heap_size /\ U64.v r % U64.v mword == 0 /\
           Seq.mem (r <: hp_addr) g_mc.vertices /\
           reachable g_mc (r <: hp_addr) (w <: hp_addr)))))
