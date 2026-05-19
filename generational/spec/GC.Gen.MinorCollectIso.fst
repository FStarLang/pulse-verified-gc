/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectIso — Implementation
/// ---------------------------------------------------------------------------
///
/// Proves the minor_collect_iso_theorem by assembling internal lemmas.

module GC.Gen.MinorCollectIso

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

module AllocLemmas = GC.Spec.Allocator.Lemmas
module Iso = GC.Gen.CombinedGraph.Isomorphism
module CheneyBFS = GC.Gen.CheneyBFS
module CheneyInj = GC.Gen.CheneyInjectivity
module CheneyDisj = GC.Gen.CheneyDisjoint
module Reach = GC.Gen.Reachability
module CheneyCorr = GC.Gen.CheneyCorrectness
module RBridge = GC.Gen.ReachabilityBridge
module CheneyDisch = GC.Gen.CheneyDischarge
module HeapGraph = GC.Spec.HeapGraph
module PromUpdate = GC.Gen.PromoteUpdate
module Mark = GC.Spec.Mark

/// ---------------------------------------------------------------------------
/// (A) Injectivity
/// ---------------------------------------------------------------------------
///
/// fwd_morphism is injective on combined-reachable vertices.
/// Proof: case split on vertex pairs:
///   MinorV a, MinorV b: fwd(a) == fwd(b) → a == b (CheneyInjectivity)
///   MajorV a, MajorV b: identity → trivial
///   MinorV a, MajorV b: fwd(a) == b impossible (CheneyDisjoint: fwd targets ∉ non-blue major)
///
/// Requires: reachability_bridge (MinorV → live_set) + reachable_major_valid_nonblue

private
let prove_injectivity
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires minor_collect_iso_preconditions minor major fp roots)
    (ensures (
      let combined_roots = pre_gc_roots roots in
      let cg = build_combined_graph minor major in
      let prom = cheney_promote minor major fp roots in
      let fwd = prom.fwd_map in
      forall (u v: combined_vertex).
        combined_reachable cg combined_roots u /\
        combined_reachable cg combined_roots v /\
        Iso.fwd_morphism fwd u == Iso.fwd_morphism fwd v ==> u == v))
  = CheneyInj.cheney_promote_fwd_injective minor major fp roots;
    CheneyDisj.cheney_promote_fwd_disjoint_nonblue minor major fp roots;
    RBridge.reachability_bridge minor major roots;
    RBridge.reachable_major_valid_nonblue minor major roots

/// ---------------------------------------------------------------------------
/// (B) Image validity
/// ---------------------------------------------------------------------------
///
/// Combined-reachable vertices map to valid mc_major vertices.
///   MinorV v: ReachabilityBridge → v ∈ live_set → fwd(v) ≠ 0
///             → cheney_fwd_targets_in_mc_major → fwd(v) valid in mc_major
///   MajorV v: reachable_major_valid_nonblue → v ∈ objects major
///             → cheney_collect_preserves_objects → v ∈ objects mc_major

private
let prove_image_validity
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
      forall (v: combined_vertex).
        combined_reachable cg combined_roots v ==>
        (let w = Iso.fwd_morphism fwd v in
         U64.v w >= U64.v mword /\ U64.v w < heap_size /\ U64.v w % U64.v mword == 0 /\
         Seq.mem (w <: hp_addr) g_mc.vertices)))
  = RBridge.reachability_bridge minor major roots;
    RBridge.reachable_major_valid_nonblue minor major roots;
    CheneyCorr.cheney_promotes_all_reachable minor major fp roots;
    CheneyDisch.cheney_fwd_targets_in_mc_major minor major fp roots;
    CheneyCorr.cheney_collect_preserves_objects minor major fp roots

/// ---------------------------------------------------------------------------
/// Main theorem: assemble all pieces
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
let minor_collect_iso_theorem
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires minor_collect_iso_preconditions minor major fp roots)
    (ensures minor_collect_isomorphism minor major fp roots)
  = // (A) Injectivity
    prove_injectivity minor major fp roots;
    // (B) Image validity (partial — forward reachability needs more work)
    prove_image_validity minor major fp roots;
    // (C) Surjectivity — needs edge backward + path induction
    // (D) Edge biconditional — needs EdgeBridge + field_correspondence
    // Forward reachability in (B) — needs edge forward + path induction
    admit () // Remaining: forward reachability, surjectivity, edge biconditional
#pop-options
