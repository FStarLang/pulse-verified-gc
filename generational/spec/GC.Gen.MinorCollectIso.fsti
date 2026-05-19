/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectIso — Isomorphism theorem for minor_collect alone
/// ---------------------------------------------------------------------------
///
/// States that minor_collect (Cheney BFS promotion + pointer update) preserves
/// the reachable graph structure: the pre-GC combined graph restricted to
/// reachable vertices is isomorphic to the post-minor-collection graph
/// restricted to reachable vertices.
///
/// KEY DESIGN:
///   - No mark/sweep: target is mc_major directly
///   - combined_roots and mc_roots are COMPUTED (not free parameters)
///   - Surjectivity is DERIVED (from edge backward + path induction)
///   - Root correspondence is DERIVED (mc_roots = rewrite_roots roots fwd by def)
///   - Forward reachability is included in the isomorphism statement
///
/// What is proven internally:
///   (A) Injectivity — from CheneyInjectivity + CheneyDisjoint
///   (B) Image validity + forward reachability — from internal infrastructure
///   (C) Surjectivity — from edge_backward + root pre-images + path induction
///   (D) Edge biconditional — from field_correspondence + EdgeBridge
///
/// What the caller provides:
///   ONLY field_correspondence (a property of promote_all + update_major_pointers)
///   plus standard operational conditions that hold at minor_collect entry.
///
/// The isomorphism is witnessed by fwd_morphism:
///   MinorV v ↦ fwd(v)   (promoted copy in major heap)
///   MajorV v ↦ v        (identity on major objects)

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
module CheneyDisj = GC.Gen.CheneyDisjoint
module Reach = GC.Gen.Reachability
module RBridge = GC.Gen.ReachabilityBridge
module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark

/// ---------------------------------------------------------------------------
/// Computed roots (no free parameters)
/// ---------------------------------------------------------------------------

/// The pre-GC combined roots: each program root tagged by its generation.
/// This is fully determined by the program roots — no caller choice.
let pre_gc_roots (roots: seq U64.t) : GTot (seq combined_vertex) =
  classify_roots roots

/// The post-minor-collection roots for the mc_major graph.
/// These are the rewritten roots = rewrite_roots roots fwd.
/// We keep them as a sequence of U64 (may include non-pointer values).
/// For graph reachability, only those that are valid obj_addrs matter.
let post_gc_roots (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : GTot (seq U64.t) =
  (cheney_collect_spec minor major fp roots).mc_roots

/// ---------------------------------------------------------------------------
/// Isomorphism statement
/// ---------------------------------------------------------------------------

/// The isomorphism relates:
///   Source: reachable subgraph of (build_combined_graph minor major) from (classify_roots roots)
///   Target: reachable subgraph of (create_graph mc_major) from (post_gc_roots ... )
///
/// Properties:
///   (A) Injectivity: fwd_morphism injective on combined-reachable vertices
///   (B) Image validity + reachability: reachable pre-images map to reachable post-vertices
///   (C) Surjectivity: mc-reachable vertices have combined-reachable pre-images
///   (D) Edge biconditional: edges preserved in both directions
let minor_collect_isomorphism
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  let combined_roots = pre_gc_roots roots in
  let cg = build_combined_graph minor major in
  let prom = cheney_promote minor major fp roots in
  let fwd = prom.fwd_map in
  let res = cheney_collect_spec minor major fp roots in
  let g_mc = create_graph res.mc_major in
  // (A) Injectivity: distinct reachable vertices → distinct addresses
  (forall (u v: combined_vertex).
    combined_reachable cg combined_roots u /\
    combined_reachable cg combined_roots v /\
    Iso.fwd_morphism fwd u == Iso.fwd_morphism fwd v ==> u == v) /\
  // (B) Image validity + forward reachability:
  //     Combined-reachable vertices map to mc_major vertices that are reachable
  //     from mc_roots. This proves the morphism lands in the reachable subgraph.
  (forall (v: combined_vertex).
    combined_reachable cg combined_roots v ==>
    (let w = Iso.fwd_morphism fwd v in
     U64.v w >= U64.v mword /\ U64.v w < heap_size /\ U64.v w % U64.v mword == 0 /\
     Seq.mem (w <: hp_addr) g_mc.vertices /\
     // Forward reachability: the image is reachable from some mc_root
     (exists (r: U64.t). Seq.mem r res.mc_roots /\
       U64.v r >= U64.v mword /\ U64.v r < heap_size /\ U64.v r % U64.v mword == 0 /\
       Seq.mem (r <: hp_addr) g_mc.vertices /\
       reachable g_mc (r <: obj_addr) (w <: obj_addr)))) /\
  // (C) Surjectivity: every mc-reachable vertex has a combined-reachable pre-image
  (forall (w: vertex_id).
    Seq.mem w g_mc.vertices /\
    (exists (r: U64.t). Seq.mem r res.mc_roots /\
       U64.v r >= U64.v mword /\ U64.v r < heap_size /\ U64.v r % U64.v mword == 0 /\
       Seq.mem (r <: hp_addr) g_mc.vertices /\
       reachable g_mc (r <: obj_addr) w) ==>
    (exists (v: combined_vertex).
      combined_reachable cg combined_roots v /\
      Iso.fwd_morphism fwd v == (w <: U64.t))) /\
  // (D) Edge biconditional: edges preserved in both directions
  (forall (u v: combined_vertex).
    combined_reachable cg combined_roots u /\
    combined_reachable cg combined_roots v /\
    (let fu = Iso.fwd_morphism fwd u in
     let fv = Iso.fwd_morphism fwd v in
     U64.v fu >= U64.v mword /\ U64.v fu < heap_size /\ U64.v fu % U64.v mword == 0 /\
     U64.v fv >= U64.v mword /\ U64.v fv < heap_size /\ U64.v fv % U64.v mword == 0) ==>
    (mem_ce (u, v) cg <==>
     Seq.mem ((Iso.fwd_morphism fwd u <: hp_addr), (Iso.fwd_morphism fwd v <: hp_addr)) g_mc.edges))

/// ---------------------------------------------------------------------------
/// Preconditions — operational conditions + field_correspondence
/// ---------------------------------------------------------------------------

/// The operational preconditions for minor collection. These are standard GC
/// invariants that a correctly initialized system maintains.
let minor_collect_operational_preconditions
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  // Heap well-formedness
  well_formed_heap major /\
  minor_wf minor /\
  // Free-list validity
  AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
  AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
  chain_objects_blue major fp /\
  CheneyDisj.nonblue_wosize_positive major /\
  // BFS completeness (no OOM during promotion)
  CheneyBFS.cheney_no_oom minor major fp roots /\
  // Remembered set is included in roots (runtime invariant)
  (forall (m: U64.t). Seq.mem m (minor_roots_from_major major) ==> Seq.mem m roots) /\
  // Live objects have positive wosize (structural: minor objects always >= 1 word)
  (let live_set = live_set_of minor major roots in
   forall (v: U64.t). Seq.mem v live_set ==> minor_wosize minor v > 0) /\
  // Pointer invariants (no dangling pointers)
  Mark.no_pointer_to_blue major /\
  RBridge.minor_no_pointer_to_blue minor major /\
  RBridge.roots_valid_nonblue roots major /\
  RBridge.major_field_one_plus_in_remembered minor major /\
  RBridge.major_field_zero_no_minor minor major /\
  // No-scan invariants (structural)
  no_scan_invariant major /\
  minor_no_scan_invariant minor

/// The full precondition for the isomorphism theorem.
///
/// Beyond operational conditions, the ONLY non-trivial obligation is
/// field_correspondence: it captures that the promote_all + update_major_pointers
/// phases faithfully copy minor object fields and rewrite pointers.
///
/// Note: field_correspondence only covers promoted minor objects (source: MinorV).
/// Edge preservation from major sources (source: MajorV) is proven internally
/// using EdgePreservation.major_field_through_minor_collect and
/// EdgePreservation.major_field_forwarded_by_minor_collect.
let minor_collect_iso_preconditions
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  // Operational conditions
  minor_collect_operational_preconditions minor major fp roots /\
  // Field correspondence for promoted objects
  // States: for each live minor object obj (with fwd(obj) ≠ 0) and each field j:
  //   - if field j was a minor pointer p with fwd(p) ≠ 0: mc_major[fwd(obj)+j] = fwd(p)
  //   - otherwise: mc_major[fwd(obj)+j] = original minor field value
  (let prom = cheney_promote minor major fp roots in
   let res = cheney_collect_spec minor major fp roots in
   field_correspondence minor major res.mc_major prom.fwd_map roots)

/// ---------------------------------------------------------------------------
/// Main theorem
/// ---------------------------------------------------------------------------

/// Minor collection preserves the reachable graph structure.
///
/// Under standard operational conditions + field_correspondence, we derive
/// the full graph isomorphism between pre-GC and post-GC reachable subgraphs.
///
/// Proof architecture:
///   (A) Injectivity: CheneyInjectivity (fwd injective on live_set)
///                    + CheneyDisjoint (fwd targets ≠ pre-existing major objects)
///                    + ReachabilityBridge (reachable MinorV → in live_set)
///   (B) Image validity: cheney_fwd_targets_in_mc_major (MinorV targets valid)
///                       + cheney_collect_preserves_objects (MajorV survive)
///       Forward reachability: induction on combined-reachable path using edge_forward
///   (C) Surjectivity: path induction in g_mc:
///       - Base: mc_root r = fwd(root_i), so pre-image is classify_roots root_i
///       - Step: if w has pre-image v (combined-reachable), and (w, w') is edge,
///         then by "inverse morphism existence" there is v' with fwd_morphism(v')=w'
///         and mem_ce(v,v') (from field faithfulness). Then v' is combined-reachable.
///   (D) Edges: EdgeBridge (forward) + field_correspondence + injectivity (backward)
///
/// This is the PRIMARY correctness theorem for minor_collect. No mark/sweep needed.
val minor_collect_iso_theorem
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires minor_collect_iso_preconditions minor major fp roots)
    (ensures minor_collect_isomorphism minor major fp roots)
