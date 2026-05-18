/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyDischarge — Implementation of partial discharge
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyDischarge

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
open GC.Gen.CombinedGraph
open GC.Gen.Cheney
open GC.Gen.Correctness

module AllocLemmas = GC.Spec.Allocator.Lemmas
module Iso = GC.Gen.CombinedGraph.Isomorphism
module TopLevel = GC.Gen.CombinedGraph.Isomorphism.TopLevel
module CheneyInj = GC.Gen.CheneyInjectivity
module CheneyDisj = GC.Gen.CheneyDisjoint
module PromUpdate = GC.Gen.PromoteUpdate
module RBridge = GC.Gen.ReachabilityBridge
module CheneyBFS = GC.Gen.CheneyBFS
module Reach = GC.Gen.Reachability
module CheneyCorr = GC.Gen.CheneyCorrectness

/// ---------------------------------------------------------------------------
/// Phase A: allocated_objects_avoid_chain from chain_objects_blue
/// ---------------------------------------------------------------------------

/// chain_objects_blue and allocated_objects_avoid_chain are definitionally
/// identical (same quantifier body). chain_objects_blue is opaque_to_smt,
/// so we must normalize to reveal its definition.
let chain_blue_implies_alloc_avoids (major: heap) (fp: U64.t)
  : Lemma (requires chain_objects_blue major fp)
          (ensures allocated_objects_avoid_chain major fp)
  = norm_spec [delta_only [`%chain_objects_blue]] (chain_objects_blue major fp)

/// ---------------------------------------------------------------------------
/// Fwd targets in mc_major: bridges promote-phase validity to post-collect
/// ---------------------------------------------------------------------------

/// All nonzero forwarding targets are valid objects in the post-collection
/// major heap (mc_major). Combines:
///   - cheney_promote_fwd_targets_valid (targets in prom.major_final)
///   - update_major_pointers_preserves_objects (objects unchanged by update)
let cheney_fwd_targets_in_mc_major
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec minor major fp roots in
      forall (a: U64.t). prom.fwd_map a <> 0UL ==>
        (U64.v (prom.fwd_map a) >= U64.v mword /\
         U64.v (prom.fwd_map a) < heap_size /\
         U64.v (prom.fwd_map a) % U64.v mword == 0 /\
         Seq.mem ((prom.fwd_map a) <: obj_addr) (objects zero_addr res.mc_major))))
  = CheneyInj.cheney_promote_fwd_targets_valid minor major fp roots;
    let prom = cheney_promote minor major fp roots in
    cheney_promote_preserves_wfh_part1 minor major fp roots;
    PromUpdate.update_major_pointers_preserves_objects prom.major_final prom.fwd_map

/// ---------------------------------------------------------------------------
/// Helper: live_set ⊆ minor_reachable minor roots when remembered ⊆ roots
/// ---------------------------------------------------------------------------

/// Proves that every object in live_set_of (which uses append roots remembered)
/// is also in minor_reachable minor roots, provided remembered ⊆ roots.
/// Uses the induction principle: P(x) = "mem x (minor_reachable minor roots)"
/// holds for roots (trivially) and is closed under successors.
private
let live_set_subset_reachable
  (minor: minor_state) (major: heap) (roots: seq U64.t)
  : Lemma
    (requires forall (m: U64.t). Seq.mem m (minor_roots_from_major major) ==> Seq.mem m roots)
    (ensures (let live_set = live_set_of minor major roots in
              forall (v: U64.t). Seq.mem v live_set ==> Seq.mem v (Reach.minor_reachable minor roots)))
  = let remembered = minor_roots_from_major major in
    let extended = Seq.append roots remembered in
    // Goal: forall v in minor_reachable minor extended ==> v in minor_reachable minor roots
    // Proof: use minor_reachable_ind with P(v) = mem v (minor_reachable minor roots)
    let p (v: U64.t) : prop = Seq.mem v (Reach.minor_reachable minor roots) in
    // Base: any root in extended that is a minor_object is in minor_reachable minor roots
    let base_case (r: U64.t)
      : Lemma (requires Seq.mem r extended /\ Seq.mem r (minor_objects minor))
              (ensures p r)
      = Seq.lemma_mem_append roots remembered;
        // r ∈ extended <==> r ∈ roots \/ r ∈ remembered
        // Since remembered ⊆ roots, r ∈ roots either way
        Reach.minor_reachable_roots minor roots
    in
    // Step: P is closed under minor_successors
    let step_case (a b: U64.t)
      : Lemma (requires p a /\ Seq.mem b (Reach.minor_successors minor a))
              (ensures p b)
      = Reach.minor_reachable_closed minor roots a b
    in
    // Apply induction for each v in live_set
    let aux (v: U64.t)
      : Lemma (requires Seq.mem v (Reach.minor_reachable minor extended))
              (ensures Seq.mem v (Reach.minor_reachable minor roots))
      = Classical.forall_intro (Classical.move_requires base_case);
        Classical.forall_intro_2 (fun a -> Classical.move_requires (step_case a));
        Reach.minor_reachable_ind minor extended p v
    in
    Classical.forall_intro (Classical.move_requires aux)

/// ---------------------------------------------------------------------------
/// Main discharge lemma
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
let discharge_structural_preconditions
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (combined_roots: seq combined_vertex)
  (major_stack: seq obj_addr)
  : Lemma
    (requires
      well_formed_heap major /\
      minor_wf minor /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp /\
      CheneyDisj.nonblue_wosize_positive major /\
      combined_roots == classify_roots roots /\
      GC.Spec.Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      RBridge.major_field_one_plus_in_remembered minor major /\
      RBridge.major_field_zero_no_minor minor major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      (forall (m: U64.t). Seq.mem m (minor_roots_from_major major) ==> Seq.mem m roots) /\
      (let live_set = live_set_of minor major roots in
       forall (v: U64.t). Seq.mem v live_set ==> minor_wosize minor v > 0) /\
      iso_remaining_preconditions minor major fp roots combined_roots major_stack)
    (ensures
      TopLevel.iso_structural_preconditions minor major fp roots combined_roots major_stack)
  = // Invoke the proven Cheney BFS theorems
    CheneyInj.cheney_promote_fwd_injective minor major fp roots;
    CheneyDisj.cheney_promote_fwd_disjoint_nonblue minor major fp roots;
    // Invoke ReachabilityBridge for conjuncts (5) and (7)
    RBridge.reachability_bridge minor major roots;
    RBridge.reachable_major_valid_nonblue minor major roots;
    // Derive conjunct (2): fwd nonzero on live_set
    // Step 1: live_set ⊆ minor_reachable minor roots
    live_set_subset_reachable minor major roots;
    // Step 2: cheney_promotes_all_reachable gives fwd v <> 0 for reachable with wosize > 0
    CheneyCorr.cheney_promotes_all_reachable minor major fp roots;
    ()
#pop-options
