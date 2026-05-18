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
/// Main discharge lemma
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let discharge_structural_preconditions
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (combined_roots: seq combined_vertex)
  (major_stack: seq obj_addr)
  : Lemma
    (requires
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp /\
      iso_remaining_preconditions minor major fp roots combined_roots major_stack)
    (ensures
      TopLevel.iso_structural_preconditions minor major fp roots combined_roots major_stack)
  = // Invoke the proven Cheney BFS theorems
    CheneyInj.cheney_promote_fwd_injective minor major fp roots;
    CheneyDisj.cheney_promote_fwd_disjoint_nonblue minor major fp roots;
    // The remaining conjuncts come from iso_remaining_preconditions.
    // Conjunct (3) — fwd injectivity on live_set:
    //   From iso_remaining we have fwd_nonzero: forall v in live_set. fwd v <> 0.
    //   From CheneyInj: fwd_injective = forall a b. fwd a <> 0 /\ fwd b <> 0 /\ fwd a == fwd b ==> a == b.
    //   Combining: forall a b in live_set. fwd a == fwd b ==> (fwd a <> 0 /\ fwd b <> 0) ==> a == b.
    // Conjunct (6) — promoted disjoint from non-blue:
    //   CheneyDisj gives: forall a obj. fwd a <> 0 /\ mem obj ... ==> fwd a <> obj.
    //   The iso conjunct adds `mem v live_set` which is weaker.
    ()
#pop-options
