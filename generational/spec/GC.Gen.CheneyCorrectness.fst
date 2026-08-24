/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyCorrectness — Proofs of Cheney collector correctness
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyCorrectness

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.PromoteUpdate
open GC.Gen.Cheney

module AllocLemmas = GC.Spec.Allocator.Lemmas

/// ---------------------------------------------------------------------------
/// Property 1: Object survival
/// ---------------------------------------------------------------------------

let cheney_collect_preserves_objects
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  =
  cheney_promote_preserves_objects minor major fp roots;
  let prom = cheney_promote minor major fp roots in
  wf_parts ();
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  update_major_pointers_preserves_objects prom.major_final prom.fwd_map

/// ---------------------------------------------------------------------------
/// Property 2: well_formed_heap_part1
/// ---------------------------------------------------------------------------

let cheney_collect_preserves_wfh_part1
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  =
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  let prom = cheney_promote minor major fp roots in
  update_major_pointers_preserves_wfh_part1 prom.major_final prom.fwd_map

/// ---------------------------------------------------------------------------
/// Property 3: Minor reset
/// ---------------------------------------------------------------------------

let cheney_collect_resets_minor
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  = ()

/// ---------------------------------------------------------------------------
/// Property 4: Root rewriting
/// ---------------------------------------------------------------------------

let cheney_collect_rewrites_roots
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  = ()

/// ---------------------------------------------------------------------------
/// Main theorem (properties 1-4, unconditional)
/// ---------------------------------------------------------------------------

let cheney_gc_correct
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  =
  cheney_collect_preserves_objects minor major fp roots;
  cheney_collect_preserves_wfh_part1 minor major fp roots;
  cheney_collect_resets_minor minor major fp roots;
  cheney_collect_rewrites_roots minor major fp roots;
  cheney_collect_preserves_fl_valid minor major fp roots

/// ---------------------------------------------------------------------------
/// Property 6: BFS completeness (conditional)
/// ---------------------------------------------------------------------------

open GC.Gen.Reachability
module BFS = GC.Gen.CheneyBFS

/// BFS completeness: delegates to CheneyBFS.cheney_promotes_all_reachable
/// which uses the reachability induction principle.
/// `w > 0 ==> b` is equivalent to `b \/ w = 0` for `w : nat`; the case split
/// diverges under the Cheney invariants, so it is discharged in isolation.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
private let disj_of_imp (w: nat) (b: bool) : Lemma (requires w > 0 ==> b) (ensures b \/ w = 0)
  = ()
#pop-options

let cheney_promotes_all_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  =
  BFS.cheney_promotes_all_reachable minor major fp roots;
  // BFS ensures: reachable /\ wosize > 0 ==> fwd <> 0
  // Goal: reachable ==> fwd <> 0 \/ wosize = 0
  // These are equivalent: (wosize > 0 ==> fwd <> 0) ↔ (fwd <> 0 \/ wosize = 0)
  // when wosize is nat (>= 0)
  let prom = cheney_promote minor major fp roots in
  let aux (x: U64.t)
    : Lemma (requires Seq.mem x (minor_reachable minor roots))
            (ensures prom.fwd_map x <> 0UL \/ minor_wosize minor x = 0)
    = disj_of_imp (minor_wosize minor x) (prom.fwd_map x <> 0UL)
  in
  Classical.forall_intro (Classical.move_requires aux)
