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
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words)
          (ensures (let res = cheney_collect_spec minor major fp roots in
                    forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                      Seq.mem x (objects zero_addr res.mc_major)))
  =
  cheney_promote_preserves_objects minor major fp roots;
  let prom = cheney_promote minor major fp roots in
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  update_major_pointers_preserves_objects prom.major_final prom.fwd_map

/// ---------------------------------------------------------------------------
/// Property 2: well_formed_heap_part1
/// ---------------------------------------------------------------------------

let cheney_collect_preserves_wfh_part1
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words)
          (ensures well_formed_heap_part1 (cheney_collect_spec minor major fp roots).mc_major)
  =
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  let prom = cheney_promote minor major fp roots in
  update_major_pointers_preserves_wfh_part1 prom.major_final prom.fwd_map

/// ---------------------------------------------------------------------------
/// Property 3: Minor reset
/// ---------------------------------------------------------------------------

let cheney_collect_resets_minor
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (ensures (let res = cheney_collect_spec minor major fp roots in
                    minor_wf res.mc_minor /\
                    U64.v res.mc_minor.bump == 0))
  = ()

/// ---------------------------------------------------------------------------
/// Property 4: Root rewriting
/// ---------------------------------------------------------------------------

let cheney_collect_rewrites_roots
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (ensures (let res = cheney_collect_spec minor major fp roots in
                    let prom = cheney_promote minor major fp roots in
                    res.mc_roots == rewrite_roots roots prom.fwd_map))
  = ()

/// ---------------------------------------------------------------------------
/// Main theorem (properties 1-4, unconditional)
/// ---------------------------------------------------------------------------

let cheney_gc_correct
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    chain_objects_blue major fp)
          (ensures (let res = cheney_collect_spec minor major fp roots in
                    let prom = cheney_promote minor major fp roots in
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                      Seq.mem x (objects zero_addr res.mc_major)) /\
                    well_formed_heap_part1 res.mc_major /\
                    AllocLemmas.fl_valid res.mc_major res.mc_fp heap_words /\
                    AllocLemmas.fl_chain_terminates res.mc_major res.mc_fp heap_words /\
                    minor_wf res.mc_minor /\
                    U64.v res.mc_minor.bump == 0 /\
                    res.mc_roots == rewrite_roots roots prom.fwd_map))
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
  : Lemma (requires BFS.cheney_no_oom minor major fp roots)
          (ensures (let prom = cheney_promote minor major fp roots in
                    forall (x: U64.t). Seq.mem x (minor_reachable minor roots) ==>
                      prom.fwd_map x <> 0UL \/ minor_wosize minor x = 0))
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
