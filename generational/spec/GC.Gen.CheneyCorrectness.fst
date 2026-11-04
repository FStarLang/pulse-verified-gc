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

open GC.Gen.Cheney.Induction
open GC.Gen.Cheney.Steps
module AllocLemmas = GC.Spec.Allocator.Lemmas

/// ---------------------------------------------------------------------------
/// Property 1: Object survival
/// ---------------------------------------------------------------------------

let cheney_collect_preserves_objects
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def) (roots: seq U64.t)
  =
  cheney_promote_preserves_objects minor major fp roots;
  let prom = cheney_promote minor major fp roots in
  wf_parts ();
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  GC.Gen.PromoteUpdate.update_walk_preserves_objects prom.major_final (in_use free prom.major_final) prom.fwd_map
