/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectIso.Bridge — Implementation
/// ---------------------------------------------------------------------------

module GC.Gen.MinorCollectIso.Bridge

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Cheney
open GC.Gen.MinorCollectIso

module WFH = GC.Gen.CheneyCorrectness.WFH

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let reduced_implies_full_preconditions
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires minor_collect_iso_reduced_preconditions minor major fp roots)
    (ensures minor_collect_iso_preconditions minor major fp roots)
  = // Derive parts 1, 3, 4 from operational conditions
    WFH.cheney_collect_preserves_wfh_part1 minor major fp roots;
    WFH.cheney_collect_preserves_wfh_part3 minor major fp roots;
    WFH.cheney_collect_preserves_wfh_part4 minor major fp roots;
    // well_formed_heap = part1 /\ part2 /\ part3 /\ part4
    // part2 is given, parts 1,3,4 derived above
    reveal_opaque (`%well_formed_heap) well_formed_heap;
    let res = cheney_collect_spec minor major fp roots in
    assert (well_formed_heap_part1 res.mc_major);
    assert (well_formed_heap_part2 res.mc_major);
    assert (well_formed_heap_part3 res.mc_major);
    assert (well_formed_heap_part4 res.mc_major)
#pop-options
