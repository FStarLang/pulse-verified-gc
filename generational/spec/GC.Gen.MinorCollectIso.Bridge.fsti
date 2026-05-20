/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectIso.Bridge — Bridge from reduced to full preconditions
/// ---------------------------------------------------------------------------
///
/// Proves that the reduced preconditions (which only require well_formed_heap_part2
/// of the post-collection heap) imply the full preconditions (which require full
/// well_formed_heap). Parts 1, 3, 4 are derived from operational conditions via
/// CheneyCorrectness.WFH.
///
/// This module is separated from MinorCollectIso to avoid polluting its SMT
/// context with the WFH preservation lemma signatures.

module GC.Gen.MinorCollectIso.Bridge

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Cheney
open GC.Gen.MinorCollectIso

/// Reduced → Full: the reduced preconditions imply the full preconditions.
val reduced_implies_full_preconditions
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires minor_collect_iso_reduced_preconditions minor major fp roots)
    (ensures minor_collect_iso_preconditions minor major fp roots)
