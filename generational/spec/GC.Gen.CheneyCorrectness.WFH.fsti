/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyCorrectness.WFH — Well-formed heap preservation (parts 1,3,4)
/// ---------------------------------------------------------------------------
///
/// Proves that cheney_collect_spec preserves well_formed_heap parts 1, 3, and 4.
/// Separated from GC.Gen.CheneyCorrectness to avoid SMT context pollution in
/// modules that import CheneyCorrectness but don't need these properties.

module GC.Gen.CheneyCorrectness.WFH

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Cheney

module AllocLemmas = GC.Spec.Allocator.Lemmas
module Part4 = GC.Gen.CheneyPart4

/// ---------------------------------------------------------------------------
/// Property: well_formed_heap_part1 preserved
/// ---------------------------------------------------------------------------

/// After collection, every object's header+body still fits within the heap.
/// Proof: promote preserves part1 (only writes into free-list nodes which
/// already fit), then update_major_pointers preserves part1 (only writes
/// field values, not headers/sizes).
val cheney_collect_preserves_wfh_part1
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
    (ensures
      well_formed_heap_part1 (cheney_collect_spec minor major fp roots).mc_major)

/// ---------------------------------------------------------------------------
/// Property: well_formed_heap_part4 preserved (no infix objects)
/// ---------------------------------------------------------------------------

/// After collection, no object in the post-collection heap has infix_tag.
/// Proof: cheney_promote preserves part4 (CheneyPart4 module), then
/// update_major_pointers preserves part4 (PromoteUpdate).
val cheney_collect_preserves_wfh_part4
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      Part4.minor_all_no_infix minor)
    (ensures
      well_formed_heap_part4 (cheney_collect_spec minor major fp roots).mc_major)

/// ---------------------------------------------------------------------------
/// Property: well_formed_heap_part3 preserved (infix well-formedness)
/// ---------------------------------------------------------------------------

/// After collection, infix well-formedness holds (vacuously, since part4 means
/// no objects have infix_tag). Proof: part1 + part4 of intermediate heap, then
/// update_major_pointers_preserves_wfh_part3.
val cheney_collect_preserves_wfh_part3
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      Part4.minor_all_no_infix minor)
    (ensures
      well_formed_heap_part3 (cheney_collect_spec minor major fp roots).mc_major)
