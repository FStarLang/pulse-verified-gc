/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyPreservation.NoBlue -- no-pointer-to-blue preservation
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyPreservation.NoBlue

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.PromoteUpdate
open GC.Gen.Cheney

module Mark = GC.Spec.Mark
module Forwarding = GC.Gen.CheneyPreservation.Forwarding
module Injectivity = GC.Gen.CheneyPreservation.Injectivity
module GenInv = GC.Gen.HeapInvariant

/// Cheney promotion alone preserves `no_pointer_to_blue` from the centralized
/// combined heap invariant.  Promoted copied fields that are already major
/// pointers are covered by `GenInv.minor_major_fields_no_blue`; copied minor
/// pointers are not major pointer fields until the later update pass.
val cheney_promote_preserves_no_pointer_to_blue_from_shape
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires GenInv.collection_heap_shape minor major fp)
    (ensures Mark.no_pointer_to_blue
      (cheney_promote minor major fp roots).major_final)

/// Rewriting fields through a forwarding map preserves `no_pointer_to_blue`
/// when the pre-update heap already has it and every non-infix forwarding
/// target is a non-blue object.
val update_major_pointers_preserves_no_pointer_to_blue
  (major: heap) (fwd: forwarding_map)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      well_formed_heap (update_major_pointers major fwd) /\
      no_scan_invariant (update_major_pointers major fwd) /\
      Mark.no_pointer_to_blue major /\
      Forwarding.fwd_valid_or_infix fwd major /\
      Injectivity.fwd_targets_not_blue fwd major)
    (ensures Mark.no_pointer_to_blue (update_major_pointers major fwd))
