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
/// `target_shape` supplies, for each unforwarded pointer field of a live major
/// object, the resolved membership and infix well-formedness of its target.  It
/// is passed as a proof function rather than a predicate because the predicate
/// that provides it (`GC.Gen.CheneyPreservation.field_old_pointer_targets_in_objects`)
/// lives downstream of this module.  Interior targets are the reason it is
/// needed: without it there is no way to reach the enclosing closure and show
/// the target's header survives the update pass.
val update_major_pointers_preserves_no_pointer_to_blue
  (major: heap) (fwd: forwarding_map)
  (target_shape:
     (src: obj_addr) -> (j: nat) ->
     Lemma (requires Seq.mem src (objects zero_addr major) /\
                     ~(is_blue src major) /\ ~(is_no_scan src major) /\
                     j < U64.v (wosize_of_object src major) /\
                     U64.v src + j * 8 + 8 <= heap_size /\
                     (U64.v src + j * 8) % 8 == 0)
           (ensures (let raw = read_word major (U64.uint_to_t (U64.v src + j * 8)) in
                     let mv = to_minor_offset raw in
                     (is_minor_pointer mv /\ fwd mv <> 0UL ==>
                       U64.v (fwd mv) >= U64.v mword /\
                       U64.v (fwd mv) < heap_size /\
                       U64.v (fwd mv) % U64.v mword == 0 /\
                       (let t : obj_addr = fwd mv in
                        Seq.mem (resolve_object t major) (objects zero_addr major) /\
                        is_blue (resolve_object t major) major = false /\
                        infix_addr_wf major (objects zero_addr major) t)) /\
                     (is_pointer raw /\ ~(is_minor_pointer mv /\ fwd mv <> 0UL) ==>
                       Seq.mem (resolve_object (raw <: obj_addr) major)
                               (objects zero_addr major) /\
                       infix_addr_wf major (objects zero_addr major)
                               (raw <: obj_addr)))))
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      well_formed_heap (update_major_pointers major fwd) /\
      no_scan_invariant (update_major_pointers major fwd) /\
      Mark.no_pointer_to_blue major /\
      Forwarding.fwd_valid_or_infix fwd major /\
      Injectivity.fwd_targets_not_blue fwd major)
    (ensures Mark.no_pointer_to_blue (update_major_pointers major fwd))
