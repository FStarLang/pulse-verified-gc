module GC.SPOT.InfixPre

module U64 = FStar.UInt64
module Seq = FStar.Seq

open FStar.Seq
open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

module SpecFields = GC.Spec.Fields
module SpecObj = GC.Spec.Object
module GenInv = GC.Gen.HeapInvariant
module CheneyBFS = GC.Gen.CheneyBFS
module GenImpl = GC.Gen.Impl
module Preconditions = GC.SPOT.Preconditions
module InfixMajor = GC.SPOT.InfixMajor

/// Everything `gen_gc` demands, discharged for the interior-pointer heap of
/// `GC.SPOT.InfixMajor`.
///
/// The nursery is empty (`GC.Gen.MinorHeap.minor_reset`), so the whole minor
/// side of the precondition is vacuous and the audit is concentrated where it
/// belongs: on the major heap, which contains a genuine OCaml infix pointer.

/// The empty nursery.  `minor_reset` ignores its argument, so this is *the*
/// reset nursery, not merely one of them (`spot_infix_minor_is_reset`).
val spot_infix_minor : minor_state

val spot_infix_minor_is_reset (ms: minor_state)
  : Lemma (ensures minor_reset ms == spot_infix_minor)

val spot_infix_minor_objects_empty : unit ->
  Lemma (ensures minor_objects spot_infix_minor == Seq.empty)

/// The single root: `Q`, the object holding the interior pointer.
val spot_infix_roots : (r:unit{InfixMajor.spot_infix_room}) -> Tot (seq U64.t)

val spot_infix_roots_len (r: unit{InfixMajor.spot_infix_room})
  : Lemma (ensures Seq.length (spot_infix_roots r) == 1 /\
                   Seq.index (spot_infix_roots r) 0 == (InfixMajor.spot_q r <: U64.t))

val spot_infix_roots_cases (r: unit{InfixMajor.spot_infix_room}) (root: U64.t)
  : Lemma (requires Seq.mem root (spot_infix_roots r))
          (ensures root == (InfixMajor.spot_q r <: U64.t))

/// The remembered set is empty: no major field of this heap holds a minor
/// pointer, because the only pointer-valued field points inside the *major*
/// heap.
val spot_infix_slots : seq U64.t

val spot_infix_fwd_array : seq U64.t

val spot_infix_fwd_array_zero : unit ->
  Lemma (ensures Preconditions.zero_forwarding_array spot_infix_fwd_array)

/// The heap-shape half of the precondition.  This is the interesting one: it
/// is `GC.SPOT.InfixMajor.spot_infix_major_heap_shape` lifted across the empty
/// nursery, and it is exactly the predicate `gen_gc` requires.
val spot_infix_collection_heap_shape (r: unit{InfixMajor.spot_infix_room})
  : Lemma (ensures
      GenInv.collection_heap_shape
        spot_infix_minor (InfixMajor.spot_infix_heap r) (InfixMajor.spot_infix_fp r))

val spot_infix_ref_table_sound (r: unit{InfixMajor.spot_infix_room})
  : Lemma (ensures
      GC.Gen.Impl.UpdatePtrs.ref_table_sound
        (InfixMajor.spot_infix_heap r) spot_infix_slots 0)

val spot_infix_ref_table_covers (r: unit{InfixMajor.spot_infix_room})
  : Lemma (ensures
      GC.Gen.Impl.UpdatePtrs.ref_table_covers_minor_ptrs
        (InfixMajor.spot_infix_heap r) spot_infix_slots 0)

val spot_infix_remembered_targets_in_roots (r: unit{InfixMajor.spot_infix_room})
  : Lemma (ensures
      GC.Gen.MinorCollectForwarding.remembered_targets_in_roots
        (InfixMajor.spot_infix_heap r) (spot_infix_roots r) spot_infix_slots 0)

val spot_infix_roots_valid (r: unit{InfixMajor.spot_infix_room})
  : Lemma (ensures
      GC.Gen.MinorCollectForwarding.roots_valid_for_minor_collection
        spot_infix_minor (InfixMajor.spot_infix_heap r) (spot_infix_roots r))

val spot_infix_minor_collect_full_pre (r: unit{InfixMajor.spot_infix_room})
  : Lemma (ensures
      Preconditions.minor_collect_full_pre
        spot_infix_minor (InfixMajor.spot_infix_heap r) (InfixMajor.spot_infix_fp r)
        (spot_infix_roots r) spot_infix_fwd_array spot_infix_slots 0)

/// The full `gen_gc` precondition, for any gray stack budget that can hold the
/// single root.
val spot_infix_gen_gc_pre (r: unit{InfixMajor.spot_infix_room}) (cap: nat{cap >= 1})
  : Lemma (ensures
      Preconditions.gen_gc_pre
        spot_infix_minor (InfixMajor.spot_infix_heap r) (InfixMajor.spot_infix_fp r)
        (spot_infix_roots r) spot_infix_fwd_array spot_infix_slots 0
        Seq.empty cap)

/// The success-side dual: the forwarding map the (empty) minor collection
/// produces is trivially well formed, which is what the major phase's
/// preconditions are stated against.
val spot_infix_cheney_no_oom (r: unit{InfixMajor.spot_infix_room})
  : Lemma (ensures
      CheneyBFS.cheney_no_oom
        spot_infix_minor (InfixMajor.spot_infix_heap r)
        (InfixMajor.spot_infix_fp r) (spot_infix_roots r))

/// The minor collection cannot run out of memory here: there is nothing to
/// promote.  Combined with `gen_gc`'s `not ok ==> cheney_oom`, this pins the
/// success flag to `true`.
val spot_infix_no_oom (r: unit{InfixMajor.spot_infix_room})
  : Lemma (ensures
      ~(CheneyBFS.cheney_oom
          spot_infix_minor (InfixMajor.spot_infix_heap r)
          (InfixMajor.spot_infix_fp r) (spot_infix_roots r)))
