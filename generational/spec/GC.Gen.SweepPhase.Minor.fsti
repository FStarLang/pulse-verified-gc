/// ---------------------------------------------------------------------------
/// GC.Gen.SweepPhase.Minor - a minor collection in the middle of a sweep
/// ---------------------------------------------------------------------------
///
/// The sweep phase meets the minor collection through the pending set: the
/// objects pending free (`GC.Spec.SweepPhase.Intrinsic.pending`, the white
/// objects in front of the cursor) are the `pf` of the generic minor-collection
/// theorems (`GC.Gen.CheneyExcept`).
///
///   * **Step B** (`sweep_collection_shape`): the sweep phase, with the
///     nursery's shape and the cross-generation condition for the pending set,
///     is the minor collection's entry shape `collection_shape_except` for that
///     set.

module GC.Gen.SweepPhase.Minor

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.SweepPhase.Intrinsic
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module GenInv = GC.Gen.HeapInvariant

/// The major half alone.
val sweep_major_shape (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_phase_inv g fp st)
          (ensures GenInv.major_shape_except g fp (pending g st))

/// **Step B: the sweep phase is the minor collection's shape** for the
/// pending set.
val sweep_collection_shape (minor: minor_state) (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_phase_inv g fp st /\
                    GenInv.minor_heap_shape minor /\
                    GenInv.minor_major_fields_not_freed minor g (pending g st))
          (ensures GenInv.collection_shape_except minor g fp (pending g st))

