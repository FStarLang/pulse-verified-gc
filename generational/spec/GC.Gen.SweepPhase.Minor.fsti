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
///   * **Step C** (`minor_keeps_sweep_phase`): the collection at the sweep's
///     phase (`GC.Gen.CheneyAt.cheney_collect_spec_except_at`) keeps the sweep
///     phase, with the same cursor and `last_fragment` and `swept_tail` the
///     last cell at or below where it was, and the same pending set: new
///     objects are never pending and no existing header changes.  The field
///     closure comes from the generic theorem
///     (`GC.Gen.CheneyExcept.cheney_collect_except_preserves_shape`) through
///     the painting (`GC.Gen.Paint`); the shape, by induction over the
///     promotions (`GC.Gen.Cheney.cheney_promote_induction`), each one a
///     promotion at the phase (`GC.Gen.SweepPhase.promote_sweep_shape`), and
///     the pointer update keeps the walk and every header.

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
module CA = GC.Gen.CheneyAt
module Paint = GC.Gen.Paint
module Ph = GC.Spec.Phase

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


/// The sweep state after a minor collection that left the heap `g'`: the
/// same cursor and `last_fragment`, and `swept_tail` the last list cell at or
/// below where it was.
let state_after (st: sweep_state) (g': heap) : GTot sweep_state =
  { st with swept_tail = Paint.max_cell_below g' (U64.v st.swept_tail) }

/// **Step C: a minor collection mid-sweep keeps the sweep phase**, with the
/// same pending set, and keeps the minor collection's shape for it.
val minor_keeps_sweep_phase (minor: minor_state) (g: heap) (fp: U64.t) (st: sweep_state)
                            (roots: seq U64.t)
  : Lemma (requires sweep_phase_inv g fp st /\
                    GenInv.minor_heap_shape minor /\
                    GenInv.minor_major_fields_not_freed minor g (pending g st))
          (ensures (let (res, ph') = CA.cheney_collect_spec_except_at (Ph.Sweeping st) minor g fp roots (pending g st) in
                    let st' = state_after st (GC.Gen.Cheney.cheney_collect_spec_except minor g fp roots (pending g st)).GC.Gen.Promote.mc_major in
                    ph' == Ph.Sweeping st' /\
                    st'.cursor == st.cursor /\ st'.last_fragment == st.last_fragment /\
                    sweep_phase_inv res.GC.Gen.Promote.mc_major res.GC.Gen.Promote.mc_fp st' /\
                    (forall (x: obj_addr). pending res.GC.Gen.Promote.mc_major st' x <==> pending g st x) /\
                    GenInv.collection_shape_except res.GC.Gen.Promote.mc_minor res.GC.Gen.Promote.mc_major
                                                   res.GC.Gen.Promote.mc_fp (pending g st)))
