/// ---------------------------------------------------------------------------
/// GC.Gen.SweepPhase.Minor - a minor collection in the middle of a sweep
/// ---------------------------------------------------------------------------
///
/// The sweep phase meets the minor collection through its view.  The generic
/// minor-collection theorems (`GC.Gen.CheneyView`) are stated for the idle
/// collection, whose promoted copies are white wherever they land; the view
/// they run on is the sweep's with what is condemned fixed at the heap `g`
/// the collection starts from (`surviving_from st g`: the allocated blocks
/// not condemned in `g`).  It counts every promoted copy, since none was
/// allocated in `g` (`surviving_from_fresh`), and at `g` it is the sweep's
/// view `surviving st`.
///
///   * **Step B** (`sweep_collection_shape`): the sweep phase, with the
///     nursery's shape and the cross-generation condition on the sweep's
///     view, is the minor collection's entry shape on that view,
///     `collection_shape_view (surviving_from st g)`.
///   * **Step C** (`minor_keeps_sweep_phase`): the collection at the sweep's
///     phase (`GC.Gen.CheneyAt.cheney_collect_spec_view_at`) keeps the sweep
///     phase, with the same cursor and `last_fragment` and `swept_tail` the
///     last cell at or below where it was, and the same condemned set: new
///     objects are never condemned and no existing header changes.
///     Well-formedness on the view comes from the generic theorem
///     (`GC.Gen.CheneyView.cheney_collect_view_preserves_shape`) through the
///     painting: a promoted copy in front of the cursor is painted black,
///     so the sweep's view of the painted heap is the collection's view of
///     the idle one (`GC.Gen.Paint.paint_surviving`).  The shape comes by
///     induction over the promotions (`GC.Gen.Cheney.cheney_promote_induction`),
///     each one a promotion at the phase (`GC.Gen.SweepPhase.promote_sweep_shape`),
///     and the pointer update keeps the walk and every header.

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

/// The major half alone, on the sweep's view and on the collection's.
val sweep_major_shape (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_phase_inv g fp st)
          (ensures GenInv.major_shape_view (surviving st) g fp /\
                   GenInv.major_shape_view (surviving_from st g) g fp)

/// **Step B: the sweep phase is the minor collection's shape** on the
/// collection's view.
val sweep_collection_shape (minor: minor_state) (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_phase_inv g fp st /\
                    GenInv.minor_heap_shape minor /\
                    GenInv.minor_major_fields_in_view (surviving st) minor g)
          (ensures GenInv.collection_shape_view (surviving_from st g) minor g fp)


/// The sweep state after a minor collection that left the heap `g'`: the
/// same cursor and `last_fragment`, and `swept_tail` the last list cell at or
/// below where it was.
let state_after (st: sweep_state) (g': heap) : GTot sweep_state =
  { st with swept_tail = Paint.max_cell_below g' (U64.v st.swept_tail) }

/// **Step C: a minor collection mid-sweep keeps the sweep phase**, with the
/// same condemned set, and keeps the minor collection's shape on its view.
val minor_keeps_sweep_phase (minor: minor_state) (g: heap) (fp: U64.t) (st: sweep_state)
                            (roots: seq U64.t)
  : Lemma (requires sweep_phase_inv g fp st /\
                    GenInv.minor_heap_shape minor /\
                    GenInv.minor_major_fields_in_view (surviving st) minor g)
          (ensures (let v = surviving_from st g in
                    let (res, ph') = CA.cheney_collect_spec_view_at (Ph.Sweeping st) v minor g fp roots in
                    let st' = state_after st (GC.Gen.Cheney.cheney_collect_spec_view v minor g fp roots).GC.Gen.Promote.mc_major in
                    ph' == Ph.Sweeping st' /\
                    st'.cursor == st.cursor /\ st'.last_fragment == st.last_fragment /\
                    sweep_phase_inv res.GC.Gen.Promote.mc_major res.GC.Gen.Promote.mc_fp st' /\
                    (forall (x: obj_addr). condemned st' res.GC.Gen.Promote.mc_major x == condemned st g x) /\
                    GenInv.collection_shape_view v res.GC.Gen.Promote.mc_minor res.GC.Gen.Promote.mc_major
                                                 res.GC.Gen.Promote.mc_fp))
