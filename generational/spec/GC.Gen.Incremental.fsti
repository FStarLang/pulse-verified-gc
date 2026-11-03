/// ---------------------------------------------------------------------------
/// GC.Gen.Incremental - the collector's state at each phase
/// ---------------------------------------------------------------------------
///
/// The incremental sweep's entry points (`GC.Gen.Impl.Incremental`) hand the
/// collector's state from one call to the next through one predicate,
/// indexed by the phase (`phase_shape minor g fp ph`):
///
///   * `Idle`: the stop-the-world shape `GC.Gen.HeapInvariant.
///     collection_heap_shape` -- what `gen_gc` demands and restores;
///   * `Sweeping st`: the sweep phase (`GC.Spec.SweepPhase.Intrinsic.
///     sweep_phase_inv g fp st`), the nursery's shape, and the
///     cross-generation condition on the sweep's view
///     (`minor_major_fields_in_view (surviving st) minor g`).
///
/// Every collector event keeps it: the start of the sweep phase
/// (`phase_shape_start`), a slice (`phase_slice_shape`, which at the end of
/// the sweep gives back the idle shape), and a minor collection at either
/// phase (`phase_shape_collection` for its entry shape on the phase's view
/// `phase_view`, `minor_keeps_phase_shape` mid-sweep).  The program's events (allocation
/// and its initialisation, field writes) are `GC.Gen.SweepPhase`'s.

module GC.Gen.Incremental

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.SweepPhase.Intrinsic
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module GenInv = GC.Gen.HeapInvariant
module SL = GC.Spec.SweepPhase.Slice
module CA = GC.Gen.CheneyAt
module Paint = GC.Gen.Paint
module Cheney = GC.Gen.Cheney
module Promote = GC.Gen.Promote
module SPM = GC.Gen.SweepPhase.Minor
module CV = GC.Gen.CheneyView

/// The view a minor collection from `g` runs on at a phase: `allocated` when
/// idle; mid-sweep, the sweep's view with what is condemned fixed at `g`
/// (`surviving_from`), which counts the copies the collection promotes and,
/// painted, is the sweep's view of the heap it leaves.
let phase_view (g: heap) (ph: Ph.gc_phase) : view =
  match ph with
  | Ph.Idle -> allocated
  | Ph.Sweeping st -> surviving_from st g

/// **The collector's state at its phase.**
[@@"opaque_to_smt"]
let phase_shape (minor: minor_state) (g: heap) (fp: U64.t) (ph: Ph.gc_phase) : prop =
  match ph with
  | Ph.Idle -> GenInv.collection_heap_shape minor g fp
  | Ph.Sweeping st ->
      sweep_phase_inv g fp st /\ GenInv.minor_heap_shape minor /\
      GenInv.minor_major_fields_in_view (surviving st) minor g

val phase_shape_idle (minor: minor_state) (g: heap) (fp: U64.t)
  : Lemma (phase_shape minor g fp Ph.Idle <==> GenInv.collection_heap_shape minor g fp)

val phase_shape_sweeping (minor: minor_state) (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (phase_shape minor g fp (Ph.Sweeping st) <==>
           (sweep_phase_inv g fp st /\ GenInv.minor_heap_shape minor /\
            GenInv.minor_major_fields_in_view (surviving st) minor g))

/// At any phase the state is the minor collection's entry shape on the
/// phase's view, and the phase is the one the collection starts from
/// (`swept_tail` is a list cell or the sentinel).
val phase_shape_collection (minor: minor_state) (g: heap) (fp: U64.t) (ph: Ph.gc_phase)
  : Lemma (requires phase_shape minor g fp ph)
          (ensures GenInv.collection_shape_view (phase_view g ph) minor g fp /\
                   Paint.phase_at ph g == ph)

/// The phase's view counts the copies a collection from `g` promotes, and
/// painting them does not change it.
val phase_view_ok (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t) (ph: Ph.gc_phase)
  : Lemma (CV.promotion_in_view (phase_view g ph) minor g fp roots /\
           Paint.colour_blind (phase_view g ph))

/// **The start of the sweep phase**, after the minor collection that emptied
/// the nursery and marking.
val phase_shape_start (minor: minor_state) (g: heap) (fp: U64.t)
  : Lemma (requires sweep_phase_inv g fp sweep_start)
          (ensures phase_shape (minor_reset minor) g fp (Ph.Sweeping sweep_start))

/// **The end of the sweep phase** is the idle shape: nothing is condemned, the
/// heap is well formed, every object is white or free, the free list is
/// exact and ascending.
val sweep_end_shape (minor: minor_state) (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires phase_shape minor g fp (Ph.Sweeping st) /\ sweep_done st)
          (ensures GenInv.collection_heap_shape minor g fp)

/// **A slice keeps the collector's state**, at whatever phase it leaves.
val phase_slice_shape (minor: minor_state) (g: heap) (fp: U64.t) (ph: Ph.gc_phase) (budget: nat)
  : Lemma (requires phase_shape minor g fp ph)
          (ensures (let (g', fp', ph') = SL.phase_slice g fp ph budget in
                    phase_shape minor g' fp' ph'))

/// A budget of more words than the heap has finishes the sweep.
val phase_slice_finishes (minor: minor_state) (g: heap) (fp: U64.t) (ph: Ph.gc_phase) (budget: nat)
  : Lemma (requires phase_shape minor g fp ph /\ budget > heap_words)
          (ensures (let (_, _, ph') = SL.phase_slice g fp ph budget in ph' == Ph.Idle))

/// **A minor collection mid-sweep keeps the collector's state**: the phase
/// it leaves is the sweep with the same cursor and `last_fragment`, and the
/// same objects condemned.
val minor_keeps_phase_shape (minor: minor_state) (g: heap) (fp: U64.t) (st: sweep_state)
                            (roots: seq U64.t)
  : Lemma (requires phase_shape minor g fp (Ph.Sweeping st))
          (ensures (let v = surviving_from st g in
                    let (res, ph') = CA.cheney_collect_spec_view_at (Ph.Sweeping st) v minor g fp roots in
                    let st' = SPM.state_after st (Cheney.cheney_collect_spec_view v minor g fp roots).Promote.mc_major in
                    ph' == Ph.Sweeping st' /\
                    st'.cursor == st.cursor /\ st'.last_fragment == st.last_fragment /\
                    (forall (x: obj_addr). condemned st' res.Promote.mc_major x == condemned st g x) /\
                    res.Promote.mc_minor == minor_reset minor /\
                    phase_shape res.Promote.mc_minor res.Promote.mc_major res.Promote.mc_fp ph'))

/// `phase_view` at each phase, as an equation (the SMT encoding does not
/// unfold a definition whose value is a function).
val phase_view_idle (g: heap) : Lemma (phase_view g Ph.Idle == allocated)

val phase_view_sweeping (g: heap) (st: sweep_state)
  : Lemma (phase_view g (Ph.Sweeping st) == surviving_from st g)
