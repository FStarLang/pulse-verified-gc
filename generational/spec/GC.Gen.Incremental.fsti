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
///     cross-generation condition for `free_incremental`
///     (`minor_major_fields_not_free (free_incremental st) minor g`).
///
/// Every collector event keeps it: the start of the sweep phase
/// (`phase_shape_start`), a slice (`phase_slice_shape`, which at the end of
/// the sweep gives back the idle shape), and a minor collection at either
/// phase, which runs at that phase with the phase's definition of free
/// (`phase_free`: `free_stw` idle, `free_incremental st` mid-sweep):
/// `phase_shape_collection` for its entry shape, `minor_keeps_phase_shape`
/// for what it leaves mid-sweep.
/// The program's events (allocation and its initialisation, field writes) are `GC.Gen.SweepPhase`'s.

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
module ST = GC.Gen.SweptTail
module Cheney = GC.Gen.Cheney
module Promote = GC.Gen.Promote
module SPM = GC.Gen.SweepPhase.Minor

/// What counts as free for a minor collection at a phase: blue (`free_stw`)
/// when idle; mid-sweep, blue or pending free (`free_incremental st`).
let phase_free (ph: Ph.gc_phase) : free_def =
  match ph with
  | Ph.Idle -> free_stw
  | Ph.Sweeping st -> free_incremental st

/// **The collector's state at its phase.**
[@@"opaque_to_smt"]
let phase_shape (minor: minor_state) (g: heap) (fp: U64.t) (ph: Ph.gc_phase) : prop =
  match ph with
  | Ph.Idle -> GenInv.collection_heap_shape minor g fp
  | Ph.Sweeping st ->
      sweep_phase_inv g fp st /\ GenInv.minor_heap_shape minor /\
      GenInv.minor_major_fields_not_free (free_incremental st) minor g

val phase_shape_idle (minor: minor_state) (g: heap) (fp: U64.t)
  : Lemma (phase_shape minor g fp Ph.Idle <==> GenInv.collection_heap_shape minor g fp)

val phase_shape_sweeping (minor: minor_state) (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (phase_shape minor g fp (Ph.Sweeping st) <==>
           (sweep_phase_inv g fp st /\ GenInv.minor_heap_shape minor /\
            GenInv.minor_major_fields_not_free (free_incremental st) minor g))

/// At any phase the state is the minor collection's entry shape at the
/// phase for the phase's definition of free, and the phase is the one the
/// allocator holds (`swept_tail` is a list cell or the sentinel).
val phase_shape_collection (minor: minor_state) (g: heap) (fp: U64.t) (ph: Ph.gc_phase)
  : Lemma (requires phase_shape minor g fp ph)
          (ensures GenInv.collection_shape_with ph (phase_free ph) minor g fp /\
                   ST.phase_at ph g == ph)

/// **The start of the sweep phase**, after the minor collection that emptied
/// the nursery and marking.
val phase_shape_start (minor: minor_state) (g: heap) (fp: U64.t)
  : Lemma (requires sweep_phase_inv g fp sweep_start)
          (ensures phase_shape (minor_reset minor) g fp (Ph.Sweeping sweep_start))

/// **The end of the sweep phase** is the idle shape: nothing is pending free, the
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
/// it leaves (the one the allocator holds after it) is the sweep with the
/// same cursor and `last_fragment`, and the same objects pending free.
val minor_keeps_phase_shape (minor: minor_state) (g: heap) (fp: U64.t) (st: sweep_state)
                            (roots: seq U64.t)
  : Lemma (requires phase_shape minor g fp (Ph.Sweeping st))
          (ensures (let res = SPM.collect_at st minor g fp roots in
                    let ph' = ST.phase_at (Ph.Sweeping st) res.Promote.mc_major in
                    let st' = SPM.state_after st res.Promote.mc_major in
                    ph' == Ph.Sweeping st' /\
                    st'.cursor == st.cursor /\ st'.last_fragment == st.last_fragment /\
                    (forall (x: obj_addr). pending_free st' res.Promote.mc_major x == pending_free st g x) /\
                    res.Promote.mc_minor == minor_reset minor /\
                    phase_shape res.Promote.mc_minor res.Promote.mc_major res.Promote.mc_fp ph'))

/// `phase_free` at each phase, as an equation (the SMT encoding does not
/// unfold a definition whose value is a function).
val phase_free_idle (_: unit) : Lemma (phase_free Ph.Idle == free_stw)

val phase_free_sweeping (st: sweep_state)
  : Lemma (phase_free (Ph.Sweeping st) == free_incremental st)
