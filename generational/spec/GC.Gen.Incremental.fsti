/// ---------------------------------------------------------------------------
/// GC.Gen.Incremental - the collector's state at each phase
/// ---------------------------------------------------------------------------
///
/// The collector's entry points (`GC.Gen.Impl`) hand the collector's state
/// from one call to the next through one predicate (`GC.Gen.Impl.gc_state`),
/// indexed by the phase (`phase_shape minor g fp ph`):
///
///   * `Idle`: the stop-the-world shape `GC.Gen.HeapInvariant.
///     collection_heap_shape` -- what `full_gc` demands and restores;
///   * `Marking`: the minor collection's shape at `free_stw` (marking frees
///     nothing) and the marking invariant
///     (`GC.Spec.MarkPhase.marking_inv`) with what the nursery's fields
///     point at held (`nursery_held`).  The program's roots are the other
///     half of what is held; they are not part of the collector's state, so
///     the entry points that take them state it of them;
///   * `Sweeping c`: the sweep phase at the cursor `c`
///     (`GC.Spec.SweepPhase.Intrinsic.sweep_inv_incremental g fp c`), the
///     nursery's shape, and the cross-generation condition for
///     `free_incremental` (`minor_major_fields_not_free (free_incremental c)
///     minor g`).
///
/// Every collector event keeps it: the start of the sweep phase
/// (`phase_shape_start`), a slice (`phase_slice_shape`, which at the end of
/// the sweep gives back the idle shape), and a minor collection at either
/// phase, which runs at that phase with the phase's definition of free
/// (`phase_free`: `free_stw` idle or marking, `free_incremental c`
/// mid-sweep):
/// `phase_shape_collection` for its entry shape, `minor_keeps_phase_shape`
/// for what it leaves mid-sweep.
/// The program's events (allocation and its initialisation, field writes) are `GC.Spec.SweepPhase.Mutator`'s.

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
module Cheney = GC.Gen.Cheney
module Promote = GC.Gen.Promote
module SPM = GC.Gen.SweepPhase.Minor
module MP = GC.Spec.MarkPhase

/// What counts as free for a minor collection at a phase: blue (`free_stw`)
/// when idle or marking; mid-sweep, blue or pending free
/// (`free_incremental c`).
let phase_free (ph: Ph.gc_phase) : free_def =
  match ph with
  | Ph.Idle | Ph.Marking -> free_stw
  | Ph.Sweeping c -> free_incremental c

/// What the nursery holds in the major heap: a major pointer in the scan
/// window of a nursery object points at `w` (such a pointer is never
/// interior: `minor_major_fields_not_free` makes it a block).
let nursery_held (minor: minor_state) (w: obj_addr) : prop =
  exists (obj: U64.t) (j: nat).
    Seq.mem obj (minor_objects minor) /\ j < minor_scan_wosize minor obj /\
    is_pointer_field (minor_read_field minor obj j) /\
    minor_read_field minor obj j == (w <: U64.t)

/// **The collector's state at its phase.**
[@@"opaque_to_smt"]
let phase_shape (minor: minor_state) (g: heap) (fp: U64.t) (ph: Ph.gc_phase) : prop =
  match ph with
  | Ph.Idle -> GenInv.collection_heap_shape minor g fp
  | Ph.Marking ->
      GenInv.collection_shape_with Ph.Marking free_stw minor g fp /\
      MP.marking_inv g (nursery_held minor)
  | Ph.Sweeping c ->
      sweep_inv_incremental g fp c /\ GenInv.minor_heap_shape minor /\
      GenInv.minor_major_fields_not_free (free_incremental c) minor g

val phase_shape_idle (minor: minor_state) (g: heap) (fp: U64.t)
  : Lemma (phase_shape minor g fp Ph.Idle <==> GenInv.collection_heap_shape minor g fp)

val phase_shape_marking (minor: minor_state) (g: heap) (fp: U64.t)
  : Lemma (phase_shape minor g fp Ph.Marking <==>
           (GenInv.collection_shape_with Ph.Marking free_stw minor g fp /\
            MP.marking_inv g (nursery_held minor)))

val phase_shape_sweeping (minor: minor_state) (g: heap) (fp: U64.t) (c: U64.t)
  : Lemma (phase_shape minor g fp (Ph.Sweeping c) <==>
           (sweep_inv_incremental g fp c /\ GenInv.minor_heap_shape minor /\
            GenInv.minor_major_fields_not_free (free_incremental c) minor g))

/// At any phase the state is the minor collection's entry shape at the
/// phase for the phase's definition of free.
val phase_shape_collection (minor: minor_state) (g: heap) (fp: U64.t) (ph: Ph.gc_phase)
  : Lemma (requires phase_shape minor g fp ph)
          (ensures GenInv.collection_shape_with ph (phase_free ph) minor g fp)

/// **The start of the sweep phase**, after the minor collection that emptied
/// the nursery and marking.
val phase_shape_start (minor: minor_state) (g: heap) (fp: U64.t)
  : Lemma (requires sweep_inv_incremental g fp sweep_start.cursor)
          (ensures phase_shape (minor_reset minor) g fp (Ph.Sweeping sweep_start.cursor))

/// **The end of the sweep phase** is the idle shape: nothing is pending free, the
/// heap is well formed, every object is white or free, the free list is
/// exact and ascending.
val sweep_end_shape (minor: minor_state) (g: heap) (fp: U64.t) (c: U64.t)
  : Lemma (requires phase_shape minor g fp (Ph.Sweeping c) /\ sweep_done c)
          (ensures GenInv.collection_heap_shape minor g fp)

/// **A major slice**, at the collector's phase: nothing when idle; mid-sweep,
/// a slice of the sweep (`SL.phase_slice`).  While marking, nothing for now:
/// the mark slice is to come (incremental-mark-plan.md, M4), and nothing
/// enters `Marking` yet.
let major_slice_spec (g: heap) (fp: U64.t) (ph: Ph.gc_phase) (budget: nat)
  : GTot (heap & U64.t & Ph.gc_phase) =
  match ph with
  | Ph.Idle -> (g, fp, Ph.Idle)
  | Ph.Marking -> (g, fp, Ph.Marking)
  | Ph.Sweeping _ -> SL.phase_slice g fp ph budget

/// **A slice keeps the collector's state**, at whatever phase it leaves.
val phase_slice_shape (minor: minor_state) (g: heap) (fp: U64.t) (ph: Ph.gc_phase) (budget: nat)
  : Lemma (requires phase_shape minor g fp ph)
          (ensures (let (g', fp', ph') = SL.phase_slice g fp ph budget in
                    phase_shape minor g' fp' ph'))

/// A budget of more words than the heap has finishes the sweep.
val phase_slice_finishes (minor: minor_state) (g: heap) (fp: U64.t) (ph: Ph.gc_phase) (budget: nat)
  : Lemma (requires phase_shape minor g fp ph /\ budget > heap_words /\ ~(Ph.Marking? ph))
          (ensures (let (_, _, ph') = SL.phase_slice g fp ph budget in ph' == Ph.Idle))

/// **A minor collection mid-sweep keeps the collector's state**: the phase
/// it leaves is the sweep at the same cursor, with the same objects pending
/// free.
val minor_keeps_phase_shape (minor: minor_state) (g: heap) (fp: U64.t) (c: U64.t)
                            (roots: seq U64.t)
  : Lemma (requires phase_shape minor g fp (Ph.Sweeping c))
          (ensures (let res = SPM.collect_at c minor g fp roots in
                    (forall (x: obj_addr). pending_free c res.Promote.mc_major x == pending_free c g x) /\
                    res.Promote.mc_minor == minor_reset minor /\
                    phase_shape res.Promote.mc_minor res.Promote.mc_major res.Promote.mc_fp (Ph.Sweeping c)))

/// `phase_free` at each phase, as an equation (the SMT encoding does not
/// unfold a definition whose value is a function).
val phase_free_idle (_: unit) : Lemma (phase_free Ph.Idle == free_stw)

val phase_free_marking (_: unit) : Lemma (phase_free Ph.Marking == free_stw)

val phase_free_sweeping (c: U64.t)
  : Lemma (phase_free (Ph.Sweeping c) == free_incremental c)
