/// ---------------------------------------------------------------------------
/// GC.Gen.SweepPhase.Minor - a minor collection in the middle of a sweep
/// ---------------------------------------------------------------------------
///
/// The sweep phase meets the minor collection through what counts as free.
/// The minor collection mid-sweep runs at the sweep's phase `Sweeping st`
/// (its promotions are allocated there: black in front of the cursor, white
/// behind it), with the sweep's own definition of free, `free_incremental st`
/// (blue, or white in front of the cursor: pending free).  The generic
/// theorem (`GC.Gen.CheneyGeneric`) applies to it directly:
///
///   * **The allocator's blocks are not free** at the sweep's phase
///     (`free_incremental_allocations_not_free`): a block allocated in front
///     of the cursor is black, one behind it is not in front of the cursor,
///     and neither is blue -- so none is pending free.  This is
///     `allocation_color` at work: a white copy in front of the cursor would
///     be pending free, and freed by the sweep while reachable.
///   * **Step B** (`sweep_collection_shape`): the sweep phase, with the
///     nursery's shape and the cross-generation condition, is the minor
///     collection's entry shape at that phase and for that definition of free.
///   * **Step C** (`minor_keeps_sweep_phase`): the collection keeps the sweep
///     phase, with the same cursor and `last_fragment`, `swept_tail` the one
///     derived from the heap it leaves (`state_after`), and the same
///     pending-free set: new objects are never pending free and no existing
///     header changes.  Well-formedness is the generic theorem's; the shape is
///     by induction over the promotions (`GC.Gen.Cheney.Induction`), each one a
///     promotion at the phase (`GC.Gen.SweepPhase.promote_sweep_shape`), and
///     the pointer update keeps the walk and every header.  Its block-level
///     facts are `minor_keeps_pending_free` and `minor_keeps_blocks`.

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
module Ph = GC.Spec.Phase
module ST = GC.Gen.SweptTail
module Cheney = GC.Gen.Cheney
module Promote = GC.Gen.Promote

/// **The allocator at the sweep's phase hands out no block pending free.**
val free_incremental_allocations_not_free (st: sweep_state)
  : Lemma (requires U64.v st.cursor % 8 == 0)
          (ensures Promote.allocations_not_free (Ph.Sweeping st) (free_incremental st))

/// The major half alone.
val sweep_major_shape (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_phase_inv g fp st)
          (ensures GenInv.major_shape_with (Ph.Sweeping st) (free_incremental st) g fp)

/// **Step B: the sweep phase is the minor collection's shape** at the
/// sweep's phase.
val sweep_collection_shape (minor: minor_state) (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_phase_inv g fp st /\
                    GenInv.minor_heap_shape minor /\
                    GenInv.minor_major_fields_not_free (free_incremental st) minor g)
          (ensures GenInv.collection_shape_with (Ph.Sweeping st) (free_incremental st) minor g fp)

/// The sweep state after a minor collection that left the heap `g'`: the
/// same cursor and `last_fragment`, and `swept_tail` the one derived from
/// `g'` (the last list cell behind the cursor).  It is the phase the
/// allocator leaves (`GC.Gen.SweptTail.phase_at`).
let state_after (st: sweep_state) (g': heap) : GTot sweep_state =
  { st with swept_tail = last_cell_behind g' (U64.v st.cursor) }

/// The collection at the sweep's phase.
let collect_at (st: sweep_state) (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t)
  : GTot Promote.minor_collect_result
  = Cheney.cheney_collect_spec_with (Ph.Sweeping st) (free_incremental st) minor g fp roots

/// **Step C: a minor collection mid-sweep keeps the sweep phase**, with the
/// same pending-free set, and keeps the minor collection's shape.
val minor_keeps_sweep_phase (minor: minor_state) (g: heap) (fp: U64.t) (st: sweep_state)
                            (roots: seq U64.t)
  : Lemma (requires sweep_phase_inv g fp st /\
                    GenInv.minor_heap_shape minor /\
                    GenInv.minor_major_fields_not_free (free_incremental st) minor g)
          (ensures (let res = collect_at st minor g fp roots in
                    let st' = state_after st res.Promote.mc_major in
                    ST.phase_at (Ph.Sweeping st) res.Promote.mc_major == Ph.Sweeping st' /\
                    st'.cursor == st.cursor /\ st'.last_fragment == st.last_fragment /\
                    sweep_phase_inv res.Promote.mc_major res.Promote.mc_fp st' /\
                    (forall (x: obj_addr). pending_free st' res.Promote.mc_major x == pending_free st g x) /\
                    GenInv.collection_shape_with (Ph.Sweeping st) (free_incremental st)
                      res.Promote.mc_minor res.Promote.mc_major res.Promote.mc_fp))

/// **Step C, block by block.**  For the collection from `g` to `g'`: what is
/// pending free is unchanged (a new object is never pending free, and no
/// existing header changes) ...
val minor_keeps_pending_free (minor: minor_state) (g: heap) (fp: U64.t) (st: sweep_state)
                             (roots: seq U64.t) (x: obj_addr)
  : Lemma (requires sweep_phase_inv g fp st /\
                    GenInv.minor_heap_shape minor /\
                    GenInv.minor_major_fields_not_free (free_incremental st) minor g)
          (ensures (let g' = (collect_at st minor g fp roots).Promote.mc_major in
                    let st' = state_after st g' in
                    st'.cursor == st.cursor /\
                    (pending_free st g x <==> pending_free st' g' x)))

/// ... every non-free block of `g` is a block of `g'` with the same header,
/// so still not free; and the only non-free blocks of `g'` that were not
/// non-free blocks of `g` are promoted copies.
val minor_keeps_blocks (minor: minor_state) (g: heap) (fp: U64.t) (st: sweep_state)
                       (roots: seq U64.t) (x: obj_addr)
  : Lemma (requires sweep_phase_inv g fp st /\
                    GenInv.minor_heap_shape minor /\
                    GenInv.minor_major_fields_not_free (free_incremental st) minor g)
          (ensures (let g' = (collect_at st minor g fp roots).Promote.mc_major in
                    let st' = state_after st g' in
                    (is_block g x /\ not (free_incremental st g x) ==>
                       is_block g' x /\ not (free_incremental st' g' x) /\
                       read_word g' (hd_address x) == read_word g (hd_address x)) /\
                    (is_block g' x /\ not (free_incremental st' g' x) /\
                     ~(is_block g x /\ not (free_incremental st g x)) ==>
                       (exists (m: U64.t). Seq.mem m (minor_objects minor) /\
                          (Cheney.cheney_promote (Ph.Sweeping st) minor g fp roots).Promote.fwd_map m == x))))
