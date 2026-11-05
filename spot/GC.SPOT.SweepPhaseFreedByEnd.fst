/// ---------------------------------------------------------------------------
/// GC.SPOT.SweepPhaseFreedByEnd - a sweep cycle frees what marking left dead
/// ---------------------------------------------------------------------------
///
/// The sweep phase's completeness (`GC.Spec.SweepPhase.Completeness`),
/// applied to a concrete cycle.  The marked heap is `GC.SPOT.SweepPhasePendingFree`'s
/// `g4`: nothing marked, a free block at the start, and the two white
/// objects `G` and `P` (`P`'s field points at `G`).  The cycle:
///
///   1. start the sweep at the marked heap (nothing allocated yet);
///   2. a slice of two steps -- the free block at the start absorbs `G`;
///   3. a minor collection at the sweep's phase, of an empty nursery;
///   4. finish the sweep (one step per word of the heap is enough).
///
/// Every event keeps the account of the non-free blocks (survivors of
/// marking or new), and at the end the theorem says that both dead-at-mark
/// objects, `G` and `P`, are freed: no allocation ran, and the empty nursery
/// promotes nothing, so no address is new (`freed_by_end_spot`).  `P` was
/// still pending free after the minor collection, so its freeing is the
/// finishing sweep's.

module GC.SPOT.SweepPhaseFreedByEnd

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.SweepPhase.Intrinsic
open GC.Spec.FusedSweep.Step
open GC.Spec.SweepPhase.Completeness
open GC.Gen.MinorHeap
open GC.SPOT.SweepPhasePendingFree

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module GenInv = GC.Gen.HeapInvariant
module Mark = GC.Spec.Mark
module SPE = GC.Spec.SweepPhase.Intrinsic.End
module SPM = GC.Gen.SweepPhase.Minor
module SPC = GC.Gen.SweepPhase.Completeness
module Ph = GC.Spec.Phase
module Promote = GC.Gen.Promote

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// The marked heap and its dead objects
/// ---------------------------------------------------------------------------

/// `g4` is a heap marking can leave: nothing grey, the tri-colour invariant,
/// and the sweep can start on it.
let marked (r: unit{room})
  : Lemma (sweep_pre (g4 r) (fp3 r) /\ Mark.noGreyObjects (g4 r) /\ Mark.tri_color_invariant (g4 r) /\
           sweep_inv_incremental (g4 r) (fp3 r) sweep_start.cursor)
  = stage3 r; stage4 r; stage5 r;
    SPE.sweep_inv_incremental_end (g4 r) (fp3 r) (cur1 r);
    can_start (g4 r) (fp3 r)

/// `G` and `P` are white in it: dead at mark.
let dead_objects (r: unit{room})
  : Lemma (white_after_mark (g4 r) (gg r) /\ white_after_mark (g4 r) (pp r))
  = stage3 r; stage4 r; stage5 r;
    let c = cend r in
    let qg = mk_hp_addr (c - 32) in
    let qp = mk_hp_addr (c - 16) in
    hd_address_spec (gg r); hd_address_spec (pp r);
    assert (W.reaches (g3 r) zero_addr (c - 32));
    assert (read_word (g4 r) qg == read_word (g3 r) qg);
    colour_of (g4 r) (gg r);
    colour_of (g4 r) (pp r);
    obj_pos (g4 r) (pp r)

/// ---------------------------------------------------------------------------
/// The cycle
/// ---------------------------------------------------------------------------

/// After the slice: `GC.SPOT.SweepPhasePendingFree`'s `g5`, at cursor `c5`.
let c5 (r: unit{room}) : GTot U64.t = (st5 r).cursor

/// After the minor collection, of the empty nursery `minor_reset m`.
let mc (r: unit{room}) (m: minor_state) (roots: seq U64.t) : GTot Promote.minor_collect_result =
  SPM.collect_at (c5 r) (minor_reset m) (g5 r) (fp5 r) roots

/// After finishing the sweep.
let fin (r: unit{room}) (m: minor_state) (roots: seq U64.t) : GTot (heap & U64.t & sweep_state) =
  let res = mc r m roots in
  sweep_steps res.Promote.mc_major res.Promote.mc_fp (state_at res.Promote.mc_major (c5 r)) heap_words

/// 1--2. The start and the slice.
let after_slice (r: unit{room})
  : Lemma (sweep_inv_incremental (g5 r) (fp5 r) (c5 r) /\
           survivor_or_new (g4 r) nothing_new (g5 r) (c5 r))
  = marked r; stage6 r;
    survivor_or_new_start (g4 r);
    state_at_start (g4 r);
    survivor_or_new_steps (g4 r) nothing_new (g4 r) (fp3 r) sweep_start.cursor 2

/// 3. The minor collection: it promotes nothing.
let after_minor (r: unit{room}) (m: minor_state) (roots: seq U64.t)
  : Lemma (let res = mc r m roots in
           sweep_inv_incremental res.Promote.mc_major res.Promote.mc_fp (c5 r) /\
           survivor_or_new (g4 r) nothing_new res.Promote.mc_major (c5 r))
  = after_slice r;
    let g = g5 r in
    let fp = fp5 r in
    let cur = c5 r in
    SPM.sweep_major_shape g fp cur;
    GenInv.collection_shape_with_after_minor_reset (Ph.Sweeping cur) (free_incremental cur) m g fp;
    GenInv.collection_shape_with_elim (Ph.Sweeping cur) (free_incremental cur) (minor_reset m) g fp;
    GenInv.minor_reset_heap_shape m;
    SPM.minor_keeps_sweep_phase (minor_reset m) g fp cur roots;
    SPC.survivor_or_new_minor (g4 r) nothing_new (minor_reset m) g fp cur roots;
    FStar.Classical.forall_intro (SPC.nothing_promoted_after_reset cur m g fp roots);
    survivor_or_new_weaken (g4 r)
      (SPC.with_promoted nothing_new cur (minor_reset m) g fp roots) nothing_new
      (mc r m roots).Promote.mc_major cur

/// **The SPOT.**  At the end of the cycle the sweep is finished, and both
/// objects dead at mark are freed.
let freed_by_end_spot (r: unit{room}) (m: minor_state) (roots: seq U64.t)
  : Lemma (let (g, fp, st) = fin r m roots in
           white_after_mark (g4 r) (gg r) /\ white_after_mark (g4 r) (pp r) /\
           sweep_inv_incremental g fp st.cursor /\ sweep_done st.cursor /\
           freed g (gg r) /\ freed g (pp r))
  = dead_objects r;
    after_minor r m roots;
    let res = mc r m roots in
    let g = res.Promote.mc_major in
    let fp = res.Promote.mc_fp in
    let cur = c5 r in
    sweep_inv_incremental_steps g fp cur heap_words;
    sweep_inv_incremental_elim g fp cur;
    assert (heap_words * 8 == heap_size);
    sweep_steps_done g fp cur heap_words;
    survivor_or_new_steps (g4 r) nothing_new g fp cur heap_words;
    let (g', fp', st') = fin r m roots in
    freed_by_end (g4 r) nothing_new g' fp' st'.cursor
