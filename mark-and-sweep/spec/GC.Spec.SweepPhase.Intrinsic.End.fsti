/// ---------------------------------------------------------------------------
/// GC.Spec.SweepPhase.Intrinsic.End - what the sweep phase leaves behind
/// ---------------------------------------------------------------------------
///
/// When the cursor reaches the end of the heap:
///
///   * *incremental* (`sweep_phase_end`): from the sweep phase alone, nothing is
///     pending, the heap is well formed, and it is swept clean (dense, exact
///     ascending free list, every object white or free, none infix);
///   * *stop-the-world* (`sweep_phase_end_stw`): with the relation to the
///     marked heap (`stw_rel`), the result satisfies the stop-the-world sweep's
///     end facts `GC.Spec.FusedSweep.End.sweep_post`, so `fused_exact`,
///     `sweep_post_wf` and the correctness pillars apply unchanged.  The whole
///     pass from the marked heap gets there through the intrinsic invariant
///     (`fused_sweep_post_intrinsic`).

module GC.Spec.SweepPhase.Intrinsic.End

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.SweepPhase.Util
open GC.Spec.SweepPhase.Intrinsic

module U64 = FStar.UInt64
module FSE = GC.Spec.FusedSweep.End
module AC = GC.Spec.Allocator.Cursor
module W = GC.Spec.Walk

/// **The end of an incremental sweep phase.**
val sweep_phase_end (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_phase_inv g fp st /\ U64.v st.cursor + 8 >= heap_size)
          (ensures swept_clean g fp /\
                   (forall (x: obj_addr). ~(pending g st x)) /\
                   well_formed_heap g)

/// **The end of a stop-the-world sweep**, from the intrinsic invariant and
/// the relation to the marked heap.
val sweep_phase_end_stw (g0 g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_phase_inv g fp st /\ stw_rel g0 g (U64.v st.cursor) /\
                    U64.v st.cursor + 8 >= heap_size)
          (ensures FSE.sweep_post g0 g fp)

/// The whole pass keeps the invariant and ends in `sweep_post`.
val sweep_from_post (g0 g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_phase_inv g fp st /\ stw_rel g0 g (U64.v st.cursor))
          (ensures (let r = sweep_from g fp st in FSE.sweep_post g0 (fst r) (snd r)))

/// The fused sweep from the heap marking left, through the intrinsic
/// invariant: `sweep_post`, and so a well-formed result.
val fused_sweep_post_intrinsic (g0: heap) (fp: U64.t)
  : Lemma (requires sweep_pre g0 fp /\ FSE.marked g0)
          (ensures (let r = fused_sweep_coalesce g0 fp in
                    FSE.sweep_post g0 (fst r) (snd r) /\ well_formed_heap (fst r)))

/// **#29 mid-sweep**: the free list is exact at every point of the sweep, so
/// an allocation fails only when no free block anywhere is big enough.
val sweep_phase_oom_no_fit (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat)
                           (tag: U64.t{U64.v tag < 256})
  : Lemma (requires sweep_phase_inv g fp st /\ wz >= 1 /\
                    (fst (AC.alloc_phase g fp (GC.Spec.Phase.Sweeping st) wz tag)).GC.Spec.Allocator.obj_out == 0UL)
          (ensures forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ is_blue x g ==>
                     U64.v (wosize_of_object x g) < wz)

/// Stop-the-world, when nothing was live after marking, everything behind the
/// cursor is one free block.
val nothing_live_one_block (g0 g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_phase_inv g fp st /\ stw_rel g0 g (U64.v st.cursor) /\
                    (forall (p: hp_addr). pos g0 p ==> not (black_at g0 p)) /\
                    U64.v zero_addr < U64.v st.cursor)
          (ensures pos g zero_addr /\ blue_at g zero_addr /\
                   W.bnext g zero_addr == U64.v st.cursor /\
                   (forall (x: nat). W.reaches g zero_addr x /\ x < U64.v st.cursor ==>
                      x == U64.v zero_addr))
