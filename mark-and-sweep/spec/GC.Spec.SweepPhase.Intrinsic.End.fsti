/// ---------------------------------------------------------------------------
/// GC.Spec.SweepPhase.Intrinsic.End - what the sweep leaves behind
/// ---------------------------------------------------------------------------
///
/// When the cursor reaches the end of the heap:
///
///   * *incremental* (`sweep_inv_incremental_end`): from the sweep invariant
///     alone, nothing is pending free, the heap is well formed, and it is
///     swept clean (dense, exact ascending free list, every object white or
///     free, none infix);
///   * *stop-the-world* (`sweep_inv_stw_end`): with the relation to the
///     marked heap, the result satisfies the stop-the-world sweep's end facts
///     `GC.Spec.FusedSweep.End.sweep_post`, so `fused_exact`, `sweep_post_wf`
///     and the correctness pillars apply.  The whole pass from the marked heap
///     gets there step by step (`fused_sweep_post`).

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
module W = GC.Spec.Walk

/// **The end of an incremental sweep phase.**
val sweep_inv_incremental_end (g: heap) (fp: U64.t) (c: U64.t)
  : Lemma (requires sweep_inv_incremental g fp c /\ U64.v c + 8 >= heap_size)
          (ensures swept_clean g fp /\
                   (forall (x: obj_addr). not (pending_free c g x)) /\
                   well_formed_heap g)

/// **The end of a stop-the-world sweep**, from the sweep invariant and the
/// relation to the marked heap.
val sweep_inv_stw_end (g0 g: heap) (fp: U64.t) (c: U64.t)
  : Lemma (requires sweep_inv_stw g0 g fp c /\ U64.v c + 8 >= heap_size)
          (ensures FSE.sweep_post g0 g fp)

/// The rest of the pass from the derived state keeps the invariant and ends
/// in `sweep_post`.
val sweep_from_post (g0 g: heap) (fp: U64.t) (c: U64.t)
  : Lemma (requires sweep_inv_stw g0 g fp c)
          (ensures (let r = sweep_from g fp (state_at g c) in FSE.sweep_post g0 (fst r) (snd r)))

/// **The fused sweep**, from the heap marking left and the free list the
/// previous cycle left: `sweep_post`, and so a well-formed result.
val fused_sweep_post (g0: heap) (fp: U64.t)
  : Lemma (requires sweep_pre g0 fp /\ FSE.marked g0)
          (ensures (let r = fused_sweep_coalesce g0 fp in
                    FSE.sweep_post g0 (fst r) (snd r) /\ well_formed_heap (fst r)))

/// Stop-the-world, when nothing was live after marking, everything behind the
/// cursor is one free block.
val nothing_live_one_block (g0 g: heap) (fp: U64.t) (c: U64.t)
  : Lemma (requires sweep_inv_stw g0 g fp c /\
                    (forall (p: hp_addr). pos g0 p ==> not (black_at g0 p)) /\
                    U64.v zero_addr < U64.v c)
          (ensures pos g zero_addr /\ blue_at g zero_addr /\
                   W.bnext g zero_addr == U64.v c /\
                   (forall (x: nat). W.reaches g zero_addr x /\ x < U64.v c ==>
                      x == U64.v zero_addr))
