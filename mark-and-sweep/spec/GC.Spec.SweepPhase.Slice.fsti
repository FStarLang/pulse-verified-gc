/// ---------------------------------------------------------------------------
/// GC.Spec.SweepPhase.Slice - one slice of the incremental sweep
/// ---------------------------------------------------------------------------
///
/// A slice runs whole sweep steps (`GC.Spec.FusedSweep.sweep_step`) from the
/// sweep state it is handed -- the one derived from the heap and the cursor
/// (`GC.Spec.SweepPhase.Intrinsic.state_at`) -- until the blocks it has
/// swept, headers included, add up to at least `budget` words, or the sweep
/// is finished.
/// It overshoots the budget by at most one block, as OCaml 4.14's
/// `sweep_slice` does (incremental-sweep-plan.md, D3).  The words swept are
/// how far the cursor has moved, in words.
///
/// A slice is some number of steps (`slice_is_steps`), so the sweep's step
/// theorems (`GC.Spec.FusedSweep.Step.sweep_inv_incremental_steps`) apply to
/// it: it keeps the sweep invariant, leaves the derived state, frees only objects
/// pending free, and the pending-free set shrinks (`sweep_slice_phase`).  It
/// stops early only when the sweep is finished, and a budget larger than the
/// heap always finishes it.
///
/// `phase_slice` is the slice at the collector's phase, which is the cursor
/// alone: nothing to do when idle; mid-sweep, the slice from the derived
/// state, and the phase it leaves is the new cursor, or idle once the cursor
/// reaches the end.

module GC.Spec.SweepPhase.Slice

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.SweepPhase.Intrinsic

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase

/// The words swept since the slice started with the cursor at `c0`.
let swept_words (c0: U64.t) (st: sweep_state) : nat =
  if U64.v st.cursor >= U64.v c0 then (U64.v st.cursor - U64.v c0) / 8 else 0

/// Step until the sweep is finished or `budget` words are swept since `c0`.
let rec slice_from (g: heap) (fp: U64.t) (st: sweep_state) (c0: U64.t) (budget: nat)
  : Tot (heap & U64.t & sweep_state) (decreases (heap_size - U64.v st.cursor))
  = if sweep_done st.cursor || not (can_sweep g st) || swept_words c0 st >= budget then (g, fp, st)
    else begin
      let (g', fp', st') = sweep_step g fp st in
      slice_from g' fp' st' c0 budget
    end

/// **A slice** of `budget` words from the sweep state `st`.
let sweep_slice (g: heap) (fp: U64.t) (st: sweep_state) (budget: nat) : heap & U64.t & sweep_state =
  slice_from g fp st st.cursor budget

/// The slice at the collector's phase.
let phase_slice (g: heap) (fp: U64.t) (ph: Ph.gc_phase) (budget: nat) : GTot (heap & U64.t & Ph.gc_phase) =
  match ph with
  | Ph.Idle -> (g, fp, Ph.Idle)
  | Ph.Sweeping c ->
      let (g', fp', st') = sweep_slice g fp (state_at g c) budget in
      (g', fp', (if sweep_done st'.cursor then Ph.Idle else Ph.Sweeping st'.cursor))

/// One unfolding of `slice_from`.
val slice_from_unfold (g: heap) (fp: U64.t) (st: sweep_state) (c0: U64.t) (budget: nat)
  : Lemma (slice_from g fp st c0 budget ==
           (if sweep_done st.cursor || not (can_sweep g st) || swept_words c0 st >= budget then (g, fp, st)
            else (let (g', fp', st') = sweep_step g fp st in slice_from g' fp' st' c0 budget)))

/// The number of steps a slice takes.
let rec slice_count (g: heap) (fp: U64.t) (st: sweep_state) (c0: U64.t) (budget: nat)
  : Tot nat (decreases (heap_size - U64.v st.cursor))
  = if sweep_done st.cursor || not (can_sweep g st) || swept_words c0 st >= budget then 0
    else begin
      let (g', fp', st') = sweep_step g fp st in
      1 + slice_count g' fp' st' c0 budget
    end

/// **A slice is some number of steps.**
val slice_is_steps (g: heap) (fp: U64.t) (st: sweep_state) (c0: U64.t) (budget: nat)
  : Lemma (slice_from g fp st c0 budget == sweep_steps g fp st (slice_count g fp st c0 budget))

/// **A slice keeps the sweep phase**: from the derived state it leaves the
/// derived state, the pending-free set shrinks, the non-free objects are the
/// same before and after (with the same size, tag and fields), the cursor
/// does not move back, and the slice stops only when the sweep is finished
/// or the budget is spent.  A budget of more words than the heap has
/// finishes the sweep.
val sweep_slice_phase (g: heap) (fp: U64.t) (c: U64.t) (budget: nat)
  : Lemma (requires sweep_inv_incremental g fp c)
          (ensures (let (g', fp', st') = sweep_slice g fp (state_at g c) budget in
                    let c' = st'.cursor in
                    st' == state_at g' c' /\
                    sweep_inv_incremental g' fp' c' /\
                    (forall (x: obj_addr). in_use (free_incremental c') g' x == in_use (free_incremental c) g x) /\
                    (forall (x: obj_addr). in_use (free_incremental c) g x ==> same_block g g' (hd_address x)) /\
                    (forall (x: obj_addr). pending_free c' g' x ==> pending_free c g x) /\
                    U64.v c' >= U64.v c /\
                    (sweep_done c' \/ swept_words c st' >= budget) /\
                    (budget > heap_words ==> sweep_done c')))
