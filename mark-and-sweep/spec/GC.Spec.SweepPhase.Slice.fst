module GC.Spec.SweepPhase.Slice

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.SweepPhase.Intrinsic

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase

#set-options "--fuel 1 --ifuel 1 --z3rlimit 10"

let slice_from_unfold g fp st c0 budget = ()

let rec slice_is_steps g fp st c0 budget
  : Lemma (ensures slice_from g fp st c0 budget == sweep_steps g fp st (slice_count g fp st c0 budget))
          (decreases (heap_size - U64.v st.cursor))
  = sweep_steps_unfold g fp st (slice_count g fp st c0 budget);
    if sweep_done st.cursor || not (can_sweep g st) || swept_words c0 st >= budget then ()
    else begin
      let (g', fp', st') = sweep_step g fp st in
      slice_is_steps g' fp' st' c0 budget
    end

/// The slice stops only when the sweep is finished or the budget is spent.
let rec slice_stops (g: heap) (fp: U64.t) (st: sweep_state) (c0: U64.t) (budget: nat)
  : Lemma (requires sweep_phase_inv g fp st.cursor /\ st == state_at g st.cursor)
          (ensures (let (_, _, st') = slice_from g fp st c0 budget in
                    sweep_done st'.cursor \/ swept_words c0 st' >= budget))
          (decreases (heap_size - U64.v st.cursor))
  = if sweep_done st.cursor || swept_words c0 st >= budget then ()
    else begin
      sweep_phase_step g fp st.cursor;
      let (g', fp', st') = sweep_step g fp st in
      slice_stops g' fp' st' c0 budget
    end

let sweep_slice_phase g fp c budget =
  let st = state_at g c in
  slice_is_steps g fp st c budget;
  sweep_phase_steps g fp c (slice_count g fp st c budget);
  slice_stops g fp st c budget;
  let (g', fp', st') = sweep_slice g fp st budget in
  sweep_phase_inv_elim g' fp' st'.cursor
