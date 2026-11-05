module GC.Spec.SweepPhase.Slice

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.SweepPhase.Intrinsic
open GC.Spec.FusedSweep.Step

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
  : Lemma (requires sweep_inv_incremental g fp st.cursor /\ st == state_at g st.cursor)
          (ensures (let (_, _, st') = slice_from g fp st c0 budget in
                    sweep_done st'.cursor \/ swept_words c0 st' >= budget))
          (decreases (heap_size - U64.v st.cursor))
  = if sweep_done st.cursor || swept_words c0 st >= budget then ()
    else begin
      sweep_inv_incremental_step g fp st.cursor;
      let (g', fp', st') = sweep_step g fp st in
      slice_stops g' fp' st' c0 budget
    end

let sweep_slice_phase g fp c budget =
  let st = state_at g c in
  slice_is_steps g fp st c budget;
  sweep_inv_incremental_steps g fp c (slice_count g fp st c budget);
  slice_stops g fp st c budget;
  let (g', fp', st') = sweep_slice g fp st budget in
  sweep_inv_incremental_elim g' fp' st'.cursor

let phase_rest_start g fp = state_at_start g

/// The pass from a state is the pass from where `k` steps leave it.
let rec sweep_from_steps (g: heap) (fp: U64.t) (st: sweep_state) (k: nat)
  : Lemma (ensures (let (g', fp', st') = sweep_steps g fp st k in
                    sweep_from g' fp' st' == sweep_from g fp st))
          (decreases k)
  = sweep_steps_unfold g fp st k;
    if k = 0 || sweep_done st.cursor || not (can_sweep g st) then ()
    else begin
      let (g', fp', st') = sweep_step g fp st in
      sweep_from_step g fp st;
      sweep_from_steps g' fp' st' (k - 1)
    end

let phase_rest_slice g fp ph budget =
  match ph with
  | Ph.Idle -> ()
  | Ph.Sweeping c ->
      let st = state_at g c in
      slice_is_steps g fp st c budget;
      sweep_from_steps g fp st (slice_count g fp st c budget);
      sweep_slice_phase g fp c budget;
      let (g', fp', st') = sweep_slice g fp st budget in
      if sweep_done st'.cursor then sweep_from_stop g' fp' st' else ()
