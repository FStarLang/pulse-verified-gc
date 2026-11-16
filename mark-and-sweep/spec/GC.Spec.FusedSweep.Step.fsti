/// ---------------------------------------------------------------------------
/// GC.Spec.FusedSweep.Step - one step keeps the sweep invariant
/// ---------------------------------------------------------------------------
///
/// One lemma per case of `GC.Spec.FusedSweep.sweep_step` (survivor; free
/// block left alone, linked or a fragment; garbage freed, linked or a
/// fragment; and the four merges -- into `swept_tail` or into the fragment
/// before the cursor, absorbing a block that was or was not on the list),
/// each concluding the clauses of the sweep invariant
/// (`GC.Spec.SweepPhase.Intrinsic.sweep_inv_incremental`) at the new cursor
/// directly: behind it the block just swept is white or free, in front of it
/// nothing changed, and the blocks that are not free are the same blocks,
/// with the same contents, so well-formedness carries over
/// (`GC.Spec.SweepPhase.Intrinsic.wf_transport`).  Combined here into one
/// statement (`sweep_inv_incremental_step`), its stop-the-world extension
/// (`sweep_inv_stw_step`), and lifted to `k` steps.

module GC.Spec.FusedSweep.Step

open GC.Spec.Base
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.SweepPhase.Intrinsic

open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64

/// ---------------------------------------------------------------------------
/// The step, case by case (for the implementation)
/// ---------------------------------------------------------------------------

let nx_of (g: heap) (st: sweep_state{can_sweep g st}) : U64.t = U64.uint_to_t (step_next g st)

let bx_of (st: sweep_state{cursor_ok st}) : hp_addr = U64.add st.cursor mword

val step_eq_black (g: heap) (fp: U64.t) (st: sweep_state{can_sweep g st})
  : Lemma (requires black_at g st.cursor)
          (ensures sweep_step g fp st ==
                   (write_word g st.cursor (white_header (read_word g st.cursor)), fp,
                    advance st (nx_of g st)))

val step_eq_blue (g: heap) (fp: U64.t) (st: sweep_state{can_sweep g st})
  : Lemma (requires blue_at g st.cursor /\ not (prev_free g st))
          (ensures sweep_step g fp st ==
                   (g, fp, (if wz_at g st.cursor >= 1
                            then { cursor = nx_of g st; swept_tail = bx_of st; last_fragment = 0UL }
                            else { cursor = nx_of g st; swept_tail = st.swept_tail;
                                   last_fragment = bx_of st })))

val step_eq_white (g: heap) (fp: U64.t) (st: sweep_state{can_sweep g st})
  : Lemma (requires not (black_at g st.cursor) /\ not (blue_at g st.cursor) /\
                    not (prev_free g st))
          (ensures (let c : hp_addr = st.cursor in
                    let wz = wz_at g c in
                    let g1 = write_word g c (free_header wz) in
                    let b = bx_of st in
                    if wz >= 1 then begin
                      let g2 = write_word g1 b (after_tail g fp st.swept_tail) in
                      let r = set_after_tail g2 fp st.swept_tail b in
                      sweep_step g fp st ==
                        (fst r, snd r, { cursor = nx_of g st; swept_tail = b; last_fragment = 0UL })
                    end else
                      sweep_step g fp st ==
                        (g1, fp, { cursor = nx_of g st; swept_tail = st.swept_tail;
                                   last_fragment = b })))

/// The block before the cursor is free: it grows over the one at the cursor.
val step_eq_merge (g: heap) (fp: U64.t) (st: sweep_state{can_sweep g st})
  : Lemma (requires not (black_at g st.cursor) /\ prev_free g st /\
                    (let p = if st.last_fragment <> 0UL then st.last_fragment else st.swept_tail in
                     is_obj p /\ wosize_at g p + wz_at g st.cursor + 1 < pow2 54))
          (ensures (let c : hp_addr = st.cursor in
                    let wz = wz_at g c in
                    let b = bx_of st in
                    let linked = blue_at g c && wz >= 1 in
                    let p = if st.last_fragment <> 0UL then st.last_fragment else st.swept_tail in
                    let g1 = write_word g (hd_address (p <: obj_addr))
                                        (free_header (wosize_at g p + wz + 1)) in
                    if st.last_fragment <> 0UL then begin
                      let nxt = if linked then read_word g b else after_tail g fp st.swept_tail in
                      let g2 = write_word g1 (p <: hp_addr) nxt in
                      let r = set_after_tail g2 fp st.swept_tail p in
                      sweep_step g fp st ==
                        (fst r, snd r, { cursor = nx_of g st; swept_tail = p; last_fragment = 0UL })
                    end
                    else if linked then begin
                      let r = set_after_tail g1 fp st.swept_tail (read_word g b) in
                      sweep_step g fp st == (fst r, snd r, advance st (nx_of g st))
                    end
                    else sweep_step g fp st == (g1, fp, advance st (nx_of g st))))


/// ---------------------------------------------------------------------------
/// One step
/// ---------------------------------------------------------------------------

/// **One step keeps the sweep invariant**, and the pending-free set shrinks.
/// The step is the stop-the-world one run from the derived state, and the
/// state it leaves is the derived one again.  It frees only objects pending
/// free: the non-free objects are the same before and after (with the same
/// size, tag and fields).
val sweep_inv_incremental_step (g: heap) (fp: U64.t) (c: U64.t)
  : Lemma (requires sweep_inv_incremental g fp c /\ U64.v c + 8 < heap_size)
          (ensures can_sweep g (state_at g c) /\
                   (let (g', fp', st') = sweep_step g fp (state_at g c) in
                    let c' = st'.cursor in
                    st' == state_at g' c' /\
                    sweep_inv_incremental g' fp' c' /\
                    (forall (x: obj_addr). in_use (free_incremental c') g' x == in_use (free_incremental c) g x) /\
                    (forall (x: obj_addr). in_use (free_incremental c) g x ==> same_block g g' (hd_address x)) /\
                    (forall (x: obj_addr). pending_free c' g' x ==> pending_free c g x) /\
                    U64.v c' > U64.v c /\ U64.v c' <= heap_size))

/// The ghost set is never carried: that the objects pending free stay among the
/// white objects marking left follows from the shrinking, step by step.
val pending_free_within_step (g: heap) (fp: U64.t) (c: U64.t) (dead: obj_addr -> prop)
  : Lemma (requires sweep_inv_incremental g fp c /\ pending_free_within g c dead /\
                    U64.v c + 8 < heap_size)
          (ensures can_sweep g (state_at g c) /\
                   (let (g', fp', st') = sweep_step g fp (state_at g c) in
                    pending_free_within g' st'.cursor dead))

/// **Stop-the-world, one step keeps the relation to the marked heap**: the
/// extra clauses follow from the step's frame -- the heap from the new
/// cursor on is unchanged, and the blocks that are not free are the same.
val sweep_inv_stw_step (g0 g: heap) (fp: U64.t) (c: U64.t)
  : Lemma (requires sweep_inv_stw g0 g fp c /\ U64.v c + 8 < heap_size)
          (ensures can_sweep g (state_at g c) /\
                   (let (g', fp', st') = sweep_step g fp (state_at g c) in
                    sweep_inv_stw g0 g' fp' st'.cursor))

/// What a step needs to be safe to run on the heap itself (the Pulse step
/// reads the header at the cursor, `swept_tail`'s and `last_fragment`'s
/// blocks, and writes a merged header): the guards
/// (`GC.Spec.FusedSweep.Inv.step_guards`), of the derived state.
val sweep_inv_incremental_ready (g: heap) (fp: U64.t) (c: U64.t)
  : Lemma (requires sweep_inv_incremental g fp c /\ U64.v c + 8 < heap_size)
          (ensures (let st = state_at g c in
                    can_sweep g st /\
                    (st.swept_tail == 0UL \/ is_obj st.swept_tail) /\
                    (st.last_fragment == 0UL \/ is_obj st.last_fragment) /\
                    (prev_free g st ==>
                      (let p = if st.last_fragment <> 0UL then st.last_fragment else st.swept_tail in
                       is_obj p /\
                       wosize_at g p + U64.v (getWosize (read_word g (st.cursor <: hp_addr))) + 1
                         < pow2 54))))

/// ---------------------------------------------------------------------------
/// Up to `k` steps
/// ---------------------------------------------------------------------------

/// **`k` steps keep the sweep invariant**: the state they leave is the
/// derived one, the pending-free set shrinks, the non-free objects are the
/// same before and after, the cursor does not move back, and it stays put
/// only if no step was asked for or the sweep is finished.
val sweep_inv_incremental_steps (g: heap) (fp: U64.t) (c: U64.t) (k: nat)
  : Lemma (requires sweep_inv_incremental g fp c)
          (ensures (let (g', fp', st') = sweep_steps g fp (state_at g c) k in
                    let c' = st'.cursor in
                    st' == state_at g' c' /\
                    sweep_inv_incremental g' fp' c' /\
                    (forall (x: obj_addr). in_use (free_incremental c') g' x == in_use (free_incremental c) g x) /\
                    (forall (x: obj_addr). in_use (free_incremental c) g x ==> same_block g g' (hd_address x)) /\
                    (forall (x: obj_addr). pending_free c' g' x ==> pending_free c g x) /\
                    U64.v c' >= U64.v c /\
                    (c' == c ==> k = 0 \/ sweep_done c)))

/// Stop-the-world, `k` steps keep the relation to the marked heap.
val sweep_inv_stw_steps (g0 g: heap) (fp: U64.t) (c: U64.t) (k: nat)
  : Lemma (requires sweep_inv_stw g0 g fp c)
          (ensures (let (g', fp', st') = sweep_steps g fp (state_at g c) k in
                    sweep_inv_stw g0 g' fp' st'.cursor))

/// A budget of one step per word of the heap finishes the sweep.
val sweep_steps_done (g: heap) (fp: U64.t) (c: U64.t) (k: nat)
  : Lemma (requires sweep_inv_incremental g fp c /\ k * 8 >= heap_size - U64.v c)
          (ensures (let (g', fp', st') = sweep_steps g fp (state_at g c) k in sweep_done st'.cursor))

/// **Sweep steps keep where the walk ends**: a step changes headers only
/// below the new cursor, and the walk still reaches it.
val sweep_steps_walk_end (g: heap) (fp: U64.t) (c: U64.t) (k: nat)
  : Lemma (requires sweep_inv_incremental g fp c)
          (ensures (let (g', _, _) = sweep_steps g fp (state_at g c) k in
                    GC.Spec.Walk.walk_end g' zero_addr == GC.Spec.Walk.walk_end g zero_addr))
