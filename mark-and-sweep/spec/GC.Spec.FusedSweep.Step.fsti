/// ---------------------------------------------------------------------------
/// GC.Spec.FusedSweep.Step - one step keeps the invariant
/// ---------------------------------------------------------------------------
///
/// One lemma per case of `GC.Spec.FusedSweep.sweep_step` (survivor; free
/// block left alone, linked or a fragment; garbage freed, linked or a
/// fragment; and the four merges -- into `swept_tail` or into the fragment
/// before the cursor, absorbing a block that was or was not on the list),
/// combined here into one statement, and lifted to the whole pass.

module GC.Spec.FusedSweep.Step

open GC.Spec.Base
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv

open GC.Spec.Heap
open GC.Spec.Object

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


/// **One step keeps the invariant.**
val sweep_step_inv (g0 g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_g0 g0 /\ sweep_inv g0 g fp st /\ U64.v st.cursor + 8 < heap_size)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in sweep_inv g0 g' fp' st'))

/// The sweep has reached the end of the heap with the invariant intact.
let sweep_done (g0 g: heap) (fp: U64.t) : prop =
  exists (st: sweep_state). sweep_inv g0 g fp st /\ U64.v st.cursor + 8 >= heap_size

/// **The whole pass keeps the invariant**, and stops at the end of the heap.
val sweep_from_done (g0 g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_g0 g0 /\ sweep_inv g0 g fp st)
          (ensures (let r = sweep_from g fp st in sweep_done g0 (fst r) (snd r)))

/// From the heap marking left, with the free list the previous cycle left.
val fused_sweep_done (g0: heap) (fp: U64.t)
  : Lemma (requires sweep_pre g0 fp)
          (ensures (let r = fused_sweep_coalesce g0 fp in sweep_done g0 (fst r) (snd r)))
