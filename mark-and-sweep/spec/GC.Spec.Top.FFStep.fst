/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFStep - one step of akhil's first-fit sweep leaves the heap
/// in front of the new cursor alone
/// ---------------------------------------------------------------------------
///
/// Design doc §13.  akhil proves that a step of the fused sweep leaves the
/// heap from the new cursor on unchanged (`FusedSweep.Step.stepped`), but
/// only inside his module.  This module derives it again from his exported
/// statements of each case (`step_eq_black`, `_blue`, `_white`, `_merge`):
/// every word a step writes -- the header at the cursor, its link word, the
/// header and link of the free block before it, the link of `swept_tail` --
/// lies below the new cursor (`tail_ok`: `swept_tail`'s block ends at or
/// before the cursor; `frag_ok`: the fragment's object is the cursor).

module GC.Spec.Top.FFStep

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
module U64 = FStar.UInt64
module FL = GC.Spec.FreeList
module SPI = GC.Spec.SweepPhase.Intrinsic
module FSS = GC.Spec.FusedSweep.Step

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// A write below `n` leaves every word from `n` on.
let rw_below (g: heap) (w: hp_addr) (v: U64.t) (n: nat) (a: hp_addr)
  : Lemma (requires U64.v w < n /\ U64.v a >= n) (ensures read_word (write_word g w v) a == read_word g a)
  = read_write_different g w a v

/// So does linking after `swept_tail`, when it lies below `n`.
let sat_below (g: heap) (fp t v: U64.t) (n: nat) (a: hp_addr)
  : Lemma (requires (t == 0UL \/ U64.v t < n) /\ U64.v a >= n)
          (ensures read_word (fst (set_after_tail g fp t v)) a == read_word g a)
  = if t = 0UL then ()
    else if is_obj t then rw_below g (t <: hp_addr) v n a

/// The caches lie below the cursor.
#push-options "--z3rlimit 40"
let caches_below (g: heap) (fp: U64.t) (c: U64.t)
  : Lemma (requires SPI.sweep_inv_incremental g fp c)
          (ensures (let st = SPI.state_at g c in
                    (st.swept_tail == 0UL \/ (U64.v st.swept_tail + 8 <= U64.v c /\ is_obj st.swept_tail)) /\
                    (st.last_fragment == 0UL \/ U64.v st.last_fragment == U64.v c)))
  = SPI.sweep_inv_incremental_elim g fp c;
    let st = SPI.state_at g c in
    tail_ok_elim g (U64.v c) st.swept_tail;
    if st.swept_tail <> 0UL then begin
      GC.Spec.FreeList.Ascending.fl_cell_facts g st.swept_tail;
      let t : obj_addr = st.swept_tail in
      wosize_of_object_spec t g;
      assert (wosize_at g st.swept_tail >= 1)
    end
#pop-options

/// **One step leaves the heap from the new cursor on.**
#push-options "--z3rlimit 40"
let step_front (g: heap) (fp: U64.t) (c: U64.t) (a: hp_addr)
  : Lemma (requires SPI.sweep_inv_incremental g fp c /\ U64.v c + 8 < heap_size /\
                    (let st = SPI.state_at g c in
                     can_sweep g st /\ U64.v a >= step_next g st))
          (ensures (let (g', _, _) = sweep_step g fp (SPI.state_at g c) in read_word g' a == read_word g a))
  = let st = SPI.state_at g c in
    FSS.sweep_inv_incremental_ready g fp c;
    caches_below g fp c;
    let n = step_next g st in
    let cc : hp_addr = st.cursor in
    let wz = wz_at g cc in
    assert (n == U64.v c + (wz + 1) * 8);
    if black_at g cc then begin
      FSS.step_eq_black g fp st;
      rw_below g cc (white_header (read_word g cc)) n a
    end
    else if prev_free g st then begin
      FSS.step_eq_merge g fp st;
      let p = if st.last_fragment <> 0UL then st.last_fragment else st.swept_tail in
      let po : obj_addr = p in
      hd_address_spec po;
      let g1 = write_word g (hd_address po) (free_header (wosize_at g p + wz + 1)) in
      rw_below g (hd_address po) (free_header (wosize_at g p + wz + 1)) n a;
      let b = FSS.bx_of st in
      let linked = blue_at g cc && wz >= 1 in
      if st.last_fragment <> 0UL then begin
        let nxt = if linked then read_word g b else after_tail g fp st.swept_tail in
        rw_below g1 (p <: hp_addr) nxt n a;
        sat_below (write_word g1 (p <: hp_addr) nxt) fp st.swept_tail p n a
      end
      else if linked then sat_below g1 fp st.swept_tail (read_word g b) n a
    end
    else if blue_at g cc then FSS.step_eq_blue g fp st
    else begin
      FSS.step_eq_white g fp st;
      let g1 = write_word g cc (free_header wz) in
      rw_below g cc (free_header wz) n a;
      if wz >= 1 then begin
        let b = FSS.bx_of st in
        rw_below g1 b (after_tail g fp st.swept_tail) n a;
        sat_below (write_word g1 b (after_tail g fp st.swept_tail)) fp st.swept_tail b n a
      end
    end
#pop-options
