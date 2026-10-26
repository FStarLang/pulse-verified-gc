(*
   Pulse GC - the fused sweep

   A loop of `GC.Spec.FusedSweep.sweep_step`s over the current heap, with the
   sweep state {cursor, swept_tail, last_fragment} and the free-list head in
   references.  The loop invariant is the spec's own
   (`GC.Spec.FusedSweep.Inv.sweep_inv`), which also supplies the facts that
   make every read and every arithmetic step safe, plus the statement that
   the rest of the pass computes the spec's result.
*)

module GC.Impl.FusedSweepCoalesce

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
module U64 = FStar.UInt64
module SpecHeap = GC.Spec.Heap
module SpecObject = GC.Spec.Object
module Header = GC.Lib.Header
module FS = GC.Spec.FusedSweep
module FSI = GC.Spec.FusedSweep.Inv
module FStep = GC.Spec.FusedSweep.Step

/// ---------------------------------------------------------------------------
/// Pure helpers
/// ---------------------------------------------------------------------------

let mk_st (c t f: U64.t) : FS.sweep_state = { FS.cursor = c; FS.swept_tail = t; FS.last_fragment = f }

/// The implementation's header constructor is the spec's.
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
let makeHeader_bridge (wz: SpecObject.wosize) (c: color) (tag: U64.t{U64.v tag < 256})
  : Lemma (GC.Impl.Object.makeHeader wz c tag == SpecObject.makeHeader wz c tag)
  = SpecObject.makeHeader_is_pack_header64 wz c tag;
    GC.Impl.Object.makeHeader_eq_pack_header wz c tag;
    U64.v_inj (GC.Impl.Object.makeHeader wz c tag) (SpecObject.makeHeader wz c tag)
#pop-options

/// Everything a step needs to be safe.
let step_ready (g: heap_state) (st: FS.sweep_state) : prop =
  FS.can_sweep g st /\
  (st.FS.swept_tail == 0UL \/ FS.is_obj st.FS.swept_tail) /\
  (st.FS.last_fragment == 0UL \/ FS.is_obj st.FS.last_fragment) /\
  (FS.prev_free g st ==>
    (let p = if st.FS.last_fragment <> 0UL then st.FS.last_fragment else st.FS.swept_tail in
     FS.is_obj p /\
     FS.wosize_at g p + U64.v (SpecObject.getWosize (SpecHeap.read_word g (st.FS.cursor <: hp_addr))) + 1
       < pow2 54))

/// `sweep_step`, total.
let step_total (g: heap_state) (fp: U64.t) (st: FS.sweep_state) : heap_state & U64.t & FS.sweep_state =
  if FS.can_sweep g st then FS.sweep_step g fp st else (g, fp, st)

let step_matches (g: heap_state) (fp: U64.t) (c t f: U64.t)
    (g': heap_state) (r: U64.t & U64.t & U64.t & U64.t) : prop =
  let (c', t', f', fp') = r in
  step_total g fp (mk_st c t f) == (g', fp', mk_st c' t' f')

let pow2_facts () : Lemma (pow2 54 * 8 <= pow2 57 /\ pow2 57 * 2 <= pow2 64 /\
                           GC.Spec.Base.heap_size < pow2 57 /\ heap_size == GC.Spec.Base.heap_size)
  = assert_norm (pow2 54 * 8 <= pow2 57 /\ pow2 57 * 2 <= pow2 64)

/// ---------------------------------------------------------------------------
/// Is the block before the cursor free?
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
fn prev_free_impl (heap: heap_t) (c t f: U64.t)
  requires is_heap heap 's ** pure (t == 0UL \/ FS.is_obj t)
  returns b: bool
  ensures is_heap heap 's ** pure (b == FS.prev_free 's (mk_st c t f))
{
  if (not (U64.eq f 0UL)) { true }
  else if (U64.eq t 0UL) { false }
  else {
    SpecHeap.hd_address_spec (t <: obj_addr);
    let th = read_word heap (U64.sub t mword);
    getWosize_eq th;
    pow2_facts ();
    assert (pure (SpecHeap.hd_address (t <: obj_addr) == U64.sub t mword));
    U64.eq (U64.add t (U64.mul (getWosize th) mword)) c
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// One step
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 60 --fuel 0 --ifuel 1"
fn sweep_step_impl (heap: heap_t) (c t f fp: U64.t)
  requires is_heap heap 's ** pure (step_ready 's (mk_st c t f))
  returns r: (U64.t & U64.t & U64.t & U64.t)
  ensures exists* s2. is_heap heap s2 ** pure (step_matches 's fp c t f s2 r)
{
  let st = Ghost.hide (mk_st c t f);
  let hdr = read_word heap c;
  getWosize_eq hdr; getColor_eq hdr; getTag_eq hdr;
  pow2_facts ();
  let wz = getWosize hdr;
  let nx = U64.add c (U64.mul (U64.add wz 1UL) mword);
  assert (pure (nx == FStep.nx_of 's st));
  let b : hp_addr = U64.add c mword;
  assert (pure (b == FStep.bx_of st));
  let col = getColor hdr;
  if (Header.Black? col) {
    FStep.step_eq_black 's fp st;
    makeHeader_bridge wz Header.White (getTag hdr);
    write_word heap c (makeHeader wz white (getTag hdr));
    (nx, t, 0UL, fp)
  } else {
    let pf = prev_free_impl heap c t f;
    if (pf) {
      let p = (if not (U64.eq f 0UL) then f else t);
      FStep.step_eq_merge 's fp st;
      SpecHeap.hd_address_spec (p <: obj_addr);
      let ph : hp_addr = U64.sub p mword;
      assert (pure (SpecHeap.hd_address (p <: obj_addr) == ph));
      let phdr = read_word heap ph;
      getWosize_eq phdr;
      let pw = getWosize phdr;
      let linked = (Header.Blue? col && U64.gt wz 0UL);
      let bl = if (linked) { read_word heap b } else { 0UL };
      let tl = if (U64.eq t 0UL) { fp } else { read_word heap t };
      let neww = U64.add (U64.add pw wz) 1UL;
      FStar.Math.Lemmas.pow2_lt_compat 64 54;
      assert (pure (FS.free_header (FS.wosize_at 's p + U64.v wz + 1) ==
                    SpecObject.makeHeader neww Header.Blue 0UL));
      makeHeader_bridge neww Header.Blue 0UL;
      write_word heap ph (makeHeader neww blue 0UL);
      if (not (U64.eq f 0UL)) {
        let nxt = (if linked then bl else tl);
        write_word heap p nxt;
        if (U64.eq t 0UL) { (nx, p, 0UL, p) }
        else { write_word heap t p; (nx, p, 0UL, fp) }
      } else if (linked) {
        write_word heap t bl;
        (nx, t, 0UL, fp)
      } else {
        (nx, t, 0UL, fp)
      }
    } else if (Header.Blue? col) {
      FStep.step_eq_blue 's fp st;
      if (U64.gt wz 0UL) { (nx, b, 0UL, fp) } else { (nx, t, b, fp) }
    } else {
      FStep.step_eq_white 's fp st;
      let tl = if (U64.eq t 0UL) { fp } else { read_word heap t };
      FStar.Math.Lemmas.pow2_lt_compat 64 54;
      assert (pure (FS.free_header (U64.v wz) == SpecObject.makeHeader wz Header.Blue 0UL));
      makeHeader_bridge wz Header.Blue 0UL;
      write_word heap c (makeHeader wz blue 0UL);
      if (U64.gt wz 0UL) {
        write_word heap b tl;
        if (U64.eq t 0UL) { (nx, b, 0UL, b) }
        else { write_word heap t b; (nx, b, 0UL, fp) }
      } else {
        (nx, t, b, fp)
      }
    }
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// The pass
/// ---------------------------------------------------------------------------

/// What the loop needs at a step, from the invariant.
let step_facts (g0 g: heap_state) (fp: U64.t) (c t f: U64.t)
  : Lemma (requires FSI.sweep_g0 g0 /\ FSI.sweep_inv g0 g fp (mk_st c t f) /\ U64.v c + 8 < heap_size)
          (ensures step_ready g (mk_st c t f) /\
                   (let (g', fp', st') = step_total g fp (mk_st c t f) in
                    FSI.sweep_inv g0 g' fp' st' /\
                    U64.v st'.FS.cursor > U64.v c /\ U64.v st'.FS.cursor <= heap_size /\
                    FS.sweep_from g fp (mk_st c t f) == FS.sweep_from g' fp' st'))
  = FSI.sweep_inv_facts g0 g fp (mk_st c t f);
    FStep.sweep_step_inv g0 g fp (mk_st c t f);
    FS.sweep_from_step g fp (mk_st c t f)

/// The pass stops at the end of the heap.
let stop_facts (g0 g: heap_state) (fp: U64.t) (c t f: U64.t)
  : Lemma (requires U64.v c + 8 >= heap_size)
          (ensures FS.sweep_from g fp (mk_st c t f) == (g, fp))
  = FS.sweep_from_stop g fp (mk_st c t f)

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
fn fused_sweep_coalesce (heap: heap_t) (fp: U64.t)
  requires is_heap heap 's ** pure (FSI.sweep_pre 's fp)
  returns new_fp: U64.t
  ensures exists* s2. is_heap heap s2 **
    pure ((s2, new_fp) == FS.fused_sweep_coalesce 's fp)
{
  FSI.sweep_start_inv 's fp;
  pow2_facts ();
  let mut cursor = (zero_addr <: U64.t);
  let mut tail = 0UL;
  let mut frag = 0UL;
  let mut head = fp;
  while (U64.lt (U64.add !cursor mword) heap_size_u64)
    invariant exists* c t f h s.
      pts_to cursor c ** pts_to tail t ** pts_to frag f ** pts_to head h **
      is_heap heap s **
      pure (U64.v c <= heap_size /\ U64.v c < pow2 57 /\
            FSI.sweep_inv 's s h (mk_st c t f) /\
            FS.sweep_from s h (mk_st c t f) == FS.fused_sweep_coalesce 's fp)
    decreases (heap_size - U64.v !cursor)
  {
    let c = !cursor;
    let t = !tail;
    let f = !frag;
    let h = !head;
    with s. assert (is_heap heap s);
    step_facts 's s h c t f;
    pow2_facts ();
    let r = sweep_step_impl heap c t f h;
    match r {
      (c', t', f', h') -> {
        cursor := c';
        tail := t';
        frag := f';
        head := h'
      }
    }
  };
  let c = !cursor;
  let t = !tail;
  let f = !frag;
  with s. assert (is_heap heap s);
  stop_facts 's s !head c t f;
  !head
}
#pop-options
