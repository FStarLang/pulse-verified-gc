/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.CPool - sweeping a pool page of a chunk, reading the bitmap
/// ---------------------------------------------------------------------------
///
/// The pool page sweep of the parallel sweep, as the prototype's
/// `sweep_pool` with the bitmap: one pass over the slots in address order,
/// where a slot is live when its header's bit is set.  A live slot is not
/// written at all (its header is white already); a dead slot becomes a free
/// slot, linked to the free slot before it as in
/// `GC.Impl.Pages.SweepPage.sweep_slots`.  At the end, a page that kept a
/// survivor has its bitmap words zeroed; a page given back has none set.
///
/// It computes exactly `SweepPage.sweep_page` of the heap the bitmap stands
/// for (`Bitmap.with_marks`): during the pass, the real heap with the marks
/// of the slots not yet passed is the specification's pass, with its
/// deferred link (`SlotLemmas.pend`), by `BitmapUnits.win_live` and
/// `win_dead`.  `pool_step_c` adds `SweepStep.push_avail` on the chunk's
/// lists, as `SweepPage.pool_step` does on the allocator's.

module GC.Impl.Pages.CPool

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Impl.Pages.Params
open GC.Impl.Pages.State
open GC.Impl.Pages.Heap
open GC.Impl.Pages.CState

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module Base = GC.Spec.Base
module SH = GC.Spec.Heap
module Hd = GC.Lib.Header
module PI = GC.Spec.Pages.PoolInit
module In = GC.Spec.Pages.Init
module SP = GC.Spec.Pages.SweepPage
module SS = GC.Spec.Pages.SweepStep
module SO = GC.Spec.Pages.SweepOrder
module BM = GC.Spec.Pages.Bitmap
module BU = GC.Spec.Pages.BitmapUnits
module PL = GC.Impl.Pages.Pool
module SL = GC.Impl.Pages.SlotLemmas
module ISP = GC.Impl.Pages.SweepPage

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Lemmas
/// ---------------------------------------------------------------------------

/// The last free slot's link is not marked.
let last_unmarked (g0: Base.heap) (bs: Seq.seq U32.t) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k <= n_slots c}) (last: U64.t)
  : Lemma (requires SL.last_ok (BM.with_marks g0 bs) i c k last /\ last <> 0UL /\ BU.pool_marks g0 bs i c)
          (ensures not (BM.marked bs (U64.v last)) /\ U64.v last + 8 <= page_base (i + 1) /\
                   page_base i <= U64.v last /\ U64.v last % 8 == 0 /\ U64.v last < Base.heap_size)
  = SL.last_where (BM.with_marks g0 bs) i c k last;
    eliminate exists (jl: nat). jl < k /\ jl < n_slots c /\ not (SP.live (BM.with_marks g0 bs) i c jl) /\
                   last == (PI.slot_link i c jl <: U64.t) /\
                   SP.nd_from (BM.with_marks g0 bs) i c (jl + 1) == SP.nd_from (BM.with_marks g0 bs) i c k
    with begin
      BU.link_unmarked g0 bs i c jl;
      PI.slot_fits i c jl
    end

/// A page of the chunk lies in the chunk's heap.
let page_in (lo hi: nat) (i: nat)
  : Lemma (requires lo <= i /\ i < hi /\ hi <= n_pages)
          (ensures page_base lo <= page_base i /\ page_base (i + 1) <= page_base hi)
  = page_base_mono lo i;
    page_base_mono (i + 1) hi

/// Words from `x` on are the start's.
let same_from (g0 s: Base.heap) (x: nat) : prop =
  forall (y: Base.hp_addr). U64.v y >= x ==> SH.read_word s y == SH.read_word g0 y

let write_from (g0 s: Base.heap) (x: nat) (a: Base.hp_addr) (v: U64.t) (x': nat)
  : Lemma (requires same_from g0 s x /\ U64.v a < x' /\ x <= x')
          (ensures same_from g0 (SH.write_word s a v) x')
  = let aux (y: Base.hp_addr) : Lemma (U64.v y >= x' ==> SH.read_word (SH.write_word s a v) y == SH.read_word g0 y)
      = BM.rw s a y v
    in
    FStar.Classical.forall_intro aux

let write_out (g0 s: Base.heap) (lo hi: nat) (a: Base.hp_addr) (v: U64.t)
  : Lemma (requires SO.hout g0 s lo hi /\ lo <= U64.v a /\ U64.v a < hi)
          (ensures SO.hout g0 (SH.write_word s a v) lo hi)
  = let aux (y: Base.hp_addr) : Lemma (U64.v y < lo \/ U64.v y >= hi ==> SH.read_word (SH.write_word s a v) y == SH.read_word g0 y)
      = BM.rw s a y v
    in
    FStar.Classical.forall_intro aux

/// The word index of slot `k`'s start, from `zero_addr`.
let slot_widx (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (BM.widx (slot_base i c k) == i * page_wsize + k * cls c)
  = PI.slot_fits i c k;
    assert (slot_base i c k - BM.zw == (i * page_wsize + k * cls c) * 8);
    FStar.Math.Lemmas.cancel_mul_div (i * page_wsize + k * cls c) 8

let page_widx_small (i: nat{i < n_pages})
  : Lemma (i * page_wsize < pow2 57 /\ pow2 57 < pow2 64)
  = page_base_mono i n_pages;
    pages_end_bound ();
    FStar.Math.Lemmas.pow2_lt_compat 64 57;
    assert (i * page_bytes <= Base.heap_size)

let widx_small (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (i * page_wsize + k * cls c < pow2 64 /\ i * page_wsize < pow2 64 /\ k * cls c < pow2 64)
  = PI.slot_fits i c k;
    page_base_mono (i + 1) n_pages;
    pages_end_bound ();
    FStar.Math.Lemmas.pow2_lt_compat 64 57

/// ---------------------------------------------------------------------------
/// The pass over the slots
/// ---------------------------------------------------------------------------

/// The pass's state after slot `k - 1`.
let pass_ok (g0 s: Base.heap) (bs: Seq.seq U32.t) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat)
            (vhd vlast vcnt: U64.t) : prop =
  k <= n_slots c /\
  BM.wm s (BU.win_slot bs i c k) == SL.pend (BM.with_marks g0 bs) i c k vlast /\
  SL.last_ok (BM.with_marks g0 bs) i c k vlast /\
  (vlast == 0UL ==> vhd == 0UL) /\
  (vlast <> 0UL ==> vhd == SP.nd_from (BM.with_marks g0 bs) i c 0) /\
  U64.v vcnt == L.length (SP.dead_list (BM.with_marks g0 bs) i c k) /\
  SO.hout g0 s (page_base i) (page_base (i + 1)) /\
  same_from g0 s (slot_base i c k)

/// One pass over the slots in address order, reading each slot's bit.
/// Kept out of line, as `SweepPage.sweep_slots`.
[@@FStar.Attributes.CPrologue "KRML_NOINLINE"]
fn sweep_slots_b (hp: cheap_t) (bm: A.array U32.t) (i: U64.t{U64.v i < n_pages}) (c: U64.t{U64.v c < n_cls})
  (cl: U64.t{U64.v cl == cls (U64.v c)}) (ns: U64.t{U64.v ns == n_slots (U64.v c)})
  (#lo #hi: erased nat) (#g0: erased Base.heap) (#bs: erased (Seq.seq U32.t))
  requires ch_heap hp lo hi g0 ** ch_bm bm lo hi bs **
           pure (lo <= U64.v i /\ U64.v i < hi /\ BU.pool_marks g0 bs (U64.v i) (U64.v c))
  returns res: (U64.t & U64.t)
  ensures exists* g'. ch_heap hp lo hi g' ** ch_bm bm lo hi bs **
          pure (BM.wm g' (BU.win_slot bs (U64.v i) (U64.v c) (n_slots (U64.v c))) ==
                  SP.sw_heap (BM.with_marks g0 bs) (U64.v i) (U64.v c) (n_slots (U64.v c)) /\
                SO.hout g0 g' (page_base (U64.v i)) (page_base (U64.v i + 1)) /\
                fst res == SP.nd_from (BM.with_marks g0 bs) (U64.v i) (U64.v c) 0 /\
                U64.v (snd res) == L.length (SP.dead_list (BM.with_marks g0 bs) (U64.v i) (U64.v c) (n_slots (U64.v c))))
{
  let w0 = Ghost.hide (BM.with_marks g0 bs);
  unfold ch_heap; fold (ch_heap hp lo hi g0);
  unfold ch_bm; fold (ch_bm bm lo hi bs);
  page_in lo hi (U64.v i);
  cls_bounds (U64.v c);
  let sh = blue_hdr_u64 cl;
  let pb = page_base_u64 i;
  let step = U64.mul cl 8UL;
  page_base_bound (U64.v i);
  page_widx_small (U64.v i);
  let wb = U64.mul i page_wsize_u64;
  SL.pend_start w0 (U64.v i) (U64.v c);
  ISP.dead_zero w0 (U64.v i) (U64.v c);
  BU.win_start g0 bs (U64.v i) (U64.v c);
  let mut k = 0UL;
  let mut hd = 0UL;
  let mut last = 0UL;
  let mut cnt = 0UL;
  while (U64.lt !k ns)
    invariant exists* vk vhd vlast vcnt s.
      R.pts_to k vk ** R.pts_to hd vhd ** R.pts_to last vlast ** R.pts_to cnt vcnt **
      ch_heap hp lo hi s ** ch_bm bm lo hi bs **
      pure (pass_ok g0 s bs (U64.v i) (U64.v c) (U64.v vk) vhd vlast vcnt /\
            U64.v pb == page_base (U64.v i) /\ U64.v step == cls (U64.v c) * 8 /\
            U64.v wb == U64.v i * page_wsize)
    decreases (n_slots (U64.v c) - U64.v !k)
  {
    let vk = !k;
    let vlast = !last;
    with s. assert (ch_heap hp lo hi s);
    PI.slot_fits (U64.v i) (U64.v c) (U64.v vk);
    ISP.dead_step w0 (U64.v i) (U64.v c) (U64.v vk);
    ISP.dead_len w0 (U64.v i) (U64.v c) (U64.v vk);
    BU.live_iff g0 bs (U64.v i) (U64.v c) (U64.v vk);
    slot_base_succ (U64.v i) (U64.v c) (U64.v vk);
    slot_widx (U64.v i) (U64.v c) (U64.v vk);
    widx_small (U64.v i) (U64.v c) (U64.v vk);
    PL.slot_base_bound (U64.v i) (U64.v c) (U64.v vk);
    FStar.Math.Lemmas.pow2_lt_compat 64 57;
    FStar.Math.Lemmas.lemma_mult_le_right (cls (U64.v c) * 8) (U64.v vk) (n_slots (U64.v c));
    FStar.Math.Lemmas.paren_mul_right (U64.v vk) (cls (U64.v c)) 8;
    let a = U64.add pb (U64.mul vk step);
    let ha : Base.hp_addr = a;
    assert (pure (ha == PI.slot_hd (U64.v i) (U64.v c) (U64.v vk)));
    let live = bm_test_w bm (U64.add wb (U64.mul vk cl)) #(U64.v a);
    if live {
      BU.win_live g0 s bs (U64.v i) (U64.v c) (U64.v vk);
      SL.pend_live w0 (U64.v i) (U64.v c) (U64.v vk) vlast;
      k := U64.add vk 1UL
    } else {
      BU.win_dead g0 s bs (U64.v i) (U64.v c) (U64.v vk);
      SL.pend_dead w0 (U64.v i) (U64.v c) (U64.v vk) vlast;
      ch_write hp ha sh;
      BM.wm_write s (BU.win_slot bs (U64.v i) (U64.v c) (U64.v vk + 1)) ha sh;
      write_out g0 s (page_base (U64.v i)) (page_base (U64.v i + 1)) ha sh;
      write_from g0 s (slot_base (U64.v i) (U64.v c) (U64.v vk)) ha sh (slot_base (U64.v i) (U64.v c) (U64.v vk + 1));
      let l = U64.add a 8UL;
      assert (pure (U64.v l == U64.v (PI.slot_link (U64.v i) (U64.v c) (U64.v vk))));
      if (vlast <> 0UL) {
        last_unmarked g0 bs (U64.v i) (U64.v c) (U64.v vk) vlast;
        SL.last_where w0 (U64.v i) (U64.v c) (U64.v vk) vlast;
        let la : Base.hp_addr = vlast;
        let s1 = Ghost.hide (SH.write_word s ha sh);
        ch_write hp la l;
        BM.wm_write s1 (BU.win_slot bs (U64.v i) (U64.v c) (U64.v vk + 1)) la l;
        write_out g0 s1 (page_base (U64.v i)) (page_base (U64.v i + 1)) la l;
        write_from g0 s1 (slot_base (U64.v i) (U64.v c) (U64.v vk + 1)) la l (slot_base (U64.v i) (U64.v c) (U64.v vk + 1));
        last := l;
        FStar.Math.Lemmas.pow2_lt_compat 64 20;
        cnt := U64.add !cnt 1UL;
        k := U64.add vk 1UL
      } else {
        hd := l;
        last := l;
        FStar.Math.Lemmas.pow2_lt_compat 64 20;
        cnt := U64.add !cnt 1UL;
        k := U64.add vk 1UL
      }
    }
  };
  let vk = !k;
  let vlast = !last;
  with s. assert (ch_heap hp lo hi s);
  SL.pend_end w0 (U64.v i) (U64.v c) vlast;
  if (vlast <> 0UL) {
    last_unmarked g0 bs (U64.v i) (U64.v c) (U64.v vk) vlast;
    let la : Base.hp_addr = vlast;
    ch_write hp la 0UL;
    BM.wm_write s (BU.win_slot bs (U64.v i) (U64.v c) (U64.v vk)) la 0UL;
    write_out g0 s (page_base (U64.v i)) (page_base (U64.v i + 1)) la 0UL;
    (!hd, !cnt)
  } else {
    (!hd, !cnt)
  }
}

/// ---------------------------------------------------------------------------
/// The page
/// ---------------------------------------------------------------------------

/// Sweep pool page `i`, whose entry is `r`; return its new entry.  The
/// page's bitmap words are zero after.
fn sweep_page_b (hp: cheap_t) (bm: A.array U32.t) (i: U64.t{U64.v i < n_pages}) (r: pinfo{is_pool r})
  (cl: U64.t{U64.v cl == cls (U64.v r.arg)}) (ns: U64.t{U64.v ns == n_slots (U64.v r.arg)})
  (#pm: erased page_map) (#lo #hi: erased nat) (#g0: erased Base.heap) (#bs: erased (Seq.seq U32.t))
  requires ch_heap hp lo hi g0 ** ch_bm bm lo hi bs **
           pure (view r == entry pm (U64.v i) /\ storable r /\ lo <= U64.v i /\ U64.v i < hi /\
                 BU.pool_marks g0 bs (U64.v i) (U64.v r.arg))
  returns r': pinfo
  ensures exists* g'. ch_heap hp lo hi g' ** ch_bm bm lo hi (BM.zero_page bs (U64.v i)) **
          pure (BM.with_marks g' (BM.zero_page bs (U64.v i)) == fst (SP.sweep_page (BM.with_marks g0 bs) pm (U64.v i)) /\
                view r' == snd (SP.sweep_page (BM.with_marks g0 bs) pm (U64.v i)) /\ storable r' /\
                SO.hout g0 g' (page_base (U64.v i)) (page_base (U64.v i + 1)))
{
  let w0 = Ghost.hide (BM.with_marks g0 bs);
  let c = r.arg;
  ISP.sweep_page_pool w0 pm (U64.v i) (U64.v c);
  let res = sweep_slots_b hp bm i c cl ns;
  with s. assert (ch_heap hp lo hi s);
  SP.dead_count w0 (U64.v i) (U64.v c) (n_slots (U64.v c));
  BU.win_end g0 s bs (U64.v i) (U64.v c);
  if (U64.lt (snd res) ns) {
    bm_zero_page bm i;
    ISP.swept_rec r c (fst res) (snd res)
  } else {
    unfold ch_bm; fold (ch_bm bm lo hi bs);
    assert (pure (not (SP.any_live w0 (U64.v i) (U64.v c) (n_slots (U64.v c)))));
    BU.freed_unmarked g0 bs (U64.v i) (U64.v c);
    assert (pure (BM.zero_page bs (U64.v i) == reveal bs));
    ch_bm_eq bm bs (BM.zero_page bs (U64.v i));
    unfold ch_heap; fold (ch_heap hp lo hi s);
    page_in lo hi (U64.v i);
    page_base_bound (U64.v i);
    page_base_mono (U64.v i) (U64.v i + 1);
    page_base_mono (U64.v i + 1) n_pages;
    let a = page_base_u64 i;
    let pa : Base.hp_addr = a;
    assert (pure (pa == In.page_addr (U64.v i)));
    PI.slot_fits (U64.v i) (U64.v c) 0;
    BM.zero_page_marked bs (U64.v i) (U64.v a);
    let ph = ISP.page_hdr_u64 ();
    ch_write hp pa ph;
    BM.wm_write s (BM.marked (BM.zero_page bs (U64.v i))) pa ph;
    write_out g0 s (page_base (U64.v i)) (page_base (U64.v i + 1)) pa ph;
    free_rec
  }
}

/// ---------------------------------------------------------------------------
/// The pool step of a chunk
/// ---------------------------------------------------------------------------

/// The chunk's lists end inside it, below page `p`.
let ftails (st: pstate) (lo p: nat) : prop =
  Seq.length st.atail == n_cls /\
  (forall (c: nat{c < n_cls}). Seq.index st.atail c <> 0UL ==>
     lo + 1 <= U64.v (Seq.index st.atail c) /\ U64.v (Seq.index st.atail c) <= p)

/// Page `q`'s link set when `b` holds, in the chunk.
fn c_next_if (t: pstate_t) (pt: A.array U64.t) (b: bool) (q: U64.t) (v: U64.t)
  (#k: erased cfix) (#st: erased pstate) (#ol: erased U64.t) (#mf: erased nat)
  requires cst t pt k st ol mf ** pure (b ==> (U64.v q < n_pages /\ k.clo <= U64.v q /\ U64.v q < k.chi))
  ensures exists* st'. cst t pt k st' ol mf **
          pure (st' == (if b && U64.v q < n_pages then set_next_at st (U64.v q) v else reveal st))
{
  if (b && U64.lt q (n_pages_u64 ())) {
    c_write_next t pt q v
  }
}

/// `SweepPage.push_avail` on the chunk's lists.
fn c_push_avail (t: pstate_t) (pt: A.array U64.t) (i: U64.t{U64.v i < n_pages}) (r: pinfo)
  (#k: erased cfix) (#st: erased pstate) (#ol: erased U64.t) (#mf: erased nat)
  requires cst t pt k st ol mf ** pure (storable r /\ in_rng k i /\ ftails st k.clo (U64.v i))
  ensures cst t pt k (SS.push_avail st (U64.v i) (view r)) ol (if is_free_rec r && U64.v i < mf then U64.v i else mf)
{
  cst_lengths t pt;
  if (is_pool r && U64.gt r.nfree 0UL) {
    let c = r.arg;
    let tl = c_read_atail t pt c;
    let id = ISP.page_id_u64 i;
    ISP.push_pool st (U64.v i) r (U64.v c) tl;
    c_write_used t pt i ({ r with next = 0UL });
    if (tl = 0UL) {
      c_write_avail t pt c id;
      c_write_atail t pt c id;
      with st'. assert (cst t pt k st' ol mf);
      rewrite (cst t pt k st' ol mf)
           as (cst t pt k (SS.push_avail st (U64.v i) (view r)) ol (if is_free_rec r && U64.v i < mf then U64.v i else mf))
    } else {
      c_write_atail t pt c id;
      c_next_if t pt (U64.sub_mod tl 1UL <> i) (U64.sub_mod tl 1UL) id;
      with st'. assert (cst t pt k st' ol mf);
      rewrite (cst t pt k st' ol mf)
           as (cst t pt k (SS.push_avail st (U64.v i) (view r)) ol (if is_free_rec r && U64.v i < mf then U64.v i else mf))
    }
  } else {
    ISP.push_plain st (U64.v i) (view r);
    c_write_entry t pt i r;
    with st' mf'. assert (cst t pt k st' ol mf');
    rewrite (cst t pt k st' ol mf')
         as (cst t pt k (SS.push_avail st (U64.v i) (view r)) ol (if is_free_rec r && U64.v i < mf then U64.v i else mf))
  }
}

/// Sweep pool page `i` of the chunk and store the result, as
/// `SweepAll.step` does on the heap the bitmap stands for.
fn pool_step_c (hp: cheap_t) (bm: A.array U32.t) (t: pstate_t) (pt: A.array U64.t)
  (i: U64.t{U64.v i < n_pages}) (r: pinfo{is_pool r})
  (#k: erased cfix) (#st: erased pstate) (#ol: erased U64.t) (#mf: erased nat)
  (#g0: erased Base.heap) (#bs: erased (Seq.seq U32.t))
  requires ch_heap hp k.clo k.chi g0 ** ch_bm bm k.clo k.chi bs ** cst t pt k st ol mf **
           pure (view r == entry st.pm (U64.v i) /\ storable r /\ in_rng k i /\
                 BU.pool_marks g0 bs (U64.v i) (U64.v r.arg) /\ ftails st k.clo (U64.v i))
  ensures exists* g' mf'.
          ch_heap hp k.clo k.chi g' ** ch_bm bm k.clo k.chi (BM.zero_page bs (U64.v i)) **
          cst t pt k (SS.push_avail st (U64.v i) (snd (SP.sweep_page (BM.with_marks g0 bs) st.pm (U64.v i)))) ol mf' **
          pure (BM.with_marks g' (BM.zero_page bs (U64.v i)) == fst (SP.sweep_page (BM.with_marks g0 bs) st.pm (U64.v i)) /\
                SO.hout g0 g' (page_base (U64.v i)) (page_base (U64.v i + 1)) /\ mf' <= mf)
{
  let cl = c_cls_at t pt r.arg;
  let ns = c_ns_at t pt r.arg;
  let r' = sweep_page_b hp bm i r cl ns #st.pm;
  c_push_avail t pt i r';
  rewrite (cst t pt k (SS.push_avail st (U64.v i) (view r')) ol (if is_free_rec r' && U64.v i < mf then U64.v i else mf))
       as (cst t pt k (SS.push_avail st (U64.v i) (snd (SP.sweep_page (BM.with_marks g0 bs) st.pm (U64.v i)))) ol
               (if is_free_rec r' && U64.v i < mf then U64.v i else mf))
}
