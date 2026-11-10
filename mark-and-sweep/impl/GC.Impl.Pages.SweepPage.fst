/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.SweepPage - sweeping one pool page, in Pulse
/// ---------------------------------------------------------------------------
///
/// `sweep_page` computes exactly `GC.Spec.Pages.SweepPage.sweep_page`, for
/// every heap, in one pass over the slots, as OCaml 5's `pool_sweep` and the
/// prototype's `sweep_pool`:
///   - the pass sweeps the slots in order: a black slot's header is made
///     white, any other slot becomes a free slot linked to the free slot
///     before it (`sw_heap`), and it counts the free slots;
///   - if fewer slots than all are free, the page had a survivor
///     (`SP.dead_count`): its entry gets the last free slot as its list
///     head and the number of free slots;
///   - if all are, the page is given back: one blue header at its start,
///     over the swept slots, and a free page's entry.
/// `pool_step` adds what `GC.Spec.Pages.SweepAll.step` does after it: the
/// entry is stored, and a page with a free slot goes at the end of its
/// class's list, so each list stays in address order (`SweepStep.push_avail`).

module GC.Impl.Pages.SweepPage

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Impl.Heap
open GC.Impl.Pages.Params
open GC.Impl.Pages.State
open GC.Impl.Pages.Heap

module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module R = Pulse.Lib.Reference
module Base = GC.Spec.Base
module SH = GC.Spec.Heap
module Hd = GC.Lib.Header
module Sh = GC.Spec.Pages.Shape
module In = GC.Spec.Pages.Init
module PI = GC.Spec.Pages.PoolInit
module SP = GC.Spec.Pages.SweepPage
module SS = GC.Spec.Pages.SweepStep
module PL = GC.Impl.Pages.Pool
module SL = GC.Impl.Pages.SlotLemmas

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The steps of the specification
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let dead_step (g: Base.heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (L.length (SP.dead_list g i c (k + 1)) ==
             (if SP.live g i c k then L.length (SP.dead_list g i c k) else L.length (SP.dead_list g i c k) + 1))
  = ()

let dead_zero (g: Base.heap) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (L.length (SP.dead_list g i c 0) == 0)
  = ()
#pop-options

#push-options "--fuel 1"
let rec dead_len (g: Base.heap) (i: nat) (c: nat{c < n_cls}) (k: nat)
  : Lemma (ensures L.length (SP.dead_list g i c k) <= k) (decreases k)
  = if k > 0 then dead_len g i c (k - 1)
#pop-options

/// `live g i c k`, read at the slot start.
let live_at (g: Base.heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (SP.live g i c k == (GC.Spec.Object.getColor (SH.read_word g (PI.slot_hd i c k)) = Hd.Black))
  = PI.slot_fits i c k

/// ---------------------------------------------------------------------------
/// Sweeping the slots
/// ---------------------------------------------------------------------------

/// Link the last free slot so far, if any, to the slot just freed.
fn link_last (heap: heap_t) (last: U64.t) (l: U64.t)
  requires is_heap heap 's ** pure (last <> 0UL ==> U64.v last < Base.heap_size /\ U64.v last % 8 == 0)
  ensures exists* s'. is_heap heap s' **
          pure (s' == (if last = 0UL || not (U64.v last < Base.heap_size && U64.v last % 8 = 0)
                       then reveal 's else SH.write_word 's last l))
{
  if (last <> 0UL) {
    write_word heap last l
  }
}

/// One pass over the slots in address order.  A freed slot's link is
/// written when the next free slot is found, and the last one's (0) at the
/// end (`SlotLemmas`), so the list runs up the page.
///
/// Kept out of line in C (`KRML_NOINLINE`, through `CPrologue`; Custard does
/// not translate `CNoInline`).  Inlined into the whole sweep, the slot loop
/// runs out of registers and reloads the heap's base address at every slot,
/// which made the sweep with half the slots live about 10% slower than the
/// prototype (measured, `pages-c/bench`).
[@@FStar.Attributes.CPrologue "KRML_NOINLINE"]
fn sweep_slots (heap: heap_t) (i: U64.t{U64.v i < n_pages}) (c: U64.t{U64.v c < n_cls})
  (cl: U64.t{U64.v cl == cls (U64.v c)}) (ns: U64.t{U64.v ns == n_slots (U64.v c)})
  requires is_heap heap 'g
  returns res: (U64.t & U64.t)
  ensures is_heap heap (SP.sw_heap 'g (U64.v i) (U64.v c) (n_slots (U64.v c))) **
          pure (fst res == SP.nd_from 'g (U64.v i) (U64.v c) 0 /\
                U64.v (snd res) == L.length (SP.dead_list 'g (U64.v i) (U64.v c) (n_slots (U64.v c))))
{
  cls_bounds (U64.v c);
  let sh = blue_hdr_u64 cl;
  SL.pend_start 'g (U64.v i) (U64.v c);
  dead_zero 'g (U64.v i) (U64.v c);
  let mut k = 0UL;
  let mut hd = 0UL;
  let mut last = 0UL;
  let mut cnt = 0UL;
  while (U64.lt !k ns)
    invariant exists* vk vhd vlast vcnt s.
      R.pts_to k vk ** R.pts_to hd vhd ** R.pts_to last vlast ** R.pts_to cnt vcnt **
      is_heap heap s **
      pure (U64.v vk <= n_slots (U64.v c) /\ s == SL.pend 'g (U64.v i) (U64.v c) (U64.v vk) vlast /\
            SL.last_ok 'g (U64.v i) (U64.v c) (U64.v vk) vlast /\
            (vlast == 0UL ==> vhd == 0UL) /\
            (vlast <> 0UL ==> vhd == SP.nd_from 'g (U64.v i) (U64.v c) 0) /\
            U64.v vcnt == L.length (SP.dead_list 'g (U64.v i) (U64.v c) (U64.v vk)))
    decreases (n_slots (U64.v c) - U64.v !k)
  {
    let vk = !k;
    let vlast = !last;
    with s. assert (is_heap heap s);
    PI.slot_fits (U64.v i) (U64.v c) (U64.v vk);
    live_at 'g (U64.v i) (U64.v c) (U64.v vk);
    dead_step 'g (U64.v i) (U64.v c) (U64.v vk);
    dead_len 'g (U64.v i) (U64.v c) (U64.v vk);
    SL.pend_hd 'g (U64.v i) (U64.v c) (U64.v vk) vlast;
    let a = PL.slot_base_cl i (U64.v c) cl vk;
    let h = read_word heap a;
    let col = get_color h;
    if (col = Hd.Black) {
      SL.pend_live 'g (U64.v i) (U64.v c) (U64.v vk) vlast;
      write_word heap a (recolour_hdr h Hd.White);
      k := U64.add vk 1UL
    } else {
      SL.pend_dead 'g (U64.v i) (U64.v c) (U64.v vk) vlast;
      write_word heap a sh;
      let l = U64.add a 8UL;
      PI.slot_fits (U64.v i) (U64.v c) (U64.v vk);
      assert (pure (U64.v l == U64.v (PI.slot_link (U64.v i) (U64.v c) (U64.v vk))));
      if (vlast <> 0UL) { SL.last_where 'g (U64.v i) (U64.v c) (U64.v vk) vlast; () } else { () };
      link_last heap vlast l;
      if (vlast = 0UL) { hd := l };
      last := l;
      FStar.Math.Lemmas.pow2_lt_compat 64 20;
      cnt := U64.add !cnt 1UL;
      k := U64.add vk 1UL
    }
  };
  let vk = !k;
  let vlast = !last;
  with s. assert (is_heap heap s);
  SL.pend_end 'g (U64.v i) (U64.v c) vlast;
  if (vlast <> 0UL) {
    SL.last_where 'g (U64.v i) (U64.v c) (U64.v vk) vlast;
    write_word heap vlast 0UL;
    with s'. assert (is_heap heap s');
    rewrite (is_heap heap s') as (is_heap heap (SP.sw_heap 'g (U64.v i) (U64.v c) (n_slots (U64.v c))));
    (!hd, !cnt)
  } else {
    rewrite (is_heap heap s)
         as (is_heap heap (SP.sw_heap 'g (U64.v i) (U64.v c) (n_slots (U64.v c))));
    (!hd, !cnt)
  }
}

/// ---------------------------------------------------------------------------
/// The page
/// ---------------------------------------------------------------------------

/// The entry of a swept pool page that keeps a survivor.
let swept_rec (r: pinfo) (c: U64.t{U64.v c < n_cls}) (hd cnt: U64.t) : pinfo =
  { code = 1uy; arg = c; swept = true; free_head = hd; nfree = cnt; next = r.next }

let page_hdr_u64 () : r: U64.t{r == In.page_hdr} =
  cls_bounds 0;
  blue_hdr_u64 page_wsize_u64

let sweep_page_pool (g: Base.heap) (pm: page_map) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires (entry pm i).kind == Pool c)
          (ensures SP.sweep_page g pm i ==
                   (if SP.any_live g i c (n_slots c) then SP.pool_swept g pm i c else SP.page_freed g i c))
  = ()

let sweep_page_other (g: Base.heap) (pm: page_map) (i: nat{i < n_pages})
  : Lemma (requires ~(Pool? (entry pm i).kind)) (ensures SP.sweep_page g pm i == (g, entry pm i))
  = ()

/// Sweep pool page `i`, whose entry is `r`, with its class's slot size `cl`
/// and slot count `ns`; return its new entry.
fn sweep_page (heap: heap_t) (i: U64.t{U64.v i < n_pages}) (r: pinfo{is_pool r})
  (cl: U64.t{U64.v cl == cls (U64.v r.arg)}) (ns: U64.t{U64.v ns == n_slots (U64.v r.arg)})
  (#pm: erased page_map)
  requires is_heap heap 'g ** pure (view r == entry pm (U64.v i) /\ storable r)
  returns r': pinfo
  ensures exists* g'. is_heap heap g' **
          pure (g' == fst (SP.sweep_page 'g pm (U64.v i)) /\ view r' == snd (SP.sweep_page 'g pm (U64.v i)) /\
                storable r')
{
  if (is_pool r) {
    let c = r.arg;
    sweep_page_pool 'g pm (U64.v i) (U64.v c);
    let res = sweep_slots heap i c cl ns;
    SP.dead_count 'g (U64.v i) (U64.v c) (n_slots (U64.v c));
    if (U64.lt (snd res) ns) {
      swept_rec r c (fst res) (snd res)
    } else {
      let a = page_base_u64 i;
      page_base_bound (U64.v i);
      page_base_mono (U64.v i) (U64.v i + 1);
      page_base_mono (U64.v i + 1) n_pages;
      let ph = page_hdr_u64 ();
      write_word heap a ph;
      free_rec
    }
  } else {
    sweep_page_other 'g pm (U64.v i);
    r
  }
}

/// ---------------------------------------------------------------------------
/// The pool step of the whole sweep
/// ---------------------------------------------------------------------------

let page_id_u64 (i: U64.t{U64.v i < n_pages}) : r: U64.t{r == SS.page_id (U64.v i)}
  = n_pages_small ();
    FStar.Math.Lemmas.pow2_lt_compat 64 54;
    U64.add i 1UL

/// The list head set when `b` holds.
fn avail_if (t: pstate_t) (b: bool) (c: U64.t{U64.v c < n_cls}) (v: U64.t) (#st: erased pstate)
  requires pages_st t st
  ensures pages_st t (if b then set_avail_at st (U64.v c) v else reveal st)
{
  if b {
    write_avail t c v
  }
}

/// Page `q`'s link set when `b` holds.
fn next_if (t: pstate_t) (b: bool) (q: U64.t) (v: U64.t) (#st: erased pstate)
  requires pages_st t st
  ensures exists* st'. pages_st t st' **
          pure (st' == (if b && U64.v q < n_pages then set_next_at st (U64.v q) v else reveal st))
{
  if (b && U64.lt q (n_pages_u64 ())) {
    write_next t q v
  }
}

/// The append, step by step, is `SweepStep.push_avail`.
let push_pool (st: pstate) (i: nat{i < n_pages}) (r: pinfo) (c: nat{c < n_cls}) (tl: U64.t)
  : Lemma (requires (view r).kind == Pool c /\ (view r).nfree > 0 /\
                    Seq.length st.avail == n_cls /\ Seq.length st.atail == n_cls /\
                    tl == Seq.index st.atail c)
          (ensures (let id = SS.page_id i in
                    let st1 = set_entry st i ({ view r with next = 0UL }) in
                    let st2 = if tl = 0UL then set_avail_at st1 c id else st1 in
                    let st3 = set_atail_at st2 c id in
                    let b = tl <> 0UL && U64.v tl - 1 <> i in
                    let q = U64.sub_mod tl 1UL in
                    (if b && U64.v q < n_pages then set_next_at st3 (U64.v q) id else st3) ==
                    SS.push_avail st i (view r)))
  = ()

let push_plain (st: pstate) (i: nat{i < n_pages}) (e: page_info)
  : Lemma (requires ~(Pool? e.kind /\ e.nfree > 0) /\ Seq.length st.avail == n_cls /\ Seq.length st.atail == n_cls)
          (ensures SS.push_avail st i e == set_entry st i e)
  = ()

/// Store the entry `r` of page `i`, and put it at the end of its class's
/// list if it is a pool page with a free slot.
fn push_avail (t: pstate_t) (i: U64.t{U64.v i < n_pages}) (r: pinfo) (#st: erased pstate)
  requires pages_st t st ** pure (storable r)
  ensures pages_st t (SS.push_avail st (U64.v i) (view r))
{
  pages_st_lengths t;
  if (is_pool r && U64.gt r.nfree 0UL) {
    let c = r.arg;
    let tl = read_atail t c;
    let id = page_id_u64 i;
    push_pool st (U64.v i) r (U64.v c) tl;
    write_used t i ({ r with next = 0UL });
    avail_if t (tl = 0UL) c id;
    write_atail t c id;
    next_if t (tl <> 0UL && U64.sub_mod tl 1UL <> i) (U64.sub_mod tl 1UL) id;
    with st'. assert (pages_st t st');
    rewrite (pages_st t st') as (pages_st t (SS.push_avail st (U64.v i) (view r)))
  } else {
    push_plain st (U64.v i) (view r);
    write_entry t i r;
    with st'. assert (pages_st t st');
    rewrite (pages_st t st') as (pages_st t (SS.push_avail st (U64.v i) (view r)))
  }
}

/// Sweep pool page `i` and store the result, as `SweepAll.step` does.
fn pool_step (heap: heap_t) (t: pstate_t) (i: U64.t{U64.v i < n_pages}) (r: pinfo{is_pool r}) (#st: erased pstate)
  requires is_heap heap 'g ** pages_st t st ** pure (view r == entry st.pm (U64.v i) /\ storable r)
  ensures exists* g' st'. is_heap heap g' ** pages_st t st' **
          pure (g' == fst (SP.sweep_page 'g st.pm (U64.v i)) /\
                st' == SS.push_avail st (U64.v i) (snd (SP.sweep_page 'g st.pm (U64.v i))))
{
  let cl = cls_at t r.arg;
  let ns = ns_at t r.arg;
  let r' = sweep_page heap i r cl ns #st.pm;
  push_avail t i r'
}
