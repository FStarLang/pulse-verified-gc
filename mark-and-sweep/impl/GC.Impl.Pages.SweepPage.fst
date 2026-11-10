/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.SweepPage - sweeping one pool page, in Pulse
/// ---------------------------------------------------------------------------
///
/// `sweep_page` computes exactly `GC.Spec.Pages.SweepPage.sweep_page`, for
/// every heap:
///   - a first pass looks for a slot whose header is black (`any_live`);
///   - if there is one, a second pass sweeps the slots in order: a black
///     slot's header is made white, any other slot becomes a free slot
///     linked to the free slot before it (`sw_heap`), and the page's entry
///     gets the last free slot as its list head and the number of free slots;
///   - if there is none, the page is given back: one blue header at its
///     start, and a free page's entry.
/// `pool_step` adds what `GC.Spec.Pages.SweepAll.step` does after it: the
/// entry is stored, and a page with a free slot goes first on its class's
/// list (`SweepStep.push_avail`).

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

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The steps of the specification
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let any_live_step (g: Base.heap) (i: nat) (c: nat{c < n_cls}) (k: nat)
  : Lemma (SP.any_live g i c (k + 1) == (SP.live g i c k || SP.any_live g i c k))
  = ()

let any_live_zero (g: Base.heap) (i: nat) (c: nat{c < n_cls}) : Lemma (SP.any_live g i c 0 == false) = ()

let sw_step (g: Base.heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (SP.sw_heap g i c (k + 1) ==
           (if SP.live g i c k
            then SH.write_word (SP.sw_heap g i c k) (PI.slot_hd i c k)
                               (GC.Spec.Object.colorHeader (SH.read_word g (PI.slot_hd i c k)) Hd.White)
            else SH.write_word (SH.write_word (SP.sw_heap g i c k) (PI.slot_hd i c k) (PI.slot_hdr c))
                               (PI.slot_link i c k) (SP.hd_upto g i c k)))
  = ()

let sw_zero (g: Base.heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) : Lemma (SP.sw_heap g i c 0 == g) = ()

let dead_step (g: Base.heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (L.length (SP.dead_list g i c (k + 1)) ==
             (if SP.live g i c k then L.length (SP.dead_list g i c k) else L.length (SP.dead_list g i c k) + 1) /\
           SP.hd_upto g i c (k + 1) ==
             (if SP.live g i c k then SP.hd_upto g i c k else (PI.slot_link i c k <: U64.t)))
  = ()

let dead_zero (g: Base.heap) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (L.length (SP.dead_list g i c 0) == 0 /\ SP.hd_upto g i c 0 == 0UL)
  = ()
#pop-options

#push-options "--fuel 1"
let rec dead_len (g: Base.heap) (i: nat) (c: nat{c < n_cls}) (k: nat)
  : Lemma (ensures L.length (SP.dead_list g i c k) <= k) (decreases k)
  = if k > 0 then dead_len g i c (k - 1)
#pop-options

/// Once a survivor is found, the page has one.
let any_live_found (g: Base.heap) (i: nat) (c: nat{c < n_cls}) (k: nat)
  : Lemma (requires SP.live g i c k /\ k < n_slots c) (ensures SP.any_live g i c (n_slots c))
  = SP.any_live_spec g i c (n_slots c)

/// `live g i c k`, read at the slot start.
let live_at (g: Base.heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (SP.live g i c k == (GC.Spec.Object.getColor (SH.read_word g (PI.slot_hd i c k)) = Hd.Black))
  = PI.slot_fits i c k

/// ---------------------------------------------------------------------------
/// Is a slot live?
/// ---------------------------------------------------------------------------

fn page_any_live (heap: heap_t) (i: U64.t{U64.v i < n_pages}) (c: U64.t{U64.v c < n_cls})
  requires is_heap heap 'g
  returns b: bool
  ensures is_heap heap 'g ** pure (b == SP.any_live 'g (U64.v i) (U64.v c) (n_slots (U64.v c)))
{
  let ns = PL.n_slots_u64 c;
  any_live_zero 'g (U64.v i) (U64.v c);
  let mut k = 0UL;
  let mut found = false;
  while (not !found && U64.lt !k ns)
    invariant exists* vk vf.
      R.pts_to k vk ** R.pts_to found vf ** is_heap heap 'g **
      pure (U64.v vk <= n_slots (U64.v c) /\
            (not vf ==> SP.any_live 'g (U64.v i) (U64.v c) (U64.v vk) == false) /\
            (vf ==> SP.any_live 'g (U64.v i) (U64.v c) (n_slots (U64.v c))))
    decreases (n_slots (U64.v c) - U64.v !k + (if !found then 0 else 1))
  {
    let vk = !k;
    PI.slot_fits (U64.v i) (U64.v c) (U64.v vk);
    live_at 'g (U64.v i) (U64.v c) (U64.v vk);
    any_live_step 'g (U64.v i) (U64.v c) (U64.v vk);
    let h = read_word heap (PL.slot_base_u64 i c vk);
    let col = get_color h;
    if (col = Hd.Black) {
      any_live_found 'g (U64.v i) (U64.v c) (U64.v vk);
      found := true
    } else {
      k := U64.add vk 1UL
    }
  };
  !found
}

/// ---------------------------------------------------------------------------
/// Sweeping the slots
/// ---------------------------------------------------------------------------

fn sweep_slots (heap: heap_t) (i: U64.t{U64.v i < n_pages}) (c: U64.t{U64.v c < n_cls})
  requires is_heap heap 'g
  returns res: (U64.t & U64.t)
  ensures is_heap heap (SP.sw_heap 'g (U64.v i) (U64.v c) (n_slots (U64.v c))) **
          pure (fst res == SP.hd_upto 'g (U64.v i) (U64.v c) (n_slots (U64.v c)) /\
                U64.v (snd res) == L.length (SP.dead_list 'g (U64.v i) (U64.v c) (n_slots (U64.v c))))
{
  let ns = PL.n_slots_u64 c;
  let sh = PL.slot_hdr_u64 c;
  sw_zero 'g (U64.v i) (U64.v c);
  dead_zero 'g (U64.v i) (U64.v c);
  let mut k = 0UL;
  let mut hd = 0UL;
  let mut cnt = 0UL;
  while (U64.lt !k ns)
    invariant exists* vk vhd vcnt s.
      R.pts_to k vk ** R.pts_to hd vhd ** R.pts_to cnt vcnt ** is_heap heap s **
      pure (U64.v vk <= n_slots (U64.v c) /\
            s == SP.sw_heap 'g (U64.v i) (U64.v c) (U64.v vk) /\
            vhd == SP.hd_upto 'g (U64.v i) (U64.v c) (U64.v vk) /\
            U64.v vcnt == L.length (SP.dead_list 'g (U64.v i) (U64.v c) (U64.v vk)))
    decreases (n_slots (U64.v c) - U64.v !k)
  {
    let vk = !k;
    with s. assert (is_heap heap s);
    PI.slot_fits (U64.v i) (U64.v c) (U64.v vk);
    live_at 'g (U64.v i) (U64.v c) (U64.v vk);
    sw_step 'g (U64.v i) (U64.v c) (U64.v vk);
    dead_step 'g (U64.v i) (U64.v c) (U64.v vk);
    dead_len 'g (U64.v i) (U64.v c) (U64.v vk);
    let a = PL.slot_base_u64 i c vk;
    SP.sw_out 'g (U64.v i) (U64.v c) (U64.v vk) a;
    let h = read_word heap a;
    let col = get_color h;
    if (col = Hd.Black) {
      write_word heap a (recolour_hdr h Hd.White);
      k := U64.add vk 1UL
    } else {
      write_word heap a sh;
      write_word heap (U64.add a 8UL) !hd;
      hd := U64.add a 8UL;
      FStar.Math.Lemmas.pow2_lt_compat 64 20;
      cls_bounds (U64.v c);
      cnt := U64.add !cnt 1UL;
      k := U64.add vk 1UL
    }
  };
  let vhd = !hd;
  let vcnt = !cnt;
  with s. assert (is_heap heap s);
  rewrite (is_heap heap s) as (is_heap heap (SP.sw_heap 'g (U64.v i) (U64.v c) (n_slots (U64.v c))));
  (vhd, vcnt)
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
                   (if SP.any_live g i c (n_slots c) then SP.pool_swept g pm i c else SP.page_freed g i))
  = ()

let sweep_page_other (g: Base.heap) (pm: page_map) (i: nat{i < n_pages})
  : Lemma (requires ~(Pool? (entry pm i).kind)) (ensures SP.sweep_page g pm i == (g, entry pm i))
  = ()

/// Sweep pool page `i`, whose entry is `r`; return its new entry.
fn sweep_page (heap: heap_t) (i: U64.t{U64.v i < n_pages}) (r: pinfo) (#pm: erased page_map)
  requires is_heap heap 'g ** pure (view r == entry pm (U64.v i))
  returns r': pinfo
  ensures exists* g'. is_heap heap g' **
          pure (g' == fst (SP.sweep_page 'g pm (U64.v i)) /\ view r' == snd (SP.sweep_page 'g pm (U64.v i)))
{
  if (is_pool r) {
    let c = r.arg;
    sweep_page_pool 'g pm (U64.v i) (U64.v c);
    let b = page_any_live heap i c;
    if b {
      let res = sweep_slots heap i c;
      dead_len 'g (U64.v i) (U64.v c) (n_slots (U64.v c));
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

let push_pool (st: pstate) (i: nat{i < n_pages}) (e: page_info) (c: nat{c < n_cls})
  : Lemma (requires e.kind == Pool c /\ e.nfree > 0 /\ Seq.length st.avail == n_cls)
          (ensures SS.push_avail st i e ==
                   set_avail_at (set_entry st i ({ e with next = Seq.index st.avail c })) c (SS.page_id i))
  = ()

let push_plain (st: pstate) (i: nat{i < n_pages}) (e: page_info)
  : Lemma (requires ~(Pool? e.kind /\ e.nfree > 0) /\ Seq.length st.avail == n_cls)
          (ensures SS.push_avail st i e == set_entry st i e)
  = ()

/// Store the entry `r` of page `i`, and put it on its class's list if it is
/// a pool page with a free slot.
fn push_avail (t: pstate_t) (i: U64.t{U64.v i < n_pages}) (r: pinfo) (#st: erased pstate)
  requires pages_st t st
  ensures pages_st t (SS.push_avail st (U64.v i) (view r))
{
  pages_st_lengths t;
  if (is_pool r && U64.gt r.nfree 0UL) {
    let c = r.arg;
    let nx = read_avail t c;
    push_pool st (U64.v i) (view r) (U64.v c);
    write_entry t i ({ r with next = nx });
    write_avail t c (page_id_u64 i);
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
fn pool_step (heap: heap_t) (t: pstate_t) (i: U64.t{U64.v i < n_pages}) (r: pinfo) (#st: erased pstate)
  requires is_heap heap 'g ** pages_st t st ** pure (view r == entry st.pm (U64.v i))
  ensures exists* g' st'. is_heap heap g' ** pages_st t st' **
          pure (g' == fst (SP.sweep_page 'g st.pm (U64.v i)) /\
                st' == SS.push_avail st (U64.v i) (snd (SP.sweep_page 'g st.pm (U64.v i))))
{
  let r' = sweep_page heap i r #st.pm;
  push_avail t i r'
}
