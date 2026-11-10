/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.Init - the empty heap of pages, in Pulse
/// ---------------------------------------------------------------------------
///
/// `init` computes exactly `GC.Spec.Pages.Init.init_heap` and `init_state`:
/// every page a free page (one blue block, a free page's entry), the heap's
/// tail after the last whole page one blue block when it has room for a
/// header and a field, and every list empty.  `Init.init_pages_ok` proves
/// that this state satisfies `pages_ok`, and `Allocator.init_inv` that it
/// satisfies the allocator's invariant in every phase.

module GC.Impl.Pages.Init

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

module U64 = FStar.UInt64
module Seq = FStar.Seq
module R = Pulse.Lib.Reference
module Base = GC.Spec.Base
module SH = GC.Spec.Heap
module FLs = GC.Spec.FreeLists
module In = GC.Spec.Pages.Init
module LI = GC.Impl.Pages.Large

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

#push-options "--fuel 1"
let free_pages_step (g: Base.heap) (k: nat{k < n_pages})
  : Lemma (In.free_pages g (k + 1) == SH.write_word (In.free_pages g k) (In.page_addr k) In.page_hdr)
  = ()

let free_pages_zero (g: Base.heap) : Lemma (In.free_pages g 0 == g) = ()
#pop-options

let page_hdr_u64 () : r: U64.t{r == In.page_hdr} =
  cls_bounds 0;
  blue_hdr_u64 page_wsize_u64

/// The heap's tail, by cases.
let tail_some (g: Base.heap) (a: Base.hp_addr) (v: U64.t)
  : Lemma (requires Base.heap_size - pages_end >= 16 /\ U64.v a == pages_end /\ v == In.tail_hdr)
          (ensures In.init_heap g == SH.write_word (In.free_pages g n_pages) a v)
  = ()

let tail_none (g: Base.heap)
  : Lemma (requires ~(Base.heap_size - pages_end >= 16))
          (ensures In.init_heap g == In.free_pages g n_pages)
  = ()

let tail_hdr_u64 (tw: U64.t{U64.v tw == In.tail_w}) : r: U64.t{r == In.tail_hdr} =
  if U64.lt tw 0x100000UL && U64.gt tw 0UL then begin
    assert_norm (pow2 20 == 0x100000);
    blue_hdr_u64 tw
  end
  else begin
    assert_norm (pow2 20 == 0x100000);
    0UL
  end

/// Every entry before `k` is a free page's.
let all_free_upto (pm: page_map) (k: nat) : prop =
  forall (i: nat{i < n_pages}). i < k ==> entry pm i == free_entry

let init_state_eq (st: pstate)
  : Lemma (requires all_free_upto st.pm n_pages)
          (ensures ({ st with avail = Seq.create n_cls 0UL; large = FLs.fls_empty }) == In.init_state)
  = Seq.lemma_eq_intro st.pm all_free

fn init (heap: heap_t) (t: pstate_t) (#st: erased pstate)
  requires is_heap heap 'g ** pages_st t st
  ensures exists* g' st'. is_heap heap g' ** pages_st t st' **
          pure (g' == In.init_heap 'g /\ st' == In.init_state)
{
  LI.bounds ();
  cls_bounds 0;
  free_rec_view ();
  free_pages_zero 'g;
  let np = n_pages_u64 ();
  let ph = page_hdr_u64 ();
  let mut k = 0UL;
  while (U64.lt !k np)
    invariant exists* vk g1 st1.
      R.pts_to k vk ** is_heap heap g1 ** pages_st t st1 **
      pure (U64.v vk <= n_pages /\ g1 == In.free_pages 'g (U64.v vk) /\ all_free_upto st1.pm (U64.v vk))
    decreases (n_pages - U64.v !k)
  {
    let vk = !k;
    free_pages_step 'g (U64.v vk);
    page_base_bound (U64.v vk);
    page_base_mono (U64.v vk) (U64.v vk + 1);
    page_base_mono (U64.v vk + 1) n_pages;
    write_word heap (page_base_u64 vk) ph;
    write_entry t vk free_rec;
    k := U64.add vk 1UL
  };
  with st1. assert (pages_st t st1);
  let vk = !k;
  assert (pure (U64.v vk == n_pages));
  clear_lists t;
  init_state_eq st1;
  pages_end_bound ();
  page_base_bound n_pages;
  let pe = page_base_u64 np;
  if (U64.gte (U64.sub heap_size_u64 pe) 16UL) {
    In.tail_bound ();
    let tw = U64.div (U64.sub heap_size_u64 pe) 8UL;
    let v = tail_hdr_u64 tw;
    tail_some 'g pe v;
    write_word heap pe v
  } else {
    tail_none 'g
  }
}
