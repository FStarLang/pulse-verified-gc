/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.State - the page allocator's state in memory
/// ---------------------------------------------------------------------------
///
/// The specification's state (`GC.Spec.Pages.Inv.pstate`) is a page map, the
/// heads of the lists of pages with a free slot (one per class), and #46's
/// list heads for the large-object area.  In memory they are three arrays:
///
///   - `pm`, one `pinfo` record per page.  A `pinfo` is the C-friendly form of
///     a `page_info`: the kind is a code (0 free, 1 pool, 2 run head,
///     3 run continuation) with its argument (the class, or the run length)
///     beside it, and the free-slot count is a machine word.  `view` reads a
///     record as a `page_info`; it is total, so a record with a bad code or
///     argument reads as a free page, and the code tests below are exactly
///     the tests `view` makes.
///   - `avail`, `n_cls` words;
///   - `large`, `n_lists` words, of which the allocator uses list 0 only.
///
/// `pages_st t st` ties the arrays to `st`.  The accessors below read and
/// write one entry or head and say what the state becomes.

module GC.Impl.Pages.State

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Impl.Pages.Params

module U8 = FStar.UInt8
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module A = Pulse.Lib.Array
module FLs = GC.Spec.FreeLists
module SC = GC.Spec.SizeClass
module Base = GC.Spec.Base
module IH = GC.Impl.Heap
module R = Pulse.Lib.Reference

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Page-map records
/// ---------------------------------------------------------------------------

type pinfo = {
  code: U8.t;          (* 0 free, 1 pool, 2 run head, 3 run continuation *)
  arg: U64.t;          (* the class of a pool page, the length of a run *)
  swept: bool;
  free_head: U64.t;
  nfree: U64.t;
  next: U64.t;
}

inline_for_extraction
let is_pool (r: pinfo) : bool = r.code = 1uy && U64.lt r.arg n_cls_u64

inline_for_extraction
let is_head (r: pinfo) : bool = r.code = 2uy && U64.gt r.arg 0UL

inline_for_extraction
let is_cont (r: pinfo) : bool = r.code = 3uy

let kind_of (r: pinfo) : page_kind =
  if is_pool r then Pool (U64.v r.arg)
  else if is_head r then LargeHead (U64.v r.arg)
  else if is_cont r then LargeCont
  else Free

let view (r: pinfo) : page_info =
  { kind = kind_of r; swept = r.swept; free_head = r.free_head;
    nfree = U64.v r.nfree; next = r.next }

/// A free page's record.
inline_for_extraction
let free_rec : pinfo =
  { code = 0uy; arg = 0UL; swept = true; free_head = 0UL; nfree = 0UL; next = 0UL }

let free_rec_view () : Lemma (view free_rec == free_entry) = ()

/// The records of a page map.
let pm_rel (s: Seq.seq pinfo) (pm: page_map) : prop =
  Seq.length s == n_pages /\
  (forall (i: nat{i < n_pages}). view (Seq.index s i) == entry pm i)

let pm_rel_upd (s: Seq.seq pinfo) (pm: page_map) (i: nat{i < n_pages}) (r: pinfo)
  : Lemma (requires pm_rel s pm)
          (ensures pm_rel (Seq.upd s i r) (Seq.upd pm i (view r)))
  = ()

/// ---------------------------------------------------------------------------
/// Sizes
/// ---------------------------------------------------------------------------

let page_bytes_bound () : Lemma (page_bytes < pow2 23 /\ page_bytes == page_wsize * 8)
  = cls_bounds 0;
    assert_norm (pow2 20 * 8 == pow2 23)

/// The number of pages, computed.
inline_for_extraction
let n_pages_u64 () : n: U64.t{U64.v n == n_pages} =
  page_bytes_bound ();
  FStar.Math.Lemmas.pow2_lt_compat 64 23;
  U64.div (U64.sub IH.heap_size_u64 IH.zero_addr) (U64.mul page_wsize_u64 8UL)

let n_pages_small () : Lemma (n_pages < pow2 54 /\ n_pages <= Base.heap_size)
  = cls_bounds 0;
    FStar.Math.Lemmas.lemma_div_mod (Base.heap_size - U64.v Base.zero_addr) page_bytes;
    FStar.Math.Lemmas.lemma_mult_le_left n_pages 8 page_bytes;
    assert_norm (pow2 57 == 8 * pow2 54)

/// ---------------------------------------------------------------------------
/// The state
/// ---------------------------------------------------------------------------

noeq type pstate_t = {
  tpm: A.array pinfo;
  tavail: A.array U64.t;
  tlarge: A.array U64.t;
}

let pages_st (t: pstate_t) (st: pstate) : slprop =
  exists* (s: Seq.seq pinfo).
    A.pts_to t.tpm s ** A.pts_to t.tavail st.avail ** A.pts_to t.tlarge st.large **
    pure (pm_rel s st.pm /\ Seq.length st.avail == n_cls /\ Seq.length st.large == SC.n_lists)

/// The facts every caller can rely on.
ghost fn pages_st_lengths (t: pstate_t) (#st: pstate)
  requires pages_st t st
  ensures pages_st t st ** pure (Seq.length st.avail == n_cls /\ Seq.length st.large == SC.n_lists)
{
  unfold pages_st;
  fold (pages_st t st)
}

/// ---------------------------------------------------------------------------
/// Accessors
/// ---------------------------------------------------------------------------

let sz_of (i: U64.t{U64.v i < n_pages}) : s: SZ.t{SZ.v s == U64.v i} =
  n_pages_small ();
  FStar.Math.Lemmas.pow2_lt_compat 64 54;
  SZ.uint64_to_sizet i

fn read_entry (t: pstate_t) (i: U64.t{U64.v i < n_pages}) (#st: erased pstate)
  requires pages_st t st
  returns r: pinfo
  ensures pages_st t st ** pure (view r == entry st.pm (U64.v i))
{
  unfold pages_st;
  with s. assert (A.pts_to t.tpm s);
  let r = t.tpm.(sz_of i);
  fold (pages_st t st);
  r
}

let set_entry (st: pstate) (i: nat{i < n_pages}) (e: page_info) : pstate =
  { st with pm = Seq.upd st.pm i e }

fn write_entry (t: pstate_t) (i: U64.t{U64.v i < n_pages}) (r: pinfo) (#st: erased pstate)
  requires pages_st t st
  ensures pages_st t (set_entry st (U64.v i) (view r))
{
  unfold pages_st;
  with s. assert (A.pts_to t.tpm s);
  t.tpm.(sz_of i) <- r;
  pm_rel_upd s st.pm (U64.v i) r;
  fold (pages_st t (set_entry st (U64.v i) (view r)))
}

let set_avail_at (st: pstate) (c: nat{c < n_cls}) (v: U64.t) : pstate =
  { st with avail = (if c < Seq.length st.avail then Seq.upd st.avail c v else st.avail) }

fn read_avail (t: pstate_t) (c: U64.t{U64.v c < n_cls}) (#st: erased pstate)
  requires pages_st t st
  returns v: U64.t
  ensures pages_st t st ** pure (Seq.length st.avail == n_cls /\ v == Seq.index st.avail (U64.v c))
{
  unfold pages_st;
  let v = t.tavail.(SZ.uint64_to_sizet c);
  fold (pages_st t st);
  v
}

fn write_avail (t: pstate_t) (c: U64.t{U64.v c < n_cls}) (v: U64.t) (#st: erased pstate)
  requires pages_st t st
  ensures pages_st t (set_avail_at st (U64.v c) v)
{
  unfold pages_st;
  t.tavail.(SZ.uint64_to_sizet c) <- v;
  fold (pages_st t (set_avail_at st (U64.v c) v))
}

let set_lhead (st: pstate) (v: U64.t) : pstate =
  { st with large = FLs.fls_set st.large 0 v }

fn read_lhead (t: pstate_t) (#st: erased pstate)
  requires pages_st t st
  returns v: U64.t
  ensures pages_st t st ** pure (v == FLs.fls_head st.large 0)
{
  unfold pages_st;
  let v = t.tlarge.(0sz);
  fold (pages_st t st);
  v
}

fn write_lhead (t: pstate_t) (v: U64.t) (#st: erased pstate)
  requires pages_st t st
  ensures pages_st t (set_lhead st v)
{
  unfold pages_st;
  t.tlarge.(0sz) <- v;
  fold (pages_st t (set_lhead st v))
}

/// Every list head 0: the lists of pages with a free slot and the large
/// lists are empty.
fn clear_lists (t: pstate_t) (#st: erased pstate)
  requires pages_st t st
  ensures pages_st t ({ st with avail = Seq.create n_cls 0UL; large = FLs.fls_empty })
{
  unfold pages_st;
  with s. assert (A.pts_to t.tpm s);
  let mut c = 0UL;
  while (U64.lt !c n_cls_u64)
    invariant exists* vc (av: Seq.seq U64.t).
      R.pts_to c vc ** A.pts_to t.tavail av **
      pure (U64.v vc <= n_cls /\ Seq.length av == n_cls /\
            (forall (i: nat). i < U64.v vc ==> Seq.index av i == 0UL))
    decreases (n_cls - U64.v !c)
  {
    let vc = !c;
    t.tavail.(SZ.uint64_to_sizet vc) <- 0UL;
    c := U64.add vc 1UL
  };
  with av. assert (A.pts_to t.tavail av);
  Seq.lemma_eq_intro av (Seq.create n_cls 0UL);
  SC.n_lists_sz_v ();
  let mut k = 0sz;
  while (SZ.lt !k SC.n_lists_sz)
    invariant exists* vk (lg: Seq.seq U64.t).
      R.pts_to k vk ** A.pts_to t.tlarge lg **
      pure (SZ.v vk <= SC.n_lists /\ Seq.length lg == SC.n_lists /\
            (forall (i: nat). i < SZ.v vk ==> Seq.index lg i == 0UL))
    decreases (SC.n_lists - SZ.v !k)
  {
    let vk = !k;
    t.tlarge.(vk) <- 0UL;
    k := SZ.add vk 1sz
  };
  with lg. assert (A.pts_to t.tlarge lg);
  Seq.lemma_eq_intro lg FLs.fls_empty;
  fold (pages_st t ({ st with avail = Seq.create n_cls 0UL; large = FLs.fls_empty }))
}
