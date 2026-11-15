/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.CPar - the parallel sweep: prepare, chunks, finish
/// ---------------------------------------------------------------------------
///
/// The parallel sweep of docs/pages-parallel-gc-design.md §2, in three
/// parts, each extracted to C:
///
///   - `par_prepare` starts the sweep (`Sweep.start_sweep`) and fixes the
///     chunk bounds (`chunk_bounds`): `n` chunks, each starting at
///     `c * n_pages / n` moved forward past run continuation pages;
///   - `sweep_chunk` sweeps chunk `c`.  It owns only the chunk's heap bytes,
///     page records, bitmap words and result record, and reads a share of
///     the word array and the bounds (`GC.Impl.Pages.CSweep.sweep_units`);
///   - `par_finish` sets the free-page hint to the lowest page any chunk
///     left free and joins the chunks' fragments onto the lists, in
///     ascending chunk order (`join_chunk`, `SweepSplit.jstep`).
///
/// `sweep_par_seq` runs the three in one thread, the chunks one after
/// another, and is proved to compute exactly `SweepAll.sweep_all` of the heap
/// the bitmap stands for, from `StartSweep.start_sweep`, with the bitmap all
/// zero after (`SweepChunks.sweep_chunks_eq`).  The trusted C driver
/// (pages-c/pages_par.c) runs the same three parts, the chunks on threads:
/// since each `sweep_chunk` owns only its chunk's memory (and shares of
/// memory no one writes), running them at the same time computes what
/// running them in order computes.

module GC.Impl.Pages.CPar

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsToRange
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Impl.Heap
open GC.Impl.Pages.Params
open GC.Impl.Pages.State
open GC.Impl.Pages.Heap
open GC.Impl.Pages.CState

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module Base = GC.Spec.Base
module SH = GC.Spec.Heap
module FLs = GC.Spec.FreeLists
module SA = GC.Spec.Pages.SweepAll
module SO = GC.Spec.Pages.SweepOrder
module BM = GC.Spec.Pages.Bitmap
module SRg = GC.Spec.Pages.SweepRange
module SSp = GC.Spec.Pages.SweepSplit
module SCh = GC.Spec.Pages.SweepChunks
module CSub = GC.Impl.Pages.CSub
module CSw = GC.Impl.Pages.CSweep

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// What a chunk owns, as ranges of the whole arrays
/// ---------------------------------------------------------------------------

/// The heap's bytes of pages `[lo, hi)`.
noextract
let hsl (g: Base.heap) (lo hi: nat) : Seq.seq U8.t =
  if lo <= hi && hi <= n_pages then begin
    pages_in_heap hi;
    page_base_mono lo hi;
    Seq.slice g (page_base lo) (page_base hi)
  end else Seq.empty

let rng_heap (heap: heap_t) (lo hi: nat) (g: Base.heap) : slprop =
  pts_to_range heap.data (page_base lo) (page_base hi) (hsl g lo hi)

/// The page records of pages `[lo, hi)`.
let rng_pm (t: pstate_t) (lo hi: nat) (ep: U64.t) (pm: page_map) : slprop =
  exists* (s: Seq.seq prec). pts_to_range t.tpm lo hi s ** pure (rng_rel s ep lo hi pm)

/// A chunk's record: its fragments `f`, its open link `ol`, and the lowest
/// page it left free `mf`.
let frag_rel (q: Seq.seq U64.t) (f: pstate) (ol: U64.t) (mf: nat) : prop =
  Seq.length q == pw /\ sl q 0 n_cls == f.avail /\ sl q n_cls n_cls == f.atail /\
  f.large == FLs.fls_set FLs.fls_empty 0 (Seq.index q o_lh) /\
  Seq.index q o_ol == ol /\ U64.v (Seq.index q o_mf) == mf

/// ---------------------------------------------------------------------------
/// One chunk
/// ---------------------------------------------------------------------------

/// The record of a chunk that has swept nothing.
let rec_start (q: Seq.seq U64.t) (j: nat) : prop =
  Seq.length q == pw /\ (forall (k: nat). k < j /\ k < pw ==> Seq.index q k == 0UL)

let record_empty (q: Seq.seq U64.t) (pm: page_map) (hi: nat)
  : Lemma (requires rec_start q (o_mf) /\ U64.v (Seq.index q o_mf) == hi /\ hi <= n_pages)
          (ensures (let st = SCh.zst pm in
                    sl q 0 n_cls == st.avail /\ sl q n_cls n_cls == st.atail /\
                    st.large == FLs.fls_set FLs.fls_empty 0 (Seq.index q o_lh) /\
                    Seq.index q o_ol == 0UL))
  = w_small ();
    Seq.lemma_eq_intro (sl q 0 n_cls) SSp.zcls;
    Seq.lemma_eq_intro (sl q n_cls n_cls) SSp.zcls;
    Seq.lemma_eq_intro (FLs.fls_set FLs.fls_empty 0 0UL) FLs.fls_empty

/// Set the record's lists to empty and its lowest free page to `hi`.
fn init_record (pt: A.array U64.t) (hi: U64.t) (#q0: erased (Seq.seq U64.t))
  requires A.pts_to pt q0 ** pure (Seq.length q0 == pw)
  ensures exists* q. A.pts_to pt q ** pure (rec_start q o_mf /\ Seq.index q o_mf == hi)
{
  w_small ();
  let mut j = 0UL;
  let e = o_mf_u64 ();
  while (U64.lt !j e)
    invariant exists* vj q.
      R.pts_to j vj ** A.pts_to pt q ** pure (U64.v vj <= o_mf /\ rec_start q (U64.v vj))
    decreases (o_mf - U64.v !j)
  {
    let vj = !j;
    pt.(psz vj) <- 0UL;
    j := U64.add vj 1UL
  };
  pt.(psz e) <- hi
}

/// The bounds' entry `c`.
let bnd_u64 (b: Seq.seq U64.t) (c: nat) : Lemma (c < Seq.length b ==> U64.v (Seq.index b c) == SCh.bnd b c) = ()

let pw_small () : Lemma (pw < pow2 24)
  = cls_above (n_cls - 1);
    cls_bounds (n_cls - 1);
    assert_norm (pow2 20 == 1048576);
    assert_norm (pow2 24 == 16777216)

let off_bound (c: nat)
  : Lemma (requires c < 256) (ensures c * pw + pw < pow2 32 /\ pow2 32 < pow2 64)
  = pw_small ();
    FStar.Math.Lemmas.lemma_mult_le_right pw (c + 1) 256;
    assert_norm (256 * pow2 24 == pow2 32);
    assert_norm (pow2 32 < pow2 64)

/// What a chunk needs of the state it starts from.
let chunk_pre (w: Seq.seq U64.t) (g: Base.heap) (bs: Seq.seq U32.t) (pm: page_map) (lo hi: nat) : prop =
  cw_ok w /\ lo <= hi /\ hi <= n_pages /\ map_ok pm /\ SRg.wreach pm lo hi /\
  (lo < hi ==> walk_page pm lo) /\ CSw.marks_from g bs pm lo hi

/// What a chunk leaves.
let chunk_res (g: Base.heap) (bs: Seq.seq U32.t) (pm: page_map) (lo hi: nat)
              (g': Base.heap) (bs': Seq.seq U32.t) (pm': page_map) (q: Seq.seq U64.t) : prop =
  exists (st': pstate) (ol': U64.t) (mf': nat).
    CSw.chunk_post g bs pm lo hi g' bs' st' ol' mf' /\ pm' == st'.pm /\ frag_rel q st' ol' mf' /\
    newfree_ge pm st'.pm lo hi mf' /\ mf' <= n_pages

/// Sweep chunk `c`, whose pages are `[lo, hi)`.
fn sweep_chunk_at (heap: heap_t) (t: pstate_t) (bm: A.array U32.t) (parts: A.array U64.t)
  (lo hi: U64.t) (c: SZ.t)
  (#p: perm) (#w: erased (Seq.seq U64.t))
  (#g: erased Base.heap) (#bs: erased (Seq.seq U32.t)) (#pm: erased page_map) (#q0: erased (Seq.seq U64.t))
  requires A.pts_to t.tw #p w **
           rng_heap heap (U64.v lo) (U64.v hi) g **
           rng_pm t (U64.v lo) (U64.v hi) (ep_of w) pm **
           ch_bm bm (U64.v lo) (U64.v hi) bs **
           pts_to_range parts (SZ.v c * pw) (SZ.v c * pw + pw) q0 **
           pure (SZ.v c < 256 /\
                 chunk_pre w g bs pm (U64.v lo) (U64.v hi))
  ensures exists* g' bs' pm' q.
          A.pts_to t.tw #p w **
          rng_heap heap (U64.v lo) (U64.v hi) g' **
          rng_pm t (U64.v lo) (U64.v hi) (ep_of w) pm' **
          ch_bm bm (U64.v lo) (U64.v hi) bs' **
          pts_to_range parts (SZ.v c * pw) (SZ.v c * pw + pw) q **
          pure (chunk_res g bs pm (U64.v lo) (U64.v hi) g' bs' pm' q)
{
  pw_small ();
  (* the heap's bytes, as an array of their own *)
  unfold rng_heap;
  pages_in_heap (U64.v hi);
  page_base_mono (U64.v lo) (U64.v hi);
  page_base_bound (U64.v lo);
  page_base_bound (U64.v hi);
  let blo = page_base_u64 lo;
  rewrite each (page_base (U64.v lo)) as (SZ.v (SZ.uint64_to_sizet blo));
  let d = CSub.range_sub heap.data (SZ.uint64_to_sizet blo) (page_base (U64.v hi));
  let hp = { cd = d; cb = blo };
  rewrite (A.pts_to d (hsl g (U64.v lo) (U64.v hi))) as (A.pts_to hp.cd (hsl g (U64.v lo) (U64.v hi)));
  fold (ch_heap hp (U64.v lo) (U64.v hi) g);
  (* the record *)
  FStar.Math.Lemmas.pow2_lt_compat 64 32;
  off_bound (SZ.v c);
  let po = SZ.uint64_to_sizet (U64.mul (SZ.sizet_to_uint64 c) (pw_u64 ()));
  assert (pure (SZ.v po == SZ.v c * pw));
  rewrite each (SZ.v c * pw) as (SZ.v po);
  pts_to_range_prop parts #(SZ.v po) #(SZ.v po + pw);
  let pt = CSub.range_sub parts po (SZ.v po + pw);
  init_record pt hi;
  with q1. assert (A.pts_to pt q1);
  record_empty q1 pm (U64.v hi);
  (* the chunk's state *)
  unfold rng_pm;
  with s. assert (pts_to_range t.tpm (U64.v lo) (U64.v hi) s);
  let cf = Ghost.hide ({ clo = U64.v lo; chi = U64.v hi; cp = p; cw = reveal w; cpm0 = reveal pm });
  rewrite (pts_to_range t.tpm (U64.v lo) (U64.v hi) s) as (pts_to_range t.tpm cf.clo cf.chi s);
  rewrite (A.pts_to t.tw #p w) as (A.pts_to t.tw #cf.cp cf.cw);
  fold (cst t pt cf (SCh.zst cf.cpm0) 0UL (U64.v hi));
  rewrite (ch_heap hp (U64.v lo) (U64.v hi) g) as (ch_heap hp cf.clo cf.chi g);
  rewrite (ch_bm bm (U64.v lo) (U64.v hi) bs) as (ch_bm bm cf.clo cf.chi bs);
  CSw.sweep_units hp bm t pt lo hi #cf #g #bs;
  with g' b' st' ol' mf'. assert (ch_heap hp cf.clo cf.chi g' ** ch_bm bm cf.clo cf.chi b' ** cst t pt cf st' ol' mf');
  (* give the memory back *)
  unfold cst;
  with s' q'. assert (pts_to_range t.tpm cf.clo cf.chi s' ** A.pts_to pt q');
  rewrite (A.pts_to t.tw #cf.cp cf.cw) as (A.pts_to t.tw #p w);
  rewrite (pts_to_range t.tpm cf.clo cf.chi s') as (pts_to_range t.tpm (U64.v lo) (U64.v hi) s');
  fold (rng_pm t (U64.v lo) (U64.v hi) (ep_of w) st'.pm);
  CSub.range_unsub parts (SZ.v po) (SZ.v po + pw) pt;
  unfold ch_heap;
  rewrite (A.pts_to hp.cd (Seq.slice g' (page_base cf.clo) (page_base cf.chi)))
       as (A.pts_to d (hsl g' (U64.v lo) (U64.v hi)));
  CSub.range_unsub heap.data (SZ.v (SZ.uint64_to_sizet blo)) (page_base (U64.v hi)) d;
  rewrite each (SZ.v (SZ.uint64_to_sizet blo)) as (page_base (U64.v lo));
  fold (rng_heap heap (U64.v lo) (U64.v hi) g');
  rewrite (ch_bm bm cf.clo cf.chi b') as (ch_bm bm (U64.v lo) (U64.v hi) b');
  CSub.range_idx parts (SZ.v c * pw) (SZ.v c * pw + pw);
  ()
}

/// **Sweep chunk `c`**, whose pages are `[bounds[c], bounds[c + 1])`.
fn sweep_chunk (heap: heap_t) (t: pstate_t) (bm: A.array U32.t) (parts: A.array U64.t)
  (bounds: A.array U64.t) (c: SZ.t)
  (#pb: perm) (#bb: erased (Seq.seq U64.t)) (#p: perm) (#w: erased (Seq.seq U64.t))
  (#g: erased Base.heap) (#bs: erased (Seq.seq U32.t)) (#pm: erased page_map) (#q0: erased (Seq.seq U64.t))
  requires A.pts_to bounds #pb bb ** A.pts_to t.tw #p w **
           rng_heap heap (SCh.bnd bb (SZ.v c)) (SCh.bnd bb (SZ.v c + 1)) g **
           rng_pm t (SCh.bnd bb (SZ.v c)) (SCh.bnd bb (SZ.v c + 1)) (ep_of w) pm **
           ch_bm bm (SCh.bnd bb (SZ.v c)) (SCh.bnd bb (SZ.v c + 1)) bs **
           pts_to_range parts (SZ.v c * pw) (SZ.v c * pw + pw) q0 **
           pure (SZ.v c + 1 < Seq.length bb /\ SZ.v c < 256 /\
                 chunk_pre w g bs pm (SCh.bnd bb (SZ.v c)) (SCh.bnd bb (SZ.v c + 1)))
  ensures exists* g' bs' pm' q.
          A.pts_to bounds #pb bb ** A.pts_to t.tw #p w **
          rng_heap heap (SCh.bnd bb (SZ.v c)) (SCh.bnd bb (SZ.v c + 1)) g' **
          rng_pm t (SCh.bnd bb (SZ.v c)) (SCh.bnd bb (SZ.v c + 1)) (ep_of w) pm' **
          ch_bm bm (SCh.bnd bb (SZ.v c)) (SCh.bnd bb (SZ.v c + 1)) bs' **
          pts_to_range parts (SZ.v c * pw) (SZ.v c * pw + pw) q **
          pure (chunk_res g bs pm (SCh.bnd bb (SZ.v c)) (SCh.bnd bb (SZ.v c + 1)) g' bs' pm' q)
{
  let lo = bounds.(c);
  let hi = bounds.(SZ.add c 1sz);
  bnd_u64 bb (SZ.v c);
  bnd_u64 bb (SZ.v c + 1);
  rewrite each (SCh.bnd bb (SZ.v c)) as (U64.v lo);
  rewrite each (SCh.bnd bb (SZ.v c + 1)) as (U64.v hi);
  sweep_chunk_at heap t bm parts lo hi c;
  with g' bs' pm' q. assert (rng_heap heap (U64.v lo) (U64.v hi) g' ** ch_bm bm (U64.v lo) (U64.v hi) bs' **
                            rng_pm t (U64.v lo) (U64.v hi) (ep_of w) pm' ** pts_to_range parts (SZ.v c * pw) (SZ.v c * pw + pw) q);
  rewrite (rng_heap heap (U64.v lo) (U64.v hi) g') as (rng_heap heap (SCh.bnd bb (SZ.v c)) (SCh.bnd bb (SZ.v c + 1)) g');
  rewrite (ch_bm bm (U64.v lo) (U64.v hi) bs') as (ch_bm bm (SCh.bnd bb (SZ.v c)) (SCh.bnd bb (SZ.v c + 1)) bs');
  rewrite (rng_pm t (U64.v lo) (U64.v hi) (ep_of w) pm') as (rng_pm t (SCh.bnd bb (SZ.v c)) (SCh.bnd bb (SZ.v c + 1)) (ep_of w) pm');
  ()
}

/// ---------------------------------------------------------------------------
/// The chunk bounds
/// ---------------------------------------------------------------------------

/// Bounds `0 .. c - 1` are fixed: from 0, in order, each a walk page.
let bnds_ok (pm: page_map) (b: Seq.seq U64.t) (c: nat) : prop =
  c <= Seq.length b /\
  (c > 0 ==> Seq.index b 0 == 0UL) /\
  (forall (k: nat). k < c ==> U64.v (Seq.index b k) <= n_pages /\ walk_page pm (U64.v (Seq.index b k))) /\
  (forall (k: nat). k + 1 < c ==> U64.v (Seq.index b k) <= U64.v (Seq.index b (k + 1)))

let bnds_upd (pm: page_map) (b: Seq.seq U64.t) (c: nat) (x: U64.t)
  : Lemma (requires bnds_ok pm b c /\ c < Seq.length b /\ U64.v x <= n_pages /\ walk_page pm (U64.v x) /\
                    (c > 0 ==> U64.v (Seq.index b (c - 1)) <= U64.v x) /\ (c == 0 ==> x == 0UL))
          (ensures bnds_ok pm (Seq.upd b c x) (c + 1))
  = ()

/// The chunk bounds: `bounds_ok`, and each chunk that is not empty starts
/// on a walk page.
let bounds_good (pm: page_map) (b: Seq.seq U64.t) (n: nat) : prop =
  Seq.length b == n + 1 /\ SCh.bounds_ok pm b n /\
  (forall (c: nat). c < n ==> SCh.bnd b c <= SCh.bnd b (c + 1) /\ SCh.bnd b (c + 1) <= n_pages /\
                      (SCh.bnd b c < SCh.bnd b (c + 1) ==> walk_page pm (SCh.bnd b c)))

/// Fixed bounds are good.
let bnds_done (pm: page_map) (b: Seq.seq U64.t) (n: nat)
  : Lemma (requires bnds_ok pm b (n + 1) /\ map_ok pm /\ n >= 1 /\ Seq.length b == n + 1 /\
                    U64.v (Seq.index b n) == n_pages)
          (ensures bounds_good pm b n)
  = let aux (c: nat) : Lemma (c < n ==> SRg.wreach pm (SCh.bnd b c) (SCh.bnd b (c + 1)))
      = if c < n then SRg.walk_reach pm (SCh.bnd b c) (SCh.bnd b (c + 1))
    in
    FStar.Classical.forall_intro aux

/// A first page is never a run's continuation.
let walk_zero (pm: page_map)
  : Lemma (requires map_ok pm) (ensures walk_page pm 0)
  = if n_pages > 0 then assert (cont_ok pm 0)

let mul_div_bound (c np nc: nat)
  : Lemma (requires c < nc /\ nc > 0 /\ np < pow2 54 /\ nc <= 256)
          (ensures c * np < pow2 62 /\ (c * np) / nc <= np)
  = FStar.Math.Lemmas.lemma_mult_le_right np c 256;
    assert_norm (256 * pow2 54 == pow2 62);
    FStar.Math.Lemmas.lemma_div_le (c * np) (nc * np) nc;
    FStar.Math.Lemmas.lemma_mult_le_right np c nc;
    FStar.Math.Lemmas.cancel_mul_div np nc

/// **The chunk bounds**: chunk `c` starts at `c * top / n`, where `top` is
/// one past the last page that is not free (the pages above it are never
/// used, as the prototype's high-water mark), or at the previous chunk's
/// start if that is later, moved forward past run continuation pages, so
/// that every run lies in the chunk of its first page.  The last chunk ends
/// at `n_pages`.
fn chunk_bounds (t: pstate_t) (bounds: A.array U64.t) (nc: U64.t) (#st: erased pstate) (#b0: erased (Seq.seq U64.t))
  requires pages_st t st ** A.pts_to bounds b0 **
           pure (Seq.length b0 == U64.v nc + 1 /\ U64.v nc >= 1 /\ U64.v nc <= 256 /\ map_ok st.pm)
  ensures exists* b. pages_st t st ** A.pts_to bounds b ** pure (bounds_good st.pm b (U64.v nc))
{
  let np = n_pages_u64 ();
  n_pages_small ();
  FStar.Math.Lemmas.pow2_lt_compat 64 62;
  walk_zero st.pm;
  (* the pages above `top` are free *)
  let mut top = np;
  let mut scan = true;
  while (!scan)
    invariant exists* vt vs.
      R.pts_to top vt ** R.pts_to scan vs ** pages_st t st ** pure (U64.v vt <= n_pages)
    decreases (U64.v !top + (if !scan then 1 else 0))
  {
    let vt = !top;
    if (vt = 0UL) {
      scan := false
    } else {
      let r = read_entry t (U64.sub vt 1UL);
      if (is_free_rec r) {
        top := U64.sub vt 1UL
      } else {
        scan := false
      }
    }
  };
  let vtop = !top;
  bounds.(0sz) <- 0UL;
  bnds_upd st.pm b0 0 0UL;
  let mut c = 1UL;
  let mut prev = 0UL;
  while (U64.lt !c nc)
    invariant exists* vc vprev b.
      R.pts_to c vc ** R.pts_to prev vprev ** A.pts_to bounds b ** pages_st t st **
      pure (1 <= U64.v vc /\ U64.v vc <= U64.v nc /\ Seq.length b == U64.v nc + 1 /\ U64.v vtop <= n_pages /\
            bnds_ok st.pm b (U64.v vc) /\ vprev == Seq.index b (U64.v vc - 1))
    decreases (U64.v nc - U64.v !c)
  {
    let vc = !c;
    let vprev = !prev;
    mul_div_bound (U64.v vc) (U64.v vtop) (U64.v nc);
    let x0 = U64.div (U64.mul vc vtop) nc;
    let mut x = (if U64.lt x0 vprev then vprev else x0);
    let mut more = true;
    while (!more)
      invariant exists* vx vm.
        R.pts_to x vx ** R.pts_to more vm ** pages_st t st **
        pure (U64.v vprev <= U64.v vx /\ U64.v vx <= n_pages /\
              (not vm ==> walk_page st.pm (U64.v vx)))
      decreases (n_pages - U64.v !x + (if !more then 1 else 0))
    {
      let vx = !x;
      if (U64.lt vx np) {
        let r = read_entry t vx;
        if (is_cont r) {
          x := U64.add vx 1UL
        } else {
          more := false
        }
      } else {
        more := false
      }
    };
    let vx = !x;
    with b. assert (A.pts_to bounds b);
    bnds_upd st.pm b (U64.v vc) vx;
    FStar.Math.Lemmas.pow2_lt_compat 64 9;
    bounds.(SZ.uint64_to_sizet vc) <- vx;
    prev := vx;
    c := U64.add vc 1UL
  };
  with vc0 vp0 b. assert (R.pts_to c vc0 ** R.pts_to prev vp0 ** A.pts_to bounds b);
  let vcf = !c;
  assert (pure (vcf == nc));
  bnds_upd st.pm b (U64.v nc) np;
  bounds.(SZ.uint64_to_sizet nc) <- np;
  with b'. assert (A.pts_to bounds b');
  assert (pure (bnds_ok st.pm b' (U64.v nc + 1)));
  assert (pure (U64.v (Seq.index b' (U64.v nc)) == n_pages /\ Seq.length b' == U64.v nc + 1));
  bnds_done st.pm b' (U64.v nc);
  assert (pure (bounds_good st.pm b' (U64.v nc)))
}
