/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.SweepRun - sweeping one large run, in Pulse
/// ---------------------------------------------------------------------------
///
/// `run_step` computes exactly what `GC.Spec.Pages.SweepAll.step` does for
/// a run: `GC.Spec.Pages.SweepRun.sweep_run` on the run, then the new list
/// head stored (`SweepStep.run_state`).  It works in two passes:
///
///   1. One pass over the run lays out `fin` (`GC.Impl.Pages.RunLemmas`):
///      a black block gets a white header; a stretch of blocks that are not
///      black becomes one free block, or, when it holds whole pages, the
///      piece before them, the pages (each given back as a free page in the
///      map) and the piece after them.  A free block of at least `lg_min`
///      words is listed: its link is written when the next listed block is
///      found, and the last one is linked to the old list head at the end.
///   2. One pass over the run's pages gives the pages that are not free
///      their entries: each stretch of them becomes a swept run
///      (`GC.Impl.Pages.RunMapLemmas`).
///
/// `run_inv` is the first pass's state: the heap and the map hold the
/// blocks `xs` laid out so far, which end at `a`.

module GC.Impl.Pages.SweepRun

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Spec.Pages.Blk
open GC.Spec.Pages.RunList
open GC.Impl.Heap
open GC.Impl.Pages.Params
open GC.Impl.Pages.State
open GC.Impl.Pages.Heap

module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module Base = GC.Spec.Base
module SH = GC.Spec.Heap
module SO = GC.Spec.Object
module Hd = GC.Lib.Header
module Sh = GC.Spec.Pages.Shape
module B = GC.Spec.Pages.Blocks
module SR = GC.Spec.Pages.SweepRun
module SS = GC.Spec.Pages.SweepStep
module RM = GC.Spec.Pages.RunMap
module Ce = GC.Spec.Pages.Cells
module FLs = GC.Spec.FreeLists
module RL = GC.Impl.Pages.RunLemmas
module RML = GC.Impl.Pages.RunMapLemmas
module LI = GC.Impl.Pages.Large
module IH = GC.Impl.Heap
module PL = GC.Impl.Pages.Pool

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Lemmas
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let dead_end_step (g: Base.heap) (a e: nat)
  : Lemma (requires RL.fits g a e /\ Sh.color_at g a <> Hd.Black)
          (ensures RL.dead_end g a e == RL.dead_end g (a + Sh.words_at g a * 8) e)
  = ()

let dead_end_stop (g: Base.heap) (a e: nat)
  : Lemma (requires ~(RL.fits g a e /\ Sh.color_at g a <> Hd.Black))
          (ensures RL.dead_end g a e == a)
  = ()
#pop-options

#push-options "--fuel 2"
let rec pages_snoc (p j: nat)
  : Lemma (requires p <= j)
          (ensures pages p (j + 1) == L.append (pages p j) [page_blk j])
          (decreases (j - p))
  = if p = j then () else pages_snoc (p + 1) j
#pop-options

#push-options "--fuel 1"
let append_nil_r (l: list blk) : Lemma (L.append l [] == l) = L.append_l_nil l
let append_nil_l (l: list blk) : Lemma (L.append [] l == l) = ()
#pop-options

let sweep_run_unfold (g: Base.heap) (pm: page_map) (h: nat{h < n_pages}) (n: pos) (fp: U64.t)
  : Lemma (requires (entry pm h).kind == LargeHead n)
          (ensures (let fs = fin g (page_base h) (page_base (h + n)) in
                    SR.sweep_run g pm h fp == (SR.wr_all g fs fp, RM.new_map pm fs h n, SR.lhead fs fp)))
  = ()

/// The header and the size the pass reads at `a`.
let words_hdr (g: Base.heap) (a: nat) (hd: U64.t)
  : Lemma (requires hd == Sh.hdr g a)
          (ensures Sh.words_at g a == U64.v (SO.getWosize hd) + 1 /\ Sh.color_at g a == SO.getColor hd)
  = ()

/// A blue header for a free block or page of `w` words.
let hval_free (g: Base.heap) (b: blk)
  : Lemma (requires b.t <> Live /\ b.w <= pow2 54) (ensures SR.hval g b == B.bhdr b.w)
  = ()

let hval_live (g: Base.heap) (b: blk)
  : Lemma (requires b.t == Live) (ensures SR.hval g b == SO.colorHeader (Sh.hdr g b.at) Hd.White)
  = ()

/// ---------------------------------------------------------------------------
/// The first pass's state
/// ---------------------------------------------------------------------------

let mkb (at: nat) (w: pos) (tg: tag) : blk = { at = at; w = w; t = tg }

/// The free block of a stretch `[r, d)`.
let stretch (r d: nat) : blk = { at = r; w = (if r + 8 <= d then (d - r) / 8 else 1); t = Dead }

let run_inv (heap: heap_t) (t: pstate_t) (first pend: R.ref U64.t)
            (g0: Base.heap) (st0: pstate) (s: nat) (xs: list blk) (a: nat) : slprop =
  exists* (g: Base.heap) (st: pstate) (vf vp: U64.t).
    is_heap heap g ** pages_st t st ** R.pts_to first vf ** R.pts_to pend vp **
    pure (RL.emit_ok g0 g xs s a vf vp /\ RML.map_in st0 st xs)

/// Read a word at or after `a`: it is as the pass found it.
fn read_ahead (heap: heap_t) (t: pstate_t) (first pend: R.ref U64.t) (x: U64.t)
  (#g0: erased Base.heap) (#st0: erased pstate) (#s: erased nat) (#xs: erased (list blk)) (#a: erased nat)
  requires run_inv heap t first pend g0 st0 s xs a **
           pure (U64.v x >= a /\ U64.v x < Base.heap_size /\ U64.v x % 8 == 0)
  returns v: U64.t
  ensures run_inv heap t first pend g0 st0 s xs a ** pure (v == Sh.hdr g0 (U64.v x))
{
  unfold run_inv;
  with g st vf vp. assert (is_heap heap g ** pages_st t st ** R.pts_to first vf ** R.pts_to pend vp);
  RL.hdr_past g0 g xs s a vf vp (U64.v x);
  let v = read_word heap x;
  fold (run_inv heap t first pend g0 st0 s xs a);
  v
}

/// Lay out one block `b` at `a`: its header, its link if it is listed, and
/// a free page's entry if it is a page.
fn emit (heap: heap_t) (t: pstate_t) (first pend: R.ref U64.t)
  (at: U64.t) (w: U64.t{U64.v w > 0}) (tg: tag) (hv: U64.t) (j: U64.t)
  (#g0: erased Base.heap) (#st0: erased pstate) (#s: erased nat) (#xs: erased (list blk)) (#a: erased nat)
  requires run_inv heap t first pend g0 st0 s xs a **
           pure (a == U64.v at /\ hv == SR.hval g0 (mkb (U64.v at) (U64.v w) tg) /\
                 U64.v at < Base.heap_size /\
                 (tg == Page ==> mkb (U64.v at) (U64.v w) tg == page_blk (U64.v j) /\ U64.v j < n_pages))
  ensures exists* (xs': list blk) (a': nat).
          run_inv heap t first pend g0 st0 s xs' a' **
          pure (xs' == L.append xs [mkb (U64.v at) (U64.v w) tg] /\ a' == bend (mkb (U64.v at) (U64.v w) tg))
{
  unfold run_inv;
  with g st vf vp. assert (is_heap heap g ** pages_st t st ** R.pts_to first vf ** R.pts_to pend vp);
  LI.bounds ();
  let b = Ghost.hide (mkb (U64.v at) (U64.v w) tg);
  let lmin = LI.lg_min_u64 ();
  let lst = (tg = Dead && U64.gte w lmin && U64.rem at 8UL = 0UL && U64.lt (U64.add at 8UL) heap_size_u64);
  if lst {
    let o = U64.add at 8UL;
    RL.emit_listed g0 g xs s (U64.v at) vf vp b;
    RML.map_in_plain st0 st xs b;
    let vp' = !pend;
    if (vp' <> 0UL) {
      wr heap at hv;
      wr heap vp' o;
      pend := o;
      fold (run_inv heap t first pend g0 st0 s (L.append xs [mkb (U64.v at) (U64.v w) tg])
                    (bend (mkb (U64.v at) (U64.v w) tg)))
    } else {
      wr heap at hv;
      first := o;
      pend := o;
      fold (run_inv heap t first pend g0 st0 s (L.append xs [mkb (U64.v at) (U64.v w) tg])
                    (bend (mkb (U64.v at) (U64.v w) tg)))
    }
  } else {
    RL.emit_plain g0 g xs s (U64.v at) vf vp b;
    wr heap at hv;
    if (tg = Page) {
      RML.map_in_page st0 st xs (U64.v j);
      free_rec_view ();
      write_entry t j free_rec;
      fold (run_inv heap t first pend g0 st0 s (L.append xs [mkb (U64.v at) (U64.v w) tg])
                    (bend (mkb (U64.v at) (U64.v w) tg)))
    } else {
      RML.map_in_plain st0 st xs b;
      fold (run_inv heap t first pend g0 st0 s (L.append xs [mkb (U64.v at) (U64.v w) tg])
                    (bend (mkb (U64.v at) (U64.v w) tg)))
    }
  }
}

/// ---------------------------------------------------------------------------
/// Laying out a stretch that is not black
/// ---------------------------------------------------------------------------

let z_u64 () : r: U64.t{U64.v r == z} = IH.zero_addr

let pg_ceil_u64 (x: U64.t{U64.v x <= Base.heap_size}) : r: U64.t{U64.v r == pg_ceil (U64.v x)}
  = LI.bounds ();
    cls_bounds 0;
    if U64.lte x (z_u64 ()) then 0UL
    else U64.div (U64.sub (U64.add (U64.sub x (z_u64 ())) (U64.mul page_wsize_u64 8UL)) 1UL)
                 (U64.mul page_wsize_u64 8UL)

let pg_floor_u64 (x: U64.t{U64.v x <= Base.heap_size}) : r: U64.t{U64.v r == pg_floor (U64.v x)}
  = LI.bounds ();
    cls_bounds 0;
    if U64.lte x (z_u64 ()) then 0UL
    else U64.div (U64.sub x (z_u64 ())) (U64.mul page_wsize_u64 8UL)

/// The pages a stretch inside the run cuts out lie in the run.
let cut_bounds (h n r d: nat)
  : Lemma (requires page_base h <= r /\ r <= d /\ d <= page_base (h + n) /\ h + n <= n_pages /\
                    r >= z /\ pg_ceil r < pg_floor d)
          (ensures h <= pg_ceil r /\ pg_floor d <= h + n /\
                   r <= page_base (pg_ceil r) /\ page_base (pg_ceil r) <= page_base (pg_floor d) /\
                   page_base (pg_floor d) <= d)
  = split_bounds r d;
    if pg_ceil r < h then page_base_lt (pg_ceil r) h;
    if pg_floor d > h + n then page_base_lt (h + n) (pg_floor d)

let piece_w (x y: nat)
  : Lemma (requires x % 8 == 0 /\ y % 8 == 0 /\ x + 8 <= y)
          (ensures (y - x) / 8 > 0 /\ x + ((y - x) / 8) * 8 == y)
  = diff8 x y

let same_start (x y: nat)
  : Lemma (requires x % 8 == 0 /\ y % 8 == 0 /\ x <= y /\ ~(x + 8 <= y)) (ensures x == y)
  = diff8 x y

#push-options "--fuel 2"
let pre_one (r p: nat)
  : Lemma (requires r + 8 <= page_base p)
          (ensures pre_of r p == [mkb r ((page_base p - r) / 8) Dead])
  = ()

let pre_none (r p: nat) : Lemma (requires ~(r + 8 <= page_base p)) (ensures pre_of r p == []) = ()

let suf_one (q e: nat)
  : Lemma (requires page_base q + 8 <= e)
          (ensures suf_of q e == [mkb (page_base q) ((e - page_base q) / 8) Dead])
  = ()

let suf_none (q e: nat) : Lemma (requires ~(page_base q + 8 <= e)) (ensures suf_of q e == []) = ()
#pop-options

let page_w_bound () : Lemma (page_wsize <= pow2 54 /\ page_wsize > 0)
  = cls_bounds 0; FStar.Math.Lemmas.pow2_lt_compat 54 20

/// The run's words fit below `pow2 54`.
let run_words (h n: nat) (x y: nat)
  : Lemma (requires h + n <= n_pages /\ page_base h <= x /\ x <= y /\ y <= page_base (h + n))
          (ensures (y - x) / 8 <= pow2 54)
  = page_base_mono (h + n) n_pages;
    LI.bounds ()

/// How the pieces of a cut stretch make up `split1`.
let cut_assoc (xs pre pg suf: list blk)
  : Lemma (L.append (L.append (L.append xs pre) pg) suf == L.append xs (L.append pre (L.append pg suf)))
  = L.append_assoc (L.append xs pre) pg suf;
    L.append_assoc xs pre (L.append pg suf)

let page_step (xs1: list blk) (p j: nat)
  : Lemma (requires p <= j)
          (ensures L.append (L.append xs1 (pages p j)) [page_blk j] == L.append xs1 (pages p (j + 1)))
  = pages_snoc p j;
    L.append_assoc xs1 (pages p j) [page_blk j]

/// Lay out the piece of `[r, page_base p)` before the first whole page.
fn emit_pre (heap: heap_t) (t: pstate_t) (first pend: R.ref U64.t)
  (h n: U64.t) (r p: U64.t)
  (#g0: erased Base.heap) (#st0: erased pstate) (#s: erased nat) (#xs: erased (list blk)) (#a: erased nat)
  requires run_inv heap t first pend g0 st0 s xs a **
           pure (a == U64.v r /\ U64.v h + U64.v n <= n_pages /\ page_base (U64.v h) <= U64.v r /\
                 U64.v r <= page_base (U64.v p) /\ U64.v p <= U64.v h + U64.v n /\ U64.v r % 8 == 0)
  ensures exists* (xs': list blk) (a': nat).
          run_inv heap t first pend g0 st0 s xs' a' **
          pure (xs' == L.append xs (pre_of (U64.v r) (U64.v p)) /\ a' == page_base (U64.v p))
{
  LI.bounds ();
  page_base_mono (U64.v p) n_pages;
  page_base_mono (U64.v h + U64.v n) n_pages;
  page_base_mono (U64.v p) (U64.v h + U64.v n);
  page_base_aligned (U64.v p);
  let pb = page_base_u64 p;
  if (U64.lte (U64.add r 8UL) pb) {
    pre_one (U64.v r) (U64.v p);
    piece_w (U64.v r) (U64.v pb);
    run_words (U64.v h) (U64.v n) (U64.v r) (U64.v pb);
    let w1 = U64.div (U64.sub pb r) 8UL;
    hval_free g0 (mkb (U64.v r) (U64.v w1) Dead);
    emit heap t first pend r w1 Dead (bhdr_u64 w1) 0UL
  } else {
    pre_none (U64.v r) (U64.v p);
    same_start (U64.v r) (U64.v pb);
    append_nil_r xs;
    ()
  }
}

/// Lay out the stretch `[r, d)`: `split1` of one free block.
fn emit_stretch (heap: heap_t) (t: pstate_t) (first pend: R.ref U64.t)
  (h: U64.t) (n: U64.t) (r d: U64.t)
  (#g0: erased Base.heap) (#st0: erased pstate) (#s: erased nat) (#xs: erased (list blk)) (#a: erased nat)
  requires run_inv heap t first pend g0 st0 s xs a **
           pure (a == U64.v r /\
                 U64.v h + U64.v n <= n_pages /\ page_base (U64.v h) <= U64.v r /\
                 U64.v r + 8 <= U64.v d /\ U64.v d <= page_base (U64.v h + U64.v n) /\
                 U64.v r % 8 == 0 /\ U64.v d % 8 == 0)
  ensures exists* (xs': list blk) (a': nat).
          run_inv heap t first pend g0 st0 s xs' a' **
          pure (xs' == L.append xs (split1 (stretch (U64.v r) (U64.v d))) /\ a' == U64.v d)
{
  LI.bounds ();
  page_base_mono (U64.v h + U64.v n) n_pages;
  page_base_mono (U64.v h) (U64.v h + U64.v n);
  page_base_bound (U64.v h);
  piece_w (U64.v r) (U64.v d);
  run_words (U64.v h) (U64.v n) (U64.v r) (U64.v d);
  let b = Ghost.hide (stretch (U64.v r) (U64.v d));
  let p = pg_ceil_u64 r;
  let q = pg_floor_u64 d;
  let w = U64.div (U64.sub d r) 8UL;
  if (U64.lt r (z_u64 ()) || U64.gte p q) {
    RL.split1_whole b;
    hval_free g0 b;
    emit heap t first pend r w Dead (bhdr_u64 w) 0UL
  } else {
    RL.split1_cut b;
    cut_bounds (U64.v h) (U64.v n) (U64.v r) (U64.v d);
    page_base_aligned (U64.v p);
    page_base_aligned (U64.v q);
    page_w_bound ();
    let xs1 = Ghost.hide (L.append xs (pre_of (U64.v r) (U64.v p)));
    emit_pre heap t first pend h n r p;
    // the whole pages
    append_nil_r xs1;
    RL.pages_nil (U64.v p) (U64.v p);
    let mut j = p;
    while (U64.lt !j q)
      invariant exists* vj (cur: list blk) (ca: nat).
        R.pts_to j vj ** run_inv heap t first pend g0 st0 s cur ca **
        pure (U64.v p <= U64.v vj /\ U64.v vj <= U64.v q /\
              cur == L.append xs1 (pages (U64.v p) (U64.v vj)) /\ ca == page_base (U64.v vj))
      decreases (U64.v q - U64.v !j)
    {
      let vj = !j;
      page_base_succ (U64.v vj);
      page_base_bound (U64.v vj);
      page_base_mono (U64.v vj + 1) n_pages;
      hval_free g0 (page_blk (U64.v vj));
      page_step xs1 (U64.v p) (U64.v vj);
      let a = page_base_u64 vj;
      emit heap t first pend a page_wsize_u64 Page (bhdr_u64 page_wsize_u64) vj;
      j := U64.add vj 1UL
    };
    // the piece after the last page
    let qb = page_base_u64 q;
    cut_assoc xs (pre_of (U64.v r) (U64.v p)) (pages (U64.v p) (U64.v q)) (suf_of (U64.v q) (U64.v d));
    if (U64.lte (U64.add qb 8UL) d) {
      suf_one (U64.v q) (U64.v d);
      piece_w (U64.v qb) (U64.v d);
      run_words (U64.v h) (U64.v n) (U64.v qb) (U64.v d);
      let w2 = U64.div (U64.sub d qb) 8UL;
      hval_free g0 (mkb (U64.v qb) (U64.v w2) Dead);
      emit heap t first pend qb w2 Dead (bhdr_u64 w2) 0UL
    } else {
      suf_none (U64.v q) (U64.v d);
      same_start (U64.v qb) (U64.v d);
      append_nil_r (L.append xs1 (pages (U64.v p) (U64.v q)));
      ()
    }
  }
}

/// ---------------------------------------------------------------------------
/// The first pass: the run's layout
/// ---------------------------------------------------------------------------

let mod8_add (a d: nat) : Lemma (requires a % 8 == 0 /\ a <= d /\ (d - a) % 8 == 0) (ensures d % 8 == 0)
  = FStar.Math.Lemmas.lemma_mod_plus_distr_l a (d - a) 8

let w8_add (a: nat) (w: pos) : Lemma (requires a % 8 == 0) (ensures (a + w * 8) % 8 == 0)
  = FStar.Math.Lemmas.lemma_mod_plus a w 8

let fin_cons (xs: list blk) (b: blk) (rest: list blk)
  : Lemma (L.append xs (b :: rest) == L.append (L.append xs [b]) rest)
  = L.append_assoc xs [b] rest; RL.append_one b rest

/// The end of the stretch of blocks that are not black, from `va`.
fn find_dead_end (heap: heap_t) (t: pstate_t) (first pend: R.ref U64.t) (va e: U64.t)
  (#g0: erased Base.heap) (#st0: erased pstate) (#s: erased nat) (#xs: erased (list blk)) (#ca: erased nat)
  requires run_inv heap t first pend g0 st0 s xs ca **
           pure (ca <= U64.v va /\ U64.v va <= U64.v e /\ U64.v e <= Base.heap_size /\ U64.v va % 8 == 0)
  returns d: U64.t
  ensures run_inv heap t first pend g0 st0 s xs ca **
          pure (U64.v d == RL.dead_end g0 (U64.v va) (U64.v e))
{
  LI.bounds ();
  let mut b = va;
  let mut more = true;
  while (!more)
    invariant exists* vb vm.
      R.pts_to b vb ** R.pts_to more vm ** run_inv heap t first pend g0 st0 s xs ca **
      pure (U64.v va <= U64.v vb /\ U64.v vb <= U64.v e /\ U64.v vb % 8 == 0 /\
            RL.dead_end g0 (U64.v va) (U64.v e) == RL.dead_end g0 (U64.v vb) (U64.v e) /\
            (not vm ==> RL.dead_end g0 (U64.v vb) (U64.v e) == U64.v vb))
    decreases (U64.v e - U64.v !b + (if !more then 1 else 0))
  {
    let vb = !b;
    if (U64.gte vb e) {
      dead_end_stop g0 (U64.v vb) (U64.v e);
      more := false
    } else {
      let hb = read_ahead heap t first pend vb;
      words_hdr g0 (U64.v vb) hb;
      let w = U64.add (get_wosize hb) 1UL;
      let col = get_color hb;
      let stop = (U64.gt (U64.add vb (U64.mul w 8UL)) e || col = Hd.Black);
      if stop {
        dead_end_stop g0 (U64.v vb) (U64.v e);
        more := false
      } else {
        dead_end_step g0 (U64.v vb) (U64.v e);
        w8_add (U64.v vb) (U64.v w);
        b := U64.add vb (U64.mul w 8UL)
      }
    }
  };
  !b
}

/// Lay out the run `[s, e)`, from the empty layout to `fin g0 s e`.
fn lay_out (heap: heap_t) (t: pstate_t) (first pend: R.ref U64.t) (h n: U64.t)
  (#g0: erased Base.heap) (#st0: erased pstate)
  requires run_inv heap t first pend g0 st0 (page_base (U64.v h)) [] (page_base (U64.v h)) **
           pure (U64.v n > 0 /\ U64.v h + U64.v n <= n_pages)
  returns fa: U64.t
  ensures exists* (xs: list blk).
          run_inv heap t first pend g0 st0 (page_base (U64.v h)) xs (U64.v fa) **
          pure (xs == fin g0 (page_base (U64.v h)) (page_base (U64.v h + U64.v n)) /\
                U64.v fa <= page_base (U64.v h + U64.v n))
{
  LI.bounds ();
  page_base_mono (U64.v h + U64.v n) n_pages;
  page_base_mono (U64.v h) (U64.v h + U64.v n);
  page_base_bound (U64.v h);
  page_base_bound (U64.v h + U64.v n);
  let sb = page_base_u64 h;
  let e = page_base_u64 (U64.add h n);
  append_nil_l (fin g0 (U64.v sb) (U64.v e));
  let mut a = sb;
  let mut go = true;
  while (!go)
    invariant exists* va vgo (xs: list blk) (ca: nat).
      R.pts_to a va ** R.pts_to go vgo **
      run_inv heap t first pend g0 st0 (page_base (U64.v h)) xs ca **
      pure (ca == U64.v va /\ U64.v sb <= U64.v va /\ U64.v va <= U64.v e /\ U64.v va % 8 == 0 /\
            fin g0 (U64.v sb) (U64.v e) == L.append xs (if vgo then fin g0 (U64.v va) (U64.v e) else []))
    decreases (U64.v e - U64.v !a + (if !go then 1 else 0))
  {
    let va = !a;
    with xs ca. assert (run_inv heap t first pend g0 st0 (page_base (U64.v h)) xs ca);
    if (U64.gte va e) {
      RL.fin_stop g0 (U64.v va) (U64.v e);
      go := false
    } else {
      let hd = read_ahead heap t first pend va;
      words_hdr g0 (U64.v va) hd;
      let w = U64.add (get_wosize hd) 1UL;
      if (U64.gt (U64.add va (U64.mul w 8UL)) e) {
        RL.fin_stop g0 (U64.v va) (U64.v e);
        go := false
      } else {
        let col = get_color hd;
        if (col = Hd.Black) {
          RL.fin_live g0 (U64.v va) (U64.v e);
          hval_live g0 (mkb (U64.v va) (U64.v w) Live);
          fin_cons xs (mkb (U64.v va) (U64.v w) Live) (fin g0 (U64.v va + U64.v w * 8) (U64.v e));
          w8_add (U64.v va) (U64.v w);
          emit heap t first pend va w Live (recolour_hdr hd Hd.White) 0UL;
          a := U64.add va (U64.mul w 8UL)
        } else {
          let d = find_dead_end heap t first pend va e;
          RL.fin_dead g0 (U64.v va) (U64.v e);
          RL.dead_end_props g0 (U64.v va) (U64.v e);
          mod8_add (U64.v va) (U64.v d);
          L.append_assoc xs (split1 (stretch (U64.v va) (U64.v d))) (fin g0 (U64.v d) (U64.v e));
          emit_stretch heap t first pend h n va d;
          a := d
        }
      }
    }
  };
  with xs ca. assert (run_inv heap t first pend g0 st0 (page_base (U64.v h)) xs ca);
  let vgo = !go;
  assert (pure (vgo == false));
  append_nil_r xs;
  assert (pure (fin g0 (U64.v sb) (U64.v e) == xs));
  assert (pure (U64.v sb == page_base (U64.v h) /\ U64.v e == page_base (U64.v h + U64.v n)));
  let fa = !a;
  rewrite (run_inv heap t first pend g0 st0 (page_base (U64.v h)) xs ca)
       as (run_inv heap t first pend g0 st0 (page_base (U64.v h)) xs (U64.v fa));
  fa
}

/// The open link gets the old list head; the layout is written.
fn close_run (heap: heap_t) (t: pstate_t) (first pend: R.ref U64.t) (fp: U64.t)
  (#g0: erased Base.heap) (#st0: erased pstate) (#s: erased nat) (#xs: erased (list blk)) (#a: erased nat)
  requires run_inv heap t first pend g0 st0 s xs a
  returns hd: U64.t
  ensures exists* g st vf vp. is_heap heap g ** pages_st t st ** R.pts_to first vf ** R.pts_to pend vp **
          pure (g == SR.wr_all g0 xs fp /\ RML.map_in st0 st xs /\ hd == SR.lhead xs fp /\ contig xs s a)
{
  unfold run_inv;
  with g st vf vp. assert (is_heap heap g ** pages_st t st ** R.pts_to first vf ** R.pts_to pend vp);
  RL.close_eq g0 g xs s a vf vp fp;
  let p = !pend;
  let f = !first;
  if (p = 0UL) {
    fp
  } else {
    wr heap p fp;
    f
  }
}

/// ---------------------------------------------------------------------------
/// The second pass: the run's pages
/// ---------------------------------------------------------------------------

let head_rec_of (r: pinfo) (m: U64.t{U64.v m > 0}) : pinfo = { r with code = 2uy; arg = m; swept = true }
let cont_rec_of (r: pinfo) : pinfo = { r with code = 3uy; swept = true }

/// The length of the stretch of pages that are not free from `jj`, before
/// `lim`: `run_from`.
fn count_run (t: pstate_t) (jj lim: U64.t) (h n: U64.t)
  (#st0 #st1 #st: erased pstate) (fs: erased (list blk))
  requires pages_st t st **
           pure (RML.pass2 st0 st1 st fs (U64.v h) (U64.v n) (U64.v jj) /\ RML.map_in st0 st1 fs /\
                 U64.v h < n_pages /\ U64.v n > 0 /\ RML.run_pages st0.pm (U64.v h) (U64.v n) /\
                 U64.v h <= U64.v jj /\ U64.v jj < U64.v lim /\ U64.v lim == U64.v h + U64.v n)
  returns m: U64.t
  ensures pages_st t st ** pure (U64.v m == RM.run_from fs (U64.v jj) (U64.v lim))
{
  let mut k = jj;
  let mut more = true;
  while (!more)
    invariant exists* vk vm.
      R.pts_to k vk ** R.pts_to more vm ** pages_st t st **
      pure (U64.v jj <= U64.v vk /\ U64.v vk <= U64.v lim /\
            RM.run_from fs (U64.v jj) (U64.v lim) ==
              (U64.v vk - U64.v jj) + (if vm then RM.run_from fs (U64.v vk) (U64.v lim) else 0))
    decreases (U64.v lim - U64.v !k + (if !more then 1 else 0))
  {
    let vk = !k;
    RML.run_from_step fs (U64.v vk) (U64.v lim);
    if (U64.gte vk lim) {
      more := false
    } else {
      RML.pass2_ahead st0 st1 st fs (U64.v h) (U64.v n) (U64.v jj) (U64.v vk);
      RML.freed_iff st0 st1 fs (U64.v h) (U64.v n) (U64.v vk);
      let r = read_entry t vk;
      if (is_free_rec r) {
        more := false
      } else {
        k := U64.add vk 1UL
      }
    }
  };
  let vk = !k;
  U64.sub vk jj
}

/// Page `jj` starts a stretch: it is the run's first page, or the page
/// before it is free.
fn starts_run (t: pstate_t) (h n jj: U64.t) (#st0 #st1 #st: erased pstate) (fs: erased (list blk))
  requires pages_st t st **
           pure (RML.pass2 st0 st1 st fs (U64.v h) (U64.v n) (U64.v jj) /\
                 U64.v h <= U64.v jj /\ U64.v jj < U64.v h + U64.v n /\ U64.v jj < n_pages /\ U64.v h < n_pages)
  returns b: bool
  ensures pages_st t st ** pure (b == (U64.v jj = U64.v h || (U64.v jj > 0 && RM.freed fs (U64.v jj - 1))))
{
  if (jj = h) {
    true
  } else {
    RML.pass2_prev st0 st1 st fs (U64.v h) (U64.v n) (U64.v jj);
    let rp = read_entry t (U64.sub jj 1UL);
    is_free_rec rp
  }
}

/// Give the run's pages that are not free their entries.
fn pass2 (t: pstate_t) (h n: U64.t) (#st0 #st1: erased pstate) (fs: erased (list blk)) (a: erased nat)
  requires pages_st t st1 **
           pure (RML.map_in st0 st1 fs /\ U64.v h < n_pages /\ U64.v n > 0 /\
                 RML.run_pages st0.pm (U64.v h) (U64.v n) /\
                 contig fs (page_base (U64.v h)) a /\ a <= page_base (U64.v h + U64.v n))
  ensures exists* st. pages_st t st **
          pure (st.pm == RM.new_map st0.pm fs (U64.v h) (U64.v n) /\
                st.avail == st0.avail /\ st.large == st0.large)
{
  RML.pass2_start st0 st1 fs (U64.v h) (U64.v n);
  let lim = U64.add h n;
  let mut j = h;
  while (U64.lt !j lim)
    invariant exists* vj st.
      R.pts_to j vj ** pages_st t st **
      pure (U64.v h <= U64.v vj /\ U64.v vj <= U64.v lim /\
            RML.pass2 st0 st1 st fs (U64.v h) (U64.v n) (U64.v vj))
    decreases (U64.v lim - U64.v !j)
  {
    let vj = !j;
    with st. assert (pages_st t st);
    RML.pass2_ahead st0 st1 st fs (U64.v h) (U64.v n) (U64.v vj) (U64.v vj);
    RML.freed_iff st0 st1 fs (U64.v h) (U64.v n) (U64.v vj);
    let r = read_entry t vj;
    if (is_free_rec r) {
      RML.pass2_free st0 st1 st fs (U64.v h) (U64.v n) (U64.v vj);
      j := U64.add vj 1UL
    } else {
      let hd = starts_run t h n vj #st0 #st1 #st fs;
      if hd {
        let m = count_run t vj lim h n #st0 #st1 #st fs;
        RML.pass2_head st0 st1 st fs (U64.v h) (U64.v n) (U64.v vj) (U64.v m);
        write_entry t vj (head_rec_of r m);
        j := U64.add vj 1UL
      } else {
        RML.pass2_cont st0 st1 st fs (U64.v h) (U64.v n) (U64.v vj);
        write_entry t vj (cont_rec_of r);
        j := U64.add vj 1UL
      }
    }
  };
  with st. assert (pages_st t st);
  let vj = !j;
  assert (pure (U64.v vj == U64.v h + U64.v n));
  assert (pure (RML.pass2 st0 st1 st fs (U64.v h) (U64.v n) (U64.v h + U64.v n)));
  RML.pass2_done st0 st1 st fs (U64.v h) (U64.v n) a;
  assert (pure (st.pm == RM.new_map st0.pm fs (U64.v h) (U64.v n)))
}

/// ---------------------------------------------------------------------------
/// The run step of the whole sweep
/// ---------------------------------------------------------------------------

let run_state_eq (st0 st: pstate) (pm': page_map) (fp': U64.t)
  : Lemma (requires st.pm == pm' /\ st.avail == st0.avail /\ st.large == st0.large)
          (ensures set_lhead st fp' == SS.run_state st0 pm' fp')
  = ()

/// Sweep the run at page `h`, whose entry is `r`, and store the new list
/// head, as `SweepAll.step` does.
fn run_step (heap: heap_t) (t: pstate_t) (h: U64.t{U64.v h < n_pages}) (r: pinfo) (#st: erased pstate)
  requires is_heap heap 'g ** pages_st t st **
           pure (view r == entry st.pm (U64.v h) /\ is_head r /\
                 RML.run_pages st.pm (U64.v h) (U64.v r.arg))
  ensures exists* g' st'. is_heap heap g' ** pages_st t st' **
          pure (g' == Mktuple3?._1 (SR.sweep_run 'g st.pm (U64.v h) (Ce.large_head st)) /\
                st' == SS.run_state st (Mktuple3?._2 (SR.sweep_run 'g st.pm (U64.v h) (Ce.large_head st)))
                                       (Mktuple3?._3 (SR.sweep_run 'g st.pm (U64.v h) (Ce.large_head st))))
{
  let n = r.arg;
  sweep_run_unfold 'g st.pm (U64.v h) (U64.v n) (Ce.large_head st);
  let fp = read_lhead t;
  let mut first = 0UL;
  let mut pend = 0UL;
  page_base_aligned (U64.v h);
  RL.emit_start 'g (page_base (U64.v h));
  RML.map_in_start st;
  fold (run_inv heap t first pend 'g st (page_base (U64.v h)) [] (page_base (U64.v h)));
  let fa = lay_out heap t first pend h n;
  with xs. assert (run_inv heap t first pend 'g st (page_base (U64.v h)) xs (U64.v fa));
  let hd = close_run heap t first pend fp;
  pass2 t h n #st xs (U64.v fa);
  with st2. assert (pages_st t st2);
  run_state_eq st st2 (RM.new_map st.pm xs (U64.v h) (U64.v n)) hd;
  write_lhead t hd
}
