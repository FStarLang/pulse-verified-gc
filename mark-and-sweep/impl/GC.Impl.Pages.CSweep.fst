/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.CSweep - sweeping one chunk
/// ---------------------------------------------------------------------------
///
/// `sweep_units` sweeps the units of a chunk `[lo, hi)` from empty lists,
/// as `GC.Impl.Pages.Sweep.sweep_all` sweeps the whole heap: a pool page with
/// `CPool.pool_step_c`, a run with `CRun.run_step_c`, skipping free pages
/// (whose lowest one it notes, for the free-page hint) and units already
/// swept.  It computes exactly `SweepRange.crange` of the heap the bitmap
/// stands for, from empty lists (`SweepChunks.chunk`), including the open
/// link; at the end the chunk has no mark left, and no page below the
/// lowest page it noted is free.
///
/// The marks it needs (`marks_from`): each unit ahead has its marks where
/// its sweep reads them (`BitmapUnits.pool_marks`, `run_marks`), and free
/// pages and swept units have none.  A unit's sweep changes the heap and the
/// bitmap only in its own span, so the units ahead keep theirs
/// (`marks_frame`).

module GC.Impl.Pages.CSweep

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
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module Base = GC.Spec.Base
module SH = GC.Spec.Heap
module Sh = GC.Spec.Pages.Shape
module SP = GC.Spec.Pages.SweepPage
module SR = GC.Spec.Pages.SweepRun
module SS = GC.Spec.Pages.SweepStep
module SA = GC.Spec.Pages.SweepAll
module SO = GC.Spec.Pages.SweepOrder
module Ce = GC.Spec.Pages.Cells
module BM = GC.Spec.Pages.Bitmap
module BU = GC.Spec.Pages.BitmapUnits
module SRg = GC.Spec.Pages.SweepRange
module SSp = GC.Spec.Pages.SweepSplit
module SCh = GC.Spec.Pages.SweepChunks
module RML = GC.Impl.Pages.RunMapLemmas
module ISw = GC.Impl.Pages.Sweep
module CP = GC.Impl.Pages.CPool
module CR = GC.Impl.Pages.CRun

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The marks a unit's sweep needs
/// ---------------------------------------------------------------------------

let no_marks (bs: Seq.seq U32.t) (lo hi: nat) : prop =
  forall (x: nat). lo <= x /\ x < hi ==> not (BM.marked bs x)

/// The marks of the unit at page `j`: none in a free page or a swept unit;
/// on slot headers of a pool page and on the walk of a run, as their sweeps
/// need.
let unit_marks (g: Base.heap) (bs: Seq.seq U32.t) (pm: page_map) (j: nat{j < n_pages}) : prop =
  match (entry pm j).kind with
  | Free -> no_marks bs (page_base j) (page_base (j + 1))
  | Pool c ->
    if (entry pm j).swept then no_marks bs (page_base j) (page_base (j + 1)) else BU.pool_marks g bs j c
  | LargeHead n ->
    if (entry pm j).swept then no_marks bs (page_base j) (page_base (j + n)) else BU.run_marks g bs j n
  | LargeCont -> True

/// The units from page `p` to page `hi` have their marks.
let marks_from (g: Base.heap) (bs: Seq.seq U32.t) (pm: page_map) (p hi: nat) : prop =
  forall (j: nat{j < n_pages}). p <= j /\ j < hi ==> unit_marks g bs pm j

/// Heaps and bitmaps that agree from `x` on.
let agree_from (g g': Base.heap) (b b': Seq.seq U32.t) (x: nat) : prop =
  (forall (y: Base.hp_addr). U64.v y >= x ==> SH.read_word g' y == SH.read_word g y) /\
  (forall (y: nat). y >= x ==> BM.marked b' y == BM.marked b y)

let hagree_from (g g': Base.heap) (x e: nat)
  : Lemma (requires forall (y: Base.hp_addr). U64.v y >= x ==> SH.read_word g' y == SH.read_word g y)
          (ensures SO.hagree g' g x e)
  = ()

#push-options "--z3rlimit 40"
/// A unit keeps its marks when nothing from its start on changes.
let unit_marks_frame (g g': Base.heap) (b b': Seq.seq U32.t) (pm pm': page_map) (j: nat{j < n_pages}) (x: nat)
  : Lemma (requires unit_marks g b pm j /\ agree_from g g' b b' x /\ page_base j >= x /\ entry pm' j == entry pm j)
          (ensures unit_marks g' b' pm' j)
  = match (entry pm j).kind with
    | Pool c ->
      if not (entry pm j).swept then begin
        let aux (k: nat) : Lemma (k < n_slots c ==> Sh.color_at g' (slot_base j c k) == Sh.color_at g (slot_base j c k))
          = if k < n_slots c then begin
              GC.Spec.Pages.PoolInit.slot_fits j c k;
              let a = GC.Spec.Pages.PoolInit.slot_hd j c k in
              assert (SH.read_word g' a == SH.read_word g a)
            end
        in
        FStar.Classical.forall_intro aux
      end
    | LargeHead n ->
      if not (entry pm j).swept then begin
        hagree_from g g' x (page_base (j + n));
        let aux (y: nat) : Lemma (BU.on_walk g' (page_base j) (page_base (j + n)) y ==
                                  BU.on_walk g (page_base j) (page_base (j + n)) y)
          = BU.on_walk_local g' g x (page_base j) (page_base (j + n)) y
        in
        FStar.Classical.forall_intro aux
      end
    | _ -> ()
#pop-options

/// **The units ahead keep their marks** after the unit at `p`, whose span
/// ends at `q`.
let marks_frame (g g': Base.heap) (b b': Seq.seq U32.t) (pm pm': page_map) (q hi: nat)
  : Lemma (requires marks_from g b pm q hi /\ agree_from g g' b b' (page_base q) /\
                    (forall (j: nat{j < n_pages}). j >= q ==> entry pm' j == entry pm j))
          (ensures marks_from g' b' pm' q hi)
  = let aux (j: nat{j < n_pages}) : Lemma (q <= j /\ j < hi ==> unit_marks g' b' pm' j)
      = if q <= j && j < hi then begin
          page_base_mono q j;
          unit_marks_frame g g' b b' pm pm' j (page_base q)
        end
    in
    FStar.Classical.forall_intro aux

/// What a unit's sweep leaves outside its span `[s, e)`.
let out_of (g g': Base.heap) (b b': Seq.seq U32.t) (s e: nat) : prop =
  SO.hout g g' s e /\ CR.marks_out b b' s e

let agree_of (g g': Base.heap) (b b': Seq.seq U32.t) (s e: nat)
  : Lemma (requires out_of g g' b b' s e) (ensures agree_from g g' b b' e)
  = ()

/// ---------------------------------------------------------------------------
/// The loop's state
/// ---------------------------------------------------------------------------

/// No page below `p` that was free when the chunk started is below `mf`.
let free0_ge (pm0: page_map) (lo p mf: nat) : prop =
  forall (j: nat{j < n_pages}). lo <= j /\ j < p /\ (entry pm0 j).kind == Free ==> j >= mf

/// The chunk's lists end inside it, below page `p`.
let ftails (st: pstate) (lo p: nat) : prop = CP.ftails st lo p

/// What stays as it was outside the chunk.
let frames (g0: Base.heap) (pm0: page_map) (bs0: Seq.seq U32.t) (lo hi: nat)
           (g: Base.heap) (b: Seq.seq U32.t) (st: pstate) : prop =
  SO.hout g0 g (page_base lo) (page_base hi) /\ words_out bs0 b lo hi /\
  (forall (j: nat{j < n_pages}). j < lo ==> entry st.pm j == entry pm0 j)

[@@"opaque_to_smt"]
let loop_ok (g0 w0: Base.heap) (pm0: page_map) (bs0: Seq.seq U32.t) (lo hi: nat)
            (g: Base.heap) (b: Seq.seq U32.t) (st: pstate) (ol: U64.t) (mf: nat) (p: nat) : prop =
  lo <= p /\ p <= hi /\ hi <= n_pages /\ map_ok pm0 /\ Seq.length b == BM.bm_len /\
  SRg.crange (BM.with_marks g b) st ol p hi == SRg.crange w0 (SCh.zst pm0) 0UL lo hi /\
  SRg.wreach st.pm p hi /\ ISw.ahead pm0 st.pm p /\ (p < hi ==> walk_page pm0 p) /\
  marks_from g b st.pm p hi /\
  no_marks b (page_base lo) (page_base p) /\
  CR.marks_out bs0 b (page_base lo) (page_base hi) /\
  ftails st lo p /\ free0_ge pm0 lo p mf /\
  (forall (j: nat{j < n_pages}). j >= p ==> entry st.pm j == entry pm0 j) /\
  frames g0 pm0 bs0 lo hi g b st

let loop_elim (g0 w0: Base.heap) (pm0: page_map) (bs0: Seq.seq U32.t) (lo hi: nat)
              (g: Base.heap) (b: Seq.seq U32.t) (st: pstate) (ol: U64.t) (mf: nat) (p: nat)
  : Lemma (requires loop_ok g0 w0 pm0 bs0 lo hi g b st ol mf p)
          (ensures lo <= p /\ p <= hi /\ hi <= n_pages /\ map_ok pm0 /\ Seq.length b == BM.bm_len /\
                   SRg.crange (BM.with_marks g b) st ol p hi == SRg.crange w0 (SCh.zst pm0) 0UL lo hi /\
                   SRg.wreach st.pm p hi /\ ISw.ahead pm0 st.pm p /\ (p < hi ==> walk_page pm0 p) /\
                   marks_from g b st.pm p hi /\ no_marks b (page_base lo) (page_base p) /\
                   CR.marks_out bs0 b (page_base lo) (page_base hi) /\
                   ftails st lo p /\ free0_ge pm0 lo p mf /\
                   (forall (j: nat{j < n_pages}). j >= p ==> entry st.pm j == entry pm0 j) /\
                   frames g0 pm0 bs0 lo hi g b st)
  = reveal_opaque (`%loop_ok) loop_ok

let loop_intro (g0 w0: Base.heap) (pm0: page_map) (bs0: Seq.seq U32.t) (lo hi: nat)
               (g: Base.heap) (b: Seq.seq U32.t) (st: pstate) (ol: U64.t) (mf: nat) (p: nat)
  : Lemma (requires lo <= p /\ p <= hi /\ hi <= n_pages /\ map_ok pm0 /\ Seq.length b == BM.bm_len /\
                    SRg.crange (BM.with_marks g b) st ol p hi == SRg.crange w0 (SCh.zst pm0) 0UL lo hi /\
                    SRg.wreach st.pm p hi /\ ISw.ahead pm0 st.pm p /\ (p < hi ==> walk_page pm0 p) /\
                    marks_from g b st.pm p hi /\ no_marks b (page_base lo) (page_base p) /\
                    CR.marks_out bs0 b (page_base lo) (page_base hi) /\
                    ftails st lo p /\ free0_ge pm0 lo p mf /\
                    (forall (j: nat{j < n_pages}). j >= p ==> entry st.pm j == entry pm0 j) /\
                    frames g0 pm0 bs0 lo hi g b st)
          (ensures loop_ok g0 w0 pm0 bs0 lo hi g b st ol mf p)
  = reveal_opaque (`%loop_ok) loop_ok

/// The walk goes on to the next unit.
let next_unit (pm0 pm: page_map) (p hi: nat)
  : Lemma (requires map_ok pm0 /\ p < hi /\ hi <= n_pages /\ walk_page pm0 p /\
                    SRg.wreach pm p hi /\ (forall (j: nat{j < n_pages}). j >= p ==> entry pm j == entry pm0 j))
          (ensures p < n_pages /\ span pm p == span pm0 p /\ p + span pm p <= hi /\
                   SRg.wreach pm (p + span pm p) hi /\
                   (p + span pm p < hi ==> walk_page pm0 (p + span pm p)))
  = SRg.wreach_next pm p hi;
    SRg.wreach_le pm (p + span pm p) hi;
    next_walk_page pm0 p p

let hout_nest (g0 g g': Base.heap) (lo p q hi: nat)
  : Lemma (requires SO.hout g0 g lo hi /\ SO.hout g g' p q /\ lo <= p /\ q <= hi)
          (ensures SO.hout g0 g' lo hi)
  = ()

let frames_step (g0: Base.heap) (pm0: page_map) (bs0: Seq.seq U32.t) (lo hi: nat)
                (g: Base.heap) (b: Seq.seq U32.t) (st: pstate) (p q: nat)
                (g': Base.heap) (b': Seq.seq U32.t) (st': pstate)
  : Lemma (requires frames g0 pm0 bs0 lo hi g b st /\ lo <= p /\ p <= q /\ q <= hi /\
                    SO.hout g g' (page_base p) (page_base q) /\ words_out b b' p q /\
                    page_base lo <= page_base p /\ page_base q <= page_base hi /\
                    (forall (j: nat{j < n_pages}). j < lo ==> entry st'.pm j == entry st.pm j))
          (ensures frames g0 pm0 bs0 lo hi g' b' st')
  = words_out_trans bs0 b b' lo hi p q;
    hout_nest g0 g g' (page_base lo) (page_base p) (page_base q) (page_base hi)

/// After the unit at `p`, whose span ends at `q`: the facts that do not
/// depend on what the unit did.
let after_unit (g0 w0: Base.heap) (pm0: page_map) (bs0: Seq.seq U32.t) (lo hi: nat)
               (g: Base.heap) (b: Seq.seq U32.t) (st: pstate) (ol: U64.t) (mf: nat) (p: nat{p < n_pages})
               (g': Base.heap) (b': Seq.seq U32.t) (st': pstate) (ol': U64.t) (mf': nat)
  : Lemma (requires loop_ok g0 w0 pm0 bs0 lo hi g b st ol mf p /\ p < hi /\
                    (let q = p + span st.pm p in
                     BM.with_marks g' b' == fst (SA.step (BM.with_marks g b) st p) /\
                     st' == snd (SA.step (BM.with_marks g b) st p) /\
                     ol' == SRg.ostep (BM.with_marks g b) st ol p /\
                     out_of g g' b b' (page_base p) (page_base q) /\
                     no_marks b' (page_base p) (page_base q) /\ Seq.length b' == BM.bm_len /\
                     ftails st' lo q /\ free0_ge pm0 lo q mf' /\
                     (forall (j: nat{j < n_pages}). j >= q ==> entry st'.pm j == entry st.pm j) /\
                     words_out b b' p q /\
                     (forall (j: nat{j < n_pages}). j < lo ==> entry st'.pm j == entry st.pm j)))
          (ensures loop_ok g0 w0 pm0 bs0 lo hi g' b' st' ol' mf' (p + span st.pm p))
  = loop_elim g0 w0 pm0 bs0 lo hi g b st ol mf p;
    next_unit pm0 st.pm p hi;
    let q = p + span st.pm p in
    SRg.crange_step (BM.with_marks g b) st ol p hi;
    SRg.step_kinds_from (BM.with_marks g b) st p;
    assert (SRg.kinds_from st'.pm st.pm q);
    SRg.wreach_kinds st'.pm st.pm q hi;
    assert (SRg.wreach st'.pm q hi);
    let kq (j: nat{j < n_pages}) : Lemma (j >= q ==> (entry st'.pm j).kind == (entry pm0 j).kind) = () in
    FStar.Classical.forall_intro kq;
    page_base_mono lo p;
    page_base_mono p q;
    page_base_mono q hi;
    agree_of g g' b b' (page_base p) (page_base q);
    marks_frame g g' b b' st.pm st'.pm q hi;
    frames_step g0 pm0 bs0 lo hi g b st p q g' b' st';
    loop_intro g0 w0 pm0 bs0 lo hi g' b' st' ol' mf' q

/// The span of a unit at a walk page.
let span_of (pm: page_map) (p: nat{p < n_pages})
  : Lemma (span pm p == (match (entry pm p).kind with LargeHead n -> n | _ -> 1))
  = ()

let push_ftails (st: pstate) (lo: nat) (p: nat{p < n_pages}) (e: page_info)
  : Lemma (requires ftails st lo p /\ lo <= p)
          (ensures ftails (SS.push_avail st p e) lo (p + 1))
  = SS.push_frame st p e;
    SS.push_entry st p e

/// The push changes no entry below the chunk.
let old_tail_ge (st: pstate) (lo: nat) (p: nat{p < n_pages}) (e: page_info)
  : Lemma (requires ftails st lo p /\ lo <= p)
          (ensures forall (j: nat{j < n_pages}). j < lo ==> entry (SS.push_avail st p e).pm j == entry st.pm j)
  = SS.push_frame st p e;
    SS.push_entry st p e

let free0_more (pm0: page_map) (lo p q: nat) (mf mf': nat)
  : Lemma (requires free0_ge pm0 lo p mf /\ mf' <= mf /\ p <= q /\
                    (forall (j: nat{j < n_pages}). p <= j /\ j < q ==> ~((entry pm0 j).kind == Free)))
          (ensures free0_ge pm0 lo q mf')
  = ()

let free0_one (pm0: page_map) (lo: nat) (p: nat{p < n_pages}) (mf mf': nat)
  : Lemma (requires free0_ge pm0 lo p mf /\ mf' <= mf /\ ~((entry pm0 p).kind == Free))
          (ensures free0_ge pm0 lo (p + 1) mf')
  = ()

/// The pages of a run are not free.
let run_not_free (pm0: page_map) (p: nat{p < n_pages}) (n: pos)
  : Lemma (requires map_ok pm0 /\ (entry pm0 p).kind == LargeHead n)
          (ensures forall (j: nat{j < n_pages}). p <= j /\ j < p + n ==> ~((entry pm0 j).kind == Free))
  = assert (run_ok pm0 p)

let free0_run (pm0: page_map) (lo: nat) (p: nat{p < n_pages}) (n: pos) (mf mf': nat)
  : Lemma (requires free0_ge pm0 lo p mf /\ mf' <= mf /\ map_ok pm0 /\ (entry pm0 p).kind == LargeHead n)
          (ensures free0_ge pm0 lo (p + n) mf')
  = run_not_free pm0 p n

/// **A pool page.**
let loop_pool (g0 w0: Base.heap) (pm0: page_map) (bs0: Seq.seq U32.t) (lo hi: nat)
              (g: Base.heap) (b: Seq.seq U32.t) (st: pstate) (ol: U64.t) (mf: nat) (p: nat{p < n_pages}) (c: nat{c < n_cls})
              (g': Base.heap) (st': pstate) (mf': nat)
  : Lemma (requires loop_ok g0 w0 pm0 bs0 lo hi g b st ol mf p /\ p < hi /\
                    not (entry st.pm p).swept /\ (entry st.pm p).kind == Pool c /\
                    BM.with_marks g' (BM.zero_page b p) == fst (SP.sweep_page (BM.with_marks g b) st.pm p) /\
                    st' == SS.push_avail st p (snd (SP.sweep_page (BM.with_marks g b) st.pm p)) /\
                    SO.hout g g' (page_base p) (page_base (p + 1)) /\ mf' <= mf)
          (ensures loop_ok g0 w0 pm0 bs0 lo hi g' (BM.zero_page b p) st' ol mf' (p + 1))
  = loop_elim g0 w0 pm0 bs0 lo hi g b st ol mf p;
    let w = BM.with_marks g b in
    let b' = BM.zero_page b p in
    ISw.step_pool w st p c;
    let e = snd (SP.sweep_page w st.pm p) in
    SS.push_entry st p e;
    SS.push_frame st p e;
    let mk (y: nat) : Lemma (BM.marked b' y == (BM.marked b y && not (page_base p <= y && y < page_base (p + 1))))
      = BM.zero_page_marked b p y
    in
    FStar.Classical.forall_intro mk;
    page_base_mono lo p;
    page_base_mono (p + 1) hi;
    push_ftails st lo p e;
    words_out_zero b b p (p + 1) p;
    old_tail_ge st lo p e;
    assert ((entry pm0 p).kind == Pool c);
    free0_one pm0 lo p mf mf';
    after_unit g0 w0 pm0 bs0 lo hi g b st ol mf p g' b' st' ol mf'

/// **A run.**
let loop_run (g0 w0: Base.heap) (pm0: page_map) (bs0: Seq.seq U32.t) (lo hi: nat)
             (g: Base.heap) (b: Seq.seq U32.t) (st: pstate) (ol: U64.t) (mf: nat) (p: nat{p < n_pages}) (n: pos)
             (g': Base.heap) (b': Seq.seq U32.t) (st': pstate) (ol': U64.t) (mf': nat)
  : Lemma (requires loop_ok g0 w0 pm0 bs0 lo hi g b st ol mf p /\ p < hi /\
                    not (entry st.pm p).swept /\ (entry st.pm p).kind == LargeHead n /\
                    (let t3 = SR.sweep_run (BM.with_marks g b) st.pm p (Ce.large_head st) in
                     BM.with_marks g' b' == Mktuple3?._1 t3 /\
                     st' == SS.run_state st (Mktuple3?._2 t3) (Mktuple3?._3 t3)) /\
                    ol' == SRg.ostep (BM.with_marks g b) st ol p /\
                    no_marks b' (page_base p) (page_base (p + n)) /\
                    CR.marks_out b b' (page_base p) (page_base (p + n)) /\ words_out b b' p (p + n) /\
                    SO.hout g g' (page_base p) (page_base (p + n)) /\ mf' <= mf)
          (ensures loop_ok g0 w0 pm0 bs0 lo hi g' b' st' ol' mf' (p + n))
  = loop_elim g0 w0 pm0 bs0 lo hi g b st ol mf p;
    let w = BM.with_marks g b in
    ISw.step_run w st p n;
    let fs = GC.Spec.Pages.RunList.fin w (page_base p) (page_base (p + n)) in
    let ent (j: nat{j < n_pages}) : Lemma ((j >= p + n \/ j < p) ==> entry st'.pm j == entry st.pm j)
      = if j >= p + n || j < p then GC.Spec.Pages.RunMap.new_map_entry st.pm fs p n j
    in
    FStar.Classical.forall_intro ent;
    page_base_mono lo p;
    assert ((entry pm0 p).kind == LargeHead n);
    free0_run pm0 lo p n mf mf';
    after_unit g0 w0 pm0 bs0 lo hi g b st ol mf p g' b' st' ol' mf'

/// **A unit the sweep leaves alone**: a free page, whose index it notes, or
/// a unit already swept.
let loop_skip (g0 w0: Base.heap) (pm0: page_map) (bs0: Seq.seq U32.t) (lo hi: nat)
              (g: Base.heap) (b: Seq.seq U32.t) (st: pstate) (ol: U64.t) (mf: nat) (p: nat{p < n_pages}) (mf': nat)
  : Lemma (requires loop_ok g0 w0 pm0 bs0 lo hi g b st ol mf p /\ p < hi /\
                    ((entry st.pm p).swept \/ ~(Pool? (entry st.pm p).kind \/ LargeHead? (entry st.pm p).kind)) /\
                    mf' <= mf /\ ((entry st.pm p).kind == Free ==> mf' <= p))
          (ensures loop_ok g0 w0 pm0 bs0 lo hi g b st ol mf' (p + span st.pm p))
  = loop_elim g0 w0 pm0 bs0 lo hi g b st ol mf p;
    next_unit pm0 st.pm p hi;
    page_base_mono lo p;
    assert (entry pm0 p == entry st.pm p);
    (match (entry pm0 p).kind with
     | LargeHead n -> free0_run pm0 lo p n mf mf'
     | Free -> ()
     | _ -> free0_one pm0 lo p mf mf');
    words_out_refl b p (p + span st.pm p);
    after_unit g0 w0 pm0 bs0 lo hi g b st ol mf p g b st ol mf'

/// The start: nothing swept, empty lists.
let loop_start (w0 g0: Base.heap) (pm0: page_map) (bs0: Seq.seq U32.t) (lo hi: nat) (mf: nat)
  : Lemma (requires w0 == BM.with_marks g0 bs0 /\ lo <= hi /\ hi <= n_pages /\ map_ok pm0 /\
                    Seq.length bs0 == BM.bm_len /\ SRg.wreach pm0 lo hi /\ (lo < hi ==> walk_page pm0 lo) /\
                    marks_from g0 bs0 pm0 lo hi)
          (ensures loop_ok g0 w0 pm0 bs0 lo hi g0 bs0 (SCh.zst pm0) 0UL mf lo)
  = words_out_refl bs0 lo hi;
    loop_intro g0 w0 pm0 bs0 lo hi g0 bs0 (SCh.zst pm0) 0UL mf lo

/// What sweeping the chunk `[lo, hi)` from `g0`, `bs0` and `pm0` leaves.
let chunk_post (g0: Base.heap) (bs0: Seq.seq U32.t) (pm0: page_map) (lo hi: nat)
               (g: Base.heap) (b: Seq.seq U32.t) (st: pstate) (ol: U64.t) (mf: nat) : prop =
  (let tt = SRg.crange (BM.with_marks g0 bs0) (SCh.zst pm0) 0UL lo hi in
   BM.with_marks g b == SRg.cg tt /\ st == SRg.cs tt /\ ol == SRg.co tt) /\
  no_marks b (page_base lo) (page_base hi) /\ CR.marks_out bs0 b (page_base lo) (page_base hi) /\
  free0_ge pm0 lo hi mf /\
  SO.hout g0 g (page_base lo) (page_base hi) /\ words_out bs0 b lo hi /\
  (forall (j: nat{j < n_pages}). j < lo \/ j >= hi ==> entry st.pm j == entry pm0 j)

/// The end: the chunk swept, no mark left, and the lowest free page noted.
let loop_end (w0 g0: Base.heap) (pm0: page_map) (bs0: Seq.seq U32.t) (lo hi: nat)
             (g: Base.heap) (b: Seq.seq U32.t) (st: pstate) (ol: U64.t) (mf: nat) (p: nat)
  : Lemma (requires w0 == BM.with_marks g0 bs0 /\ loop_ok g0 w0 pm0 bs0 lo hi g b st ol mf p /\ p >= hi)
          (ensures chunk_post g0 bs0 pm0 lo hi g b st ol mf)
  = loop_elim g0 w0 pm0 bs0 lo hi g b st ol mf p;
    SRg.crange_stop (BM.with_marks g b) st ol p hi

let marks_at (g: Base.heap) (b: Seq.seq U32.t) (pm: page_map) (p: nat{p < n_pages}) (hi: nat)
  : Lemma (requires marks_from g b pm p hi /\ p < hi) (ensures unit_marks g b pm p)
  = ()

let ostep_run (w: Base.heap) (st: pstate) (ol: U64.t) (p: nat{p < n_pages}) (n: pos) (lh o: U64.t)
  : Lemma (requires not (entry st.pm p).swept /\ (entry st.pm p).kind == LargeHead n /\
                    lh == Ce.large_head st /\ o == SRg.open_of (SRg.run_fs w p n))
          (ensures SRg.ostep w st ol p == (if lh = 0UL && o <> 0UL then o else ol))
  = ()

/// **Sweep the units of the chunk** `[lo, hi)`, from empty lists.
fn sweep_units (hp: cheap_t) (bm: A.array U32.t) (t: pstate_t) (pt: A.array U64.t) (lo hi: U64.t)
  (#cf: erased cfix) (#g0: erased Base.heap) (#bs0: erased (Seq.seq U32.t))
  requires ch_heap hp cf.clo cf.chi g0 ** ch_bm bm cf.clo cf.chi bs0 **
           cst t pt cf (SCh.zst cf.cpm0) 0UL (U64.v hi) **
           pure (U64.v lo == cf.clo /\ U64.v hi == cf.chi /\ cf.clo <= cf.chi /\ cf.chi <= n_pages /\ map_ok cf.cpm0 /\
                 SRg.wreach cf.cpm0 cf.clo cf.chi /\ (cf.clo < cf.chi ==> walk_page cf.cpm0 cf.clo) /\
                 marks_from g0 bs0 cf.cpm0 cf.clo cf.chi)
  ensures exists* g' b' st' ol' mf'.
          ch_heap hp cf.clo cf.chi g' ** ch_bm bm cf.clo cf.chi b' ** cst t pt cf st' ol' mf' **
          pure (chunk_post g0 bs0 cf.cpm0 cf.clo cf.chi g' b' st' ol' mf')
{
  let w0 = Ghost.hide (BM.with_marks g0 bs0);
  cst_lengths t pt;
  unfold ch_bm; fold (ch_bm bm cf.clo cf.chi bs0);
  loop_start w0 g0 cf.cpm0 bs0 cf.clo cf.chi (U64.v hi);
  let mut p = lo;
  while (U64.lt !p hi)
    invariant exists* vp g b st ol mf.
      R.pts_to p vp ** ch_heap hp cf.clo cf.chi g ** ch_bm bm cf.clo cf.chi b ** cst t pt cf st ol mf **
      pure (loop_ok g0 w0 cf.cpm0 bs0 cf.clo cf.chi g b st ol mf (U64.v vp) /\ U64.v vp <= U64.v hi)
    decreases (U64.v hi - U64.v !p)
  {
    let vp = !p;
    with g b st ol mf. assert (ch_heap hp cf.clo cf.chi g ** ch_bm bm cf.clo cf.chi b ** cst t pt cf st ol mf);
    loop_elim g0 w0 cf.cpm0 bs0 cf.clo cf.chi g b st ol mf (U64.v vp);
    next_unit cf.cpm0 st.pm (U64.v vp) cf.chi;
    marks_at g b st.pm (U64.v vp) cf.chi;
    let r = c_read_entry t pt vp;
    if (r.swept) {
      if (is_head r) {
        loop_skip g0 w0 cf.cpm0 bs0 cf.clo cf.chi g b st ol mf (U64.v vp) mf;
        p := U64.add vp r.arg
      } else {
        if (is_free_rec r) {
          c_note_free t pt vp;
          loop_skip g0 w0 cf.cpm0 bs0 cf.clo cf.chi g b st ol mf (U64.v vp) (if U64.v vp < mf then U64.v vp else mf);
          p := U64.add vp 1UL
        } else {
          loop_skip g0 w0 cf.cpm0 bs0 cf.clo cf.chi g b st ol mf (U64.v vp) mf;
          p := U64.add vp 1UL
        }
      }
    } else {
      if (is_pool r) {
        let rp : (x: pinfo{is_pool x}) = r;
        CP.pool_step_c hp bm t pt vp rp;
        with g' mf'. assert (ch_heap hp cf.clo cf.chi g' ** cst t pt cf _ ol mf');
        loop_pool g0 w0 cf.cpm0 bs0 cf.clo cf.chi g b st ol mf (U64.v vp) (U64.v r.arg) g'
                  (SS.push_avail st (U64.v vp) (snd (SP.sweep_page (BM.with_marks g b) st.pm (U64.v vp)))) mf';
        p := U64.add vp 1UL
      } else {
        if (is_head r) {
          let lh = c_read_lhead t pt;
          ISw.run_reached cf.cpm0 st.pm (U64.v vp) (U64.v r.arg);
          let o = CR.run_step_c hp bm t pt vp r;
          ostep_run (BM.with_marks g b) st ol (U64.v vp) (U64.v r.arg) lh o;
          if (lh = 0UL && o <> 0UL) {
            c_write_ol t pt o;
            with g' b' st' mf'. assert (ch_heap hp cf.clo cf.chi g' ** ch_bm bm cf.clo cf.chi b' ** cst t pt cf st' o mf');
            loop_run g0 w0 cf.cpm0 bs0 cf.clo cf.chi g b st ol mf (U64.v vp) (U64.v r.arg) g' b' st' o mf';
            p := U64.add vp r.arg
          } else {
            with g' b' st' mf'. assert (ch_heap hp cf.clo cf.chi g' ** ch_bm bm cf.clo cf.chi b' ** cst t pt cf st' ol mf');
            loop_run g0 w0 cf.cpm0 bs0 cf.clo cf.chi g b st ol mf (U64.v vp) (U64.v r.arg) g' b' st' ol mf';
            p := U64.add vp r.arg
          }
        } else {
          if (is_free_rec r) {
            c_note_free t pt vp;
            loop_skip g0 w0 cf.cpm0 bs0 cf.clo cf.chi g b st ol mf (U64.v vp) (if U64.v vp < mf then U64.v vp else mf);
            p := U64.add vp 1UL
          } else {
            loop_skip g0 w0 cf.cpm0 bs0 cf.clo cf.chi g b st ol mf (U64.v vp) mf;
            p := U64.add vp 1UL
          }
        }
      }
    }
  };
  with vp g b st ol mf. assert (R.pts_to p vp ** ch_heap hp cf.clo cf.chi g ** ch_bm bm cf.clo cf.chi b ** cst t pt cf st ol mf);
  let vpf = !p;
  assert (pure (U64.v vpf >= U64.v hi));
  loop_end w0 g0 cf.cpm0 bs0 cf.clo cf.chi g b st ol mf (U64.v vp);
  assert (pure (chunk_post g0 bs0 cf.cpm0 cf.clo cf.chi g b st ol mf));
  ()
}
