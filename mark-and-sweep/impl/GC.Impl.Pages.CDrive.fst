/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.CDrive - the parallel sweep, run in one thread
/// ---------------------------------------------------------------------------
///
/// `sweep_par_seq` runs the parallel sweep's three parts in one thread:
/// `par_prepare`, then `CPar.sweep_chunk` for chunks 0, 1, ..., then
/// `par_finish`.  Between them it only regroups its memory, ghostly: before
/// chunk `c` it cuts the chunk's ranges out of the heap, the page records,
/// the bitmap and the chunks' records (`CSub.split3`), and after it puts them
/// back (`CSub.join3`).
///
/// **`sweep_par_seq` computes exactly `SweepAll.sweep_all` of the heap the
/// bitmap stands for, from `StartSweep.start_sweep`, and leaves the bitmap
/// all zero**, when the bitmap's marks lie where the sweep reads them
/// (`CSweep.marks_from`) and the map is well formed.  The proof is
/// `SweepChunks.sweep_chunks_eq`: the chunks, one after another from empty
/// lists, then the joins in ascending chunk order.
///
/// The C driver runs the same three parts with the chunks on threads; each
/// chunk's `sweep_chunk` owns only its own ranges, so the order does not
/// matter.

module GC.Impl.Pages.CDrive

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
open GC.Impl.Pages.CState
open GC.Impl.Pages.CJoin

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module A = Pulse.Lib.Array
module AC = Pulse.Lib.Array.Core
module R = Pulse.Lib.Reference
module Base = GC.Spec.Base
module SH = GC.Spec.Heap
module FLs = GC.Spec.FreeLists
module SA = GC.Spec.Pages.SweepAll
module SSt = GC.Spec.Pages.StartSweep
module SO = GC.Spec.Pages.SweepOrder
module BM = GC.Spec.Pages.Bitmap
module SRg = GC.Spec.Pages.SweepRange
module SSp = GC.Spec.Pages.SweepSplit
module SCh = GC.Spec.Pages.SweepChunks
module HE = GC.Gen.HeapExtensional
module CSub = GC.Impl.Pages.CSub
module CSw = GC.Impl.Pages.CSweep
module CP = GC.Impl.Pages.CPar
module ISw = GC.Impl.Pages.Sweep

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Putting a chunk's ranges back
/// ---------------------------------------------------------------------------

noextract
let tsl3 (#t: Type0) (s1 s2 s3: Seq.seq t) : Seq.seq t = Seq.append s1 (Seq.append s2 s3)

#push-options "--z3rlimit 40"
/// The heap with the chunk's bytes from `g'` and the others from `g` is `g'`,
/// when `g'` is `g` outside the chunk.
let assemble_heap (g g': Base.heap) (a b: nat)
  : Lemma (requires a <= b /\ b <= Base.heap_size /\ a % 8 == 0 /\ b % 8 == 0 /\ SO.hout g g' a b)
          (ensures tsl3 (CSub.tsl g 0 a) (CSub.tsl g' a b) (CSub.tsl g b Base.heap_size) == reveal g')
  = let h = tsl3 (CSub.tsl g 0 a) (CSub.tsl g' a b) (CSub.tsl g b Base.heap_size) in
    assert (Seq.length h == Base.heap_size);
    let h : Base.heap = h in
    let byte (i: nat{i < Base.heap_size})
      : Lemma (Seq.index h i == (if a <= i && i < b then Seq.index g' i else Seq.index g i))
      = ()
    in
    let word (x: nat) : Lemma (x < Base.heap_size /\ x % 8 == 0 ==>
                               SH.read_word h (U64.uint_to_t x) == SH.read_word g' (U64.uint_to_t x))
      = if x < Base.heap_size && x % 8 = 0 then begin
          let y : Base.hp_addr = U64.uint_to_t x in
          SH.read_word_spec h y;
          SH.read_word_spec g' y;
          SH.read_word_spec g y;
          byte x; byte (x + 1); byte (x + 2); byte (x + 3);
          byte (x + 4); byte (x + 5); byte (x + 6); byte (x + 7);
          if x < a then assert (x + 8 <= a)
          else if x >= b then ()
          else assert (x + 8 <= b)
        end
    in
    FStar.Classical.forall_intro word;
    HE.heap_read_word_ext h g'
#pop-options

let assemble_seq (#t: Type0) (s s': Seq.seq t) (a b: nat)
  : Lemma (requires a <= b /\ b <= Seq.length s /\ Seq.length s' == Seq.length s /\
                    (forall (i: nat). i < Seq.length s /\ (i < a \/ i >= b) ==> Seq.index s' i == Seq.index s i))
          (ensures tsl3 (CSub.tsl s 0 a) (CSub.tsl s' a b) (CSub.tsl s b (Seq.length s)) == s')
  = Seq.lemma_eq_intro (tsl3 (CSub.tsl s 0 a) (CSub.tsl s' a b) (CSub.tsl s b (Seq.length s))) s'

let tsl3_len (#t: Type0) (s s': Seq.seq t) (lo hi n: nat)
  : Lemma (requires lo <= hi /\ hi <= n /\ Seq.length s == n /\ Seq.length s' == hi - lo)
          (ensures Seq.length (tsl3 (CSub.tsl s 0 lo) s' (CSub.tsl s hi n)) == n)
  = ()

let tsl3_index (#t: Type0) (s s': Seq.seq t) (lo hi n: nat) (i: nat)
  : Lemma (requires lo <= hi /\ hi <= n /\ Seq.length s == n /\ Seq.length s' == hi - lo /\ i < n)
          (ensures Seq.length (tsl3 (CSub.tsl s 0 lo) s' (CSub.tsl s hi n)) == n /\
                   Seq.index (tsl3 (CSub.tsl s 0 lo) s' (CSub.tsl s hi n)) i ==
                   (if i < lo then Seq.index s i else if i < hi then Seq.index s' (i - lo) else Seq.index s i))
  = let a = CSub.tsl s 0 lo in
    let r = Seq.append s' (CSub.tsl s hi n) in
    if i < lo then Seq.lemma_index_app1 a r i
    else begin
      Seq.lemma_index_app2 a r i;
      if i < hi then Seq.lemma_index_app1 s' (CSub.tsl s hi n) (i - lo)
      else Seq.lemma_index_app2 s' (CSub.tsl s hi n) (i - lo)
    end

/// The records of the chunk's pages, as a range.
let rng_slice (s: Seq.seq prec) (ep: U64.t) (pm: page_map) (lo hi: nat)
  : Lemma (requires pm_rel s ep pm /\ lo <= hi /\ hi <= n_pages /\
                    (forall (i: nat). i < n_pages ==> U64.v (Seq.index s i).sep <= U64.v ep))
          (ensures rng_rel (CSub.tsl s lo hi) ep lo hi pm)
  = ()

/// The records back, with the chunk's from `s'`.
let rng_back (s s': Seq.seq prec) (ep: U64.t) (pm pm': page_map) (lo hi: nat)
  : Lemma (requires pm_rel s ep pm /\ rng_rel s' ep lo hi pm' /\ lo <= hi /\ hi <= n_pages /\
                    (forall (i: nat). i < n_pages ==> U64.v (Seq.index s i).sep <= U64.v ep) /\
                    (forall (j: nat{j < n_pages}). j < lo \/ j >= hi ==> entry pm' j == entry pm j))
          (ensures (let s2 = tsl3 (CSub.tsl s 0 lo) s' (CSub.tsl s hi n_pages) in
                    pm_rel s2 ep pm' /\ (forall (i: nat). i < n_pages ==> U64.v (Seq.index s2 i).sep <= U64.v ep)))
  = let s2 = tsl3 (CSub.tsl s 0 lo) s' (CSub.tsl s hi n_pages) in
    tsl3_len s s' lo hi n_pages;
    let at (i: nat{i < n_pages})
      : Lemma (view (to_pinfo ep (Seq.index s2 i)) == entry pm' i /\ U64.v (Seq.index s2 i).sep <= U64.v ep)
      = tsl3_index s s' lo hi n_pages i
    in
    FStar.Classical.forall_intro at

/// ---------------------------------------------------------------------------
/// The state between chunks
/// ---------------------------------------------------------------------------

/// Chunk `c`'s record's first word.
noextract
let poff (c: nat) : nat = c * pw

noextract
let qat (q: Seq.seq U64.t) (i: nat) : U64.t = if i < Seq.length q then Seq.index q i else 0UL

/// No page of `[lo, hi)` below `mf` is free.
let free_ge (pm: page_map) (lo hi: nat) (mf: nat) : prop =
  forall (j: nat{j < n_pages}). lo <= j /\ j < hi /\ (entry pm j).kind == Free ==> j >= mf

/// Each fragment's tail is a page of its class.
let tails_in (f: pstate) (pm: page_map) : prop =
  forall (d: nat{d < n_cls}). SSp.at f.atail d <> 0UL ==>
    U64.v (SSp.at f.atail d) >= 1 /\ U64.v (SSp.at f.atail d) - 1 < n_pages /\
    (entry pm (U64.v (SSp.at f.atail d) - 1)).kind == Pool d

/// Chunk `k` is done: its record holds its fragments and lowest free page.
let chunk_done (w0: Base.heap) (pm0: page_map) (b: Seq.seq U64.t) (k: nat) (pm: page_map) (q: Seq.seq U64.t) : prop =
  let fo = SCh.frag w0 pm0 b k in
  let mf = U64.v (qat q (poff k + o_mf)) in
  frag_rel (CSub.tsl q (poff k) (poff k + pw)) (fst fo) (snd fo) mf /\
  free_ge pm (SCh.bnd b k) (SCh.bnd b (k + 1)) mf /\ tails_in (fst fo) pm

/// **The state before chunk `c`**: the real heap and bitmap stand for the
/// chunks before `c`, swept one after another (`SweepChunks.chunks`);
/// nothing from chunk `c` on has changed; and the chunks before `c` are done.
let drv_ok (g: Base.heap) (bs: Seq.seq U32.t) (pm0: page_map) (b: Seq.seq U64.t) (n: nat) (ep: U64.t) (c: nat)
           (gc: Base.heap) (bsc: Seq.seq U32.t) (sc: Seq.seq prec) (pmc: page_map) (qc: Seq.seq U64.t) : prop =
  let w0 = BM.with_marks g bs in
  c <= n /\
  BM.with_marks gc bsc == fst (SCh.chunks w0 pm0 b c) /\ pmc == snd (SCh.chunks w0 pm0 b c) /\
  pm_rel sc ep pmc /\ (forall (i: nat). i < n_pages ==> U64.v (Seq.index sc i).sep <= U64.v ep) /\
  SO.hout g gc (page_base 0) (page_base (SCh.bnd b c)) /\
  words_out bs bsc 0 (SCh.bnd b c) /\
  (forall (j: nat{j < n_pages}). j >= SCh.bnd b c ==> entry pmc j == entry pm0 j) /\
  CSw.no_marks bsc (page_base 0) (page_base (SCh.bnd b c)) /\
  Seq.length qc == poff n /\ Seq.length bsc == BM.bm_len /\
  (forall (k: nat). k < c ==> chunk_done w0 pm0 b k pmc qc)

/// What the whole sweep needs at the start.
let start_ok (g: Base.heap) (bs: Seq.seq U32.t) (pm0: page_map) (b: Seq.seq U64.t) (n: nat) (w: Seq.seq U64.t) : prop =
  map_ok pm0 /\ CP.bounds_good pm0 b n /\ cw_ok w /\ Seq.length bs == BM.bm_len /\
  CSw.marks_from g bs pm0 0 n_pages /\ n >= 1 /\ n <= 256

/// The marks the bitmap holds from page `lo` on are the start's.
let marks_from_words (bs b: Seq.seq U32.t) (lo: nat) (x: nat)
  : Lemma (requires words_out bs b 0 lo /\ Seq.length bs == BM.bm_len /\ x >= page_base lo /\ lo <= n_pages)
          (ensures BM.marked b x == BM.marked bs x)
  = if BM.in_pages x then begin
      BM.bpp_mul ();
      let i = BM.page_of_word x in
      FStar.Math.Lemmas.lemma_div_mod (x - BM.zw) page_bytes;
      if i < lo then page_base_mono (i + 1) lo;
      BM.widx_page i x;
      FStar.Math.Lemmas.lemma_mult_le_right BM.bpp lo i
    end

/// **What chunk `c` needs**, from the state before it.
let chunk_pre_of (g: Base.heap) (bs: Seq.seq U32.t) (pm0: page_map) (b: Seq.seq U64.t) (n: nat) (ep: U64.t) (c: nat)
                 (w: Seq.seq U64.t) (gc: Base.heap) (bsc: Seq.seq U32.t) (sc: Seq.seq prec) (pmc: page_map) (qc: Seq.seq U64.t)
  : Lemma (requires start_ok g bs pm0 b n w /\ drv_ok g bs pm0 b n ep c gc bsc sc pmc qc /\ c < n)
          (ensures CP.chunk_pre w gc bsc pmc (SCh.bnd b c) (SCh.bnd b (c + 1)))
  = let lo = SCh.bnd b c in
    let hi = SCh.bnd b (c + 1) in
    SCh.bounds_at pm0 b n c;
    SCh.chunks_map_ok (BM.with_marks g bs) pm0 b c;
    SRg.wreach_kinds pmc pm0 lo hi;
    let mk (x: nat) : Lemma (x >= page_base lo ==> BM.marked bsc x == BM.marked bs x)
      = if x >= page_base lo then marks_from_words bs bsc lo x
    in
    FStar.Classical.forall_intro mk;
    let sub (j: nat{j < n_pages}) : Lemma (lo <= j /\ j < hi ==> CSw.unit_marks g bs pm0 j) = () in
    FStar.Classical.forall_intro sub;
    CSw.marks_frame g gc bs bsc pm0 pmc lo hi

/// The record of an earlier chunk is kept when chunk `c`'s is put back.
let rec_keep (qc q_c: Seq.seq U64.t) (n c k: nat)
  : Lemma (requires Seq.length qc == poff n /\ Seq.length q_c == pw /\ c < n /\ k < c)
          (ensures (let qc' = tsl3 (CSub.tsl qc 0 (poff c)) q_c (CSub.tsl qc (poff c + pw) (poff n)) in
                    CSub.tsl qc' (poff k) (poff k + pw) == CSub.tsl qc (poff k) (poff k + pw) /\
                    qat qc' (poff k + o_mf) == qat qc (poff k + o_mf)))
  = FStar.Math.Lemmas.lemma_mult_le_right pw (k + 1) c;
    FStar.Math.Lemmas.lemma_mult_le_right pw (c + 1) n;
    let qc' = tsl3 (CSub.tsl qc 0 (poff c)) q_c (CSub.tsl qc (poff c + pw) (poff n)) in
    tsl3_len qc q_c (poff c) (poff c + pw) (poff n);
    let ix (i: nat) : Lemma (i < c * pw ==> Seq.index qc' i == Seq.index qc i)
      = if i < c * pw then tsl3_index qc q_c (poff c) (poff c + pw) (poff n) i
    in
    FStar.Classical.forall_intro ix;
    Seq.lemma_eq_intro (CSub.tsl qc' (poff k) (poff k + pw)) (CSub.tsl qc (poff k) (poff k + pw))

/// Chunk `c`'s record, put back.
let rec_new (qc q_c: Seq.seq U64.t) (n c: nat)
  : Lemma (requires Seq.length qc == poff n /\ Seq.length q_c == pw /\ c < n)
          (ensures (let qc' = tsl3 (CSub.tsl qc 0 (poff c)) q_c (CSub.tsl qc (poff c + pw) (poff n)) in
                    Seq.length qc' == poff n /\
                    CSub.tsl qc' (poff c) (poff c + pw) == q_c /\
                    qat qc' (poff c + o_mf) == Seq.index q_c o_mf))
  = FStar.Math.Lemmas.lemma_mult_le_right pw (c + 1) n;
    let qc' = tsl3 (CSub.tsl qc 0 (poff c)) q_c (CSub.tsl qc (poff c + pw) (poff n)) in
    tsl3_len qc q_c (poff c) (poff c + pw) (poff n);
    let ix (i: nat) : Lemma (c * pw <= i /\ i < c * pw + pw ==> Seq.index qc' i == Seq.index q_c (i - c * pw))
      = if c * pw <= i && i < c * pw + pw then tsl3_index qc q_c (poff c) (poff c + pw) (poff n) i
    in
    FStar.Classical.forall_intro ix;
    w_small ();
    Seq.lemma_eq_intro (CSub.tsl qc' (poff c) (poff c + pw)) q_c

/// Earlier chunks stay done.
let done_keep (w0: Base.heap) (pm0: page_map) (b: Seq.seq U64.t) (n: nat) (k c: nat)
              (pm pm': page_map) (q q': Seq.seq U64.t)
  : Lemma (requires SCh.bounds_ok pm0 b n /\ k < c /\ c < n /\ chunk_done w0 pm0 b k pm q /\
                    CSub.tsl q' (poff k) (poff k + pw) == CSub.tsl q (poff k) (poff k + pw) /\
                    qat q' (poff k + o_mf) == qat q (poff k + o_mf) /\
                    (forall (j: nat{j < n_pages}). j < SCh.bnd b c ==> entry pm' j == entry pm j))
          (ensures chunk_done w0 pm0 b k pm' q')
  = SCh.frag_ok w0 pm0 b n k;
    SCh.bnd_mono pm0 b n (k + 1) c

/// The new chunk is done.
let done_new (w0: Base.heap) (pm0: page_map) (b: Seq.seq U64.t) (n: nat) (c: nat)
             (gc: Base.heap) (bsc: Seq.seq U32.t) (pmc: page_map) (st': pstate) (ol': U64.t) (mf': nat)
             (q': Seq.seq U64.t) (q_c: Seq.seq U64.t)
  : Lemma (requires SCh.bounds_ok pm0 b n /\ c < n /\
                    BM.with_marks gc bsc == fst (SCh.chunks w0 pm0 b c) /\ pmc == snd (SCh.chunks w0 pm0 b c) /\
                    (let tt = SRg.crange (BM.with_marks gc bsc) (SCh.zst pmc) 0UL (SCh.bnd b c) (SCh.bnd b (c + 1)) in
                     st' == SRg.cs tt /\ ol' == SRg.co tt) /\
                    CSw.free0_ge pmc (SCh.bnd b c) (SCh.bnd b (c + 1)) mf' /\
                    newfree_ge pmc st'.pm (SCh.bnd b c) (SCh.bnd b (c + 1)) mf' /\
                    frag_rel q_c st' ol' mf' /\
                    CSub.tsl q' (poff c) (poff c + pw) == q_c /\ qat q' (poff c + o_mf) == Seq.index q_c o_mf)
          (ensures chunk_done w0 pm0 b c st'.pm q')
  = SCh.frag_ok w0 pm0 b n c

let words_compose (bs bsc bs': Seq.seq U32.t) (a b c: nat)
  : Lemma (requires words_out bs bsc a b /\ words_out bsc bs' b c /\ a <= b /\ b <= c)
          (ensures words_out bs bs' a c)
  = FStar.Math.Lemmas.lemma_mult_le_right BM.bpp a b;
    FStar.Math.Lemmas.lemma_mult_le_right BM.bpp b c

/// Earlier chunks stay done, all of them.
let done_all (w0: Base.heap) (pm0: page_map) (b: Seq.seq U64.t) (n: nat) (c: nat)
             (pm pm': page_map) (q q_c: Seq.seq U64.t)
  : Lemma (requires SCh.bounds_ok pm0 b n /\ c < n /\ Seq.length q == poff n /\ Seq.length q_c == pw /\
                    (forall (k: nat). k < c ==> chunk_done w0 pm0 b k pm q) /\
                    (forall (j: nat{j < n_pages}). j < SCh.bnd b c ==> entry pm' j == entry pm j))
          (ensures (let q' = tsl3 (CSub.tsl q 0 (poff c)) q_c (CSub.tsl q (poff c + pw) (poff n)) in
                    forall (k: nat). k < c ==> chunk_done w0 pm0 b k pm' q'))
  = let q' = tsl3 (CSub.tsl q 0 (poff c)) q_c (CSub.tsl q (poff c + pw) (poff n)) in
    let one (k: nat) : Lemma (k < c ==> chunk_done w0 pm0 b k pm' q')
      = if k < c then begin
          rec_keep q q_c n c k;
          done_keep w0 pm0 b n k c pm pm' q q'
        end
    in
    FStar.Classical.forall_intro one

let done_combine (w0: Base.heap) (pm0: page_map) (b: Seq.seq U64.t) (c: nat) (pm' pm'': page_map) (q': Seq.seq U64.t)
  : Lemma (requires (forall (k: nat). k < c ==> chunk_done w0 pm0 b k pm' q') /\ chunk_done w0 pm0 b c pm'' q' /\ pm' == pm'')
          (ensures forall (k: nat). k < c + 1 ==> chunk_done w0 pm0 b k pm' q')
  = ()

/// What chunk `c` leaves, in the form the step needs.
let chunk_out (gc: Base.heap) (bsc: Seq.seq U32.t) (pmc: page_map) (lo hi: nat) (ep: U64.t)
              (g': Base.heap) (bs': Seq.seq U32.t) (s': Seq.seq prec) (pm': page_map) (q_c: Seq.seq U64.t) : prop =
  CP.chunk_res gc bsc pmc lo hi g' bs' pm' q_c /\ rng_rel s' ep lo hi pm'

#push-options "--z3rlimit 40"
/// **The driver's step**: after chunk `c`, with its ranges put back.
let drv_step (g: Base.heap) (bs: Seq.seq U32.t) (pm0: page_map) (b: Seq.seq U64.t) (n: nat) (ep: U64.t) (c: nat)
             (w: Seq.seq U64.t) (gc: Base.heap) (bsc: Seq.seq U32.t) (sc: Seq.seq prec) (pmc: page_map) (qc: Seq.seq U64.t)
             (g': Base.heap) (bs': Seq.seq U32.t) (s': Seq.seq prec) (pm': page_map) (q_c: Seq.seq U64.t)
  : Lemma (requires start_ok g bs pm0 b n w /\ drv_ok g bs pm0 b n ep c gc bsc sc pmc qc /\ c < n /\
                    chunk_out gc bsc pmc (SCh.bnd b c) (SCh.bnd b (c + 1)) ep g' bs' s' pm' q_c /\
                    Seq.length q_c == pw)
          (ensures (let lo = SCh.bnd b c in
                    let hi = SCh.bnd b (c + 1) in
                    drv_ok g bs pm0 b n ep (c + 1) g' bs'
                           (tsl3 (CSub.tsl sc 0 lo) s' (CSub.tsl sc hi n_pages)) pm'
                           (tsl3 (CSub.tsl qc 0 (poff c)) q_c (CSub.tsl qc (poff c + pw) (poff n)))))
  = let lo = SCh.bnd b c in
    let hi = SCh.bnd b (c + 1) in
    let w0 = BM.with_marks g bs in
    SCh.bounds_at pm0 b n c;
    SCh.bnd_mono pm0 b n (c + 1) n;
    SCh.chunks_unfold w0 pm0 b c;
    eliminate exists (st': pstate) (ol': U64.t) (mf': nat).
      CSw.chunk_post gc bsc pmc lo hi g' bs' st' ol' mf' /\ pm' == st'.pm /\ frag_rel q_c st' ol' mf' /\
      newfree_ge pmc st'.pm lo hi mf' /\ mf' <= n_pages
    with begin
      let sc' = tsl3 (CSub.tsl sc 0 lo) s' (CSub.tsl sc hi n_pages) in
      let qc' = tsl3 (CSub.tsl qc 0 (poff c)) q_c (CSub.tsl qc (poff c + pw) (poff n)) in
      rng_back sc s' ep pmc pm' lo hi;
      page_base_mono 0 lo;
      page_base_mono lo hi;
      words_compose bs bsc bs' 0 lo hi;
      rec_new qc q_c n c;
      done_all w0 pm0 b n c pmc pm' qc q_c;
      done_new w0 pm0 b n c gc bsc pmc st' ol' mf' qc' q_c;
      let nm (x: nat) : Lemma (page_base 0 <= x /\ x < page_base hi ==> not (BM.marked bs' x))
        = if page_base 0 <= x && x < page_base lo then assert (BM.marked bs' x == BM.marked bsc x)
      in
      FStar.Classical.forall_intro nm;
      let w1 = fst (SCh.chunks w0 pm0 b (c + 1)) in
      assert (BM.with_marks g' bs' == w1);
      assert (pm' == snd (SCh.chunks w0 pm0 b (c + 1)));
      assert (SO.hout g g' (page_base 0) (page_base hi));
      assert (forall (j: nat{j < n_pages}). j >= hi ==> entry pm' j == entry pm0 j);
      assert (CSw.no_marks bs' (page_base 0) (page_base hi));
      assert (Seq.length bs' == BM.bm_len);
      done_combine w0 pm0 b c pm' st'.pm qc'
    end
#pop-options

let drv_start (g: Base.heap) (bs: Seq.seq U32.t) (pm0: page_map) (b: Seq.seq U64.t) (n: nat) (ep: U64.t)
              (w: Seq.seq U64.t) (s0: Seq.seq prec) (q0: Seq.seq U64.t)
  : Lemma (requires start_ok g bs pm0 b n w /\ pm_rel s0 ep pm0 /\
                    (forall (i: nat). i < n_pages ==> U64.v (Seq.index s0 i).sep <= U64.v ep) /\
                    Seq.length q0 == poff n)
          (ensures drv_ok g bs pm0 b n ep 0 g bs s0 pm0 q0)
  = SCh.chunks_zero (BM.with_marks g bs) pm0 b;
    words_out_refl bs 0 (SCh.bnd b 0)

/// The first bitmap word of page `x`.
noextract
let bw (x: nat) : nat = x * BM.bpp

/// The bounds of chunk `c`'s pieces.
let pieces (b: Seq.seq U64.t) (pm0: page_map) (n c: nat)
  : Lemma (requires SCh.bounds_ok pm0 b n /\ c < n)
          (ensures (let lo = SCh.bnd b c in let hi = SCh.bnd b (c + 1) in
                    lo <= hi /\ hi <= n_pages /\
                    page_base lo <= page_base hi /\ page_base hi <= Base.heap_size /\
                    bw lo <= bw hi /\ bw hi <= BM.bm_len /\
                    poff c + pw <= poff n))
  = SCh.bounds_at pm0 b n c;
    SCh.bnd_mono pm0 b n (c + 1) n;
    page_base_mono (SCh.bnd b c) (SCh.bnd b (c + 1));
    pages_in_heap (SCh.bnd b (c + 1));
    bm_len_ok (SCh.bnd b c) (SCh.bnd b (c + 1));
    FStar.Math.Lemmas.lemma_mult_le_right pw (c + 1) n

let hsl_tsl (g: Base.heap) (lo hi: nat)
  : Lemma (requires lo <= hi /\ hi <= n_pages)
          (ensures CSub.tsl g (page_base lo) (page_base hi) == CP.hsl g lo hi)
  = pages_in_heap hi; page_base_mono lo hi

let bsl_tsl (bs: Seq.seq U32.t) (i j: nat) : Lemma (CSub.tsl bs i j == bsl bs i j) = ()


let res_facts (gc: Base.heap) (bsc: Seq.seq U32.t) (pmc: page_map) (lo hi: nat)
              (g': Base.heap) (bs': Seq.seq U32.t) (pm': page_map) (q: Seq.seq U64.t)
  : Lemma (requires CP.chunk_res gc bsc pmc lo hi g' bs' pm' q)
          (ensures SO.hout gc g' (page_base lo) (page_base hi) /\ words_out bsc bs' lo hi /\ Seq.length q == pw /\
                   (forall (j: nat{j < n_pages}). j < lo \/ j >= hi ==> entry pm' j == entry pmc j))
  = ()

let words_index (bs b: Seq.seq U32.t) (lo hi: nat)
  : Lemma (requires words_out bs b lo hi)
          (ensures Seq.length b == Seq.length bs /\
                   (forall (i: nat). i < Seq.length bs /\ (i < bw lo \/ i >= bw hi) ==> Seq.index b i == Seq.index bs i))
  = ()

/// Chunk `vc`, with its pieces cut out and put back.
fn chunk_iter (heap: heap_t) (t: pstate_t) (bm: A.array U32.t) (parts: A.array U64.t) (bounds: A.array U64.t)
  (nc vc: U64.t)
  (#g: erased Base.heap) (#bs: erased (Seq.seq U32.t)) (#w: erased (Seq.seq U64.t))
  (#bb: erased (Seq.seq U64.t)) (#pm0: erased page_map) (#pb: perm)
  (#gc: erased Base.heap) (#bsc: erased (Seq.seq U32.t)) (#sc: erased (Seq.seq prec)) (#qc: erased (Seq.seq U64.t))
  requires is_heap heap gc ** A.pts_to t.tpm sc ** A.pts_to t.tw w ** A.pts_to bm bsc ** A.pts_to parts qc **
           A.pts_to bounds #pb bb **
           pure (start_ok g bs pm0 bb (U64.v nc) w /\ U64.v vc < U64.v nc /\
                 drv_ok g bs pm0 bb (U64.v nc) (ep_of w) (U64.v vc) gc bsc sc
                        (snd (SCh.chunks (BM.with_marks g bs) pm0 bb (U64.v vc))) qc)
  ensures exists* gc' bsc' sc' qc'.
          is_heap heap gc' ** A.pts_to t.tpm sc' ** A.pts_to t.tw w ** A.pts_to bm bsc' ** A.pts_to parts qc' **
          A.pts_to bounds #pb bb **
          pure (drv_ok g bs pm0 bb (U64.v nc) (ep_of w) (U64.v vc + 1) gc' bsc' sc'
                       (snd (SCh.chunks (BM.with_marks g bs) pm0 bb (U64.v vc + 1))) qc')
{
  let ep = Ghost.hide (ep_of w);
  let w0 = Ghost.hide (BM.with_marks g bs);
    let pmc = Ghost.hide (snd (SCh.chunks w0 pm0 bb (U64.v vc)));
    chunk_pre_of g bs pm0 bb (U64.v nc) ep (U64.v vc) w gc bsc sc pmc qc;
    let lo = Ghost.hide (SCh.bnd bb (U64.v vc));
    let hi = Ghost.hide (SCh.bnd bb (U64.v vc + 1));
    pieces bb pm0 (U64.v nc) (U64.v vc);
    (* cut out the chunk's pieces *)
    unfold is_heap;
    CSub.split3 heap.data (page_base lo) (page_base hi);
    hsl_tsl gc lo hi;
    rewrite (pts_to_range heap.data (page_base lo) (page_base hi) (CSub.tsl gc (page_base lo) (page_base hi)))
         as (CP.rng_heap heap lo hi gc);
    CSub.split3 t.tpm lo hi;
    rng_slice sc ep pmc lo hi;
    fold (CP.rng_pm t lo hi ep pmc);
    CSub.split3 bm (bw lo) (bw hi);
    bsl_tsl bsc (bw lo) (bw hi);
    rewrite (pts_to_range bm (bw lo) (bw hi) (CSub.tsl bsc (bw lo) (bw hi)))
         as (pts_to_range bm (bw lo) (bw hi) (bsl bsc (bw lo) (bw hi)));
    fold (ch_bm bm lo hi bsc);
    CSub.split3 parts (poff (U64.v vc)) (poff (U64.v vc) + pw);
    FStar.Math.Lemmas.pow2_lt_compat 64 9;
    let sc_ = SZ.uint64_to_sizet vc;
    CSub.range_idx parts #(poff (U64.v vc)) #(poff (U64.v vc) + pw) (SZ.v sc_ * pw) (SZ.v sc_ * pw + pw);
    rewrite (CP.rng_heap heap lo hi gc) as (CP.rng_heap heap (SCh.bnd bb (SZ.v sc_)) (SCh.bnd bb (SZ.v sc_ + 1)) gc);
    rewrite (CP.rng_pm t lo hi ep pmc) as (CP.rng_pm t (SCh.bnd bb (SZ.v sc_)) (SCh.bnd bb (SZ.v sc_ + 1)) (ep_of w) pmc);
    rewrite (ch_bm bm lo hi bsc) as (ch_bm bm (SCh.bnd bb (SZ.v sc_)) (SCh.bnd bb (SZ.v sc_ + 1)) bsc);
    (* the chunk *)
    CP.sweep_chunk heap t bm parts bounds sc_ #pb #bb #1.0R #w #gc #bsc #pmc;
    with g' bs' pm' q_c. assert (CP.rng_heap heap (SCh.bnd bb (SZ.v sc_)) (SCh.bnd bb (SZ.v sc_ + 1)) g' **
                                ch_bm bm (SCh.bnd bb (SZ.v sc_)) (SCh.bnd bb (SZ.v sc_ + 1)) bs' **
                                CP.rng_pm t (SCh.bnd bb (SZ.v sc_)) (SCh.bnd bb (SZ.v sc_ + 1)) (ep_of w) pm' **
                                pts_to_range parts (SZ.v sc_ * pw) (SZ.v sc_ * pw + pw) q_c);
    (* put the pieces back *)
    rewrite (CP.rng_heap heap (SCh.bnd bb (SZ.v sc_)) (SCh.bnd bb (SZ.v sc_ + 1)) g') as (CP.rng_heap heap lo hi g');
    unfold CP.rng_heap;
    hsl_tsl g' lo hi;
    rewrite (pts_to_range heap.data (page_base lo) (page_base hi) (CP.hsl g' lo hi))
         as (pts_to_range heap.data (page_base lo) (page_base hi) (CSub.tsl g' (page_base lo) (page_base hi)));
    CSub.join3 heap.data (page_base lo) (page_base hi) Base.heap_size;
    res_facts gc bsc pmc lo hi g' bs' pm' q_c;
    page_base_aligned lo;
    page_base_aligned hi;
    assemble_heap gc g' (page_base lo) (page_base hi);
    rewrite (A.pts_to heap.data (tsl3 (CSub.tsl gc 0 (page_base lo)) (CSub.tsl g' (page_base lo) (page_base hi))
                                      (CSub.tsl gc (page_base hi) Base.heap_size)))
         as (A.pts_to heap.data g');
    fold (is_heap heap g');
    (* the page records *)
    rewrite (CP.rng_pm t (SCh.bnd bb (SZ.v sc_)) (SCh.bnd bb (SZ.v sc_ + 1)) (ep_of w) pm') as (CP.rng_pm t lo hi ep pm');
    unfold CP.rng_pm;
    with s'. assert (pts_to_range t.tpm lo hi s');
    CSub.join3 t.tpm lo hi n_pages;
    rng_back sc s' ep pmc pm' lo hi;
    (* the bitmap *)
    rewrite (ch_bm bm (SCh.bnd bb (SZ.v sc_)) (SCh.bnd bb (SZ.v sc_ + 1)) bs') as (ch_bm bm lo hi bs');
    unfold ch_bm;
    bsl_tsl bs' (bw lo) (bw hi);
    rewrite (pts_to_range bm (lo * BM.bpp) (hi * BM.bpp) (bsl bs' (lo * BM.bpp) (hi * BM.bpp)))
         as (pts_to_range bm (bw lo) (bw hi) (CSub.tsl bs' (bw lo) (bw hi)));
    CSub.join3 bm (bw lo) (bw hi) BM.bm_len;
    words_index bsc bs' lo hi;
    assemble_seq bsc bs' (bw lo) (bw hi);
    rewrite (A.pts_to bm (tsl3 (CSub.tsl bsc 0 (bw lo)) (CSub.tsl bs' (bw lo) (bw hi)) (CSub.tsl bsc (bw hi) BM.bm_len)))
         as (A.pts_to bm bs');
    (* the records *)
    CSub.range_idx parts #(SZ.v sc_ * pw) #(SZ.v sc_ * pw + pw) (poff (U64.v vc)) (poff (U64.v vc) + pw);
    CSub.join3 parts (poff (U64.v vc)) (poff (U64.v vc) + pw) (poff (U64.v nc));
    drv_step g bs pm0 bb (U64.v nc) ep (U64.v vc) w gc bsc sc pmc qc g' bs' s' pm' q_c;
  ()
}

/// **The chunks, one after another.**
fn chunks_seq (heap: heap_t) (t: pstate_t) (bm: A.array U32.t) (parts: A.array U64.t) (bounds: A.array U64.t)
  (nc: U64.t)
  (#g: erased Base.heap) (#bs: erased (Seq.seq U32.t)) (#s0: erased (Seq.seq prec)) (#w: erased (Seq.seq U64.t))
  (#q0: erased (Seq.seq U64.t)) (#bb: erased (Seq.seq U64.t)) (#pm0: erased page_map) (#pb: perm)
  requires is_heap heap g ** A.pts_to t.tpm s0 ** A.pts_to t.tw w ** A.pts_to bm bs ** A.pts_to parts q0 **
           A.pts_to bounds #pb bb **
           pure (start_ok g bs pm0 bb (U64.v nc) w /\ pm_rel s0 (ep_of w) pm0 /\
                 (forall (i: nat). i < n_pages ==> U64.v (Seq.index s0 i).sep <= U64.v (ep_of w)) /\
                 Seq.length q0 == poff (U64.v nc))
  ensures exists* gn bsn sn qn.
          is_heap heap gn ** A.pts_to t.tpm sn ** A.pts_to t.tw w ** A.pts_to bm bsn ** A.pts_to parts qn **
          A.pts_to bounds #pb bb **
          pure (drv_ok g bs pm0 bb (U64.v nc) (ep_of w) (U64.v nc) gn bsn sn
                       (snd (SCh.chunks (BM.with_marks g bs) pm0 bb (U64.v nc))) qn)
{
  let ep = Ghost.hide (ep_of w);
  let w0 = Ghost.hide (BM.with_marks g bs);
  drv_start g bs pm0 bb (U64.v nc) ep w s0 q0;
  SCh.chunks_zero w0 pm0 bb;
  let mut c = 0UL;
  while (U64.lt !c nc)
    invariant exists* vc gc bsc sc qc.
      R.pts_to c vc ** is_heap heap gc ** A.pts_to t.tpm sc ** A.pts_to t.tw w ** A.pts_to bm bsc **
      A.pts_to parts qc ** A.pts_to bounds #pb bb **
      pure (U64.v vc <= U64.v nc /\
            drv_ok g bs pm0 bb (U64.v nc) ep (U64.v vc) gc bsc sc (snd (SCh.chunks w0 pm0 bb (U64.v vc))) qc)
    decreases (U64.v nc - U64.v !c)
  {
    let vc = !c;
    chunk_iter heap t bm parts bounds nc vc #g #bs #w #bb #pm0 #pb;
    c := U64.add vc 1UL
  };
  with vc gc bsc sc qc. assert (R.pts_to c vc ** is_heap heap gc ** A.pts_to t.tpm sc ** A.pts_to bm bsc ** A.pts_to parts qc);
  let vcf = !c;
  assert (pure (vcf == nc));
  ()
}

/// ---------------------------------------------------------------------------
/// After the chunks
/// ---------------------------------------------------------------------------

/// Every page lies in a chunk.
let rec tile (pm0: page_map) (b: Seq.seq U64.t) (n: nat) (k: nat) (j: nat)
  : Lemma (requires SCh.bounds_ok pm0 b n /\ k <= n /\ SCh.bnd b k <= j /\ j < n_pages)
          (ensures exists (c: nat). k <= c /\ c < n /\ SCh.bnd b c <= j /\ j < SCh.bnd b (c + 1))
          (decreases (n - k))
  = if k = n then ()
    else if j < SCh.bnd b (k + 1) then ()
    else tile pm0 b n (k + 1) j

/// No page below `h` is free, when `h` is at most every chunk's lowest free
/// page.
let hint_ok (w0: Base.heap) (pm0: page_map) (b: Seq.seq U64.t) (n: nat) (pm: page_map) (q: Seq.seq U64.t) (h: nat)
  : Lemma (requires SCh.bounds_ok pm0 b n /\ (forall (k: nat). k < n ==> chunk_done w0 pm0 b k pm q) /\
                    (forall (k: nat). k < n ==> h <= U64.v (qat q (poff k + o_mf))))
          (ensures none_free_below pm h)
  = let aux (j: nat{j < n_pages}) : Lemma (j < h ==> ~((entry pm j).kind == Free))
      = if j < h then begin
          tile pm0 b n 0 j;
          eliminate exists (c: nat). 0 <= c /\ c < n /\ SCh.bnd b c <= j /\ j < SCh.bnd b (c + 1)
          with assert (chunk_done w0 pm0 b c pm q)
        end
    in
    FStar.Classical.forall_intro aux

/// No mark anywhere: the bitmap is all zero, and the heap is the one it
/// stood for.
let all_zero (bs: Seq.seq U32.t)
  : Lemma (requires Seq.length bs == BM.bm_len /\ CSw.no_marks bs (page_base 0) (page_base n_pages))
          (ensures bs == Seq.create BM.bm_len 0ul)
  = BM.bpp_mul ();
    let w (j: nat{j < BM.bm_len}) : Lemma (Seq.index bs j == 0ul)
      = let i = j / BM.bpp in
        FStar.Math.Lemmas.lemma_div_mod j BM.bpp;
        FStar.Math.Lemmas.lemma_mult_le_right BM.bpp (i + 1) n_pages;
        assert (i < n_pages);
        let none (x: nat) : Lemma (page_base i <= x /\ x < page_base (i + 1) ==> not (BM.marked bs x))
          = if page_base i <= x && x < page_base (i + 1) then begin
              page_base_mono 0 i;
              page_base_mono (i + 1) n_pages
            end
        in
        FStar.Classical.forall_intro none;
        BM.page_words_zero bs i;
        assert (Seq.index (BM.zero_page bs i) j == 0ul)
    in
    FStar.Classical.forall_intro w;
    Seq.lemma_eq_intro bs (Seq.create BM.bm_len 0ul)

let marks_none (g: Base.heap) (bs: Seq.seq U32.t)
  : Lemma (requires CSw.no_marks bs (page_base 0) (page_base n_pages))
          (ensures BM.with_marks g bs == g)
  = let none (a: Base.hp_addr) : Lemma (not (BM.marked bs (U64.v a)))
      = page_base_mono n_pages n_pages
    in
    FStar.Classical.forall_intro none;
    BM.wm_none g (BM.marked bs)

/// The lists the joins build end on pages of their classes.
let rec join_tails (w0: Base.heap) (pm0: page_map) (b: Seq.seq U64.t) (n: nat) (pm: page_map) (q: Seq.seq U64.t) (k: nat)
  : Lemma (requires SCh.bounds_ok pm0 b n /\ k <= n /\ (forall (c: nat). c < n ==> chunk_done w0 pm0 b c pm q))
          (ensures jtails (SCh.ljoin w0 pm0 b k) (SCh.pjoin pm w0 pm0 b k))
          (decreases k)
  = SCh.joins_zero w0 w0 pm pm0 b;
    if k > 0 then begin
      join_tails w0 pm0 b n pm q (k - 1);
      SCh.joins_unfold w0 w0 pm pm0 b (k - 1);
      SCh.ljoin_tails w0 pm0 b n (k - 1);
      let l = SCh.ljoin w0 pm0 b (k - 1) in
      let f = fst (SCh.frag w0 pm0 b (k - 1)) in
      let p = SCh.pjoin pm w0 pm0 b (k - 1) in
      SSp.javail_len l f;
      let kd (j: nat{j < n_pages}) : Lemma ((entry (SSp.jpm p l f) j).kind == (entry p j).kind)
        = SSp.entry_jpm p l f j
      in
      FStar.Classical.forall_intro kd;
      let rec kp (k': nat) : Lemma (requires k' <= n) (ensures forall (j: nat{j < n_pages}). (entry (SCh.pjoin pm w0 pm0 b k') j).kind == (entry pm j).kind) (decreases k')
        = SCh.joins_zero w0 w0 pm pm0 b;
          if k' > 0 then begin
            kp (k' - 1);
            SCh.joins_unfold w0 w0 pm pm0 b (k' - 1);
            let aux (j: nat{j < n_pages})
              : Lemma ((entry (SCh.pjoin pm w0 pm0 b k') j).kind == (entry (SCh.pjoin pm w0 pm0 b (k' - 1)) j).kind)
              = SSp.entry_jpm (SCh.pjoin pm w0 pm0 b (k' - 1)) (SCh.ljoin w0 pm0 b (k' - 1)) (fst (SCh.frag w0 pm0 b (k' - 1))) j
            in
            FStar.Classical.forall_intro aux
          end
      in
      kp (k - 1);
      assert (chunk_done w0 pm0 b (k - 1) pm q)
    end

/// What the finish needs: the chunks done.
let fin_pre (w0: Base.heap) (st0: pstate) (b: Seq.seq U64.t) (n: nat) (w: Seq.seq U64.t)
            (gn: Base.heap) (sn: Seq.seq prec) (pmn: page_map) (qn: Seq.seq U64.t) : prop =
  SCh.empty_st st0 /\ SCh.bounds_ok st0.pm b n /\ n >= 1 /\ n <= 256 /\
  w_ok w st0 /\ U64.v (Seq.index (mt_of w) 1) >= 1 /\
  pm_rel sn (Seq.index (mt_of w) 1) pmn /\
  (forall (i: nat). i < n_pages ==> U64.v (Seq.index sn i).sep <= U64.v (Seq.index (mt_of w) 1)) /\
  gn == fst (SCh.chunks w0 st0.pm b n) /\ pmn == snd (SCh.chunks w0 st0.pm b n) /\
  (forall (k: nat). k < n ==> chunk_done w0 st0.pm b k pmn qn) /\ Seq.length qn == poff n

let hint_step (q: Seq.seq U64.t) (n: nat) (k: nat) (h: U64.t) (x: U64.t)
  : Lemma (requires (forall (k': nat). k' < k ==> U64.v h <= U64.v (qat q (poff k' + o_mf))) /\ x == qat q (poff k + o_mf))
          (ensures (let h' = if U64.lt x h then x else h in
                    forall (k': nat). k' < k + 1 ==> U64.v h' <= U64.v (qat q (poff k' + o_mf))))
  = ()

let start_join (gn w0: Base.heap) (st0: pstate) (b: Seq.seq U64.t) (pmn: page_map)
  : Lemma (requires SCh.empty_st st0)
          (ensures SCh.hjoin gn w0 st0.pm b 0 == gn /\
                   SCh.with_pm (SCh.ljoin w0 st0.pm b 0) (SCh.pjoin pmn w0 st0.pm b 0) == { st0 with pm = pmn })
  = SCh.joins_zero gn w0 pmn st0.pm b

ghost fn ih_eq (heap: heap_t) (g1 g2: Base.heap)
  requires is_heap heap g1 ** pure (g1 == g2)
  ensures is_heap heap g2
{
  rewrite (is_heap heap g1) as (is_heap heap g2)
}

/// One join, in the joins' terms.
let join_eq (w0 gn: Base.heap) (pm0 pmn: page_map) (b: Seq.seq U64.t) (k: nat)
  : Lemma (let st = SCh.with_pm (SCh.ljoin w0 pm0 b k) (SCh.pjoin pmn w0 pm0 b k) in
           let fo = SCh.frag w0 pm0 b k in
           SSp.jstep (SCh.hjoin gn w0 pm0 b k) st (fst fo) (snd fo) ==
           (SCh.hjoin gn w0 pm0 b (k + 1), SCh.with_pm (SCh.ljoin w0 pm0 b (k + 1)) (SCh.pjoin pmn w0 pm0 b (k + 1))))
  = let st = SCh.with_pm (SCh.ljoin w0 pm0 b k) (SCh.pjoin pmn w0 pm0 b k) in
    let f = fst (SCh.frag w0 pm0 b k) in
    SCh.joins_unfold gn w0 pmn pm0 b k;
    SCh.jst_cong (SCh.pjoin pmn w0 pm0 b k) st (SCh.ljoin w0 pm0 b k) f f

/// The finish's lists, before chunk `k` is joined.
let fin_rel (w0 gn: Base.heap) (pm0 pmn: page_map) (b: Seq.seq U64.t) (k: nat) (g: Base.heap) (st: pstate) : prop =
  g == SCh.hjoin gn w0 pm0 b k /\ st == SCh.with_pm (SCh.ljoin w0 pm0 b k) (SCh.pjoin pmn w0 pm0 b k)

let qslice (q: Seq.seq U64.t) (k: nat)
  : Lemma (requires poff k + pw <= Seq.length q)
          (ensures CSub.tsl q (poff k) (poff k + pw) == Seq.slice q (poff k) (poff k + pw))
  = ()

/// **The finish**: the free-page hint, then each chunk's fragments joined
/// onto the lists, in ascending chunk order.
fn par_finish (heap: heap_t) (t: pstate_t) (parts: A.array U64.t) (nc: U64.t)
  (#gn: erased Base.heap) (#sn: erased (Seq.seq prec)) (#w: erased (Seq.seq U64.t)) (#qn: erased (Seq.seq U64.t))
  (#pp: perm) (#w0: erased Base.heap) (#st0: erased pstate) (#bb: erased (Seq.seq U64.t)) (#pmn: erased page_map)
  requires is_heap heap gn ** A.pts_to t.tpm sn ** A.pts_to t.tw w ** A.pts_to parts #pp qn **
           pure (fin_pre w0 st0 bb (U64.v nc) w gn sn pmn qn)
  ensures exists* g' st'. is_heap heap g' ** pages_st t st' ** A.pts_to parts #pp qn **
          pure ((g', st') == SCh.sweep_chunks w0 st0 bb (U64.v nc))
{
  (* the hint: the lowest page any chunk left free *)
  let np = n_pages_u64 ();
  let mut h = np;
  let mut k = 0UL;
  CP.pw_small ();
  while (U64.lt !k nc)
    invariant exists* vk vh.
      R.pts_to k vk ** R.pts_to h vh ** A.pts_to parts #pp qn **
      pure (U64.v vk <= U64.v nc /\ U64.v vh <= n_pages /\
            (forall (k': nat). k' < U64.v vk ==> U64.v vh <= U64.v (qat qn (poff k' + o_mf))))
    decreases (U64.v nc - U64.v !k)
  {
    let vk = !k;
    let vh = !h;
    CP.off_bound (U64.v vk);
    let x = parts.(SZ.uint64_to_sizet (U64.add (U64.mul vk (pw_u64 ())) (o_mf_u64 ())));
    hint_step qn (U64.v nc) (U64.v vk) vh x;
    if (U64.lt x vh) { h := x };
    k := U64.add vk 1UL
  };
  let vh = !h;
  hint_ok w0 st0.pm bb (U64.v nc) pmn qn (U64.v vh);
  w_small ();
  w_upd w o_mt 2 0 vh;
  t.tw.(wsz (o_mt_u64 ())) <- vh;
  let fs = Ghost.hide ({ reveal st0 with pm = reveal pmn });
  fold (pages_st t fs);
  (* the joins *)
  start_join gn w0 st0 bb pmn;
  ps_eq t fs (SCh.with_pm (SCh.ljoin w0 st0.pm bb 0) (SCh.pjoin pmn w0 st0.pm bb 0));
  ih_eq heap gn (SCh.hjoin gn w0 st0.pm bb 0);
  let mut j = 0UL;
  while (U64.lt !j nc)
    invariant exists* vj.
      R.pts_to j vj ** A.pts_to parts #pp qn **
      is_heap heap (SCh.hjoin gn w0 st0.pm bb (U64.v vj)) **
      pages_st t (SCh.with_pm (SCh.ljoin w0 st0.pm bb (U64.v vj)) (SCh.pjoin pmn w0 st0.pm bb (U64.v vj))) **
      pure (U64.v vj <= U64.v nc)
    decreases (U64.v nc - U64.v !j)
  {
    let vj = !j;
    let fo = Ghost.hide (SCh.frag w0 st0.pm bb (U64.v vj));
    assert (pure (chunk_done w0 st0.pm bb (U64.v vj) pmn qn));
    qslice qn (U64.v vj);
    join_tails w0 st0.pm bb (U64.v nc) pmn qn (U64.v vj);
    SCh.frag_ok w0 st0.pm bb (U64.v nc) (U64.v vj);
    join_chunk heap t parts vj #pp #qn #(SCh.hjoin gn w0 st0.pm bb (U64.v vj))
               #(SCh.with_pm (SCh.ljoin w0 st0.pm bb (U64.v vj)) (SCh.pjoin pmn w0 st0.pm bb (U64.v vj)))
               #(fst fo) #(snd fo) #(U64.v (qat qn (poff (U64.v vj) + o_mf)));
    join_eq w0 gn st0.pm pmn bb (U64.v vj);
    with g' st'. assert (is_heap heap g' ** pages_st t st');
    ih_eq heap g' (SCh.hjoin gn w0 st0.pm bb (U64.v (U64.add vj 1UL)));
    ps_eq t st' (SCh.with_pm (SCh.ljoin w0 st0.pm bb (U64.v (U64.add vj 1UL)))
                             (SCh.pjoin pmn w0 st0.pm bb (U64.v (U64.add vj 1UL))));
    j := U64.add vj 1UL
  };
  let vj = !j;
  assert (pure (vj == nc));
  ()
}

/// ---------------------------------------------------------------------------
/// The whole parallel sweep, in one thread
/// ---------------------------------------------------------------------------

/// **The start**: a new sweep epoch and empty lists (`Sweep.start_sweep`),
/// then the chunk bounds.
fn par_prepare (t: pstate_t) (bounds: A.array U64.t) (nc: U64.t) (#st: erased pstate) (#b0: erased (Seq.seq U64.t))
  requires pages_st t st ** A.pts_to bounds b0 **
           pure (Seq.length b0 == U64.v nc + 1 /\ U64.v nc >= 1 /\ U64.v nc <= 256 /\ map_ok st.pm)
  ensures exists* b. pages_st t (SSt.start_sweep st) ** A.pts_to bounds b **
          pure (CP.bounds_good (SSt.start_sweep st).pm b (U64.v nc))
{
  ISw.start_sweep t;
  SSt.clear_map_ok st.pm;
  CP.chunk_bounds t bounds nc
}

let cw_of (w: Seq.seq U64.t) (st: pstate) (s: Seq.seq prec)
  : Lemma (requires w_ok w st /\ meta_ok s (mt_of w) st.pm /\ pm_rel s (Seq.index (mt_of w) 1) st.pm)
          (ensures cw_ok w /\ ep_of w == Seq.index (mt_of w) 1 /\
                   (forall (i: nat). i < n_pages ==> U64.v (Seq.index s i).sep <= U64.v (ep_of w)))
  = w_lengths w st

let start_empty (st: pstate) : Lemma (SCh.empty_st (SSt.start_sweep st)) = ()

/// The chunks' end, for the finish.
let drv_fin (g: Base.heap) (bs: Seq.seq U32.t) (st0: pstate) (b: Seq.seq U64.t) (n: nat) (w: Seq.seq U64.t)
            (gn: Base.heap) (bsn: Seq.seq U32.t) (sn: Seq.seq prec) (qn: Seq.seq U64.t)
  : Lemma (requires start_ok g bs st0.pm b n w /\ SCh.empty_st st0 /\ w_ok w st0 /\
                    ep_of w == Seq.index (mt_of w) 1 /\
                    drv_ok g bs st0.pm b n (ep_of w) n gn bsn sn (snd (SCh.chunks (BM.with_marks g bs) st0.pm b n)) qn)
          (ensures fin_pre (BM.with_marks g bs) st0 b n w gn sn (snd (SCh.chunks (BM.with_marks g bs) st0.pm b n)) qn /\
                   bsn == Seq.create BM.bm_len 0ul)
  = SCh.bounds_at st0.pm b n 0;
    assert (SCh.bnd b n == n_pages);
    all_zero bsn;
    marks_none gn bsn

let final_eq (w0: Base.heap) (st: pstate) (st0: pstate) (b: Seq.seq U64.t) (n: nat) (g': Base.heap) (st': pstate)
  : Lemma (requires st0 == SSt.start_sweep st /\ (g', st') == SCh.sweep_chunks w0 st0 b n /\
                    SCh.sweep_chunks w0 st0 b n == SA.sweep_all w0 st0)
          (ensures (g', st') == SA.sweep_all w0 (SSt.start_sweep st))
  = ()

/// **The parallel sweep, run in one thread.**  From a heap `g` whose marks
/// are the bits of `bs`, it computes exactly `SweepAll.sweep_all` of the heap
/// the bitmap stands for (`Bitmap.with_marks g bs`), from
/// `StartSweep.start_sweep st`, and leaves the bitmap all zero.  It needs the
/// marks where the sweep reads them (`CSweep.marks_from`) and a well-formed
/// map.
fn sweep_par_seq (heap: heap_t) (t: pstate_t) (bm: A.array U32.t) (parts: A.array U64.t) (bounds: A.array U64.t)
  (nc: U64.t)
  (#g: erased Base.heap) (#st: erased pstate) (#bs: erased (Seq.seq U32.t))
  (#q0: erased (Seq.seq U64.t)) (#b0: erased (Seq.seq U64.t))
  requires is_heap heap g ** pages_st t st ** A.pts_to bm bs ** A.pts_to parts q0 ** A.pts_to bounds b0 **
           pure (Seq.length bs == BM.bm_len /\ Seq.length q0 == poff (U64.v nc) /\
                 Seq.length b0 == U64.v nc + 1 /\ U64.v nc >= 1 /\ U64.v nc <= 256 /\
                 map_ok st.pm /\ CSw.marks_from g bs (SSt.start_sweep st).pm 0 n_pages)
  ensures exists* g' st' bs' q b.
          is_heap heap g' ** pages_st t st' ** A.pts_to bm bs' ** A.pts_to parts q ** A.pts_to bounds b **
          pure ((g', st') == SA.sweep_all (BM.with_marks g bs) (SSt.start_sweep st) /\
                bs' == Seq.create BM.bm_len 0ul)
{
  par_prepare t bounds nc;
  with b. assert (A.pts_to bounds b);
  let st0 = Ghost.hide (SSt.start_sweep st);
  start_empty st;
  SSt.clear_map_ok st.pm;
  unfold pages_st;
  with s w. assert (A.pts_to t.tpm s ** A.pts_to t.tw w);
  cw_of w st0 s;
  chunks_seq heap t bm parts bounds nc #g #bs #s #w #q0 #b #st0.pm #1.0R;
  with gn bsn sn qn. assert (is_heap heap gn ** A.pts_to t.tpm sn ** A.pts_to bm bsn ** A.pts_to parts qn);
  drv_fin g bs st0 b (U64.v nc) w gn bsn sn qn;
  par_finish heap t parts nc #gn #sn #w #qn #1.0R #(BM.with_marks g bs) #st0 #b
             #(snd (SCh.chunks (BM.with_marks g bs) st0.pm b (U64.v nc)));
  with g' st'. assert (is_heap heap g' ** pages_st t st');
  SCh.sweep_chunks_eq (BM.with_marks g bs) st0 b (U64.v nc);
  final_eq (BM.with_marks g bs) st st0 b (U64.v nc) g' st';
  ()
}
