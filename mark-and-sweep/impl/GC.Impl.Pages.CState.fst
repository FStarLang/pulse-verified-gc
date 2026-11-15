/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.CState - what one chunk of the parallel sweep owns
/// ---------------------------------------------------------------------------
///
/// A chunk of the parallel sweep (docs/pages-parallel-gc-design.md §2.1)
/// sweeps the pages `[lo, hi)` and owns only:
///   - **the heap's bytes** `[page_base lo, page_base hi)`: `ch_heap`, a
///     sub-array of the heap (`Pulse.Lib.Array.Core.sub`, a pointer
///     addition in C), read and written a word at a time with the same
///     `GC.Impl.ArrayWord` primitives as the whole heap;
///   - **the page map's records** `[lo, hi)`: a `pts_to_range` of `tpm`;
///   - **its result record**, a sub-array of the chunks' records `parts`:
///     the heads and tails of its fragments of the class lists, the head of
///     its fragment of list 0, its open link, and the lowest page it made
///     free (`o_lh`, `o_ol`, `o_mf`);
///   - **the bitmap's words** of its pages: `ch_bm`, a `pts_to_range`;
///   - a fraction of the word array `tw`, for the class tables and the
///     sweep epoch, which no chunk writes.
///
/// As in `GC.Impl.Pages.State`, each predicate ties the memory to a whole
/// ghost value (a heap, a `pstate`, a bitmap) of which the chunk owns a
/// part, so that the specification's whole-heap functions and lemmas apply
/// unchanged; the accessors below have the specifications of `State`'s and
/// `Heap`'s, with the addresses and pages they touch inside the chunk.
/// `cst` also keeps the lowest page made free (`mf`) as `write_entry` keeps
/// the free-page hint.

module GC.Impl.Pages.CState

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsToRange
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Impl.Pages.Params
open GC.Impl.Pages.State

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module A = Pulse.Lib.Array
module AC = Pulse.Lib.Array.Core
module APT = Pulse.Lib.Array.PtsTo
module AW = GC.Impl.ArrayWord
module IH = GC.Impl.Heap
module Base = GC.Spec.Base
module SH = GC.Spec.Heap
module FLs = GC.Spec.FreeLists
module SC = GC.Spec.SizeClass
module BM = GC.Spec.Pages.Bitmap
module B = GC.Spec.Pages.Blocks
module Sh = GC.Spec.Pages.Shape
module R = Pulse.Lib.Reference

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The chunk's heap
/// ---------------------------------------------------------------------------

/// The chunk's bytes: `cd` points at the heap's byte `cb`.
noeq type cheap_t = {
  cd: A.array U8.t;
  cb: U64.t;
}

let pages_in_heap (hi: nat) : Lemma (requires hi <= n_pages) (ensures page_base hi <= Base.heap_size)
  = page_base_mono hi n_pages; pages_end_bound ()

/// The chunk's bytes hold those of the whole heap `g`.
let ch_heap (hp: cheap_t) (lo hi: nat) (g: Base.heap) : slprop =
  exists* (s: Seq.seq U8.t).
    A.pts_to hp.cd s **
    pure (lo <= hi /\ hi <= n_pages /\ U64.v hp.cb == page_base lo /\ page_base lo <= page_base hi /\
          page_base hi <= Base.heap_size /\ s == Seq.slice g (page_base lo) (page_base hi))

/// The word at `a` lies in the chunk.
let in_chunk (lo hi: nat) (a: nat) : prop = page_base lo <= a /\ a + 8 <= page_base hi /\ a % 8 == 0

let read_slice (g: Base.heap) (lo hi: nat) (a: Base.hp_addr)
  : Lemma (requires lo <= U64.v a /\ U64.v a + 8 <= hi /\ hi <= Base.heap_size)
          (ensures AW.read_u64_spec (Seq.slice g lo hi) (U64.v a - lo) == SH.read_word g a)
  = SH.read_word_spec g a

let slice_upd (g: Seq.seq U8.t) (lo hi: nat) (a: nat) (b: U8.t)
  : Lemma (requires lo <= a /\ a < hi /\ hi <= Seq.length g)
          (ensures Seq.slice (Seq.upd g a b) lo hi == Seq.upd (Seq.slice g lo hi) (a - lo) b)
  = Seq.lemma_eq_intro (Seq.slice (Seq.upd g a b) lo hi) (Seq.upd (Seq.slice g lo hi) (a - lo) b)

#push-options "--z3rlimit 40"
let write_slice (g: Base.heap) (lo hi: nat) (a: Base.hp_addr) (v: U64.t)
  : Lemma (requires lo <= U64.v a /\ U64.v a + 8 <= hi /\ hi <= Base.heap_size)
          (ensures AW.write_u64_spec (Seq.slice g lo hi) (U64.v a - lo) v == Seq.slice (SH.write_word g a v) lo hi)
  = let x = U64.v a in
    SH.write_word_spec g a v;
    let s0 : Seq.seq U8.t = g in
    let s1 = Seq.upd s0 x (SH.uint64_to_uint8 v) in
    let s2 = Seq.upd s1 (x+1) (SH.uint64_to_uint8 (U64.shift_right v 8ul)) in
    let s3 = Seq.upd s2 (x+2) (SH.uint64_to_uint8 (U64.shift_right v 16ul)) in
    let s4 = Seq.upd s3 (x+3) (SH.uint64_to_uint8 (U64.shift_right v 24ul)) in
    let s5 = Seq.upd s4 (x+4) (SH.uint64_to_uint8 (U64.shift_right v 32ul)) in
    let s6 = Seq.upd s5 (x+5) (SH.uint64_to_uint8 (U64.shift_right v 40ul)) in
    let s7 = Seq.upd s6 (x+6) (SH.uint64_to_uint8 (U64.shift_right v 48ul)) in
    slice_upd s0 lo hi x (SH.uint64_to_uint8 v);
    slice_upd s1 lo hi (x+1) (SH.uint64_to_uint8 (U64.shift_right v 8ul));
    slice_upd s2 lo hi (x+2) (SH.uint64_to_uint8 (U64.shift_right v 16ul));
    slice_upd s3 lo hi (x+3) (SH.uint64_to_uint8 (U64.shift_right v 24ul));
    slice_upd s4 lo hi (x+4) (SH.uint64_to_uint8 (U64.shift_right v 32ul));
    slice_upd s5 lo hi (x+5) (SH.uint64_to_uint8 (U64.shift_right v 40ul));
    slice_upd s6 lo hi (x+6) (SH.uint64_to_uint8 (U64.shift_right v 48ul));
    slice_upd s7 lo hi (x+7) (SH.uint64_to_uint8 (U64.shift_right v 56ul))
#pop-options

let off_of (hp: cheap_t) (a: U64.t) : Pure SZ.t
  (requires U64.v hp.cb <= U64.v a)
  (ensures fun r -> SZ.v r == U64.v a - U64.v hp.cb)
  = SZ.uint64_to_sizet (U64.sub a hp.cb)

/// The word at `a`.
inline_for_extraction
fn ch_read (hp: cheap_t) (a: Base.hp_addr) (#lo #hi: erased nat) (#g: erased Base.heap)
  requires ch_heap hp lo hi g ** pure (in_chunk lo hi (U64.v a))
  returns v: U64.t
  ensures ch_heap hp lo hi g ** pure (v == SH.read_word g a)
{
  unfold ch_heap;
  with s. assert (A.pts_to hp.cd s);
  read_slice g (page_base lo) (page_base hi) a;
  let v = AW.read_u64_le hp.cd (off_of hp a);
  fold (ch_heap hp lo hi g);
  v
}

/// Write the word at `a`.
inline_for_extraction
fn ch_write (hp: cheap_t) (a: Base.hp_addr) (v: U64.t) (#lo #hi: erased nat) (#g: erased Base.heap)
  requires ch_heap hp lo hi g ** pure (in_chunk lo hi (U64.v a))
  ensures ch_heap hp lo hi (SH.write_word g a v)
{
  unfold ch_heap;
  with s. assert (A.pts_to hp.cd s);
  write_slice g (page_base lo) (page_base hi) a v;
  AW.write_u64_le hp.cd (off_of hp a) v;
  fold (ch_heap hp lo hi (SH.write_word g a v))
}

/// `Shape.hdr g a`, at an address of the chunk.
inline_for_extraction
fn ch_hdr (hp: cheap_t) (a: U64.t) (#lo #hi: erased nat) (#g: erased Base.heap)
  requires ch_heap hp lo hi g ** pure (in_chunk lo hi (U64.v a))
  returns v: U64.t
  ensures ch_heap hp lo hi g ** pure (v == Sh.hdr g (U64.v a))
{
  unfold ch_heap;
  fold (ch_heap hp lo hi g);
  ch_read hp a
}

/// `Blocks.wr g a v`, at an address of the chunk.
inline_for_extraction
fn ch_wr (hp: cheap_t) (a: U64.t) (v: U64.t) (#lo #hi: erased nat) (#g: erased Base.heap)
  requires ch_heap hp lo hi g ** pure (in_chunk lo hi (U64.v a))
  ensures ch_heap hp lo hi (B.wr g (U64.v a) v)
{
  unfold ch_heap;
  fold (ch_heap hp lo hi g);
  ch_write hp a v;
  rewrite (ch_heap hp lo hi (SH.write_word g a v)) as (ch_heap hp lo hi (B.wr g (U64.v a) v))
}

/// ---------------------------------------------------------------------------
/// The chunk's bits
/// ---------------------------------------------------------------------------

/// The chunk's bitmap words hold those of the whole bitmap `bs`.
/// `bs`'s words `[i, j)`, empty when they are not in `bs`.
noextract
let bsl (bs: Seq.seq U32.t) (i j: nat) : Seq.seq U32.t =
  if i <= j && j <= Seq.length bs then Seq.slice bs i j else Seq.empty

let ch_bm (bm: A.array U32.t) (lo hi: nat) (bs: Seq.seq U32.t) : slprop =
  pts_to_range bm (lo * BM.bpp) (hi * BM.bpp) (bsl bs (lo * BM.bpp) (hi * BM.bpp)) **
  pure (Seq.length bs == BM.bm_len /\ lo <= hi /\ hi <= n_pages)

let bm_len_ok (lo hi: nat)
  : Lemma (requires lo <= hi /\ hi <= n_pages)
          (ensures lo * BM.bpp <= hi * BM.bpp /\ hi * BM.bpp <= BM.bm_len)
  = FStar.Math.Lemmas.lemma_mult_le_right BM.bpp lo hi;
    FStar.Math.Lemmas.lemma_mult_le_right BM.bpp hi n_pages

let bm_word_in (lo hi: nat) (a: nat)
  : Lemma (requires in_chunk lo hi a /\ hi <= n_pages)
          (ensures BM.in_pages a /\ lo * BM.bpp <= BM.widx a / 32 /\ BM.widx a / 32 < hi * BM.bpp)
  = let i = BM.page_of_word a in
    BM.bpp_mul ();
    page_base_mono hi n_pages;
    FStar.Math.Lemmas.lemma_div_mod (a - BM.zw) page_bytes;
    assert (page_base i <= a /\ a < page_base (i + 1));
    if i < lo then page_base_mono (i + 1) lo;
    if i >= hi then page_base_mono hi i;
    BM.widx_page i a;
    FStar.Math.Lemmas.lemma_mult_le_right BM.bpp lo i;
    FStar.Math.Lemmas.lemma_mult_le_right BM.bpp (i + 1) hi

let z_u64 () : r: U64.t{U64.v r == BM.zw} = IH.zero_addr

/// The bitmap word and bit of the word at `a`.
inline_for_extraction
let bm_widx (a: U64.t{U64.v a >= BM.zw /\ BM.in_pages (U64.v a)}) : r: U64.t{U64.v r == BM.widx (U64.v a)}
  = let d = U64.sub a (z_u64 ()) in
    FStar.UInt.shift_right_value_lemma #64 (U64.v d) 3;
    assert_norm (pow2 3 == 8);
    U64.shift_right d 3ul

/// Is the word at `a` marked?
inline_for_extraction
fn bm_test (bm: A.array U32.t) (a: U64.t) (#lo #hi: erased nat) (#bs: erased (Seq.seq U32.t))
  requires ch_bm bm lo hi bs ** pure (in_chunk lo hi (U64.v a))
  returns b: bool
  ensures ch_bm bm lo hi bs ** pure (b == BM.marked bs (U64.v a))
{
  unfold ch_bm;
  bm_len_ok lo hi;
  bm_word_in lo hi (U64.v a);
  BM.widx_bound (U64.v a);
  let wi = bm_widx a;
  FStar.Math.Lemmas.pow2_lt_compat 64 32;
  FStar.UInt.shift_right_value_lemma #64 (U64.v wi) 5;
  assert_norm (pow2 5 == 32);
  let w = pts_to_range_index bm (SZ.uint64_to_sizet (U64.shift_right wi 5ul));
  let k = FStar.Int.Cast.uint64_to_uint32 (U64.logand wi 31UL);
  FStar.UInt.logand_mask #64 (U64.v wi) 5;
  assert_norm (pow2 5 - 1 == 31);
  BM.bit_test w k;
  fold (ch_bm bm lo hi bs);
  (U32.logand (U32.shift_right w k) 1ul <> 0ul)
}

let bsl_upd (bs: Seq.seq U32.t) (i j: nat) (x: nat) (v: U32.t)
  : Lemma (requires i <= x /\ x < j /\ j <= Seq.length bs)
          (ensures bsl (Seq.upd bs x v) i j == Seq.upd (bsl bs i j) (x - i) v)
  = Seq.lemma_eq_intro (bsl (Seq.upd bs x v) i j) (Seq.upd (bsl bs i j) (x - i) v)

/// Clear the bit of the word at `a`.
inline_for_extraction
fn bm_clear (bm: A.array U32.t) (a: U64.t) (#lo #hi: erased nat) (#bs: erased (Seq.seq U32.t))
  requires ch_bm bm lo hi bs ** pure (in_chunk lo hi (U64.v a))
  ensures ch_bm bm lo hi (BM.clear_bit bs (U64.v a))
{
  unfold ch_bm;
  bm_len_ok lo hi;
  bm_word_in lo hi (U64.v a);
  BM.widx_bound (U64.v a);
  let wi = bm_widx a;
  FStar.Math.Lemmas.pow2_lt_compat 64 32;
  FStar.UInt.shift_right_value_lemma #64 (U64.v wi) 5;
  assert_norm (pow2 5 == 32);
  let j = SZ.uint64_to_sizet (U64.shift_right wi 5ul);
  let w = pts_to_range_index bm j;
  let k = FStar.Int.Cast.uint64_to_uint32 (U64.logand wi 31UL);
  FStar.UInt.logand_mask #64 (U64.v wi) 5;
  assert_norm (pow2 5 - 1 == 31);
  pts_to_range_upd bm j (BM.clear_word w k);
  bsl_upd bs (lo * BM.bpp) (hi * BM.bpp) (SZ.v j) (BM.clear_word w k);
  BM.clear_bit_len bs (U64.v a);
  fold (ch_bm bm lo hi (BM.clear_bit bs (U64.v a)))
}

/// Page `i`'s words, zeroed below word `j`.
noextract
let zero_upto (bs: Seq.seq U32.t) (i: nat) (j: nat) : Seq.seq U32.t =
  Seq.init (Seq.length bs) (fun (x: nat{x < Seq.length bs}) ->
    if i * BM.bpp <= x && x < j then 0ul else Seq.index bs x)

let zero_upto_start (bs: Seq.seq U32.t) (i: nat)
  : Lemma (zero_upto bs i (i * BM.bpp) == bs)
  = Seq.lemma_eq_intro (zero_upto bs i (i * BM.bpp)) bs

let zero_upto_step (bs: Seq.seq U32.t) (i: nat) (j: nat)
  : Lemma (requires i * BM.bpp <= j /\ j < Seq.length bs)
          (ensures zero_upto bs i (j + 1) == Seq.upd (zero_upto bs i j) j 0ul)
  = Seq.lemma_eq_intro (zero_upto bs i (j + 1)) (Seq.upd (zero_upto bs i j) j 0ul)

let zero_upto_end (bs: Seq.seq U32.t) (i: nat)
  : Lemma (zero_upto bs i ((i + 1) * BM.bpp) == BM.zero_page bs i)
  = Seq.lemma_eq_intro (zero_upto bs i ((i + 1) * BM.bpp)) (BM.zero_page bs i)

/// The bitmap has fewer words than a 57-bit number.
let bm_len_small () : Lemma (BM.bm_len < pow2 57 /\ pow2 57 < pow2 64)
  = BM.bpp_mul ();
    page_base_mono n_pages n_pages;
    pages_end_bound ();
    FStar.Math.Lemmas.pow2_lt_compat 64 57;
    assert (n_pages * page_bytes <= Base.heap_size);
    FStar.Math.Lemmas.paren_mul_right n_pages 256 BM.bpp;
    FStar.Math.Lemmas.swap_mul n_pages 256

let bpp_u64 () : r: U64.t{U64.v r == BM.bpp} =
  BM.bpp_mul ();
  cls_bounds 0;
  U64.div page_wsize_u64 32UL

/// Zero page `i`'s bitmap words.
fn bm_zero_page (bm: A.array U32.t) (i: U64.t) (#lo #hi: erased nat) (#bs: erased (Seq.seq U32.t))
  requires ch_bm bm lo hi bs ** pure (lo <= U64.v i /\ U64.v i < hi)
  ensures ch_bm bm lo hi (BM.zero_page bs (U64.v i))
{
  unfold ch_bm;
  bm_len_ok lo hi;
  let b = bpp_u64 ();
  FStar.Math.Lemmas.lemma_mult_le_right BM.bpp (U64.v i + 1) hi;
  FStar.Math.Lemmas.lemma_mult_le_right BM.bpp lo (U64.v i);
  FStar.Math.Lemmas.lemma_mult_le_right BM.bpp hi n_pages;
  bm_len_small ();
  let j0 = U64.mul i b;
  let j1 = U64.add j0 b;
  zero_upto_start bs (U64.v i);
  let mut j = j0;
  while (U64.lt !j j1)
    invariant exists* vj s.
      R.pts_to j vj ** pts_to_range bm (lo * BM.bpp) (hi * BM.bpp) s **
      pure (U64.v j0 <= U64.v vj /\ U64.v vj <= U64.v j1 /\
            s == bsl (zero_upto bs (U64.v i) (U64.v vj)) (lo * BM.bpp) (hi * BM.bpp))
    decreases (U64.v j1 - U64.v !j)
  {
    let vj = !j;
    let sj = SZ.uint64_to_sizet vj;
    pts_to_range_upd bm sj 0ul;
    zero_upto_step bs (U64.v i) (U64.v vj);
    bsl_upd (zero_upto bs (U64.v i) (U64.v vj)) (lo * BM.bpp) (hi * BM.bpp) (U64.v vj) 0ul;
    j := U64.add vj 1UL
  };
  zero_upto_end bs (U64.v i);
  BM.zero_page_marked bs (U64.v i) 0;
  fold (ch_bm bm lo hi (BM.zero_page bs (U64.v i)))
}

/// ---------------------------------------------------------------------------
/// The chunk's map and lists
/// ---------------------------------------------------------------------------

/// The chunk's record: the heads of its fragments of the class lists, their
/// tails, the head of its fragment of list 0, its open link and the lowest
/// page it made free; padded to whole cache lines.
noextract
let o_lh : nat = 2 * n_cls
noextract
let o_ol : nat = 2 * n_cls + 1
noextract
let o_mf : nat = 2 * n_cls + 2
noextract
let pw : nat = 2 * n_cls + 10

let o_lh_u64 () : r: U64.t{U64.v r == o_lh} = w_small (); U64.mul 2UL n_cls_u64
let o_ol_u64 () : r: U64.t{U64.v r == o_ol} = w_small (); U64.add (U64.mul 2UL n_cls_u64) 1UL
let o_mf_u64 () : r: U64.t{U64.v r == o_mf} = w_small (); U64.add (U64.mul 2UL n_cls_u64) 2UL
let pw_u64 () : r: U64.t{U64.v r == pw} = w_small (); U64.add (U64.mul 2UL n_cls_u64) 10UL

/// A position of the record as an index.
let psz (j: U64.t{U64.v j < pw}) : s: SZ.t{SZ.v s == U64.v j} =
  w_small ();
  FStar.Math.Lemmas.pow2_lt_compat 64 24;
  SZ.uint64_to_sizet j

/// The tables and the epoch of the word array.
let cw_ok (w: Seq.seq U64.t) : prop =
  Seq.length w == w_len /\
  sl w o_cf (small_max + 1) == cof_seq /\ sl w o_cl n_cls == cls_seq /\ sl w o_ns n_cls == ns_seq /\
  U64.v (Seq.index (mt_of w) 1) >= 1

noextract
let ep_of (w: Seq.seq U64.t) : U64.t =
  if Seq.length w = w_len && Seq.length (mt_of w) = 2 then Seq.index (mt_of w) 1 else 1UL

/// The records `[lo, hi)` are the map's in epoch `ep`.
let rng_rel (s: Seq.seq prec) (ep: U64.t) (lo hi: nat) (pm: page_map) : prop =
  hi <= n_pages /\ lo <= hi /\ Seq.length s == hi - lo /\
  (forall (j: nat). lo <= j /\ j < hi ==>
     view (to_pinfo ep (Seq.index s (j - lo))) == entry pm j /\
     U64.v (Seq.index s (j - lo)).sep <= U64.v ep)

/// A page of the chunk that is free now and was not at its start is at or
/// above `mf`.
let newfree_ge (pm0 pm: page_map) (lo hi: nat) (mf: nat) : prop =
  forall (j: nat{j < n_pages}). lo <= j /\ j < hi /\ (entry pm j).kind == Free /\ ~((entry pm0 j).kind == Free) ==>
    j >= mf

/// What stays fixed while a chunk is swept.
noeq type cfix = {
  clo: nat;              (* the chunk's pages *)
  chi: nat;
  cp: perm;              (* its share of the word array *)
  cw: Seq.seq U64.t;     (* the word array *)
  cpm0: page_map;        (* the map when the chunk started *)
}

/// The chunk's map and lists, as the state `st`, with open link `ol` and
/// lowest page made free `mf`.
let cst (t: pstate_t) (pt: A.array U64.t) (k: cfix) (st: pstate) (ol: U64.t) (mf: nat) : slprop =
  exists* (s: Seq.seq prec) (q: Seq.seq U64.t).
    pts_to_range t.tpm k.clo k.chi s ** A.pts_to t.tw #k.cp k.cw ** A.pts_to pt q **
    pure (cw_ok k.cw /\ rng_rel s (ep_of k.cw) k.clo k.chi st.pm /\
          Seq.length q == pw /\ sl q 0 n_cls == st.avail /\ sl q n_cls n_cls == st.atail /\
          st.large == FLs.fls_set FLs.fls_empty 0 (Seq.index q o_lh) /\
          Seq.index q o_ol == ol /\ U64.v (Seq.index q o_mf) == mf /\ mf <= n_pages /\
          newfree_ge k.cpm0 st.pm k.clo k.chi mf)

let in_rng (k: cfix) (i: U64.t) : prop = k.clo <= U64.v i /\ U64.v i < k.chi

let ep_read (w: Seq.seq U64.t)
  : Lemma (requires cw_ok w)
          (ensures o_mt + 1 < Seq.length w /\ Seq.index w (o_mt + 1) == ep_of w /\ U64.v (ep_of w) >= 1)
  = w_small (); sl_index w o_mt 2 1

ghost fn cst_lengths (t: pstate_t) (pt: A.array U64.t) (#k: cfix) (#st: pstate) (#ol: U64.t) (#mf: nat)
  requires cst t pt k st ol mf
  ensures cst t pt k st ol mf **
          pure (Seq.length st.avail == n_cls /\ Seq.length st.atail == n_cls /\ k.chi <= n_pages /\
                Seq.length st.large == SC.n_lists /\ FLs.fls_head st.large 0 == FLs.fls_head st.large 0)
{
  unfold cst;
  w_small ();
  fold (cst t pt k st ol mf)
}

fn c_read_entry (t: pstate_t) (pt: A.array U64.t) (i: U64.t{U64.v i < n_pages})
  (#k: erased cfix) (#st: erased pstate) (#ol: erased U64.t) (#mf: erased nat)
  requires cst t pt k st ol mf ** pure (in_rng k i)
  returns r: pinfo
  ensures cst t pt k st ol mf ** pure (view r == entry st.pm (U64.v i) /\ storable r)
{
  unfold cst;
  with s q. assert (pts_to_range t.tpm k.clo k.chi s ** A.pts_to pt q);
  w_small ();
  ep_read k.cw;
  let ep = t.tw.(wsz (U64.add (o_mt_u64 ()) 1UL));
  let p = pts_to_range_index t.tpm (sz_of i);
  to_storable ep p;
  fold (cst t pt k st ol mf);
  to_pinfo ep p
}

let rng_upd (s: Seq.seq prec) (ep: U64.t) (lo hi: nat) (pm: page_map) (i: nat{i < n_pages}) (r: pinfo)
  : Lemma (requires rng_rel s ep lo hi pm /\ lo <= i /\ i < hi /\ U64.v ep >= 1 /\ storable r)
          (ensures rng_rel (Seq.upd s (i - lo) (of_pinfo ep r)) ep lo hi (Seq.upd pm i (view r)))
  = to_of ep r

let mf_upd (pm0 pm: page_map) (lo hi: nat) (mf: nat) (i: nat{i < n_pages}) (r: pinfo)
  : Lemma (requires newfree_ge pm0 pm lo hi mf)
          (ensures newfree_ge pm0 (Seq.upd pm i (view r)) lo hi (if is_free_rec r && i < mf then i else mf))
  = is_free_rec_kind r

/// `State.write_entry`: the record of page `i`, and the lowest page made
/// free lowered to `i` when `r` is a free page's.
fn c_write_entry (t: pstate_t) (pt: A.array U64.t) (i: U64.t{U64.v i < n_pages}) (r: pinfo)
  (#k: erased cfix) (#st: erased pstate) (#ol: erased U64.t) (#mf: erased nat)
  requires cst t pt k st ol mf ** pure (in_rng k i /\ storable r)
  ensures cst t pt k (set_entry st (U64.v i) (view r)) ol (if is_free_rec r && U64.v i < mf then U64.v i else mf)
{
  unfold cst;
  with s q. assert (pts_to_range t.tpm k.clo k.chi s ** A.pts_to pt q);
  w_small ();
  ep_read k.cw;
  let ep = t.tw.(wsz (U64.add (o_mt_u64 ()) 1UL));
  pts_to_range_upd t.tpm (sz_of i) (of_pinfo ep r);
  rng_upd s ep k.clo k.chi st.pm (U64.v i) r;
  mf_upd k.cpm0 st.pm k.clo k.chi mf (U64.v i) r;
  if (is_free_rec r) {
    let m = pt.(psz (o_mf_u64 ()));
    if (U64.lt i m) {
      pt.(psz (o_mf_u64 ())) <- i;
      sl_upd q 0 n_cls o_mf i;
      sl_upd q n_cls n_cls o_mf i;
      fold (cst t pt k (set_entry st (U64.v i) (view r)) ol (if is_free_rec r && U64.v i < mf then U64.v i else mf))
    } else {
      fold (cst t pt k (set_entry st (U64.v i) (view r)) ol (if is_free_rec r && U64.v i < mf then U64.v i else mf))
    }
  } else {
    fold (cst t pt k (set_entry st (U64.v i) (view r)) ol (if is_free_rec r && U64.v i < mf then U64.v i else mf))
  }
}

/// `State.write_used`: a record that is not a free page's.
fn c_write_used (t: pstate_t) (pt: A.array U64.t) (i: U64.t{U64.v i < n_pages}) (r: pinfo)
  (#k: erased cfix) (#st: erased pstate) (#ol: erased U64.t) (#mf: erased nat)
  requires cst t pt k st ol mf ** pure (in_rng k i /\ not (is_free_rec r))
  ensures cst t pt k (set_entry st (U64.v i) (view r)) ol mf
{
  unfold cst;
  with s q. assert (pts_to_range t.tpm k.clo k.chi s ** A.pts_to pt q);
  w_small ();
  ep_read k.cw;
  let ep = t.tw.(wsz (U64.add (o_mt_u64 ()) 1UL));
  pts_to_range_upd t.tpm (sz_of i) (of_pinfo ep r);
  rng_upd s ep k.clo k.chi st.pm (U64.v i) r;
  mf_upd k.cpm0 st.pm k.clo k.chi mf (U64.v i) r;
  fold (cst t pt k (set_entry st (U64.v i) (view r)) ol mf)
}

let rng_next (s: Seq.seq prec) (ep: U64.t) (lo hi: nat) (pm: page_map) (i: nat{i < n_pages}) (v: U64.t)
  : Lemma (requires rng_rel s ep lo hi pm /\ lo <= i /\ i < hi)
          (ensures (let p = Seq.index s (i - lo) in
                    rng_rel (Seq.upd s (i - lo) ({ p with pnext = v })) ep lo hi
                            (Seq.upd pm i ({ entry pm i with next = v }))))
  = ()

/// `State.write_next`: page `i`'s class-list link.
fn c_write_next (t: pstate_t) (pt: A.array U64.t) (i: U64.t{U64.v i < n_pages}) (v: U64.t)
  (#k: erased cfix) (#st: erased pstate) (#ol: erased U64.t) (#mf: erased nat)
  requires cst t pt k st ol mf ** pure (in_rng k i)
  ensures cst t pt k (set_next_at st (U64.v i) v) ol mf
{
  unfold cst;
  with s q. assert (pts_to_range t.tpm k.clo k.chi s ** A.pts_to pt q);
  let p = pts_to_range_index t.tpm (sz_of i);
  pts_to_range_upd t.tpm (sz_of i) ({ p with pnext = v });
  rng_next s (ep_of k.cw) k.clo k.chi st.pm (U64.v i) v;
  fold (cst t pt k (set_next_at st (U64.v i) v) ol mf)
}

/// `State.read_atail` and the writes of the list heads and tails.
fn c_read_atail (t: pstate_t) (pt: A.array U64.t) (c: U64.t{U64.v c < n_cls})
  (#k: erased cfix) (#st: erased pstate) (#ol: erased U64.t) (#mf: erased nat)
  requires cst t pt k st ol mf
  returns v: U64.t
  ensures cst t pt k st ol mf ** pure (Seq.length st.atail == n_cls /\ v == Seq.index st.atail (U64.v c))
{
  unfold cst;
  with s q. assert (pts_to_range t.tpm k.clo k.chi s ** A.pts_to pt q);
  w_small ();
  sl_index q n_cls n_cls (U64.v c);
  let v = pt.(psz (U64.add n_cls_u64 c));
  fold (cst t pt k st ol mf);
  v
}

fn c_write_atail (t: pstate_t) (pt: A.array U64.t) (c: U64.t{U64.v c < n_cls}) (v: U64.t)
  (#k: erased cfix) (#st: erased pstate) (#ol: erased U64.t) (#mf: erased nat)
  requires cst t pt k st ol mf
  ensures cst t pt k (set_atail_at st (U64.v c) v) ol mf
{
  unfold cst;
  with s q. assert (pts_to_range t.tpm k.clo k.chi s ** A.pts_to pt q);
  w_small ();
  let j = U64.add n_cls_u64 c;
  pt.(psz j) <- v;
  sl_upd q 0 n_cls (U64.v j) v;
  sl_upd q n_cls n_cls (U64.v j) v;
  fold (cst t pt k (set_atail_at st (U64.v c) v) ol mf)
}

fn c_write_avail (t: pstate_t) (pt: A.array U64.t) (c: U64.t{U64.v c < n_cls}) (v: U64.t)
  (#k: erased cfix) (#st: erased pstate) (#ol: erased U64.t) (#mf: erased nat)
  requires cst t pt k st ol mf
  ensures cst t pt k (set_avail_at st (U64.v c) v) ol mf
{
  unfold cst;
  with s q. assert (pts_to_range t.tpm k.clo k.chi s ** A.pts_to pt q);
  w_small ();
  pt.(psz c) <- v;
  sl_upd q 0 n_cls (U64.v c) v;
  sl_upd q n_cls n_cls (U64.v c) v;
  fold (cst t pt k (set_avail_at st (U64.v c) v) ol mf)
}

/// List 0's head.
fn c_read_lhead (t: pstate_t) (pt: A.array U64.t)
  (#k: erased cfix) (#st: erased pstate) (#ol: erased U64.t) (#mf: erased nat)
  requires cst t pt k st ol mf
  returns v: U64.t
  ensures cst t pt k st ol mf ** pure (v == FLs.fls_head st.large 0)
{
  unfold cst;
  with s q. assert (pts_to_range t.tpm k.clo k.chi s ** A.pts_to pt q);
  w_small ();
  let v = pt.(psz (o_lh_u64 ()));
  FLs.fls_head_set FLs.fls_empty 0 0 v;
  fold (cst t pt k st ol mf);
  v
}

let set_twice (v w: U64.t)
  : Lemma (FLs.fls_set (FLs.fls_set FLs.fls_empty 0 w) 0 v == FLs.fls_set FLs.fls_empty 0 v)
  = Seq.lemma_eq_intro (FLs.fls_set (FLs.fls_set FLs.fls_empty 0 w) 0 v) (FLs.fls_set FLs.fls_empty 0 v)

fn c_write_lhead (t: pstate_t) (pt: A.array U64.t) (v: U64.t)
  (#k: erased cfix) (#st: erased pstate) (#ol: erased U64.t) (#mf: erased nat)
  requires cst t pt k st ol mf
  ensures cst t pt k (set_lhead st v) ol mf
{
  unfold cst;
  with s q. assert (pts_to_range t.tpm k.clo k.chi s ** A.pts_to pt q);
  w_small ();
  pt.(psz (o_lh_u64 ())) <- v;
  sl_upd q 0 n_cls o_lh v;
  sl_upd q n_cls n_cls o_lh v;
  set_twice v (Seq.index q o_lh);
  fold (cst t pt k (set_lhead st v) ol mf)
}

/// The open link.
fn c_write_ol (t: pstate_t) (pt: A.array U64.t) (v: U64.t)
  (#k: erased cfix) (#st: erased pstate) (#ol: erased U64.t) (#mf: erased nat)
  requires cst t pt k st ol mf
  ensures cst t pt k st v mf
{
  unfold cst;
  with s q. assert (pts_to_range t.tpm k.clo k.chi s ** A.pts_to pt q);
  w_small ();
  pt.(psz (o_ol_u64 ())) <- v;
  sl_upd q 0 n_cls o_ol v;
  sl_upd q n_cls n_cls o_ol v;
  fold (cst t pt k st v mf)
}

/// The class tables.
fn c_cls_at (t: pstate_t) (pt: A.array U64.t) (c: U64.t{U64.v c < n_cls})
  (#k: erased cfix) (#st: erased pstate) (#ol: erased U64.t) (#mf: erased nat)
  requires cst t pt k st ol mf
  returns r: U64.t
  ensures cst t pt k st ol mf ** pure (U64.v r == cls (U64.v c))
{
  unfold cst;
  w_small ();
  cls_index (U64.v c);
  sl_index k.cw o_cl n_cls (U64.v c);
  let r = t.tw.(wsz (U64.add (o_cl_u64 ()) c));
  fold (cst t pt k st ol mf);
  r
}

fn c_ns_at (t: pstate_t) (pt: A.array U64.t) (c: U64.t{U64.v c < n_cls})
  (#k: erased cfix) (#st: erased pstate) (#ol: erased U64.t) (#mf: erased nat)
  requires cst t pt k st ol mf
  returns r: U64.t
  ensures cst t pt k st ol mf ** pure (U64.v r == n_slots (U64.v c))
{
  unfold cst;
  w_small ();
  cls_index (U64.v c);
  sl_index k.cw o_ns n_cls (U64.v c);
  let r = t.tw.(wsz (U64.add (o_ns_u64 ()) c));
  fold (cst t pt k st ol mf);
  r
}

ghost fn ch_bm_eq (bm: A.array U32.t) (#lo #hi: nat) (bs1 bs2: Seq.seq U32.t)
  requires ch_bm bm lo hi bs1 ** pure (bs1 == bs2)
  ensures ch_bm bm lo hi bs2
{
  rewrite (ch_bm bm lo hi bs1) as (ch_bm bm lo hi bs2)
}

ghost fn ch_heap_eq (hp: cheap_t) (#lo #hi: nat) (g1 g2: Base.heap)
  requires ch_heap hp lo hi g1 ** pure (g1 == g2)
  ensures ch_heap hp lo hi g2
{
  rewrite (ch_heap hp lo hi g1) as (ch_heap hp lo hi g2)
}

/// A free page met by the walk: the lowest free page is at most it.
fn c_note_free (t: pstate_t) (pt: A.array U64.t) (i: U64.t{U64.v i < n_pages})
  (#k: erased cfix) (#st: erased pstate) (#ol: erased U64.t) (#mf: erased nat)
  requires cst t pt k st ol mf
  ensures cst t pt k st ol (if U64.v i < mf then U64.v i else mf)
{
  unfold cst;
  with s q. assert (pts_to_range t.tpm k.clo k.chi s ** A.pts_to pt q);
  w_small ();
  let m = pt.(psz (o_mf_u64 ()));
  if (U64.lt i m) {
    pt.(psz (o_mf_u64 ())) <- i;
    sl_upd q 0 n_cls o_mf i;
    sl_upd q n_cls n_cls o_mf i;
    fold (cst t pt k st ol (if U64.v i < mf then U64.v i else mf))
  } else {
    fold (cst t pt k st ol (if U64.v i < mf then U64.v i else mf))
  }
}

/// The bitmap words outside pages `[lo, hi)` are those of `bs`.
let words_out (bs b: Seq.seq U32.t) (lo hi: nat) : prop =
  Seq.length b == Seq.length bs /\
  (forall (j: nat). j < Seq.length bs /\ (j < lo * BM.bpp \/ j >= hi * BM.bpp) ==> Seq.index b j == Seq.index bs j)

let words_out_clear (bs b: Seq.seq U32.t) (lo hi: nat) (a: nat)
  : Lemma (requires words_out bs b lo hi /\ Seq.length bs == BM.bm_len /\ page_base lo <= a /\ a + 8 <= page_base hi /\
                    a % 8 == 0 /\ hi <= n_pages)
          (ensures words_out bs (BM.clear_bit b a) lo hi)
  = bm_word_in lo hi a;
    BM.clear_bit_len b a

let words_out_zero (bs b: Seq.seq U32.t) (lo hi: nat) (i: nat)
  : Lemma (requires words_out bs b lo hi /\ lo <= i /\ i < hi)
          (ensures words_out bs (BM.zero_page b i) lo hi)
  = FStar.Math.Lemmas.lemma_mult_le_right BM.bpp lo i;
    FStar.Math.Lemmas.lemma_mult_le_right BM.bpp (i + 1) hi

let words_out_refl (bs: Seq.seq U32.t) (lo hi: nat) : Lemma (words_out bs bs lo hi) = ()

let words_out_trans (b0 b1 b2: Seq.seq U32.t) (lo hi lo' hi': nat)
  : Lemma (requires words_out b0 b1 lo hi /\ words_out b1 b2 lo' hi' /\ lo <= lo' /\ hi' <= hi)
          (ensures words_out b0 b2 lo hi)
  = FStar.Math.Lemmas.lemma_mult_le_right BM.bpp lo lo';
    FStar.Math.Lemmas.lemma_mult_le_right BM.bpp hi' hi

/// The bit of the word whose index from `zero_addr` is `wi`: as `bm_test`,
/// with the index computed by the caller.
inline_for_extraction
fn bm_test_w (bm: A.array U32.t) (wi: U64.t) (#a: erased nat) (#lo #hi: erased nat) (#bs: erased (Seq.seq U32.t))
  requires ch_bm bm lo hi bs ** pure (in_chunk lo hi a /\ U64.v wi == BM.widx a)
  returns b: bool
  ensures ch_bm bm lo hi bs ** pure (b == BM.marked bs a)
{
  unfold ch_bm;
  bm_len_ok lo hi;
  bm_word_in lo hi a;
  BM.widx_bound a;
  FStar.Math.Lemmas.pow2_lt_compat 64 32;
  FStar.UInt.shift_right_value_lemma #64 (U64.v wi) 5;
  assert_norm (pow2 5 == 32);
  let w = pts_to_range_index bm (SZ.uint64_to_sizet (U64.shift_right wi 5ul));
  let k = FStar.Int.Cast.uint64_to_uint32 (U64.logand wi 31UL);
  FStar.UInt.logand_mask #64 (U64.v wi) 5;
  assert_norm (pow2 5 - 1 == 31);
  BM.bit_test w k;
  fold (ch_bm bm lo hi bs);
  (U32.logand (U32.shift_right w k) 1ul <> 0ul)
}
