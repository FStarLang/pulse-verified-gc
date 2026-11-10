/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.State - the page allocator's state in memory
/// ---------------------------------------------------------------------------
///
/// The specification's state (`GC.Spec.Pages.Inv.pstate`) is a page map, the
/// heads of the lists of pages with a free slot (one per class), and #46's
/// list heads for the large-object area.  In memory they are three arrays:
///
///   - `pm`, one `prec` record per page.  The accessors read and write a
///     record as a `pinfo`, the C-friendly form of a `page_info`: the kind is
///     a code (0 free, 1 pool, 2 run head, 3 run continuation) with its
///     argument (the class, or the run length) beside it, and the free-slot
///     count is a machine word.  `view` reads a `pinfo` as a `page_info`; it
///     is total, so a record with a bad code or argument reads as a free
///     page, and the code tests below are exactly the tests `view` makes.
///   - `avail`, `n_cls` words;
///   - `large`, `n_lists` words, of which the allocator uses list 0 only;
///   - `meta`, two words: the free-page hint and the sweep epoch;
///   - three constant tables, as the prototype's `cls_of`, `cls_wh` and
///     `cls_ns`: the class of each size, the slot size and the slots per
///     page of each class.  `init` fills them; `pages_st` fixes their
///     contents to the specification's values.  (KaRaMeL writes a function
///     of constants as a chain of tests, which the C compiler does not
///     always make a table.)
///
/// **The sweep epoch.**  A stored record keeps, instead of a swept bit, the
/// epoch in which it was last swept (`sep`); it is swept when that is the
/// current epoch, and a free page is always swept.  So `start_epoch`, which
/// makes every page that is not free unswept (`StartSweep.clear_map`), only
/// adds one to the epoch, as OCaml 5's sweep start only swaps list heads;
/// it visits the pages only in the one cycle in 2^64 where the epoch wraps.
///
/// **The free-page hint.**  No page below the hint is free, so the search for
/// a free page, or for a run of them, starts there (the prototype's
/// `free_hint`).  `write_entry` lowers it when it writes a free page below
/// it.
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

/// A free page's record, as a test.
inline_for_extraction
let is_free_rec (r: pinfo) : bool = not (is_pool r) && not (is_head r) && not (is_cont r)

let is_free_rec_kind (r: pinfo) : Lemma (is_free_rec r <==> (view r).kind == Free) = ()

/// A stored record: a `pinfo` with the epoch of its last sweep in place of
/// the swept bit.
type prec = {
  pcode: U8.t;
  parg: U64.t;
  sep: U64.t;
  pfree_head: U64.t;
  pnfree: U64.t;
  pnext: U64.t;
}

/// The record a stored record stands for in epoch `ep`.
inline_for_extraction
let to_pinfo (ep: U64.t) (p: prec) : pinfo =
  let r0 = { code = p.pcode; arg = p.parg; swept = true;
             free_head = p.pfree_head; nfree = p.pnfree; next = p.pnext } in
  { r0 with swept = is_free_rec r0 || p.sep = ep }

/// A record stored in epoch `ep`: swept now, or never (epoch 0).
inline_for_extraction
let of_pinfo (ep: U64.t) (r: pinfo) : prec =
  { pcode = r.code; parg = r.arg; sep = (if r.swept then ep else 0UL);
    pfree_head = r.free_head; pnfree = r.nfree; pnext = r.next }

/// What may be stored: a free page's record is swept.
let storable (r: pinfo) : prop = is_free_rec r ==> r.swept

let to_of (ep: U64.t) (r: pinfo)
  : Lemma (requires U64.v ep >= 1 /\ storable r)
          (ensures view (to_pinfo ep (of_pinfo ep r)) == view r)
  = ()

let to_storable (ep: U64.t) (p: prec) : Lemma (storable (to_pinfo ep p)) = ()

/// The records of a page map, in epoch `ep`.
let pm_rel (s: Seq.seq prec) (ep: U64.t) (pm: page_map) : prop =
  Seq.length s == n_pages /\
  (forall (i: nat{i < n_pages}). view (to_pinfo ep (Seq.index s i)) == entry pm i)

let pm_rel_upd (s: Seq.seq prec) (ep: U64.t) (pm: page_map) (i: nat{i < n_pages}) (r: pinfo)
  : Lemma (requires pm_rel s ep pm /\ U64.v ep >= 1 /\ storable r)
          (ensures pm_rel (Seq.upd s i (of_pinfo ep r)) ep (Seq.upd pm i (view r)))
  = to_of ep r

/// No page below `h` is free.
let none_free_below (pm: page_map) (h: nat) : prop =
  forall (j: nat{j < n_pages}). j < h ==> (entry pm j).kind =!= Free

/// The hint and the epoch: no free page below the hint, and no record
/// swept in a later epoch than the current one.
let meta_ok (s: Seq.seq prec) (m: Seq.seq U64.t) (pm: page_map) : prop =
  Seq.length m == 2 /\ Seq.length s == n_pages /\
  U64.v (Seq.index m 1) >= 1 /\
  U64.v (Seq.index m 0) <= n_pages /\
  none_free_below pm (U64.v (Seq.index m 0)) /\
  (forall (i: nat{i < n_pages}). U64.v (Seq.index s i).sep <= U64.v (Seq.index m 1))

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
  tpm: A.array prec;
  tavail: A.array U64.t;
  tlarge: A.array U64.t;
  tmeta: A.array U64.t;   (* the free-page hint, the sweep epoch *)
  tcof: A.array U64.t;    (* small_max + 1 words: the class of each size *)
  tcls: A.array U64.t;    (* n_cls words: the slot size of each class *)
  tns: A.array U64.t;     (* n_cls words: the slots per page of each class *)
}

/// The tables' contents.
let cof_val (w: nat{w <= small_max}) : U64.t =
  if w >= 1 then (assert (n_cls == U64.v n_cls_u64); U64.uint_to_t (class_of w)) else 0UL

let cof_seq : Seq.seq U64.t = Seq.init (small_max + 1) cof_val

let cls_val (c: nat{c < n_cls}) : U64.t =
  cls_bounds c; FStar.Math.Lemmas.pow2_lt_compat 64 20; U64.uint_to_t (cls c)

let cls_seq : Seq.seq U64.t = Seq.init n_cls cls_val

let ns_val (c: nat{c < n_cls}) : U64.t =
  cls_bounds c; FStar.Math.Lemmas.pow2_lt_compat 64 20; U64.uint_to_t (n_slots c)

let ns_seq : Seq.seq U64.t = Seq.init n_cls ns_val

let cof_index (w: nat{1 <= w /\ w <= small_max})
  : Lemma (Seq.length cof_seq == small_max + 1 /\ U64.v (Seq.index cof_seq w) == class_of w)
  = assert (n_cls == U64.v n_cls_u64)

let cls_index (c: nat{c < n_cls})
  : Lemma (Seq.length cls_seq == n_cls /\ U64.v (Seq.index cls_seq c) == cls c /\
           Seq.length ns_seq == n_cls /\ U64.v (Seq.index ns_seq c) == n_slots c)
  = cls_bounds c; FStar.Math.Lemmas.pow2_lt_compat 64 20

let tables (t: pstate_t) : slprop =
  A.pts_to t.tcof cof_seq ** A.pts_to t.tcls cls_seq ** A.pts_to t.tns ns_seq

let pages_st (t: pstate_t) (st: pstate) : slprop =
  exists* (s: Seq.seq prec) (m: Seq.seq U64.t).
    A.pts_to t.tpm s ** A.pts_to t.tavail st.avail ** A.pts_to t.tlarge st.large **
    A.pts_to t.tmeta m ** tables t **
    pure (meta_ok s m st.pm /\ pm_rel s (Seq.index m 1) st.pm /\
          Seq.length st.avail == n_cls /\ Seq.length st.large == SC.n_lists)

/// The arrays before `init`: of the right lengths, holding anything.
let pages_raw (t: pstate_t) : slprop =
  exists* (s: Seq.seq prec) (m av lg cf cl ns: Seq.seq U64.t).
    A.pts_to t.tpm s ** A.pts_to t.tavail av ** A.pts_to t.tlarge lg ** A.pts_to t.tmeta m **
    A.pts_to t.tcof cf ** A.pts_to t.tcls cl ** A.pts_to t.tns ns **
    pure (Seq.length s == n_pages /\ Seq.length m == 2 /\
          Seq.length av == n_cls /\ Seq.length lg == SC.n_lists /\
          Seq.length cf == small_max + 1 /\ Seq.length cl == n_cls /\ Seq.length ns == n_cls)

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
  ensures pages_st t st ** pure (view r == entry st.pm (U64.v i) /\ storable r)
{
  unfold pages_st;
  with s m. assert (A.pts_to t.tpm s ** A.pts_to t.tmeta m);
  let ep = t.tmeta.(1sz);
  let p = t.tpm.(sz_of i);
  to_storable ep p;
  fold (pages_st t st);
  to_pinfo ep p
}

let set_entry (st: pstate) (i: nat{i < n_pages}) (e: page_info) : pstate =
  { st with pm = Seq.upd st.pm i e }

/// The hint stays valid when page `i` gets record `r`, lowered to `i` when
/// `r` is a free page's below it.
let hint_upd (pm: page_map) (h: nat) (i: nat{i < n_pages}) (r: pinfo)
  : Lemma (requires none_free_below pm h)
          (ensures none_free_below (Seq.upd pm i (view r)) (if is_free_rec r && i < h then i else h))
  = ()

let write_ok (s: Seq.seq prec) (m: Seq.seq U64.t) (pm: page_map) (i: nat{i < n_pages}) (r: pinfo)
  : Lemma (requires meta_ok s m pm /\ pm_rel s (Seq.index m 1) pm /\ storable r)
          (ensures (let ep = Seq.index m 1 in
                    let h = Seq.index m 0 in
                    let s' = Seq.upd s i (of_pinfo ep r) in
                    let pm' = Seq.upd pm i (view r) in
                    pm_rel s' ep pm' /\
                    (is_free_rec r /\ i < U64.v h ==> meta_ok s' (Seq.upd m 0 (U64.uint_to_t i)) pm') /\
                    (~(is_free_rec r /\ i < U64.v h) ==> meta_ok s' m pm')))
  = let ep = Seq.index m 1 in
    pm_rel_upd s ep pm i r;
    hint_upd pm (U64.v (Seq.index m 0)) i r

fn write_entry (t: pstate_t) (i: U64.t{U64.v i < n_pages}) (r: pinfo) (#st: erased pstate)
  requires pages_st t st ** pure (storable r)
  ensures pages_st t (set_entry st (U64.v i) (view r))
{
  unfold pages_st;
  with s m. assert (A.pts_to t.tpm s ** A.pts_to t.tmeta m);
  let ep = t.tmeta.(1sz);
  let h = t.tmeta.(0sz);
  t.tpm.(sz_of i) <- of_pinfo ep r;
  write_ok s m st.pm (U64.v i) r;
  if (is_free_rec r && U64.lt i h) {
    t.tmeta.(0sz) <- i;
    fold (pages_st t (set_entry st (U64.v i) (view r)))
  } else {
    fold (pages_st t (set_entry st (U64.v i) (view r)))
  }
}

/// `write_entry` for a record that is not a free page's: the hint stays as
/// it is, so it is not read.
fn write_used (t: pstate_t) (i: U64.t{U64.v i < n_pages}) (r: pinfo) (#st: erased pstate)
  requires pages_st t st ** pure (not (is_free_rec r))
  ensures pages_st t (set_entry st (U64.v i) (view r))
{
  unfold pages_st;
  with s m. assert (A.pts_to t.tpm s ** A.pts_to t.tmeta m);
  let ep = t.tmeta.(1sz);
  t.tpm.(sz_of i) <- of_pinfo ep r;
  write_ok s m st.pm (U64.v i) r;
  fold (pages_st t (set_entry st (U64.v i) (view r)))
}

/// A pool page's free-slot list head and count, and its class-list link,
/// read without the rest of the entry.
fn read_slots (t: pstate_t) (i: U64.t{U64.v i < n_pages}) (#st: erased pstate)
  requires pages_st t st
  returns r: prec
  ensures pages_st t st ** pure (r.pfree_head == (entry st.pm (U64.v i)).free_head /\
                                 U64.v r.pnfree == (entry st.pm (U64.v i)).nfree /\
                                 r.pnext == (entry st.pm (U64.v i)).next)
{
  unfold pages_st;
  let r = t.tpm.(sz_of i);
  fold (pages_st t st);
  r
}

/// The entry with a new free-slot list head and count.
let set_slots (st: pstate) (i: nat{i < n_pages}) (fh: U64.t) (nf: U64.t) : pstate =
  set_entry st i ({ entry st.pm i with free_head = fh; nfree = U64.v nf })

let slots_ok (s: Seq.seq prec) (m: Seq.seq U64.t) (pm: page_map) (i: nat{i < n_pages}) (fh nf: U64.t)
  : Lemma (requires meta_ok s m pm /\ pm_rel s (Seq.index m 1) pm)
          (ensures (let pm' = Seq.upd pm i ({ entry pm i with free_head = fh; nfree = U64.v nf }) in
                    let p = Seq.index s i in
                    meta_ok (Seq.upd s i ({ p with pfree_head = fh; pnfree = nf })) m pm' /\
                    pm_rel (Seq.upd s i ({ p with pfree_head = fh; pnfree = nf })) (Seq.index m 1) pm'))
  = ()

/// Write only the free-slot list head and count: the record is stored back
/// with its other fields as read, which the C compiler does not store again.
fn write_slots (t: pstate_t) (i: U64.t{U64.v i < n_pages}) (fh nf: U64.t) (#st: erased pstate)
  requires pages_st t st
  ensures pages_st t (set_slots st (U64.v i) fh nf)
{
  unfold pages_st;
  with s m. assert (A.pts_to t.tpm s ** A.pts_to t.tmeta m);
  let p = t.tpm.(sz_of i);
  t.tpm.(sz_of i) <- { p with pfree_head = fh; pnfree = nf };
  slots_ok s m st.pm (U64.v i) fh nf;
  fold (pages_st t (set_slots st (U64.v i) fh nf))
}

/// The free-page hint.
fn read_hint (t: pstate_t) (#st: erased pstate)
  requires pages_st t st
  returns h: U64.t
  ensures pages_st t st ** pure (U64.v h <= n_pages /\ none_free_below st.pm (U64.v h))
{
  unfold pages_st;
  let h = t.tmeta.(0sz);
  fold (pages_st t st);
  h
}

fn write_hint (t: pstate_t) (h: U64.t) (#st: erased pstate)
  requires pages_st t st ** pure (U64.v h <= n_pages /\ none_free_below st.pm (U64.v h))
  ensures pages_st t st
{
  unfold pages_st;
  t.tmeta.(0sz) <- h;
  fold (pages_st t st)
}

/// ---------------------------------------------------------------------------
/// The tables
/// ---------------------------------------------------------------------------

let small_sz (w: U64.t{U64.v w <= small_max}) : s: SZ.t{SZ.v s == U64.v w} =
  cls_bounds (n_cls - 1);
  FStar.Math.Lemmas.pow2_lt_compat 64 20;
  SZ.uint64_to_sizet w

/// The class of a block of `w` words, header included.
fn class_at (t: pstate_t) (w: U64.t{1 <= U64.v w /\ U64.v w <= small_max}) (#st: erased pstate)
  requires pages_st t st
  returns r: U64.t
  ensures pages_st t st ** pure (U64.v r == class_of (U64.v w))
{
  unfold pages_st;
  unfold tables;
  cof_index (U64.v w);
  let r = t.tcof.(small_sz w);
  fold (tables t);
  fold (pages_st t st);
  r
}

/// The slot size of class `c`.
fn cls_at (t: pstate_t) (c: U64.t{U64.v c < n_cls}) (#st: erased pstate)
  requires pages_st t st
  returns r: U64.t
  ensures pages_st t st ** pure (U64.v r == cls (U64.v c))
{
  unfold pages_st;
  unfold tables;
  cls_index (U64.v c);
  let r = t.tcls.(SZ.uint64_to_sizet c);
  fold (tables t);
  fold (pages_st t st);
  r
}

/// The slots per page of class `c`.
fn ns_at (t: pstate_t) (c: U64.t{U64.v c < n_cls}) (#st: erased pstate)
  requires pages_st t st
  returns r: U64.t
  ensures pages_st t st ** pure (U64.v r == n_slots (U64.v c))
{
  unfold pages_st;
  unfold tables;
  cls_index (U64.v c);
  let r = t.tns.(SZ.uint64_to_sizet c);
  fold (tables t);
  fold (pages_st t st);
  r
}

/// Fill the tables, once, from the parameters' functions.
fn fill_tables (t: pstate_t)
  requires exists* (cf cl ns: Seq.seq U64.t).
             A.pts_to t.tcof cf ** A.pts_to t.tcls cl ** A.pts_to t.tns ns **
             pure (Seq.length cf == small_max + 1 /\ Seq.length cl == n_cls /\ Seq.length ns == n_cls)
  ensures tables t
{
  cls_bounds (n_cls - 1);
  FStar.Math.Lemmas.pow2_lt_compat 64 20;
  let sm = cls_u64 (U64.sub n_cls_u64 1UL);
  t.tcof.(0sz) <- 0UL;
  let mut w = 1UL;
  while (U64.lte !w sm)
    invariant exists* vw (cf: Seq.seq U64.t).
      R.pts_to w vw ** A.pts_to t.tcof cf **
      pure (1 <= U64.v vw /\ U64.v vw <= small_max + 1 /\ Seq.length cf == small_max + 1 /\
            (forall (i: nat). i < U64.v vw ==> Seq.index cf i == cof_val i))
    decreases (small_max + 1 - U64.v !w)
  {
    let vw = !w;
    t.tcof.(small_sz vw) <- class_u64 vw;
    w := U64.add vw 1UL
  };
  with cf. assert (A.pts_to t.tcof cf);
  Seq.lemma_eq_intro cf cof_seq;
  let mut c = 0UL;
  while (U64.lt !c n_cls_u64)
    invariant exists* vc (cl ns: Seq.seq U64.t).
      R.pts_to c vc ** A.pts_to t.tcls cl ** A.pts_to t.tns ns **
      pure (U64.v vc <= n_cls /\ Seq.length cl == n_cls /\ Seq.length ns == n_cls /\
            (forall (i: nat). i < U64.v vc ==> Seq.index cl i == cls_val i /\ Seq.index ns i == ns_val i))
    decreases (n_cls - U64.v !c)
  {
    let vc = !c;
    t.tcls.(SZ.uint64_to_sizet vc) <- cls_u64 vc;
    t.tns.(SZ.uint64_to_sizet vc) <- n_slots_u64 vc;
    c := U64.add vc 1UL
  };
  with cl ns. assert (A.pts_to t.tcls cl ** A.pts_to t.tns ns);
  Seq.lemma_eq_intro cl cls_seq;
  Seq.lemma_eq_intro ns ns_seq;
  rewrite (A.pts_to t.tcof cf) as (A.pts_to t.tcof cof_seq);
  rewrite (A.pts_to t.tcls cl) as (A.pts_to t.tcls cls_seq);
  rewrite (A.pts_to t.tns ns) as (A.pts_to t.tns ns_seq);
  fold (tables t)
}

/// ---------------------------------------------------------------------------
/// The sweep epoch
/// ---------------------------------------------------------------------------

/// `GC.Spec.Pages.StartSweep.unsweep`, `clear_map`: every page that is not
/// free becomes unswept.
let unswept (e: page_info) : page_info =
  if e.kind = Free then e else { e with swept = false }

let unswept_map (pm: page_map) : page_map =
  Seq.init n_pages (fun (j: nat{j < n_pages}) -> unswept (entry pm j))

/// The next epoch: every stored epoch is now past.
let next_epoch (s: Seq.seq prec) (m: Seq.seq U64.t) (pm: page_map)
  : Lemma (requires meta_ok s m pm /\ pm_rel s (Seq.index m 1) pm /\
                    U64.v (Seq.index m 1) < pow2 64 - 1)
          (ensures (let m' = Seq.upd m 1 (U64.add (Seq.index m 1) 1UL) in
                    meta_ok s m' (unswept_map pm) /\ pm_rel s (Seq.index m' 1) (unswept_map pm)))
  = ()

/// Stored record `p`, swept in no epoch.
let unsep (p: prec) : prec = { p with sep = 0UL }

/// Records before `j` swept in no epoch, the rest as they were.
let unsep_upto (s0 s: Seq.seq prec) (j: nat) : prop =
  Seq.length s == Seq.length s0 /\
  (forall (i: nat). i < Seq.length s ==> Seq.index s i == (if i < j then unsep (Seq.index s0 i) else Seq.index s0 i))

/// The epoch wraps: epoch 1, every record swept in none.
let wrap_epoch (s0 s: Seq.seq prec) (m: Seq.seq U64.t) (pm: page_map)
  : Lemma (requires meta_ok s0 m pm /\ pm_rel s0 (Seq.index m 1) pm /\ unsep_upto s0 s n_pages)
          (ensures (let m' = Seq.upd m 1 1UL in
                    meta_ok s m' (unswept_map pm) /\ pm_rel s (Seq.index m' 1) (unswept_map pm)))
  = ()

/// Every page that is not free becomes unswept: one more epoch.
fn start_epoch (t: pstate_t) (#st: erased pstate)
  requires pages_st t st
  ensures pages_st t ({ st with pm = unswept_map st.pm })
{
  unfold pages_st;
  with s0 m. assert (A.pts_to t.tpm s0 ** A.pts_to t.tmeta m);
  let ep = t.tmeta.(1sz);
  if (U64.lt ep 0xFFFFFFFFFFFFFFFFUL) {
    assert_norm (pow2 64 - 1 == 0xFFFFFFFFFFFFFFFF);
    next_epoch s0 m st.pm;
    t.tmeta.(1sz) <- U64.add ep 1UL;
    fold (pages_st t ({ st with pm = unswept_map st.pm }))
  } else {
    let np = n_pages_u64 ();
    let mut j = 0UL;
    while (U64.lt !j np)
      invariant exists* vj s.
        R.pts_to j vj ** A.pts_to t.tpm s **
        pure (U64.v vj <= n_pages /\ unsep_upto s0 s (U64.v vj))
      decreases (n_pages - U64.v !j)
    {
      let vj = !j;
      let p = t.tpm.(sz_of vj);
      t.tpm.(sz_of vj) <- unsep p;
      j := U64.add vj 1UL
    };
    with s. assert (A.pts_to t.tpm s);
    wrap_epoch s0 s m st.pm;
    t.tmeta.(1sz) <- 1UL;
    fold (pages_st t ({ st with pm = unswept_map st.pm }))
  }
}

/// ---------------------------------------------------------------------------
/// The list heads
/// ---------------------------------------------------------------------------

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

fn clear_heads (t: pstate_t)
  requires exists* (av lg: Seq.seq U64.t). A.pts_to t.tavail av ** A.pts_to t.tlarge lg **
             pure (Seq.length av == n_cls /\ Seq.length lg == SC.n_lists)
  ensures A.pts_to t.tavail (Seq.create n_cls 0UL) ** A.pts_to t.tlarge FLs.fls_empty
{
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
  rewrite (A.pts_to t.tavail av) as (A.pts_to t.tavail (Seq.create n_cls 0UL));
  rewrite (A.pts_to t.tlarge lg) as (A.pts_to t.tlarge FLs.fls_empty)
}

/// Every list head 0: the lists of pages with a free slot and the large
/// lists are empty.
fn clear_lists (t: pstate_t) (#st: erased pstate)
  requires pages_st t st
  ensures pages_st t ({ st with avail = Seq.create n_cls 0UL; large = FLs.fls_empty })
{
  unfold pages_st;
  clear_heads t;
  fold (pages_st t ({ st with avail = Seq.create n_cls 0UL; large = FLs.fls_empty }))
}

/// ---------------------------------------------------------------------------
/// The arrays at the start
/// ---------------------------------------------------------------------------

/// A free page's record, stored.
inline_for_extraction
let free_prec : prec =
  { pcode = 0uy; parg = 0UL; sep = 1UL; pfree_head = 0UL; pnfree = 0UL; pnext = 0UL }

/// The state of a heap of free pages with every list empty.
let empty_state : pstate = { pm = all_free; avail = Seq.create n_cls 0UL; large = FLs.fls_empty }

let reset_done (s: Seq.seq prec) (m: Seq.seq U64.t)
  : Lemma (requires Seq.length s == n_pages /\ Seq.length m == 2 /\
                    Seq.index m 0 == 0UL /\ Seq.index m 1 == 1UL /\
                    (forall (i: nat). i < n_pages ==> Seq.index s i == free_prec))
          (ensures meta_ok s m all_free /\ pm_rel s (Seq.index m 1) all_free)
  = ()

/// Every page free, every list empty, epoch 1 and hint 0, from any arrays of
/// the right lengths.
fn reset_state (t: pstate_t)
  requires pages_raw t
  ensures pages_st t empty_state
{
  unfold pages_raw;
  let np = n_pages_u64 ();
  let mut j = 0UL;
  while (U64.lt !j np)
    invariant exists* vj s.
      R.pts_to j vj ** A.pts_to t.tpm s **
      pure (U64.v vj <= n_pages /\ Seq.length s == n_pages /\
            (forall (i: nat). i < U64.v vj ==> Seq.index s i == free_prec))
    decreases (n_pages - U64.v !j)
  {
    let vj = !j;
    t.tpm.(sz_of vj) <- free_prec;
    j := U64.add vj 1UL
  };
  t.tmeta.(0sz) <- 0UL;
  t.tmeta.(1sz) <- 1UL;
  with s m. assert (A.pts_to t.tpm s ** A.pts_to t.tmeta m);
  reset_done s m;
  clear_heads t;
  fill_tables t;
  fold (pages_st t empty_state)
}
