/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.TopMinor - the pages code with its nursery and remembered set
/// ---------------------------------------------------------------------------
///
/// Design doc §18, step 2.  `crep2 c sty es`: the code's state represents
/// the configuration after the events `es` (`GC.Impl.Pages.Top.crep`), and
/// besides: the nursery is the configuration's (`is_minor`, bottom-up, as
/// `GC.Spec.Top.Young` reads it), the remembered set is a table of field
/// addresses in order (`CodeMinor.tbl_ok`), every remembered slot is a
/// scannable field of a kept block (`CodeMinor.rem_ok`), and the run has not
/// stopped.  The wrappers:
///   - `init2`: the start, an empty nursery and table;
///   - `alloc2`: `EAlloc`, then the Fill's young fields appended to the
///     table (the barrier's `binit`, each slot once, in order);
///   - `yalloc2`: `EYoungAlloc`, a bump allocation in the nursery;
///   - `minor2`: `EMinor`, the Pulse minor collection on the roots the
///     model forwards (the program's young roots, then the remembered
///     slots' young words), the table emptied; on a failed allocation the
///     run stops (`stopped2`);
///   - `handover2`: a minor collection, then `EHandover`;
///   - `sweep2`, `roots2`, `read2`: step 1's events, the nursery and the
///     table unchanged.

module GC.Impl.Pages.TopMinor

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Impl.MinorHeap
open GC.Impl.Heap
open GC.Impl.Pages.State
module SB = GC.Spec.Base
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Top.Run

module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
module Seq = FStar.Seq
module L = FStar.List.Tot
module M = GC.Spec.Top.Heap
module T = GC.Spec.Top.Iface
module W = GC.Spec.Top.Word
module Abs = GC.Spec.Top.Abs
module BF = GC.Spec.Top.ByteFacts
module PAl = GC.Spec.Top.PagesAlloc
module AT = GC.Spec.Pages.AllocTag
module CP = GC.Spec.Top.CodePages
module CR = GC.Spec.Top.CodeRun
module CM = GC.Spec.Top.CodeMinor
module PT = GC.Impl.Pages.Top
module Fw = GC.Impl.Pages.Forward

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The representation
/// ---------------------------------------------------------------------------

/// The code's state.
noeq type cstate = {
  heap: heap_t;
  t: pstate_t;
  pr: R.ref U8.t;
  cr: R.ref U64.t;
  mh: minor_heap_t;
  tb: A.array U64.t;
  tn: R.ref SZ.t;
}

/// What the nursery and the table keep of the configuration.
let side (es: list event) (d: minor_heap) (b: U64.t) (tv: Seq.seq U64.t) (n: nat) : prop =
  let x = CP.xc es in
  Fw.mst d b == x.w.cyng /\ CM.tbl_ok tv n x.w.crem /\ CM.rem_ok x /\ x.stopped == false

/// **The code's state represents the configuration after `es`.**
let crep2 (c: cstate) (sty: style) (es: list event) : slprop =
  PT.crep c.heap c.t c.pr c.cr sty es **
  (exists* (d: minor_heap) (b: U64.t) (tv: Seq.seq U64.t) (n: SZ.t).
     is_minor c.mh d b ** A.pts_to c.tb tv ** R.pts_to c.tn n **
     pure (CP.good sty es /\ side es d b tv (SZ.v n)))

/// ---------------------------------------------------------------------------
/// The start
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let init_side (sty: style) (tv: Seq.seq U64.t)
  : Lemma (requires n_pages > 0)
          (ensures CP.good sty [] /\ side [] (Seq.create minor_heap_size 0uy) 0UL tv 0)
  = CP.init_cfg sty;
    CR.nil_run CP.pc sty W.msize W.ywords;
    let x = CP.xc [] in
    assert (x == init_config CP.pc W.msize W.ywords);
    assert (x.w.crem == [] /\ x.stopped == false);
    assert (x.w.cyng == GC.Spec.Top.Young.yinit W.ywords);
    let ms = minor_init (Seq.create minor_heap_size 0uy) in
    U64.v_inj ms.bump 0UL;
    assert (ms == { data = ms.data; bump = ms.bump });
    CM.rem_nil x
#pop-options

/// **The start**: when there is a page, the initial configuration, an
/// empty nursery and table.
fn init2 (c: cstate) (sty: erased style)
  requires is_heap c.heap 'g ** pages_raw c.t ** R.pts_to c.pr 'p0 ** R.pts_to c.cr 'c0 **
           is_minor c.mh 'd 'b ** A.pts_to c.tb 'tv ** R.pts_to c.tn 'n
  returns ok: bool
  ensures (if ok then crep2 c sty []
           else is_heap c.heap 'g ** pages_raw c.t ** R.pts_to c.pr 'p0 ** R.pts_to c.cr 'c0 **
                is_minor c.mh 'd 'b ** A.pts_to c.tb 'tv ** R.pts_to c.tn 'n)
{
  let ok = PT.init_top c.heap c.t c.pr c.cr sty;
  if ok {
    rewrite (if ok then PT.crep c.heap c.t c.pr c.cr sty []
             else is_heap c.heap 'g ** pages_raw c.t ** R.pts_to c.pr 'p0 ** R.pts_to c.cr 'c0)
         as (PT.crep c.heap c.t c.pr c.cr sty []);
    unfold PT.crep;
    with x cv. assert (is_heap c.heap (CP.hof x) ** R.pts_to c.cr cv);
    fold (PT.crep c.heap c.t c.pr c.cr sty []);
    minor_heap_reset c.mh;
    c.tn := 0sz;
    init_side sty 'tv;
    fold (crep2 c sty []);
    true
  } else {
    rewrite (if ok then PT.crep c.heap c.t c.pr c.cr sty []
             else is_heap c.heap 'g ** pages_raw c.t ** R.pts_to c.pr 'p0 ** R.pts_to c.cr 'c0)
         as (is_heap c.heap 'g ** pages_raw c.t ** R.pts_to c.pr 'p0 ** R.pts_to c.cr 'c0);
    false
  }
}

/// ---------------------------------------------------------------------------
/// Allocation, its Fill, and the table
/// ---------------------------------------------------------------------------

/// The run-time test for a young word.
inline_for_extraction
let young_u64 (w: U64.t) : (r: bool{r == W.is_young_w w}) =
  U64.rem w 8UL = 0UL && U64.gte w 8UL && U64.lt w minor_heap_size_u64

/// What the allocation does to the nursery, the remembered set and the run.
#push-options "--z3rlimit 40"
let alloc_side (sty: style) (es: list event) (wz: nat) (tag: nat) (vs: list M.value) (ws: Seq.seq U64.t)
               (d: minor_heap) (b: U64.t) (tv: Seq.seq U64.t) (n: nat)
  : Lemma (requires CP.good sty es /\ side es d b tv n /\ tag < 256 /\ wz >= 1 /\
                    CR.allowed CP.pc sty (CP.xc es) (EAlloc wz tag vs) /\
                    Seq.length ws == wz /\
                    (forall (i: nat). i < wz ==> Seq.index ws i == W.concv (L.index vs i)))
          (ensures (let x = CP.xc es in
                    let (_, _, o) = AT.alloc_tag (PAl.iph x.ph) (CP.hof x) (CP.sof x).ps wz (PAl.tg tag) in
                    let es' = L.append es [EAlloc wz tag vs] in
                    let x' = CP.xc es' in
                    CP.good sty es' /\
                    (o == 0UL ==> side es' d b tv n) /\
                    (o =!= 0UL ==>
                       Abs.pos (BF.maddr o) + 8 == U64.v o /\ U64.v o + 8 * wz <= SB.heap_size /\
                       Fw.mst d b == x'.w.cyng /\ CM.rem_ok x' /\ x'.stopped == false /\
                       x'.w.crem == L.append x.w.crem (CM.ynew_s (BF.maddr o) (tag < 251) ws 0))))
  = let x = CP.xc es in
    let e = EAlloc wz tag vs in
    let (g', _, o) = AT.alloc_tag (PAl.iph x.ph) (CP.hof x) (CP.sof x).ps wz (PAl.tg tag) in
    if o = 0UL then begin
      CP.alloc_none sty es wz tag vs;
      CP.snoc sty es e
    end
    else begin
      CP.alloc_some sty es wz tag vs;
      CP.snoc sty es e;
      CM.alloc_rem sty es wz tag vs;
      CM.ynew_code g' (BF.maddr o) 0 vs ws
    end
#pop-options

#push-options "--fuel 1"
let pre0 (rem: list M.slot) (m: nat) (sc: bool) (ws: Seq.seq U64.t)
  : Lemma (L.append rem (CM.ypre m sc ws 0) == rem)
  = L.append_l_nil rem
#pop-options

/// A Fill slot's address.
let slot_at (o: U64.t) (m k wz: nat)
  : Lemma (requires Abs.pos m + 8 == U64.v o /\ U64.v o + 8 * wz <= SB.heap_size /\ k < wz)
          (ensures U64.v o + 8 * k < pow2 64 /\ U64.v (CM.slot_word (m, k)) == U64.v o + 8 * k)
  = CM.slot_word_hp m k

/// **`EAlloc`**: the allocation of the phase, the Fill, then the Fill's
/// young fields of a scannable block appended to the table, in order.  The
/// table must have room for the block's fields.
#push-options "--z3rlimit 40"
fn alloc2 (c: cstate) (wz: U64.t{U64.v wz >= 1}) (tag: U64.t{U64.v tag < 256}) (fs: A.array U64.t) (#p: perm)
  (#ws: erased (Seq.seq U64.t)) (#sty: erased style) (#es: erased (list event)) (vs: erased (list M.value))
  requires crep2 c sty es ** A.pts_to fs #p ws **
           pure (Seq.length ws == U64.v wz /\ L.length vs == U64.v wz /\
                 (forall (i: nat). i < U64.v wz ==> Seq.index ws i == W.concv (L.index vs i)) /\
                 CR.allowed CP.pc sty (CP.xc es) (EAlloc (U64.v wz) (U64.v tag) vs) /\
                 L.length (CP.xc es).w.crem + U64.v wz <= A.length c.tb)
  returns o: U64.t
  ensures crep2 c sty (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]) ** A.pts_to fs #p ws **
          pure (o == 0UL ==> CP.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]) == CP.xc es)
{
  unfold crep2;
  with d b tv n. assert (is_minor c.mh d b ** A.pts_to c.tb tv ** R.pts_to c.tn n);
  A.pts_to_len c.tb;
  let o = PT.alloc_top c.heap c.t c.pr c.cr wz tag fs vs;
  alloc_side sty es (U64.v wz) (U64.v tag) vs ws d b tv (SZ.v n);
  if (o = 0UL) {
    fold (crep2 c sty (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]));
    o
  } else {
    let sc = U64.lt tag 251UL;
    let m : erased nat = BF.maddr o;
    assert (pure (Abs.pos m + 8 == U64.v o /\ U64.v o + 8 * U64.v wz <= SB.heap_size));
    pre0 (CP.xc es).w.crem m sc ws;
    let mut k = 0UL;
    while (U64.lt !k wz)
      invariant exists* vk tvk nk.
        R.pts_to k vk ** A.pts_to c.tb tvk ** R.pts_to c.tn nk ** A.pts_to fs #p ws **
        pure (U64.v vk <= U64.v wz /\ Seq.length tvk == A.length c.tb /\
              Abs.pos m + 8 == U64.v o /\ U64.v o + 8 * U64.v wz <= SB.heap_size /\
              SZ.v nk <= L.length (CP.xc es).w.crem + U64.v vk /\
              CM.tbl_ok tvk (SZ.v nk) (L.append (CP.xc es).w.crem (CM.ypre m sc ws (U64.v vk))))
      decreases (U64.v wz - U64.v !k)
    {
      let vk = !k;
      with tvk nk. assert (A.pts_to c.tb tvk ** R.pts_to c.tn nk);
      let w = fs.(SZ.uint64_to_sizet vk);
      CM.ypre_step m sc ws (U64.v vk);
      if (sc && young_u64 w) {
        let nv = !c.tn;
        slot_at o m (U64.v vk) (U64.v wz);
        let a = U64.add o (U64.mul 8UL vk);
        U64.v_inj a (CM.slot_word (reveal m, U64.v vk));
        c.tb.(nv) <- a;
        CM.tbl_snoc tvk (SZ.v nk) (L.append (CP.xc es).w.crem (CM.ypre m sc ws (U64.v vk))) (reveal m, U64.v vk);
        L.append_assoc (CP.xc es).w.crem (CM.ypre m sc ws (U64.v vk)) [(reveal m, U64.v vk)];
        c.tn := SZ.add nv 1sz;
        k := U64.add vk 1UL
      } else {
        CM.tbl_keep tvk (SZ.v nk) (L.append (CP.xc es).w.crem (CM.ypre m sc ws (U64.v vk)));
        L.append_assoc (CP.xc es).w.crem (CM.ypre m sc ws (U64.v vk)) [];
        k := U64.add vk 1UL
      }
    };
    CM.ypre_len m sc ws;
    fold (crep2 c sty (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]));
    o
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// The events that leave the nursery and the table
/// ---------------------------------------------------------------------------

/// The step keeps what the nursery and the table represent.
let leave_side (sty: style) (es: list event) (e: event) (d: minor_heap) (b: U64.t) (tv: Seq.seq U64.t) (n: nat)
  : Lemma (requires CP.good sty es /\ side es d b tv n /\ CR.allowed CP.pc sty (CP.xc es) e /\
                    CM.leaves_rem e /\ ~(EYoungAlloc? e) /\ ~(EWrite? e) /\
                    CP.xc (L.append es [e]) == step CP.pc (CP.xc es) e)
          (ensures side (L.append es [e]) d b tv n)
  = CM.rem_leave sty es e

/// **A sweep step**: `ESweep`, or `EEnd` when the sweep is done.
fn sweep2 (c: cstate) (#sty: erased style) (#es: erased (list event))
  requires crep2 c sty es ** pure (T.Sweeping? (CP.xc es).ph)
  returns more: bool
  ensures crep2 c sty (L.append es [if more then ESweep else EEnd])
{
  unfold crep2;
  with d b tv n. assert (is_minor c.mh d b ** A.pts_to c.tb tv ** R.pts_to c.tn n);
  let more = PT.sweep_step_top c.heap c.t c.pr c.cr;
  leave_side sty es (if more then ESweep else EEnd) d b tv (SZ.v n);
  unfold PT.crep;
  with x cv. assert (is_heap c.heap (CP.hof x) ** R.pts_to c.cr cv);
  fold (PT.crep c.heap c.t c.pr c.cr sty (L.append es [if more then ESweep else EEnd]));
  fold (crep2 c sty (L.append es [if more then ESweep else EEnd]));
  more
}

/// **`ERoots`**: the program's roots, replaced.
ghost fn roots2 (c: cstate) (#sty: erased style) (#es: erased (list event)) (rs: list M.value)
  requires crep2 c sty es ** pure (CR.allowed CP.pc sty (CP.xc es) (ERoots rs))
  ensures crep2 c sty (L.append es [ERoots rs])
{
  unfold crep2;
  with d b tv n. assert (is_minor c.mh d b ** A.pts_to c.tb tv ** R.pts_to c.tn n);
  PT.roots_top c.heap c.t c.pr c.cr rs;
  leave_side sty es (ERoots rs) d b tv (SZ.v n);
  unfold PT.crep;
  with x cv. assert (is_heap c.heap (CP.hof x) ** R.pts_to c.cr cv);
  fold (PT.crep c.heap c.t c.pr c.cr sty (L.append es [ERoots rs]));
  fold (crep2 c sty (L.append es [ERoots rs]))
}

/// **`ERead`** of a major block's field into a new root.
ghost fn read2 (c: cstate) (#sty: erased style) (#es: erased (list event)) (o i: nat)
  requires crep2 c sty es ** pure (CR.allowed CP.pc sty (CP.xc es) (ERead (M.Major o) i))
  ensures crep2 c sty (L.append es [ERead (M.Major o) i])
{
  unfold crep2;
  with d b tv n. assert (is_minor c.mh d b ** A.pts_to c.tb tv ** R.pts_to c.tn n);
  PT.read_top c.heap c.t c.pr c.cr o i;
  leave_side sty es (ERead (M.Major o) i) d b tv (SZ.v n);
  unfold PT.crep;
  with x cv. assert (is_heap c.heap (CP.hof x) ** R.pts_to c.cr cv);
  fold (PT.crep c.heap c.t c.pr c.cr sty (L.append es [ERead (M.Major o) i]));
  fold (crep2 c sty (L.append es [ERead (M.Major o) i]))
}

/// ---------------------------------------------------------------------------
/// Young allocation
/// ---------------------------------------------------------------------------

module Y = GC.Spec.Top.Young
module Obj = GC.Impl.Object
module Hdr = GC.Lib.Header

/// The white header the nursery's allocation writes.
let hdr_eq (wz: U64.t) (tag: U64.t)
  : Lemma (requires U64.v wz >= 1 /\ U64.v wz < pow2 54 /\ U64.v tag < 256)
          (ensures Obj.makeHeader wz Hdr.White tag == W.enc_hdr (Y.white_hdr (U64.v wz) (U64.v tag)))
  = Obj.makeHeader_eq_pack_header wz Hdr.White tag;
    U64.v_inj (Obj.makeHeader wz Hdr.White tag) (W.enc_hdr (Y.white_hdr (U64.v wz) (U64.v tag)))

/// A word written into the nursery, as the model writes it.
let mwrite_eq (d: minor_heap) (p: U64.t) (v: U64.t)
  : Lemma (requires U64.v p % 8 == 0 /\ U64.v p + 8 <= minor_heap_size)
          (ensures Y.mwrite d (U64.v p) v == minor_write_word_t d p v)
  = Y.msz ();
    U64.uv_inv p;
    assert (Y.ok_pos (U64.v p));
    assert (minor_write_word_t d p v == minor_write_word d p v);
    assert (Y.mwrite d (U64.v p) v == minor_write_word d (U64.uint_to_t (U64.v p)) v)
      by (FStar.Tactics.norm [delta_only [`%Y.mwrite]; iota; zeta; primops]; FStar.Tactics.smt ())

/// The fields, one at a time.
#push-options "--fuel 1"
let wf_step (d: minor_heap) (p: nat) (vs: list M.value) (k: nat)
  : Lemma (requires k < L.length vs)
          (ensures Y.write_fields d p (CP.ldrop k vs) ==
                   Y.write_fields (Y.mwrite d p (W.concv (L.index vs k))) (p + 8) (CP.ldrop (k + 1) vs))
  = CP.ldrop_cons k vs

let wf_done (d: minor_heap) (p: nat) (vs: list M.value)
  : Lemma (Y.write_fields d p (CP.ldrop (L.length vs) vs) == d)
  = CP.ldrop_all vs
#pop-options

/// The room test does not overflow.
let room_arith (bv wz: U64.t)
  : Lemma (requires U64.v bv <= minor_heap_size /\ U64.v wz <= max_young_wosize)
          (ensures U64.v wz + 1 < pow2 64 /\ 8 * (U64.v wz + 1) < pow2 64 /\
                   U64.v bv + 8 * (U64.v wz + 1) < pow2 64 /\ U64.v wz < pow2 54)
  = max_young_object_fits ();
    Y.msz ();
    assert_norm (pow2 57 + pow2 57 < pow2 64);
    assert_norm (pow2 57 == 8 * pow2 54)

/// The bump past a young block.
let bump_next (bv wz: U64.t)
  : Lemma (requires U64.v bv % 8 == 0 /\ U64.v bv + 8 * (U64.v wz + 1) <= minor_heap_size)
          (ensures (U64.v bv + 8 * (U64.v wz + 1)) % 8 == 0)
  = FStar.Math.Lemmas.modulo_addition_lemma (U64.v bv) 8 (U64.v wz + 1)

/// A field's offset in the nursery.
let yfield_at (bv wz: U64.t) (k: nat)
  : Lemma (requires U64.v bv % 8 == 0 /\ U64.v bv + 8 * (U64.v wz + 1) <= minor_heap_size /\ k < U64.v wz)
          (ensures U64.v bv + 8 + 8 * k + 8 <= minor_heap_size /\ (U64.v bv + 8 + 8 * k) % 8 == 0 /\
                   8 * k < pow2 64 /\ 8 + 8 * k < pow2 64 /\ U64.v bv + 8 + 8 * k < pow2 64)
  = Y.msz ()

/// What the allocation does to the run.
#push-options "--z3rlimit 40"
let yalloc_side (sty: style) (es: list event) (wz: M.size_t) (tag: M.tag_t) (vs: list M.value)
                (d: minor_heap) (b: U64.t) (tv: Seq.seq U64.t) (n: nat)
  : Lemma (requires CP.good sty es /\ side es d b tv n /\
                    style_ok sty (CP.xc es) (EYoungAlloc wz tag vs) /\ mutator_ok (CP.xc es) (EYoungAlloc wz tag vs) /\
                    wz <= max_young_wosize /\ U64.v b % 8 == 0 /\ U64.v b + 8 * (wz + 1) <= minor_heap_size)
          (ensures (Y.msz ();
                    let d1 = Y.mwrite d (U64.v b) (W.enc_hdr (Y.white_hdr wz tag)) in
                    let d2 = Y.write_fields d1 (U64.v b + 8) vs in
                    let b2 = U64.uint_to_t (U64.v b + 8 * (wz + 1)) in
                    let es' = L.append es [EYoungAlloc wz tag vs] in
                    CP.good sty es' /\ side es' d2 b2 tv n /\
                    CP.hof (CP.xc es') == CP.hof (CP.xc es) /\ CP.sof (CP.xc es') == CP.sof (CP.xc es) /\
                    (CP.xc es').ph == (CP.xc es).ph))
  = let x = CP.xc es in
    let e = EYoungAlloc wz tag vs in
    assert (Some? (Y.yalloc x.w.cyng wz tag vs));
    assert (CR.allowed CP.pc sty x e);
    CP.snoc sty es e;
    CM.rem_leave sty es e
#pop-options

/// The fields of a young block, written in order after its header.
#push-options "--z3rlimit 40"
fn yfill (mh: minor_heap_t) (bv: U64.t) (wz: U64.t) (fs: A.array U64.t) (#p: perm)
  (#ws: erased (Seq.seq U64.t)) (vs: erased (list M.value))
  requires is_minor mh 'd 'b ** A.pts_to fs #p ws **
           pure (U64.v bv % 8 == 0 /\ U64.v bv + 8 * (U64.v wz + 1) <= minor_heap_size /\
                 Seq.length ws == U64.v wz /\ L.length vs == U64.v wz /\
                 (forall (i: nat). i < U64.v wz ==> Seq.index ws i == W.concv (L.index vs i)))
  ensures exists* d2. is_minor mh d2 'b ** A.pts_to fs #p ws **
          pure (d2 == Y.write_fields 'd (U64.v bv + 8) vs)
{
  CP.ldrop_zero (reveal vs);
  let mut k = 0UL;
  while (U64.lt !k wz)
    invariant exists* vk dk.
      R.pts_to k vk ** is_minor mh dk 'b ** A.pts_to fs #p ws **
      pure (U64.v vk <= U64.v wz /\
            Y.write_fields dk (U64.v bv + 8 + 8 * U64.v vk) (CP.ldrop (U64.v vk) vs) ==
            Y.write_fields 'd (U64.v bv + 8) vs)
    decreases (U64.v wz - U64.v !k)
  {
    let vk = !k;
    with dk. assert (is_minor mh dk 'b);
    let w = fs.(SZ.uint64_to_sizet vk);
    wf_step dk (U64.v bv + 8 + 8 * U64.v vk) vs (U64.v vk);
    yfield_at bv wz (U64.v vk);
    let a = U64.add bv (U64.add 8UL (U64.mul 8UL vk));
    mwrite_eq dk a w;
    minor_write mh a w;
    k := U64.add vk 1UL
  };
  with vk dk. assert (R.pts_to k vk ** is_minor mh dk 'b);
  assert (pure (U64.v vk == L.length vs));
  assert (pure (Y.write_fields dk (U64.v bv + 8 + 8 * U64.v vk) (CP.ldrop (U64.v vk) vs) ==
                Y.write_fields 'd (U64.v bv + 8) vs));
  wf_done dk (U64.v bv + 8 + 8 * U64.v vk) vs;
  assert (pure (Y.write_fields dk (U64.v bv + 8 + 8 * U64.v vk) (CP.ldrop (U64.v vk) vs) == dk))
}
#pop-options

/// **`EYoungAlloc`**: a white header at the bump, the fields after it, the
/// bump past them.  Returns the object's address, or 0 when the object is
/// too big or the nursery has no room: then no event.
#push-options "--z3rlimit 40"
fn yalloc2 (c: cstate) (wz: U64.t{U64.v wz >= 1}) (tag: U64.t{U64.v tag < 256}) (fs: A.array U64.t) (#p: perm)
  (#ws: erased (Seq.seq U64.t)) (#sty: erased style) (#es: erased (list event)) (vs: erased (list M.value))
  requires crep2 c sty es ** A.pts_to fs #p ws **
           pure (Seq.length ws == U64.v wz /\ L.length vs == U64.v wz /\
                 (forall (i: nat). i < U64.v wz ==> Seq.index ws i == W.concv (L.index vs i)) /\
                 style_ok sty (CP.xc es) (EYoungAlloc (U64.v wz) (U64.v tag) vs) /\
                 mutator_ok (CP.xc es) (EYoungAlloc (U64.v wz) (U64.v tag) vs))
  returns o: U64.t
  ensures A.pts_to fs #p ws **
          (if o = 0UL then crep2 c sty es else crep2 c sty (L.append es [EYoungAlloc (U64.v wz) (U64.v tag) vs]))
{
  unfold crep2;
  with d b tv n. assert (is_minor c.mh d b ** A.pts_to c.tb tv ** R.pts_to c.tn n);
  unfold is_minor;
  let bv = !c.mh.bump_ref;
  fold (is_minor c.mh d b);
  if (U64.lte wz max_young_wosize_u64) {
  room_arith bv wz;
  if (U64.lte (U64.add bv (U64.mul 8UL (U64.add wz 1UL))) minor_heap_size_u64) {
    Y.msz ();
    hdr_eq wz tag;
    let hdr = Obj.makeHeader wz Hdr.White tag;
    mwrite_eq d bv hdr;
    minor_write c.mh bv hdr;
    yfill c.mh bv wz fs vs;
    with dk. assert (is_minor c.mh dk b);
    let b2 = U64.add bv (U64.mul 8UL (U64.add wz 1UL));
    bump_next bv wz;
    unfold is_minor;
    c.mh.bump_ref := b2;
    fold (is_minor c.mh dk b2);
    yalloc_side sty es (U64.v wz) (U64.v tag) vs d b tv (SZ.v n);
    PT.young_top c.heap c.t c.pr c.cr (EYoungAlloc (U64.v wz) (U64.v tag) vs);
    fold (crep2 c sty (L.append es [EYoungAlloc (U64.v wz) (U64.v tag) vs]));
    let o = U64.add bv 8UL;
    rewrite (crep2 c sty (L.append es [EYoungAlloc (U64.v wz) (U64.v tag) vs])) as (if o = 0UL then crep2 c sty es else crep2 c sty (L.append es [EYoungAlloc (U64.v wz) (U64.v tag) vs]));
    o
  } else {
    fold (crep2 c sty es);
    rewrite (crep2 c sty es) as (if 0UL = 0UL then crep2 c sty es else crep2 c sty (L.append es [EYoungAlloc (U64.v wz) (U64.v tag) vs]));
    0UL
  }
  } else {
    fold (crep2 c sty es);
    rewrite (crep2 c sty es) as (if 0UL = 0UL then crep2 c sty es else crep2 c sty (L.append es [EYoungAlloc (U64.v wz) (U64.v tag) vs]));
    0UL
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// The minor collection's inputs
/// ---------------------------------------------------------------------------

module FA = GC.Gen.ForwardingArray

let fsz : (n: SZ.t{SZ.v n == FA.fwd_array_size}) = SZ.uint64_to_sizet (U64.div minor_heap_size_u64 8UL)

/// Zero the forwarding array.
fn zero_fwd (fa: A.array U64.t)
  requires A.pts_to fa 'v ** pure (Seq.length 'v == FA.fwd_array_size)
  ensures exists* v. A.pts_to fa v **
          pure (Seq.length v == FA.fwd_array_size /\ (forall (i: nat). i < FA.fwd_array_size ==> Seq.index v i == 0UL))
{
  let mut i = 0sz;
  while (SZ.lt !i fsz)
    invariant exists* vi v.
      R.pts_to i vi ** A.pts_to fa v **
      pure (SZ.v vi <= FA.fwd_array_size /\ Seq.length v == FA.fwd_array_size /\
            (forall (j: nat). j < SZ.v vi ==> Seq.index v j == 0UL))
    decreases (FA.fwd_array_size - SZ.v !i)
  {
    let vi = !i;
    fa.(vi) <- 0UL;
    i := SZ.add vi 1sz
  }
}

/// The run-time test for a word `ysel` keeps.
inline_for_extraction
let ysel_u64 (w: U64.t) : (r: bool{r == (W.is_young_w w && U64.v w + 8 <= minor_heap_size)}) =
  young_u64 w && U64.lte w (U64.sub minor_heap_size_u64 8UL)

let ysel_len (w: U64.t)
  : Lemma (Seq.length (CM.ysel w) == (if W.is_young_w w && U64.v w + 8 <= minor_heap_size then 1 else 0) /\
           (W.is_young_w w && U64.v w + 8 <= minor_heap_size ==> Seq.index (CM.ysel w) 0 == w))
  = ()

/// The table's entries are field addresses.
let tbl_addrs (g: SB.heap) (tv: Seq.seq U64.t) (n: nat) : prop =
  n <= Seq.length tv /\ (forall (k: nat). k < n ==> U64.v (Seq.index tv k) % 8 == 0 /\ U64.v (Seq.index tv k) < SB.heap_size)

#push-options "--fuel 1"
let ypre0 (g: SB.heap) (tv: Seq.seq U64.t) : Lemma (CM.ypre_tbl g tv 0 == Seq.empty) = ()
#pop-options

/// **How many roots the remembered slots add.**
#push-options "--z3rlimit 40"
fn count_young (heap: heap_t) (tb: A.array U64.t) (n: SZ.t) (#g: erased SB.heap) (#tv: erased (Seq.seq U64.t))
  requires is_heap heap g ** A.pts_to tb tv ** pure (tbl_addrs g tv (SZ.v n))
  returns m: SZ.t
  ensures is_heap heap g ** A.pts_to tb tv ** pure (SZ.v m == Seq.length (CM.ypre_tbl g tv (SZ.v n)) /\ SZ.v m <= SZ.v n)
{
  ypre0 g tv;
  let mut k = 0sz;
  let mut m = 0sz;
  while (SZ.lt !k n)
    invariant exists* vk vm.
      R.pts_to k vk ** R.pts_to m vm ** is_heap heap g ** A.pts_to tb tv **
      pure (SZ.v vk <= SZ.v n /\ SZ.v vm == Seq.length (CM.ypre_tbl g tv (SZ.v vk)) /\ SZ.v vm <= SZ.v vk)
    decreases (SZ.v n - SZ.v !k)
  {
    let vk = !k;
    let vm = !m;
    let a = tb.(vk);
    let w = read_word heap a;
    CM.ypre_tbl_step g tv (SZ.v vk);
    ysel_len w;
    if (ysel_u64 w) { m := SZ.add vm 1sz } else { () };
    k := SZ.add vk 1sz
  };
  !m
}
#pop-options

/// The prefix grows with `k`.
let ypre_mono (g: SB.heap) (tv: Seq.seq U64.t) (k n: nat)
  : Lemma (requires k <= n /\ n <= Seq.length tv)
          (ensures Seq.length (CM.ypre_tbl g tv k) <= Seq.length (CM.ypre_tbl g tv n))
  = CM.ypre_tbl_all g tv k n;
    CM.ypre_tbl_eq g tv n

/// One more word at the end.
let snoc_idx (yv a s: Seq.seq U64.t) (j: nat)
  : Lemma (requires j < Seq.length yv + Seq.length a + Seq.length s)
          (ensures Seq.index (Seq.append yv (Seq.append a s)) j ==
                   (if j < Seq.length yv + Seq.length a then Seq.index (Seq.append yv a) j
                    else Seq.index s (j - Seq.length yv - Seq.length a)))
  = Seq.append_assoc yv a s

/// A total update.
let upd_at (s: Seq.seq U64.t) (i: nat) (w: U64.t) : Seq.seq U64.t =
  if i < Seq.length s then Seq.upd s i w else s

/// The roots built so far, one table entry on.
let inv_next (yv a: Seq.seq U64.t) (w: U64.t) (rv: Seq.seq U64.t) (vp: nat)
  : Lemma (requires vp == Seq.length yv + Seq.length a /\ vp <= Seq.length rv /\
                    (forall (j: nat). j < vp ==> Seq.index rv j == Seq.index (Seq.append yv a) j))
          (ensures (let a' = Seq.append a (CM.ysel w) in
                    (Seq.length (CM.ysel w) == 0 ==>
                       (forall (j: nat). j < vp ==> Seq.index rv j == Seq.index (Seq.append yv a') j)) /\
                    (Seq.length (CM.ysel w) == 1 /\ vp < Seq.length rv ==>
                       (forall (j: nat). j < vp + 1 ==>
                          Seq.index (upd_at rv vp w) j == Seq.index (Seq.append yv a') j))))
  = ysel_len w;
    let a' = Seq.append a (CM.ysel w) in
    let one (j: nat)
      : Lemma (j < vp + Seq.length (CM.ysel w) ==>
               j < Seq.length yv + Seq.length a' /\
               Seq.index (Seq.append yv a') j ==
               (if j < vp then Seq.index (Seq.append yv a) j else Seq.index (CM.ysel w) (j - vp)))
      = if j < vp + Seq.length (CM.ysel w) then snoc_idx yv a (CM.ysel w) j in
    FStar.Classical.forall_intro one

/// Push `w` at `vp` when `ysel` keeps it.
fn push_if (ra: A.array U64.t) (vp: SZ.t) (w: U64.t) (#rv: erased (Seq.seq U64.t))
  requires A.pts_to ra rv **
           pure (SZ.v vp + Seq.length (CM.ysel w) <= Seq.length rv /\ SZ.fits (Seq.length rv))
  returns vp': SZ.t
  ensures exists* rv'. A.pts_to ra rv' **
          pure (Seq.length rv' == Seq.length rv /\ SZ.v vp' == SZ.v vp + Seq.length (CM.ysel w) /\
                (Seq.length (CM.ysel w) == 1 ==> rv' == upd_at rv (SZ.v vp) w) /\
                (Seq.length (CM.ysel w) == 0 ==> rv' == rv))
{
  ysel_len w;
  if (ysel_u64 w) {
    SZ.fits_lte (SZ.v vp + 1) (Seq.length rv);
    ra.(vp) <- w;
    SZ.add vp 1sz
  } else {
    vp
  }
}

/// **The roots of the promotion**: the program's young roots `yv`, then
/// the table's young words.
#push-options "--z3rlimit 40"
fn fill_roots (heap: heap_t) (tb: A.array U64.t) (n: SZ.t) (yr: A.array U64.t) (k0: SZ.t) (ra: A.array U64.t)
  (#g: erased SB.heap) (#tv: erased (Seq.seq U64.t)) (#p: perm) (#yv: erased (Seq.seq U64.t))
  requires is_heap heap g ** A.pts_to tb tv ** A.pts_to yr #p yv ** A.pts_to ra 'rv **
           pure (tbl_addrs g tv (SZ.v n) /\ Seq.length yv == SZ.v k0 /\
                 Seq.length 'rv == SZ.v k0 + Seq.length (CM.ypre_tbl g tv (SZ.v n)) /\
                 SZ.fits (Seq.length 'rv))
  ensures is_heap heap g ** A.pts_to tb tv ** A.pts_to yr #p yv **
          A.pts_to ra (Seq.append yv (CM.ypre_tbl g tv (SZ.v n)))
{
  let mut i = 0sz;
  while (SZ.lt !i k0)
    invariant exists* vi rv.
      R.pts_to i vi ** A.pts_to ra rv ** A.pts_to yr #p yv **
      pure (SZ.v vi <= SZ.v k0 /\ Seq.length rv == Seq.length 'rv /\
            (forall (j: nat). j < SZ.v vi ==> Seq.index rv j == Seq.index yv j))
    decreases (SZ.v k0 - SZ.v !i)
  {
    let vi = !i;
    let w = yr.(vi);
    ra.(vi) <- w;
    i := SZ.add vi 1sz
  };
  ypre0 g tv;
  ypre_mono g tv 0 (SZ.v n);
  Seq.append_empty_r (reveal yv);
  let mut k = 0sz;
  let mut pos = k0;
  while (SZ.lt !k n)
    invariant exists* vk vp rv.
      R.pts_to k vk ** R.pts_to pos vp ** A.pts_to ra rv ** is_heap heap g ** A.pts_to tb tv **
      pure (SZ.v vk <= SZ.v n /\ Seq.length rv == Seq.length 'rv /\
            SZ.v vp == SZ.v k0 + Seq.length (CM.ypre_tbl g tv (SZ.v vk)) /\ SZ.v vp <= Seq.length rv /\
            (forall (j: nat). j < SZ.v vp ==> Seq.index rv j == Seq.index (Seq.append yv (CM.ypre_tbl g tv (SZ.v vk))) j))
    decreases (SZ.v n - SZ.v !k)
  {
    let vk = !k;
    let vp = !pos;
    with rv. assert (A.pts_to ra rv);
    let a = tb.(vk);
    let w = read_word heap a;
    CM.ypre_tbl_step g tv (SZ.v vk);
    ysel_len w;
    ypre_mono g tv (SZ.v vk + 1) (SZ.v n);
    inv_next yv (CM.ypre_tbl g tv (SZ.v vk)) w rv (SZ.v vp);
    let vp' = push_if ra vp w;
    pos := vp';
    k := SZ.add vk 1sz
  };
  with rv. assert (A.pts_to ra rv);
  assert (pure (Seq.equal rv (Seq.append yv (CM.ypre_tbl g tv (SZ.v n)))));
  rewrite (A.pts_to ra rv) as (A.pts_to ra (Seq.append yv (CM.ypre_tbl g tv (SZ.v n))))
}
#pop-options

/// ---------------------------------------------------------------------------
/// The minor collection
/// ---------------------------------------------------------------------------

module IM = GC.Impl.Pages.Minor
module V = Pulse.Lib.Vec
module LV = GC.Spec.Top.PagesLive

/// **The run stopped**: a minor collection's allocation failed.  The state
/// is the code's; the run is one of `pc` whose last configuration has
/// stopped, so no further event is allowed.
let stopped2 (c: cstate) (sty: style) (es: list event) : slprop =
  exists* (g: SB.heap) (st: GC.Spec.Pages.Inv.pstate) (ph: U8.t) (cv: U64.t) (d: minor_heap) (b: U64.t) (tv: Seq.seq U64.t) (n: SZ.t).
    is_heap c.heap g ** pages_st c.t st ** R.pts_to c.pr ph ** R.pts_to c.cr cv **
    is_minor c.mh d b ** A.pts_to c.tb tv ** R.pts_to c.tn n **
    pure (CP.good sty es /\ (CP.xc es).stopped == true)

#push-options "--fuel 1"
let tbl_nil (tv: Seq.seq U64.t) : Lemma (CM.tbl_ok tv 0 []) = ()
#pop-options

/// After a collection that did not fail.
#push-options "--z3rlimit 40"
let minor_side (sty: style) (es: list event) (d: minor_heap) (b: U64.t) (tv: Seq.seq U64.t)
  : Lemma (requires CP.good sty es /\ (CP.xc es).stopped == false /\ ~(CM.mfailed (CP.xc es)) /\
                    Fw.mst d b == minor_reset (CP.xc es).w.cyng)
          (ensures (let x = CP.xc es in
                    let es' = L.append es [EMinor] in
                    let x' = CP.xc es' in
                    CP.good sty es' /\ side es' d b tv 0 /\ x' == step CP.pc x EMinor /\
                    CP.hof x' == (CM.mres x).GC.Spec.Pages.Promote.rmajor /\
                    (CP.sof x').ps == (CM.mres x).GC.Spec.Pages.Promote.rst /\ x'.ph == x.ph))
  = let x = CP.xc es in
    CM.minor_cfg x;
    CP.allowed_gc sty es EMinor;
    CP.snoc sty es EMinor;
    CM.rem_nil (CP.xc (L.append es [EMinor]));
    tbl_nil tv

/// After a collection that failed.
let minor_stop (sty: style) (es: list event)
  : Lemma (requires CP.good sty es /\ (CP.xc es).stopped == false /\ CM.mfailed (CP.xc es))
          (ensures CP.good sty (L.append es [EMinor]) /\ (CP.xc (L.append es [EMinor])).stopped == true)
  = let x = CP.xc es in
    CM.minor_cfg x;
    CP.allowed_gc sty es EMinor;
    CP.snoc sty es EMinor
#pop-options

/// The table's entries are field addresses, at a configuration of the run.
let tbl_addrs_of (sty: style) (es: list event) (tv: Seq.seq U64.t) (n: nat)
  : Lemma (requires CP.good sty es /\ CM.rem_ok (CP.xc es) /\ CM.tbl_ok tv n (CP.xc es).w.crem)
          (ensures tbl_addrs (CP.hof (CP.xc es)) tv n)
  = let one (k: nat) : Lemma (k < n ==> U64.v (Seq.index tv k) % 8 == 0 /\ U64.v (Seq.index tv k) < SB.heap_size)
      = if k < n then CM.tbl_addr sty es tv n k in
    FStar.Classical.forall_intro one

/// **`EMinor`**: the Pulse minor collection on the roots the model forwards
/// (the program's young roots `yv`, given by the caller, then the young
/// words of the remembered slots, read through the table), the table
/// emptied.  Returns false when an allocation failed: the run has stopped.
/// The forwarding array and the queue are scratch space.
#push-options "--z3rlimit 40"
fn minor2 (c: cstate) (fa q yr: A.array U64.t) (k0: SZ.t) (#p: perm) (#yv: erased (Seq.seq U64.t))
  (#sty: erased style) (#es: erased (list event))
  requires crep2 c sty es ** A.pts_to fa 'fv ** A.pts_to q 'qv ** A.pts_to yr #p yv **
           pure (Seq.length 'fv == FA.fwd_array_size /\ Seq.length 'qv == FA.queue_size /\
                 Seq.length yv == SZ.v k0 /\
                 yv == LV.yroots (Y.ycabs (CP.xc es).w.cyng) (CP.xc es).w.croots /\
                 SZ.fits (SZ.v k0 + L.length (CP.xc es).w.crem))
  returns ok: bool
  ensures (exists* fv' qv'. A.pts_to fa fv' ** A.pts_to q qv') ** A.pts_to yr #p yv **
          (if ok then crep2 c sty (L.append es [EMinor]) else stopped2 c sty (L.append es [EMinor])) **
          pure (ok ==> CP.xc (L.append es [EMinor]) == step CP.pc (CP.xc es) EMinor /\
                       (CP.xc (L.append es [EMinor])).ph == (CP.xc es).ph)
{
  unfold crep2;
  with d b tv n. assert (is_minor c.mh d b ** A.pts_to c.tb tv ** R.pts_to c.tn n);
  unfold PT.crep;
  with x cv. assert (is_heap c.heap (CP.hof x) ** R.pts_to c.cr cv);
  CM.minor_pre_code sty es;
  CM.at_phase_of x.ph (CP.sof x);
  tbl_addrs_of sty es tv (SZ.v n);
  CM.tbl_sound sty es tv (SZ.v n);
  CM.tbl_covers sty es tv (SZ.v n);
  CM.roots_code sty es tv (SZ.v n);
  A.pts_to_len c.tb;
  zero_fwd fa;
  let nv = !c.tn;
  let m = count_young c.heap c.tb nv;
  SZ.fits_lte (SZ.v k0 + SZ.v m) (SZ.v k0 + L.length (CP.xc es).w.crem);
  let len = SZ.add k0 m;
  let rv = V.alloc 0UL len;
  V.to_array_pts_to rv;
  let ra = V.vec_to_array rv;
  rewrite (A.pts_to (V.vec_to_array rv) (Seq.create (SZ.v len) 0UL)) as (A.pts_to ra (Seq.create (SZ.v len) 0UL));
  fill_roots c.heap c.tb nv yr k0 ra;
  let phc = !c.pr;
  CP.marking_code x.ph;
  let ok = IM.minor_collect c.mh c.heap c.t (phc = 1uy) ra len fa q c.tb nv
             #(CM.mtal x) #(PAl.iph x.ph);
  with d' b' g' st' rs'. assert (is_minor c.mh d' b' ** is_heap c.heap g' ** pages_st c.t st' ** A.pts_to ra rs');
  rewrite (A.pts_to ra rs') as (A.pts_to (V.vec_to_array rv) rs');
  V.to_vec_pts_to rv;
  V.free rv;
  if ok {
    minor_side sty es d' b' tv;
    c.tn := 0sz;
    rewrite (is_heap c.heap g') as (is_heap c.heap (CP.hof (CP.xc (L.append es [EMinor]))));
    rewrite (pages_st c.t st') as (pages_st c.t (CP.sof (CP.xc (L.append es [EMinor]))).ps);
    rewrite (R.pts_to c.pr (CP.phase_code x.ph)) as (R.pts_to c.pr (CP.phase_code (CP.xc (L.append es [EMinor])).ph));
    fold (PT.crep c.heap c.t c.pr c.cr sty (L.append es [EMinor]));
    fold (crep2 c sty (L.append es [EMinor]));
    rewrite (crep2 c sty (L.append es [EMinor]))
         as (if ok then crep2 c sty (L.append es [EMinor]) else stopped2 c sty (L.append es [EMinor]));
    ok
  } else {
    minor_stop sty es;
    fold (stopped2 c sty (L.append es [EMinor]));
    rewrite (stopped2 c sty (L.append es [EMinor]))
         as (if ok then crep2 c sty (L.append es [EMinor]) else stopped2 c sty (L.append es [EMinor]));
    ok
  }
}
#pop-options

/// **`EHandover`**, after a minor collection: the remembered set is empty
/// when the sweep starts (design doc §18, step 2).  Returns false when the
/// collection's allocation failed: the run has stopped before the
/// hand-over.  The mark is done after the collection (`mark_done`: a fact
/// of the mark, linked in step 4).
#push-options "--z3rlimit 40"
fn handover2 (c: cstate) (fa q yr: A.array U64.t) (k0: SZ.t) (#p: perm) (#yv: erased (Seq.seq U64.t))
  (#sty: erased style) (#es: erased (list event))
  requires crep2 c sty es ** A.pts_to fa 'fv ** A.pts_to q 'qv ** A.pts_to yr #p yv **
           pure (Seq.length 'fv == FA.fwd_array_size /\ Seq.length 'qv == FA.queue_size /\
                 Seq.length yv == SZ.v k0 /\
                 yv == LV.yroots (Y.ycabs (CP.xc es).w.cyng) (CP.xc es).w.croots /\
                 SZ.fits (SZ.v k0 + L.length (CP.xc es).w.crem) /\
                 T.Marking? (CP.xc es).ph /\ T.mark_done (mj (step CP.pc (CP.xc es) EMinor)))
  returns ok: bool
  ensures (exists* fv' qv'. A.pts_to fa fv' ** A.pts_to q qv') ** A.pts_to yr #p yv **
          (if ok then crep2 c sty (L.append (L.append es [EMinor]) [EHandover])
           else stopped2 c sty (L.append es [EMinor]))
{
  let ok = minor2 c fa q yr k0;
  if ok {
    rewrite (if ok then crep2 c sty (L.append es [EMinor]) else stopped2 c sty (L.append es [EMinor]))
         as (crep2 c sty (L.append es [EMinor]));
    unfold crep2;
    with d b tv n. assert (is_minor c.mh d b ** A.pts_to c.tb tv ** R.pts_to c.tn n);
    PT.handover_top c.heap c.t c.pr c.cr;
    leave_side sty (L.append es [EMinor]) EHandover d b tv (SZ.v n);
    unfold PT.crep;
    with x cv. assert (is_heap c.heap (CP.hof x) ** R.pts_to c.cr cv);
    fold (PT.crep c.heap c.t c.pr c.cr sty (L.append (L.append es [EMinor]) [EHandover]));
    fold (crep2 c sty (L.append (L.append es [EMinor]) [EHandover]));
    rewrite (crep2 c sty (L.append (L.append es [EMinor]) [EHandover]))
         as (if ok then crep2 c sty (L.append (L.append es [EMinor]) [EHandover])
             else stopped2 c sty (L.append es [EMinor]));
    ok
  } else {
    rewrite (if ok then crep2 c sty (L.append es [EMinor]) else stopped2 c sty (L.append es [EMinor]))
         as (stopped2 c sty (L.append es [EMinor]));
    rewrite (stopped2 c sty (L.append es [EMinor]))
         as (if ok then crep2 c sty (L.append (L.append es [EMinor]) [EHandover])
             else stopped2 c sty (L.append es [EMinor]));
    ok
  }
}
#pop-options
