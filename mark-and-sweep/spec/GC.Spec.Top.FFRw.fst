/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFRw - the pointer update's rewrite, read as the model's
/// forwarding
/// ---------------------------------------------------------------------------
///
/// `rw_ok`: a word the pointer update rewrites through the promotion's map
/// reads as the model's `fwdv` of its value, when a young pointer it holds
/// that the nursery resolves was covered by the promotion (its block
/// forwarded, an infix address forwarded itself).  A dangling young pointer
/// has no entry (`dangling`), a word of no young pointer is left alone.
/// GC.Spec.Top.PagesRw's statements and proofs, over first-fit (design doc §13).

module GC.Spec.Top.FFRw

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.ByteRep
open GC.Spec.Top.FFAlloc
open GC.Spec.Top.FFReplay
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module U64 = FStar.UInt64
module P = GC.Spec.Pages.Promote
module PL = GC.Spec.Pages.Promote.Loop
module PR = GC.Spec.Top.PromoteRun
module PC = GC.Spec.Top.PromoteCopy
module PU = GC.Spec.Top.PromoteUpdate
module Y = GC.Spec.Top.Young
module YI = GC.Spec.Top.YoungInfix
module Q = GC.Spec.Top.FFQueue
module Q0 = GC.Spec.Top.PagesQueue
module LV = GC.Spec.Top.PagesLive
module BM = GC.Spec.Top.ByteMark
module PM = GC.Spec.Top.FFMinor
module F = GC.Spec.Top.PagesFwd
module D = GC.Spec.Top.FFDone
module FW = GC.Spec.Pages.Promote.Follow

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// A copy's address is a major pointer to its block.
let copy_word (#s: Type0) (a: P.tal s) (g: heap) (v: obj_addr)
  : Lemma (requires in_use a.P.free g v)
          (ensures is_pointer v /\ absv v == M.VPtr (M.Major (maddr v)) /\ pos (maddr v) + 8 == U64.v v)
  = obj_maddr g v;
    absv_major v (maddr v)

/// An address inside a copy, at a field offset.
let inner_word (ob: U64.t) (k: nat) (v: U64.t)
  : Lemma (requires is_pointer ob /\ U64.v v == U64.v ob + 8 * k /\ U64.v v < heap_size)
          (ensures is_pointer v /\ absv v == M.VPtr (M.Major (ptr_b ob + k)))
  = ptr_decode ob;
    absv_major v (ptr_b ob + k)

/// A word of no young pointer is left alone.
let not_young (fwd: forwarding_map) (f: U64.t)
  : Lemma (requires forall (a: nat). absv f =!= M.VPtr (M.Young a))
          (ensures PU.rw fwd f == f)
  = if is_minor_pointer f then begin
      GC.Gen.Base.zero_addr_above_minor ();
      base_facts ();
      absv_young f ((U64.v f - 8) / 8)
    end

/// The forwarding map's entries.
let entries_of (ph: T.phase U64.t) (st: ffst) (cw: T.cworld heap minor_state) (w: M.world)
  : Lemma (requires D.dpre ph st cw w)
          (ensures (let cs = D.cs_of ph st cw in
                    PL.entries (ptal ph st) cw.T.cyng (gl cw.T.cmaj st) cs.P.major cs.P.fwd /\
                    FW.entries_follow cw.T.cyng cs.P.fwd /\
                    PR.qok (ptal ph st) cw.T.cyng (gl cw.T.cmaj st) st.fp cs))
  = D.end_sok ph st cw w

/// **A dangling young pointer has no entry.**
#push-options "--z3rlimit 40"
let dangling (ph: T.phase U64.t) (st: ffst) (cw: T.cworld heap minor_state) (w: M.world) (f: U64.t) (a: nat)
  : Lemma (requires D.dpre ph st cw w /\ absv f == M.VPtr (M.Young a) /\ M.resolve w.M.yng a == None)
          (ensures (D.cs_of ph st cw).P.fwd f == 0UL)
  = let cs = D.cs_of ph st cw in
    let ms = cw.T.cyng in
    entries_of ph st cw w;
    D.dpre_elim ph st cw w;
    PM.views cw w;
    PM.ctx_start ph st cw w;
    absv_young f a;
    Y.msz ();
    if cs.P.fwd f <> 0UL then begin
      assert (PL.entry (ptal ph st) ms (gl cw.T.cmaj st) cs.P.major cs.P.fwd f);
      let r = resolve_minor ms f in
      if is_infix_in_minor ms f then FW.parent_facts_at ms f;
      assert (Seq.mem r (minor_objects ms));
      U64.v_inj f (U64.uint_to_t (8 * a + 8));
      LV.field_young w.M.yng ms f;
      assert (FW.follow_ok ms f);
      YI.young_resolve_follow w.M.yng ms a
    end
#pop-options

let ptr_b_maddr (v: U64.t) : Lemma (requires is_pointer v) (ensures ptr_b v == maddr v) = base_facts ()

/// The copy of a forwarded young block.
#push-options "--z3rlimit 40"
let copy_of_fwd (ph: T.phase U64.t) (st: ffst) (cw: T.cworld heap minor_state) (w: M.world) (o: nat)
  : Lemma (requires D.dpre ph st cw w /\ M.is_block w.M.yng o /\ 8 * o + 8 < pow2 64 /\
                    (D.cs_of ph st cw).P.fwd (PC.yobj o) <> 0UL)
          (ensures (let cs = D.cs_of ph st cw in
                    let ob = cs.P.fwd (PC.yobj o) in
                    is_pointer ob /\ absv ob == M.VPtr (M.Major (maddr ob)) /\
                    F.fwd_of (D.cps_of ph st cw) o == Some (maddr ob) /\
                    U64.v ob + minor_wosize cw.T.cyng (PC.yobj o) * 8 <= heap_size))
  = let cs = D.cs_of ph st cw in
    let ms = cw.T.cyng in
    entries_of ph st cw w;
    D.dpre_elim ph st cw w;
    PM.views cw w;
    PC.young_obj w.M.yng ms o;
    let x = PC.yobj o in
    assert (PL.entry (ptal ph st) ms (gl cw.T.cmaj st) cs.P.major cs.P.fwd x);
    let ob : obj_addr = cs.P.fwd x in
    copy_word (ptal ph st) cs.P.major ob;
    assert (Seq.mem x cs.P.queue);
    let i = FStar.Seq.Properties.index_mem x cs.P.queue in
    D.end_keys ph st cw w;
    F.fwd_queue cs.P.queue cs.P.fwd (Seq.length cs.P.queue) i;
    LV.yof_v o
#pop-options

let res_le (y: M.mheap) (a o: nat) : Lemma (requires M.resolve y a == Some o) (ensures o <= a) = ()

/// The infix entry, at its offset in the closure's copy.
let infix_rewrite (ob f p fv: U64.t) (a o wz: nat)
  : Lemma (requires is_pointer ob /\ U64.v ob + wz * 8 <= heap_size /\ U64.v p == 8 * o + 8 /\
                    U64.v f == 8 * a + 8 /\ o <= a /\ U64.v f - U64.v p < wz * 8 /\
                    U64.v fv == U64.v ob + (U64.v f - U64.v p))
          (ensures is_pointer fv /\ absv fv == M.VPtr (M.Major (ptr_b ob + (a - o))))
  = inner_word ob (a - o) fv

let entry_infix (#s: Type0) (tl: P.tal s) (ms: minor_state) (g0 g: heap) (fwd: forwarding_map) (f: U64.t)
  : Lemma (requires PL.entries tl ms g0 g fwd /\ fwd f <> 0UL /\ is_infix_in_minor ms f)
          (ensures U64.v f >= U64.v (infix_parent ms f) /\
                   U64.v (fwd f) == U64.v (fwd (infix_parent ms f)) + (U64.v f - U64.v (infix_parent ms f)))
  = assert (PL.entry tl ms g0 g fwd f)

let yobj_val (o: nat) : Lemma (requires 8 * o + 8 < pow2 64) (ensures U64.v (PC.yobj o) == 8 * o + 8) = ()

let case_plain (f p ob fv: U64.t) (a o: nat)
  : Lemma (requires U64.v f == 8 * a + 8 /\ f == p /\ U64.v p == 8 * o + 8 /\ fv == ob /\
                    absv ob == M.VPtr (M.Major (maddr ob)))
          (ensures absv fv == M.VPtr (M.Major (maddr ob + (a - o))))
  = ()

/// The facts the rewrite of a covered young pointer reads.
#push-options "--z3rlimit 40"
let live_setup (ph: T.phase U64.t) (st: ffst) (cw: T.cworld heap minor_state) (w: M.world) (f: U64.t) (a o: nat)
  : Lemma (requires D.dpre ph st cw w /\ absv f == M.VPtr (M.Young a) /\ M.resolve w.M.yng a == Some o /\
                    PR.covered cw.T.cyng (D.cs_of ph st cw) f)
          (ensures (let cs = D.cs_of ph st cw in
                    let ms = cw.T.cyng in
                    8 * o + 8 < pow2 64 /\ o <= a /\ U64.v f == 8 * a + 8 /\ U64.v (PC.yobj o) == 8 * o + 8 /\
                    resolve_minor ms f == PC.yobj o /\ is_minor_pointer f /\ cs.P.fwd (PC.yobj o) <> 0UL /\
                    PR.covered ms cs f /\
                    (let ob = cs.P.fwd (PC.yobj o) in
                     is_pointer ob /\ absv ob == M.VPtr (M.Major (maddr ob)) /\ ptr_b ob == maddr ob /\
                     F.fwd_of (D.cps_of ph st cw) o == Some (maddr ob) /\
                     U64.v ob + minor_wosize ms (PC.yobj o) * 8 <= heap_size) /\
                    PL.entries (ptal ph st) ms (gl cw.T.cmaj st) cs.P.major cs.P.fwd /\
                    FW.entries_follow ms cs.P.fwd))
  = let cs = D.cs_of ph st cw in
    let ms = cw.T.cyng in
    let y = w.M.yng in
    res_le y a o;
    D.dpre_elim ph st cw w;
    PM.views cw w;
    PM.ctx_start ph st cw w;
    Y.yrepr_elim y ms;
    absv_young f a;
    Y.msz ();
    D.res_bound y a o;
    U64.v_inj f (U64.uint_to_t (8 * a + 8));
    D.cov_fwd y ms cs a o;
    LV.a1_lt a;
    Y.young_resolve y ms a o;
    copy_of_fwd ph st cw w o;
    ptr_b_maddr (cs.P.fwd (PC.yobj o));
    yobj_val o;
    PR.covered_def ms cs f;
    entries_of ph st cw w;
    GC.Gen.Base.zero_addr_above_minor ();
    base_facts ();
    assert (8 * o + 8 < pow2 64);
    assert (o <= a);
    assert (U64.v f == 8 * a + 8);
    assert (U64.v (PC.yobj o) == 8 * o + 8);
    assert (resolve_minor ms f == PC.yobj o);
    assert (is_minor_pointer f);
    assert (cs.P.fwd (PC.yobj o) <> 0UL);
    assert (PR.covered ms cs f);
    assert (FW.entries_follow ms cs.P.fwd)
#pop-options

/// **A covered young pointer to a block is rewritten to the same offset in
/// its copy.**
let rw_live (ph: T.phase U64.t) (st: ffst) (cw: T.cworld heap minor_state) (w: M.world) (f: U64.t) (a o: nat)
  : Lemma (requires D.dpre ph st cw w /\ absv f == M.VPtr (M.Young a) /\ M.resolve w.M.yng a == Some o /\
                    PR.covered cw.T.cyng (D.cs_of ph st cw) f)
          (ensures (let cs = D.cs_of ph st cw in
                    exists (c: nat). F.fwd_of (D.cps_of ph st cw) o == Some c /\
                      PU.rw cs.P.fwd f == cs.P.fwd f /\ absv (cs.P.fwd f) == M.VPtr (M.Major (c + (a - o)))))
  = let cs = D.cs_of ph st cw in
    let ms = cw.T.cyng in
    live_setup ph st cw w f a o;
    let ob = cs.P.fwd (PC.yobj o) in
    let p = PC.yobj o in
    PR.covered_def ms cs f;
    if is_infix_in_minor ms f then begin
      assert (cs.P.fwd f <> 0UL);
      entry_infix (ptal ph st) ms (gl cw.T.cmaj st) cs.P.major cs.P.fwd f;
      assert (infix_parent ms f == p);
      assert (FW.infix_at ms f);
      infix_rewrite ob f p (cs.P.fwd f) a o (minor_wosize ms p)
    end
    else begin
      resolve_minor_non_infix ms f;
      case_plain f p ob (cs.P.fwd f) a o
    end

/// **The rewrite is the model's forwarding.**
#push-options "--z3rlimit 40"
let rw_ok (ph: T.phase U64.t) (st: ffst) (cw: T.cworld heap minor_state) (w: M.world) (f: U64.t)
  : Lemma (requires D.dpre ph st cw w /\
                    (forall (a: nat). absv f == M.VPtr (M.Young a) /\ Some? (M.resolve w.M.yng a) ==>
                       PR.covered cw.T.cyng (D.cs_of ph st cw) f))
          (ensures absv (PU.rw (D.cs_of ph st cw).P.fwd f) ==
                   T.fwdv w.M.yng (F.fwd_of (D.cps_of ph st cw)) (absv f))
  = match absv f with
    | M.VPtr (M.Young a) ->
      (match M.resolve w.M.yng a with
       | Some o -> rw_live ph st cw w f a o
       | None -> dangling ph st cw w f a)
    | _ -> not_young (D.cs_of ph st cw).P.fwd f
#pop-options
