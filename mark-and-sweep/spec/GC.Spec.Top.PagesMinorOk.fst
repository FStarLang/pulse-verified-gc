/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PagesMinorOk - the minor collection of pages meets the contract
/// ---------------------------------------------------------------------------
///
/// `pages_minor_ok : minor_ok byte_rep pminor`.  `OutOfRoom` is justified by
/// the refused promotion (`PagesMinor.oor_ok`); `Done` gives the model heap
/// `cabs` of the updated heap, with: the size; the forwarding map exactly the
/// live young blocks, each once (`PagesDone`); each copy on words free
/// before, of the young block's header in the phase's colour, its fields
/// forwarded (`PagesDone2.copy_field`); the blocks in use before and the
/// copies (`PagesDone.done_in_use`); every block in use before with its
/// header, and those the program may use with their fields forwarded
/// (`PagesDone2.old_field`); the roots forwarded; the page invariant after
/// the update (`collect_inv`, the instance's invariant read back); a well-
/// formed reading.

module GC.Spec.Top.PagesMinorOk

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Spec.Pages.Inv
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.ByteRep
open GC.Spec.Top.PagesAlloc
open GC.Spec.Top.PagesReplay
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module U64 = FStar.UInt64
module P = GC.Spec.Pages.Promote
module PCo = GC.Spec.Pages.Promote.Collect
module PR = GC.Spec.Top.PromoteRun
module Y = GC.Spec.Top.Young
module LV = GC.Spec.Top.PagesLive
module BM = GC.Spec.Top.ByteMark
module PM = GC.Spec.Top.PagesMinor
module F = GC.Spec.Top.PagesFwd
module D = GC.Spec.Top.PagesDone
module D2 = GC.Spec.Top.PagesDone2
module PI = GC.Spec.Pages.Promote.Idle
module PPI = GC.Spec.Pages.PromoteInst
module Fl = GC.Spec.Pages.Promote.Fail


#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The roots, the invariant, the reading
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let rec map_ext (f g: M.value -> M.value) (l: list M.value)
  : Lemma (requires forall (v: M.value). f v == g v) (ensures L.map f l == L.map g l)
  = match l with [] -> () | _ :: tl -> map_ext f g tl
#pop-options

let fwdv_eq (y y': M.mheap) (fwd: nat -> option nat) (v: M.value)
  : Lemma (requires forall (a: nat). M.resolve y a == M.resolve y' a) (ensures T.fwdv y fwd v == T.fwdv y' fwd v)
  = match v with
    | M.VPtr (M.Young a) -> assert (M.resolve y a == M.resolve y' a)
    | _ -> ()

/// The roots forwarded, on any view of the nursery.
let roots_eq (y y': M.mheap) (fwd: nat -> option nat) (rs: list M.value)
  : Lemma (requires R.heq y y') (ensures L.map (T.fwdv y fwd) rs == L.map (T.fwdv y' fwd) rs)
  = assert (forall (a: nat). M.resolve y a == M.resolve y' a);
    FStar.Classical.forall_intro (FStar.Classical.move_requires (fwdv_eq y y' fwd));
    map_ext (T.fwdv y fwd) (T.fwdv y' fwd) rs

/// The instance's invariant is the page invariant of the phase.
let tal_back (ph: T.phase pprog) (st: pst) (g: heap) (s: pstate)
  : Lemma (requires (ptal ph st).P.inv g s) (ensures GC.Spec.Pages.MidSweepAlloc.inv_sw (iph ph) g s)
  = ()

/// **The page invariant after the update.**
#push-options "--z3rlimit 40"
let inv_after (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world)
  : Lemma (requires D.dpre ph st cw w)
          (ensures (let r = D.r_of ph st cw in pa.T.inv ph r.P.rmajor (tst r.P.rmajor r.P.rst)))
  = let cs = D.cs_of ph st cw in
    let r = D.r_of ph st cw in
    D.dpre_elim ph st cw w;
    PM.ctx_start ph st cw w;
    PCo.collect_inv_w (ptal ph st) cw.T.cyng (gl cw.T.cmaj st) st.ps (LV.roots_of (BM.cview cw));
    tal_back ph st r.P.rmajor r.P.rst;
    set_low_self r.P.rmajor;
    D.end_ri ph st cw w;
    D.end_hd ph st cw w;
    ri_elim_wf ph st cw.T.cmaj w.M.yng cs.P.major (tst cs.P.major cs.P.st) (cabs cs.P.major) (D.cps_of ph st cw)
#pop-options

/// **The reading after the update is well formed.**
let wf_after (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world)
  : Lemma (requires D.dpre ph st cw w) (ensures M.well_formed (cabs (D.r_of ph st cw).P.rmajor))
  = let g = (D.cs_of ph st cw).P.major in
    let g' = (D.r_of ph st cw).P.rmajor in
    D.end_walk ph st cw w;
    D.end_hd ph st cw w;
    assert (forall (o: nat). M.is_block (cabs g') o == M.is_block (cabs g) o);
    assert (forall (o: nat). M.hdr_of (cabs g') o == M.hdr_of (cabs g) o);
    assert (forall (o x: nat). M.covers (cabs g') o x == M.covers (cabs g) o x)

/// A copy's words were free before.
#push-options "--z3rlimit 40"
let copy_free (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world) (o c x: nat)
  : Lemma (requires D.dpre ph st cw w /\ F.fwd_of (D.cps_of ph st cw) o == Some c /\
                    M.covers (cabs (D.r_of ph st cw).P.rmajor) c x)
          (ensures T.free_word pa st cw.T.cmaj w.M.maj x)
  = let g = (D.cs_of ph st cw).P.major in
    D2.copy_facts ph st cw w o c;
    D.end_hd ph st cw w;
    D.dpre_elim ph st cw w;
    copy_ok_def ph st cw.T.cmaj w.M.yng (cabs g) o c;
    assert (M.covers (cabs g) c x);
    assert (T.free_word pa st cw.T.cmaj (cabs cw.T.cmaj) x);
    assert (forall (b: nat). M.covers (cabs cw.T.cmaj) b x == M.covers w.M.maj b x)
#pop-options

/// ---------------------------------------------------------------------------
/// The contract
/// ---------------------------------------------------------------------------

let post_intro (#t: Type0) (#k: T.sweep_kind) (a: T.allocator t k) (ph: T.phase k.T.progress) (st: a.T.state)
               (hc: t) (w: M.world) (hc': t) (st': a.T.state)
               (roots': list M.value) (fwd: nat -> option nat) (h': M.mheap)
  : Lemma (requires
       h'.M.size == w.M.maj.M.size /\
       (forall (o: nat). Some? (fwd o) <==> (M.is_block w.M.yng o /\ M.minor_live w o)) /\
       (forall (o1 o2 c: nat). fwd o1 == Some c /\ fwd o2 == Some c ==> o1 == o2) /\
       (forall (o c: nat). fwd o == Some c ==>
          (forall (w': nat). M.covers h' c w' ==> T.free_word a st hc w.M.maj w') /\
          h'.M.hd c == Some ({ M.wz = M.wz_of w.M.yng o; M.tag = M.tag_of w.M.yng o; M.col = T.colour_at k ph c }) /\
          (forall (i: nat). i < M.wz_of w.M.yng o ==> M.field h' c i == T.fwd_field w.M.yng o i w.M.yng fwd)) /\
       (forall (x: nat). T.in_use a st' hc' h' x <==> (T.in_use a st hc w.M.maj x \/ (exists (o: nat). fwd o == Some x))) /\
       (forall (x: nat). T.in_use a st hc w.M.maj x ==>
          h'.M.hd x == w.M.maj.M.hd x /\
          (T.live_target a ph st hc w.M.maj x ==>
             (forall (i: nat). i < M.wz_of w.M.maj x ==> M.field h' x i == T.fwd_field w.M.maj x i w.M.yng fwd))) /\
       roots' == L.map (T.fwdv w.M.yng fwd) w.M.roots /\
       a.T.inv ph hc' st' /\ M.well_formed h')
          (ensures T.minor_post_done a ph st hc w hc' st' roots' fwd h')
  = assert (T.minor_post_done a ph st hc w hc' st' roots' fwd h')
      by (FStar.Tactics.V2.norm [delta_only [`%T.minor_post_done]; iota; zeta];
          FStar.Tactics.V2.assumption ())

/// What a copy gives, sealed.
[@@"opaque_to_smt"]
let cpost (ph: T.phase pprog) (st: pst) (hc: heap) (w: M.world) (fwd: nat -> option nat) (h': M.mheap) (o c: nat) : prop =
  (forall (w': nat). M.covers h' c w' ==> T.free_word pa st hc w.M.maj w') /\
  h'.M.hd c == Some ({ M.wz = M.wz_of w.M.yng o; M.tag = M.tag_of w.M.yng o; M.col = T.colour_at pk ph c }) /\
  (forall (i: nat). i < M.wz_of w.M.yng o ==> M.field h' c i == T.fwd_field w.M.yng o i w.M.yng fwd)

/// What an old block gives, sealed.
[@@"opaque_to_smt"]
let opost (ph: T.phase pprog) (st: pst) (hc: heap) (w: M.world) (fwd: nat -> option nat) (h': M.mheap) (x: nat) : prop =
  h'.M.hd x == w.M.maj.M.hd x /\
  (T.live_target pa ph st hc w.M.maj x ==>
     (forall (i: nat). i < M.wz_of w.M.maj x ==> M.field h' x i == T.fwd_field w.M.maj x i w.M.yng fwd))

/// The contract's `Done` post, from the sealed parts.
let post_pages (ph: T.phase pprog) (st: pst) (hc: heap) (w: M.world) (hc': heap) (st': pst)
               (roots': list M.value) (fwd: nat -> option nat) (h': M.mheap)
  : Lemma (requires
       h'.M.size == w.M.maj.M.size /\
       (forall (o: nat). Some? (fwd o) <==> (M.is_block w.M.yng o /\ M.minor_live w o)) /\
       (forall (o1 o2 c: nat). fwd o1 == Some c /\ fwd o2 == Some c ==> o1 == o2) /\
       (forall (o c: nat). fwd o == Some c ==> cpost ph st hc w fwd h' o c) /\
       (forall (x: nat). T.in_use pa st' hc' h' x <==> (T.in_use pa st hc w.M.maj x \/ (exists (o: nat). fwd o == Some x))) /\
       (forall (x: nat). T.in_use pa st hc w.M.maj x ==> opost ph st hc w fwd h' x) /\
       roots' == L.map (T.fwdv w.M.yng fwd) w.M.roots /\
       pa.T.inv ph hc' st' /\ M.well_formed h')
          (ensures T.minor_post_done pa ph st hc w hc' st' roots' fwd h')
  = assert (T.minor_post_done pa ph st hc w hc' st' roots' fwd h')
      by (let open FStar.Tactics.V2 in
          norm [delta_only [`%T.minor_post_done; `%cpost; `%opost]; iota; zeta];
          iter (fun b -> try norm_binding_type [delta_only [`%cpost; `%opost]; iota; zeta] b with | _ -> ())
               (cur_vars ());
          assumption ())

/// The copies, one by one.
let copy_post (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world) (o c: nat)
  : Lemma (requires D.dpre ph st cw w /\ F.fwd_of (D.cps_of ph st cw) o == Some c)
          (ensures cpost ph st cw.T.cmaj w (F.fwd_of (D.cps_of ph st cw)) (cabs (D.r_of ph st cw).P.rmajor) o c)
  = D2.copy_facts ph st cw w o c;
    D.end_hd ph st cw w;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (copy_free ph st cw w o c));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (D2.copy_field ph st cw w o c));
    reveal_opaque (`%cpost) (cpost ph st cw.T.cmaj w (F.fwd_of (D.cps_of ph st cw)) (cabs (D.r_of ph st cw).P.rmajor) o c)

/// The old blocks, one by one.
let old_post (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world) (x: nat)
  : Lemma (requires D.dpre ph st cw w /\ T.in_use pa st cw.T.cmaj w.M.maj x)
          (ensures opost ph st cw.T.cmaj w (F.fwd_of (D.cps_of ph st cw)) (cabs (D.r_of ph st cw).P.rmajor) x)
  = D2.old_facts ph st cw w x;
    D.end_hd ph st cw w;
    (if FStar.IndefiniteDescription.strong_excluded_middle (T.live_target pa ph st cw.T.cmaj w.M.maj x) then
       FStar.Classical.forall_intro (FStar.Classical.move_requires (D2.old_field ph st cw w x)));
    reveal_opaque (`%opost) (opost ph st cw.T.cmaj w (F.fwd_of (D.cps_of ph st cw)) (cabs (D.r_of ph st cw).P.rmajor) x)

/// The copies' clause.
let copies_clause (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world)
  : Lemma (requires D.dpre ph st cw w)
          (ensures forall (o c: nat). F.fwd_of (D.cps_of ph st cw) o == Some c ==>
                     cpost ph st cw.T.cmaj w (F.fwd_of (D.cps_of ph st cw)) (cabs (D.r_of ph st cw).P.rmajor) o c)
  = FStar.Classical.forall_intro_2 (fun o c -> FStar.Classical.move_requires (copy_post ph st cw w o) c)

/// The old blocks' clause.
let olds_clause (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world)
  : Lemma (requires D.dpre ph st cw w)
          (ensures forall (x: nat). T.in_use pa st cw.T.cmaj w.M.maj x ==>
                     opost ph st cw.T.cmaj w (F.fwd_of (D.cps_of ph st cw)) (cabs (D.r_of ph st cw).P.rmajor) x)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (old_post ph st cw w))

/// The forwarding map's clauses.
let fwd_clause (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world)
  : Lemma (requires D.dpre ph st cw w)
          (ensures (let fwd = F.fwd_of (D.cps_of ph st cw) in
                    (forall (o: nat). Some? (fwd o) <==> (M.is_block w.M.yng o /\ M.minor_live w o)) /\
                    (forall (o1 o2 c: nat). fwd o1 == Some c /\ fwd o2 == Some c ==> o1 == o2)))
  = let fwd = F.fwd_of (D.cps_of ph st cw) in
    let b (o: nat) : Lemma (Some? (fwd o) <==> (M.is_block w.M.yng o /\ M.minor_live w o))
      = (match fwd o with Some c -> D.fwd_live ph st cw w o c | None -> ());
        FStar.Classical.move_requires (D.fwd_complete ph st cw w) o in
    FStar.Classical.forall_intro b;
    FStar.Classical.forall_intro_3 (fun o1 o2 c -> FStar.Classical.move_requires (D.fwd_inj ph st cw w o1 o2) c)

/// **The `Done` case.**
#push-options "--z3rlimit 40"
let done_post (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world)
  : Lemma (requires D.dpre ph st cw w)
          (ensures (let r = D.r_of ph st cw in
                    let fwd = F.fwd_of (D.cps_of ph st cw) in
                    T.minor_post_done pa ph st cw.T.cmaj w r.P.rmajor (tst r.P.rmajor r.P.rst)
                      (L.map (T.fwdv (Y.ycabs cw.T.cyng) fwd) cw.T.croots) fwd (cabs r.P.rmajor)))
  = let r = D.r_of ph st cw in
    let fwd = F.fwd_of (D.cps_of ph st cw) in
    D.dpre_elim ph st cw w;
    PM.views cw w;
    fwd_clause ph st cw w;
    copies_clause ph st cw w;
    D.done_in_use ph st cw w;
    olds_clause ph st cw w;
    BM.yrepr_heq w.M.yng cw.T.cyng;
    roots_eq (Y.ycabs cw.T.cyng) w.M.yng fwd cw.T.croots;
    inv_after ph st cw w;
    wf_after ph st cw w;
    post_pages ph st cw.T.cmaj w r.P.rmajor (tst r.P.rmajor r.P.rst)
      (L.map (T.fwdv (Y.ycabs cw.T.cyng) fwd) cw.T.croots) fwd (cabs r.P.rmajor)
#pop-options

let dpre_intro (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world)
  : Lemma (requires T.cviews byte_rep cw w /\ T.minor_pre pa ph st cw.T.cmaj w /\
                    ~(Fl.failed (ptal ph st) cw.T.cyng (gl cw.T.cmaj st) st.ps (LV.roots_of (BM.cview cw))))
          (ensures D.dpre ph st cw w)
  = reveal_opaque (`%D.dpre) (D.dpre ph st cw w)

/// The contract at one view.
#push-options "--z3rlimit 40"
let minor_m_ok (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world)
  : Lemma (requires T.cviews byte_rep cw w) (ensures T.minor_m byte_rep PM.pminor ph st cw w)
  = let pre () : Lemma (requires T.minor_pre pa ph st cw.T.cmaj w)
                       (ensures (match PM.pcollect ph st cw with
                                 | T.OutOfRoom -> T.oor_justified byte_rep pa ph st cw w
                                 | T.Done hc' st' roots' fwd ->
                                   exists (h': M.mheap). byte_rep.R.repr h' hc' /\
                                     T.minor_post_done pa ph st cw.T.cmaj w hc' st' roots' fwd h'))
      = if Fl.failed (ptal ph st) cw.T.cyng (gl cw.T.cmaj st) st.ps (LV.roots_of (BM.cview cw))
        then PM.oor_ok ph st cw w
        else begin
          dpre_intro ph st cw w;
          done_post ph st cw w;
          let r = D.r_of ph st cw in
          assert (byte_rep.R.repr (cabs r.P.rmajor) r.P.rmajor)
        end in
    FStar.Classical.move_requires pre ()
#pop-options

/// **The minor collection of pages meets the minor contract.**
let pages_minor_ok () : Lemma (T.minor_ok byte_rep PM.pminor)
  = let one (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state)
      : Lemma (T.minor_at byte_rep PM.pminor ph st cw)
      = FStar.Classical.forall_intro (FStar.Classical.move_requires (minor_m_ok ph st cw)) in
    FStar.Classical.forall_intro_3 one
