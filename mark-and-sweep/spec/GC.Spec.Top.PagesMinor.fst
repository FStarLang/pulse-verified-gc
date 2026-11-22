/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PagesMinor - the minor collection of pages, as a component
/// ---------------------------------------------------------------------------
///
/// `pminor`: the minor collection of GC.Spec.Pages.Promote with the page
/// allocator's instance for the phase (`PagesReplay.ptal`: the idle,
/// marking and sweeping instances), on the page heap `gl h st`, forwarding
/// the young pointers the model resolves among the roots and remembered
/// slots (`PagesLive.roots_of`).  It reports `OutOfRoom` exactly when the
/// promotion refused a live object (`PromoteRun.wit`); otherwise it
/// returns akhil's pointer update of the promoted heap (`Promote.collect`),
/// the page state, the roots forwarded and the forwarding map read on the
/// model: the lookup in the list of promotions (young block, copy) the
/// queue records (`PagesFwd.fwd_of`; the contract asks for a total map).
///
/// This module: the component, what the promotion needs from the minor
/// collection's precondition (`ctx_start`, `run_done`), and the
/// `OutOfRoom` case of the contract (`oor_ok`).

module GC.Spec.Top.PagesMinor

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
module PL = GC.Spec.Pages.Promote.Loop
module PI = GC.Spec.Pages.Promote.Idle
module PPI = GC.Spec.Pages.PromoteInst
module PR = GC.Spec.Top.PromoteRun
module PC = GC.Spec.Top.PromoteCopy
module Y = GC.Spec.Top.Young
module YI = GC.Spec.Top.YoungInfix
module Q = GC.Spec.Top.PagesQueue
module O = GC.Spec.Top.PagesOor
module LV = GC.Spec.Top.PagesLive
module BM = GC.Spec.Top.ByteMark
module F = GC.Spec.Top.PagesFwd
module GenInv = GC.Gen.HeapInvariant
module MS = GC.Spec.Pages.MidSweep
module PA = GC.Spec.Pages.Allocator
module PMP = GC.Spec.Pages.MarkPhase

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The component
/// ---------------------------------------------------------------------------

/// **The minor collection.**
let pcollect (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) : GTot (T.minor_result heap pk pa) =
  let ms = cw.T.cyng in
  let tl = ptal ph st in
  let g0 = gl cw.T.cmaj st in
  let w = BM.cview cw in
  let roots = LV.roots_of w in
  let cs = P.promote tl ms g0 st.ps roots in
  if FStar.IndefiniteDescription.strong_excluded_middle (PR.wit tl ms (LV.live w ms) g0 st.ps cs.P.queue)
  then T.OutOfRoom
  else
    let r = P.collect tl ms g0 st.ps roots in
    let cps = Q.copies cs.P.queue cs.P.fwd (Seq.length cs.P.queue) in
    let y = Y.ycabs ms in
    T.Done r.P.rmajor (tst r.P.rmajor r.P.rst) (L.map (T.fwdv y (F.fwd_of cps)) cw.T.croots) (F.fwd_of cps)

let pminor : T.minor heap minor_state pk pa = { T.collect = pcollect }

/// ---------------------------------------------------------------------------
/// What the promotion needs
/// ---------------------------------------------------------------------------

/// The page invariant gives the instance's invariant and contract.
let tal_start (ph: T.phase pprog) (st: pst) (h0: heap)
  : Lemma (requires pa.T.inv ph h0 st)
          (ensures (ptal ph st).P.inv (gl h0 st) st.ps /\ P.contract (ptal ph st))
  = match ph with
    | T.Idle -> PI.idle_contract ()
    | T.Marking -> PPI.mark_contract ()
    | T.Sweeping _ -> PPI.sw_contract st.ps.pm

/// Two views of the same world trace the same young blocks.
let rec mlive_heq (w1 w2: M.world) (o: nat) (l: M.mlive w1 o)
  : Lemma (requires R.heq w1.M.maj w2.M.maj /\ R.heq w1.M.yng w2.M.yng /\ w1.M.roots == w2.M.roots /\
                    w1.M.rem == w2.M.rem)
          (ensures M.minor_live w2 o) (decreases l)
  = assert (forall (a: nat). M.resolve w1.M.yng a == M.resolve w2.M.yng a);
    match l with
    | M.LRoot _ a _ -> let l' : M.mlive w2 o = M.LRoot o a () in ()
    | M.LRem _ x i a _ -> let l' : M.mlive w2 o = M.LRem o x i a () in ()
    | M.LStep y _ l0 _ ->
      mlive_heq w1 w2 y l0;
      let l2 = FStar.IndefiniteDescription.indefinite_description_ghost (M.mlive w2 y) (fun _ -> True) in
      assert (M.young_edge w2.M.yng y o);
      let l' : M.mlive w2 o = M.LStep y o l2 () in ()

let live_heq (w1 w2: M.world) (o: nat)
  : Lemma (requires R.heq w1.M.maj w2.M.maj /\ R.heq w1.M.yng w2.M.yng /\ w1.M.roots == w2.M.roots /\
                    w1.M.rem == w2.M.rem)
          (ensures M.minor_live w1 o <==> M.minor_live w2 o)
  = let a () : Lemma (requires M.minor_live w1 o) (ensures M.minor_live w2 o)
      = let l = FStar.IndefiniteDescription.indefinite_description_ghost (M.mlive w1 o) (fun _ -> True) in
        mlive_heq w1 w2 o l in
    let b () : Lemma (requires M.minor_live w2 o) (ensures M.minor_live w1 o)
      = let l = FStar.IndefiniteDescription.indefinite_description_ghost (M.mlive w2 o) (fun _ -> True) in
        mlive_heq w2 w1 o l in
    FStar.Classical.move_requires a ();
    FStar.Classical.move_requires b ()

/// The view of the collector's world, and any view of it.
let views (cw: T.cworld heap minor_state) (w: M.world)
  : Lemma (requires T.cviews byte_rep cw w)
          (ensures R.heq w.M.maj (BM.cview cw).M.maj /\ R.heq w.M.yng (BM.cview cw).M.yng /\
                   w.M.roots == (BM.cview cw).M.roots /\ w.M.rem == (BM.cview cw).M.rem /\
                   Y.yrepr w.M.yng cw.T.cyng /\ Y.yrepr (BM.cview cw).M.yng cw.T.cyng)
  = BM.yrepr_heq w.M.yng cw.T.cyng;
    Y.yrepr_elim w.M.yng cw.T.cyng;
    Y.ycabs_facts cw.T.cyng;
    R.heq_refl (Y.ycabs cw.T.cyng);
    Y.yrepr_intro (Y.ycabs cw.T.cyng) cw.T.cyng

/// One major field of a nursery object: a block in use for the instance.
#push-options "--z3rlimit 40"
let mmf_one (ph: T.phase pprog) (st: pst) (h0: heap) (w: M.world) (ms: minor_state) (obj: U64.t) (j: nat)
  : Lemma (requires pa.T.inv ph h0 st /\ R.heq w.M.maj (cabs h0) /\ Y.yrepr w.M.yng ms /\
                    T.young_sound pa ph st h0 w /\
                    Seq.mem obj (minor_objects ms) /\ j < minor_scan_wosize ms obj /\
                    is_pointer_field (minor_read_field ms obj j))
          (ensures in_use (ptal ph st).P.free (gl h0 st) ((minor_read_field ms obj j) <: obj_addr))
  = let y = w.M.yng in
    Q.obj_young y ms obj;
    let o = Q.yof obj in
    PC.young_obj y ms o;
    minor_scan_wosize_cases ms obj;
    let f = minor_read_field ms obj j in
    PC.young_field y ms o j;
    ptr_decode f;
    let b = ptr_b f in
    assert (M.ptr_field y o j);
    assert (M.is_block w.M.maj b);
    let g0 = gl h0 st in
    cabs_set_low h0 st.lo;
    assert (M.is_block (cabs g0) b);
    abs_is_block g0 b;
    abs_header g0 b;
    is_white_iff f g0;
    is_blue_iff f g0;
    assert (T.live_target pa ph st h0 w.M.maj b);
    match ph with
    | T.Sweeping p -> MS.uw_same p.ppm st.ps.pm (pos b)
    | _ -> ()
#pop-options

let young_ok_heq (y y': M.mheap) : Lemma (requires M.young_ok y /\ R.heq y y') (ensures M.young_ok y')
  = assert (forall (o: nat). M.is_block y' o == M.is_block y o);
    assert (forall (o: nat). M.hdr_of y' o == M.hdr_of y o);
    assert (forall (o w: nat). M.covers y' o w == M.covers y o w)

let yinfix_heq (y y': M.mheap) : Lemma (requires T.young_infix_ok y /\ R.heq y y') (ensures T.young_infix_ok y')
  = assert (forall (o: nat). M.is_block y' o == M.is_block y o);
    assert (forall (o: nat). M.hdr_of y' o == M.hdr_of y o);
    assert (forall (o i: nat). M.field y' o i == M.field y o i)

/// **What the promotion needs**, from the minor collection's precondition.
let ctx_start (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world)
  : Lemma (requires T.cviews byte_rep cw w /\ T.minor_pre pa ph st cw.T.cmaj w)
          (ensures PL.ctx (ptal ph st) cw.T.cyng (gl cw.T.cmaj st) /\
                   (ptal ph st).P.inv (gl cw.T.cmaj st) st.ps)
  = let ms = cw.T.cyng in
    let h0 = cw.T.cmaj in
    views cw w;
    tal_start ph st h0;
    YI.young_infix_wf w.M.yng ms;
    P.contract_wf (ptal ph st) (gl h0 st) st.ps;
    GenInv.minor_major_fields_not_free_intro (ptal ph st).P.free ms (gl h0 st)
      (fun obj j -> mmf_one ph st h0 w ms obj j)

/// **The promotion's outcome**, on the collector's world.
let run_done (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world)
  : Lemma (requires T.cviews byte_rep cw w /\ T.minor_pre pa ph st cw.T.cmaj w)
          (ensures (let ms = cw.T.cyng in
                    let wc = BM.cview cw in
                    let tl = ptal ph st in
                    let g0 = gl cw.T.cmaj st in
                    let roots = LV.roots_of wc in
                    let cs = P.promote tl ms g0 st.ps roots in
                    PR.sok tl ms (LV.live wc ms) g0 st.ps cs /\
                    (PR.wit tl ms (LV.live wc ms) g0 st.ps cs.P.queue \/
                     ((forall (i: nat). i < Seq.length roots ==> PR.covered ms cs (Seq.index roots i)) /\
                      PR.scanned ms cs (Seq.length cs.P.queue)))))
  = let ms = cw.T.cyng in
    let wc = BM.cview cw in
    views cw w;
    ctx_start ph st cw w;
    young_ok_heq w.M.yng wc.M.yng;
    yinfix_heq w.M.yng wc.M.yng;
    LV.live_closed wc ms;
    LV.roots_just wc ms;
    PR.promote_done (ptal ph st) ms (LV.live wc ms) (gl cw.T.cmaj st) st.ps (LV.roots_of wc)

/// ---------------------------------------------------------------------------
/// OutOfRoom
/// ---------------------------------------------------------------------------

let qpre_intro (ph: T.phase pprog) (st0: pst) (h0: heap) (y: M.mheap) (w: M.world) (ms: minor_state)
               (cs: P.gstate pstate)
  : Lemma (requires pa.T.inv ph h0 st0 /\ M.well_formed w.M.maj /\ R.heq w.M.maj (cabs h0) /\
                    T.young_sound pa ph st0 h0 w /\ w.M.yng == y /\ Y.yrepr y ms /\
                    PR.qok (ptal ph st0) ms (gl h0 st0) st0.ps cs)
          (ensures Q.qpre ph st0 h0 y w ms cs)
  = reveal_opaque (`%Q.qpre) (Q.qpre ph st0 h0 y w ms cs)

let fpre_intro (ph: T.phase pprog) (st0: pst) (h0: heap) (y: M.mheap) (w: M.world) (ms: minor_state)
               (cs: P.gstate pstate) (k: nat) (x: U64.t)
  : Lemma (requires Q.qpre ph st0 h0 y w ms cs /\ k <= Seq.length cs.P.queue /\
                    Seq.mem x (minor_objects ms) /\ minor_wosize ms x > 0 /\
                    PR.fails_at (ptal ph st0) ms (gl h0 st0) st0.ps cs.P.queue k x)
          (ensures O.fpre ph st0 h0 y w ms cs k x)
  = reveal_opaque (`%O.fpre) (O.fpre ph st0 h0 y w ms cs k x)

/// A block of the failing order: a young block, live.
#push-options "--z3rlimit 40"
let ys_live (w wc: M.world) (ms: minor_state) (q: seq U64.t) (k: nat) (x: U64.t) (o: nat)
  : Lemma (requires L.memP o (O.ys_from q 0 k x) /\ Y.yrepr w.M.yng ms /\ k <= Seq.length q /\
                    R.heq w.M.maj wc.M.maj /\ R.heq w.M.yng wc.M.yng /\ w.M.roots == wc.M.roots /\
                    w.M.rem == wc.M.rem /\
                    LV.live wc ms x /\ (forall (i: nat). i < Seq.length q ==> LV.live wc ms (Seq.index q i)))
          (ensures M.is_block w.M.yng o /\ M.minor_live w o)
  = O.ys_mem q 0 k x o;
    if o = Q.yof x then begin
      Q.obj_young w.M.yng ms x;
      live_heq wc w o
    end
    else begin
      let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
                (fun i -> 0 <= i /\ i < k /\ i < Seq.length q /\ o == Q.yof (Seq.index q i)) in
      Q.obj_young w.M.yng ms (Seq.index q i);
      live_heq wc w o
    end
#pop-options

/// The queue's objects are nursery objects.
let queue_objs (#s: Type0) (a: P.tal s) (ms: minor_state) (g0: heap) (st0: s) (cs: P.gstate s)
  : Lemma (requires PR.qok a ms g0 st0 cs)
          (ensures PR.qdistinct cs.P.queue /\
                   (forall (i: nat). i < Seq.length cs.P.queue ==> Seq.mem (Seq.index cs.P.queue i) (minor_objects ms)))
  = let one (i: nat) : Lemma (i < Seq.length cs.P.queue ==> Seq.mem (Seq.index cs.P.queue i) (minor_objects ms))
      = if i < Seq.length cs.P.queue then assert (PR.qentry a ms g0 st0 cs i) in
    FStar.Classical.forall_intro one

/// The failing order, from a witness `(k, x)`.
#push-options "--z3rlimit 40"
let oor_from (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world)
             (cs: P.gstate pstate) (k: nat) (x: U64.t)
  : Lemma (requires T.cviews byte_rep cw w /\ T.minor_pre pa ph st cw.T.cmaj w /\
                    PR.sok (ptal ph st) cw.T.cyng (LV.live (BM.cview cw) cw.T.cyng) (gl cw.T.cmaj st) st.ps cs /\
                    k <= Seq.length cs.P.queue /\ Seq.mem x (minor_objects cw.T.cyng) /\
                    minor_wosize cw.T.cyng x > 0 /\ LV.live (BM.cview cw) cw.T.cyng x /\
                    (forall (j: nat). j < k ==> Seq.index cs.P.queue j =!= x) /\
                    PR.fails_at (ptal ph st) cw.T.cyng (gl cw.T.cmaj st) st.ps cs.P.queue k x)
          (ensures T.oor_justified byte_rep pa ph st cw w)
  = let ms = cw.T.cyng in
    let h0 = cw.T.cmaj in
    let wc = BM.cview cw in
    let q = cs.P.queue in
    views cw w;
    qpre_intro ph st h0 w.M.yng w ms cs;
    fpre_intro ph st h0 w.M.yng w ms cs k x;
    O.at_start ph st h0 ms q;
    O.fold_none ph st h0 w.M.yng w ms cs 0 k x h0 st;
    queue_objs (ptal ph st) ms (gl h0 st) st.ps cs;
    O.ys_norep w.M.yng ms q 0 k x;
    let ys = O.ys_from q 0 k x in
    FStar.Classical.forall_intro (FStar.Classical.move_requires (ys_live w wc ms q k x));
    assert (L.noRepeats ys /\ (forall (o: nat). L.memP o ys ==> M.is_block w.M.yng o /\ M.minor_live w o) /\
            T.alloc_fold byte_rep pa ph cw.T.cmaj st w.M.yng ys == None)
#pop-options

/// **A refused promotion justifies `OutOfRoom`.**
let oor_ok (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world)
  : Lemma (requires T.cviews byte_rep cw w /\ T.minor_pre pa ph st cw.T.cmaj w /\
                    (let wc = BM.cview cw in
                     let cs = P.promote (ptal ph st) cw.T.cyng (gl cw.T.cmaj st) st.ps (LV.roots_of wc) in
                     PR.wit (ptal ph st) cw.T.cyng (LV.live wc cw.T.cyng) (gl cw.T.cmaj st) st.ps cs.P.queue))
          (ensures T.oor_justified byte_rep pa ph st cw w)
  = let ms = cw.T.cyng in
    let wc = BM.cview cw in
    let tl = ptal ph st in
    let g0 = gl cw.T.cmaj st in
    let cs = P.promote tl ms g0 st.ps (LV.roots_of wc) in
    run_done ph st cw w;
    let k = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun k -> exists (x: U64.t).
                 k <= Seq.length cs.P.queue /\ Seq.mem x (minor_objects ms) /\ ~(is_infix_in_minor ms x) /\
                 minor_wosize ms x > 0 /\ LV.live wc ms x /\
                 (forall (j: nat). j < k ==> Seq.index cs.P.queue j =!= x) /\ PR.fails_at tl ms g0 st.ps cs.P.queue k x) in
    let x = FStar.IndefiniteDescription.indefinite_description_ghost U64.t
              (fun x -> k <= Seq.length cs.P.queue /\ Seq.mem x (minor_objects ms) /\ ~(is_infix_in_minor ms x) /\
                 minor_wosize ms x > 0 /\ LV.live wc ms x /\
                 (forall (j: nat). j < k ==> Seq.index cs.P.queue j =!= x) /\ PR.fails_at tl ms g0 st.ps cs.P.queue k x) in
    oor_from ph st cw w cs k x
