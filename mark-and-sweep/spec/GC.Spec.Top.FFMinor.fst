/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFMinor - the minor collection over first-fit, as a
/// component
/// ---------------------------------------------------------------------------
///
/// `ffminor`: the minor collection of GC.Spec.Pages.Promote with first-fit's
/// instance for the phase (`FFReplay.ptal`: `FFPromote.fftal`), on the heap
/// `gl h st`, forwarding the young pointers the model resolves among the
/// roots and remembered slots (`PagesLive.roots_of`).  It reports
/// `OutOfRoom` exactly when the promotion refused a live object
/// (`PromoteRun.wit`); otherwise it returns akhil's pointer update of the
/// promoted heap (`Promote.collect`), the free-list head, the roots
/// forwarded and the forwarding map read on the model: the lookup in the
/// list of promotions (young block, copy) the queue records
/// (`PagesFwd.fwd_of`; the contract asks for a total map).
/// GC.Spec.Top.PagesMinor's statements and proofs, over first-fit.
/// This module: the component, what the promotion needs from the minor
/// collection's precondition (`ctx_start`, `run_done`), and the
/// `OutOfRoom` case of the contract (`oor_ok`).

module GC.Spec.Top.FFMinor

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
open GC.Spec.Top.Low
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
module FFP = GC.Spec.Top.FFPromote
module FWr = GC.Spec.Top.FFWrite
module PR = GC.Spec.Top.PromoteRun
module PC = GC.Spec.Top.PromoteCopy
module Y = GC.Spec.Top.Young
module YI = GC.Spec.Top.YoungInfix
module Q = GC.Spec.Top.FFQueue
module Q0 = GC.Spec.Top.PagesQueue
module O = GC.Spec.Top.FFOor
module LV = GC.Spec.Top.PagesLive
module BM = GC.Spec.Top.ByteMark
module F = GC.Spec.Top.PagesFwd
module GenInv = GC.Gen.HeapInvariant
module FW = GC.Spec.Pages.Promote.Follow

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The component
/// ---------------------------------------------------------------------------

/// **The minor collection.**
let pcollect (ph: T.phase U64.t) (st: ffst) (cw: T.cworld heap minor_state) : GTot (T.minor_result heap ffk ffa) =
  let ms = cw.T.cyng in
  let tl = ptal ph st in
  let g0 = gl cw.T.cmaj st in
  let w = BM.cview cw in
  let roots = LV.roots_of w in
  let cs = P.promote tl ms g0 st.fp roots in
  if FStar.IndefiniteDescription.strong_excluded_middle (PR.wit tl ms (LV.live w ms) g0 st.fp cs.P.queue)
  then T.OutOfRoom
  else
    let r = P.collect tl ms g0 st.fp roots in
    let cps = Q0.copies cs.P.queue cs.P.fwd (Seq.length cs.P.queue) in
    let y = Y.ycabs ms in
    T.Done r.P.rmajor (tst r.P.rmajor r.P.rst) (L.map (T.fwdv y (F.fwd_of cps)) cw.T.croots) (F.fwd_of cps)

let ffminor : T.minor heap minor_state ffk ffa = { T.collect = pcollect }

/// ---------------------------------------------------------------------------
/// What the promotion needs
/// ---------------------------------------------------------------------------

/// The first-fit invariant gives the instance's invariant and contract.
let tal_start (ph: T.phase U64.t) (st: ffst) (h0: heap)
  : Lemma (requires ffa.T.inv ph h0 st)
          (ensures (ptal ph st).P.inv (gl h0 st) st.fp /\ P.contract (ptal ph st))
  = FWr.fshape_inv ph h0 st;
    FFP.ff_contract ph

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

/// A block the program may use is in use for the instance.
#push-options "--z3rlimit 40"
let live_in_use (ph: T.phase U64.t) (st: ffst) (h0: heap) (m: M.mheap) (x: nat)
  : Lemma (requires ffa.T.inv ph h0 st /\ R.heq m (cabs h0) /\ T.live_target ffa ph st h0 m x)
          (ensures pos x + 8 < heap_size /\ in_use (ptal ph st).P.free (gl h0 st) (obj_of x))
  = let g0 = gl h0 st in
    cabs_set_low h0 st.lo;
    assert (M.is_block (cabs g0) x);
    abs_is_block g0 x;
    abs_header g0 x;
    is_white_iff (obj_of x) g0;
    is_blue_iff (obj_of x) g0;
    match ph with
    | T.Sweeping c ->
      reveal_opaque (`%sshape) (sshape g0 st.fp c);
      GC.Spec.SweepPhase.Intrinsic.sweep_inv_incremental_elim g0 st.fp c;
      base_facts ()
    | _ -> ()
#pop-options

/// One major field of a nursery object: it resolves to a block in use for
/// the instance, through a well-formed infix address (G39: an infix pointer
/// into a major closure is one).
#push-options "--z3rlimit 40"
let mt_one (ph: T.phase U64.t) (st: ffst) (h0: heap) (w: M.world) (ms: minor_state) (obj: U64.t) (j: nat)
  : Lemma (requires ffa.T.inv ph h0 st /\ R.heq w.M.maj (cabs h0) /\ Y.yrepr w.M.yng ms /\
                    T.young_sound ffa ph st h0 w /\
                    Seq.mem obj (minor_objects ms) /\ j < minor_scan_wosize ms obj /\
                    is_pointer_field (minor_read_field ms obj j))
          (ensures (let v : obj_addr = minor_read_field ms obj j in
                    in_use (ptal ph st).P.free (gl h0 st) (resolve_object v (gl h0 st)) /\
                    infix_addr_wf (gl h0 st) (objects zero_addr (gl h0 st)) v))
  = let y = w.M.yng in
    Q0.obj_young y ms obj;
    let o = Q0.yof obj in
    PC.young_obj y ms o;
    minor_scan_wosize_cases ms obj;
    let f = minor_read_field ms obj j in
    PC.young_field y ms o j;
    ptr_decode f;
    let b = ptr_b f in
    assert (M.ptr_field y o j);
    assert (T.sound_value ffa ph st h0 w.M.maj (M.VPtr (M.Major b)));
    let x = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun x -> M.resolve w.M.maj b == Some x /\ T.live_target ffa ph st h0 w.M.maj x) in
    let g0 = gl h0 st in
    cabs_set_low h0 st.lo;
    assert (M.resolve (cabs g0) b == Some x);
    GC.Spec.Top.ByteWrite.resolve_abs_of_cabs g0 b x;
    tal_start ph st h0;
    P.contract_wf (ptal ph st) g0 st.fp;
    wf_with_parts ();
    ptr_resolve g0 b x;
    live_in_use ph st h0 w.M.maj x;
    assert (resolve_object f g0 == obj_of x)
#pop-options

let young_ok_heq (y y': M.mheap) : Lemma (requires M.young_ok y /\ R.heq y y') (ensures M.young_ok y')
  = assert (forall (o: nat). M.is_block y' o == M.is_block y o);
    assert (forall (o: nat). M.hdr_of y' o == M.hdr_of y o);
    assert (forall (o w: nat). M.covers y' o w == M.covers y o w)

let follow_at_heq (y y': M.mheap) (a: nat) : Lemma (requires T.follow_at y a /\ R.heq y y') (ensures T.follow_at y' a)
  = assert (forall (o: nat). M.is_block y' o == M.is_block y o);
    assert (forall (o: nat). M.hdr_of y' o == M.hdr_of y o);
    assert (forall (o w: nat). M.covers y' o w == M.covers y o w);
    if FStar.IndefiniteDescription.strong_excluded_middle (exists (o: nat). M.covers y' o a /\ o < a) then begin
      assert (R.field_word y' a);
      assert (y'.M.body a == y.M.body a);
      assert (M.resolve y' a == M.resolve y a)
    end

let yfollow_heq (y y': M.mheap) : Lemma (requires T.young_follow_ok y /\ R.heq y y') (ensures T.young_follow_ok y')
  = let one (o i a: nat)
      : Lemma (M.ptr_field y' o i /\ M.field y' o i == M.VPtr (M.Young a) ==> T.follow_at y' a)
      = if M.ptr_field y' o i && M.field y' o i = M.VPtr (M.Young a) then begin
          assert (M.is_block y' o == M.is_block y o);
          assert (M.hdr_of y' o == M.hdr_of y o);
          assert (M.field y' o i == M.field y o i);
          assert (M.ptr_field y o i);
          assert (M.field y o i == M.VPtr (M.Young a));
          assert (T.follow_at y a);
          follow_at_heq y y' a
        end in
    FStar.Classical.forall_intro_3 one

/// **What the promotion needs**, from the minor collection's precondition.
#push-options "--z3rlimit 40"
let ctx_start (ph: T.phase U64.t) (st: ffst) (cw: T.cworld heap minor_state) (w: M.world)
  : Lemma (requires T.cviews byte_rep cw w /\ T.minor_pre ffa ph st cw.T.cmaj w)
          (ensures PL.ctx_w (ptal ph st) cw.T.cyng (gl cw.T.cmaj st) /\
                   PL.cpre_w (ptal ph st) cw.T.cyng (gl cw.T.cmaj st) st.fp (LV.roots_of (BM.cview cw)) /\
                   (ptal ph st).P.inv (gl cw.T.cmaj st) st.fp)
  = let ms = cw.T.cyng in
    let h0 = cw.T.cmaj in
    let wc = BM.cview cw in
    views cw w;
    tal_start ph st h0;
    YI.young_minor_wf w.M.yng ms;
    LV.fields_follow_of w.M.yng ms;
    young_ok_heq w.M.yng wc.M.yng;
    LV.roots_follow_of wc ms;
    P.contract_wf (ptal ph st) (gl h0 st) st.fp;
    GenInv.minor_major_fields_not_free_intro (ptal ph st).P.free ms (gl h0 st)
      (fun obj j -> mt_one ph st h0 w ms obj j)
#pop-options

/// **The promotion's outcome**, on the collector's world.
let run_done (ph: T.phase U64.t) (st: ffst) (cw: T.cworld heap minor_state) (w: M.world)
  : Lemma (requires T.cviews byte_rep cw w /\ T.minor_pre ffa ph st cw.T.cmaj w)
          (ensures (let ms = cw.T.cyng in
                    let wc = BM.cview cw in
                    let tl = ptal ph st in
                    let g0 = gl cw.T.cmaj st in
                    let roots = LV.roots_of wc in
                    let cs = P.promote tl ms g0 st.fp roots in
                    PR.sok tl ms (LV.live wc ms) g0 st.fp cs /\
                    (PR.wit tl ms (LV.live wc ms) g0 st.fp cs.P.queue \/
                     ((forall (i: nat). i < Seq.length roots ==> PR.covered ms cs (Seq.index roots i)) /\
                      PR.scanned ms cs (Seq.length cs.P.queue)))))
  = let ms = cw.T.cyng in
    let wc = BM.cview cw in
    views cw w;
    ctx_start ph st cw w;
    young_ok_heq w.M.yng wc.M.yng;
    yfollow_heq w.M.yng wc.M.yng;
    LV.live_closed wc ms;
    LV.roots_just wc ms;
    PR.promote_done (ptal ph st) ms (LV.live wc ms) (gl cw.T.cmaj st) st.fp (LV.roots_of wc)

/// ---------------------------------------------------------------------------
/// OutOfRoom
/// ---------------------------------------------------------------------------

let qpre_intro (ph: T.phase U64.t) (st0: ffst) (h0: heap) (y: M.mheap) (w: M.world) (ms: minor_state)
               (cs: P.gstate U64.t)
  : Lemma (requires ffa.T.inv ph h0 st0 /\ M.well_formed w.M.maj /\ R.heq w.M.maj (cabs h0) /\
                    T.young_sound ffa ph st0 h0 w /\ w.M.yng == y /\ Y.yrepr y ms /\
                    PR.qok (ptal ph st0) ms (gl h0 st0) st0.fp cs)
          (ensures Q.qpre ph st0 h0 y w ms cs)
  = reveal_opaque (`%Q.qpre) (Q.qpre ph st0 h0 y w ms cs)

let fpre_intro (ph: T.phase U64.t) (st0: ffst) (h0: heap) (y: M.mheap) (w: M.world) (ms: minor_state)
               (cs: P.gstate U64.t) (k: nat) (x: U64.t)
  : Lemma (requires Q.qpre ph st0 h0 y w ms cs /\ k <= Seq.length cs.P.queue /\
                    Seq.mem x (minor_objects ms) /\ minor_wosize ms x > 0 /\
                    PR.fails_at (ptal ph st0) ms (gl h0 st0) st0.fp cs.P.queue k x)
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
    if o = Q0.yof x then begin
      Q0.obj_young w.M.yng ms x;
      live_heq wc w o
    end
    else begin
      let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
                (fun i -> 0 <= i /\ i < k /\ i < Seq.length q /\ o == Q0.yof (Seq.index q i)) in
      Q0.obj_young w.M.yng ms (Seq.index q i);
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
let oor_from (ph: T.phase U64.t) (st: ffst) (cw: T.cworld heap minor_state) (w: M.world)
             (cs: P.gstate U64.t) (k: nat) (x: U64.t)
  : Lemma (requires T.cviews byte_rep cw w /\ T.minor_pre ffa ph st cw.T.cmaj w /\
                    PR.sok (ptal ph st) cw.T.cyng (LV.live (BM.cview cw) cw.T.cyng) (gl cw.T.cmaj st) st.fp cs /\
                    k <= Seq.length cs.P.queue /\ Seq.mem x (minor_objects cw.T.cyng) /\
                    minor_wosize cw.T.cyng x > 0 /\ LV.live (BM.cview cw) cw.T.cyng x /\
                    (forall (j: nat). j < k ==> Seq.index cs.P.queue j =!= x) /\
                    PR.fails_at (ptal ph st) cw.T.cyng (gl cw.T.cmaj st) st.fp cs.P.queue k x)
          (ensures T.oor_justified byte_rep ffa ph st cw w)
  = let ms = cw.T.cyng in
    let h0 = cw.T.cmaj in
    let wc = BM.cview cw in
    let q = cs.P.queue in
    views cw w;
    qpre_intro ph st h0 w.M.yng w ms cs;
    fpre_intro ph st h0 w.M.yng w ms cs k x;
    O.at_start ph st h0 ms q;
    O.fold_none ph st h0 w.M.yng w ms cs 0 k x h0 st;
    queue_objs (ptal ph st) ms (gl h0 st) st.fp cs;
    O.ys_norep w.M.yng ms q 0 k x;
    let ys = O.ys_from q 0 k x in
    FStar.Classical.forall_intro (FStar.Classical.move_requires (ys_live w wc ms q k x));
    assert (L.noRepeats ys /\ (forall (o: nat). L.memP o ys ==> M.is_block w.M.yng o /\ M.minor_live w o) /\
            T.alloc_fold byte_rep ffa ph cw.T.cmaj st w.M.yng ys == None)
#pop-options

/// **A refused promotion justifies `OutOfRoom`.**
let oor_ok (ph: T.phase U64.t) (st: ffst) (cw: T.cworld heap minor_state) (w: M.world)
  : Lemma (requires T.cviews byte_rep cw w /\ T.minor_pre ffa ph st cw.T.cmaj w /\
                    (let wc = BM.cview cw in
                     let cs = P.promote (ptal ph st) cw.T.cyng (gl cw.T.cmaj st) st.fp (LV.roots_of wc) in
                     PR.wit (ptal ph st) cw.T.cyng (LV.live wc cw.T.cyng) (gl cw.T.cmaj st) st.fp cs.P.queue))
          (ensures T.oor_justified byte_rep ffa ph st cw w)
  = let ms = cw.T.cyng in
    let wc = BM.cview cw in
    let tl = ptal ph st in
    let g0 = gl cw.T.cmaj st in
    let cs = P.promote tl ms g0 st.fp (LV.roots_of wc) in
    run_done ph st cw w;
    let k = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun k -> exists (x: U64.t).
                 k <= Seq.length cs.P.queue /\ Seq.mem x (minor_objects ms) /\ ~(is_infix_in_minor ms x) /\
                 minor_wosize ms x > 0 /\ LV.live wc ms x /\
                 (forall (j: nat). j < k ==> Seq.index cs.P.queue j =!= x) /\ PR.fails_at tl ms g0 st.fp cs.P.queue k x) in
    let x = FStar.IndefiniteDescription.indefinite_description_ghost U64.t
              (fun x -> k <= Seq.length cs.P.queue /\ Seq.mem x (minor_objects ms) /\ ~(is_infix_in_minor ms x) /\
                 minor_wosize ms x > 0 /\ LV.live wc ms x /\
                 (forall (j: nat). j < k ==> Seq.index cs.P.queue j =!= x) /\ PR.fails_at tl ms g0 st.fp cs.P.queue k x) in
    oor_from ph st cw w cs k x
