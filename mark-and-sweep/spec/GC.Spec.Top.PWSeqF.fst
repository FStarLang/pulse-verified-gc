/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PWSeqF - what the pages sequential witness run shows
/// ---------------------------------------------------------------------------
///
/// Design doc §17.  On the run `PWSeq.es_seq` (the sweep has `k = ksw () > 0`
/// steps, from event 14):
///   - `seq_cycle`: events 7 to 14 + k are a cycle (`is_cycle`);
///   - `seq_every_event`: every kind of event occurs;
///   - `seq_start`: at the cycle's start (7), A is the only outside
///     reference, A, B and K are reachable, C is in use and unreachable;
///   - `seq_minor_phases`: minor collections at 8 (marking), 13 (sweeping)
///     and 19 + k (idle);
///   - `seq_freed`: C is free after the cycle (15 + k);
///   - `seq_promotes`: the last collection is `Done`, and promotes Y1 and Y2.

module GC.Spec.Top.PWSeqF

open GC.Spec.Top.Run
open GC.Spec.Top.PWDesc
open GC.Spec.Top.PWRun
open GC.Spec.Top.PWPre
open GC.Spec.Top.PWCyc
open GC.Spec.Top.PWSeq
open GC.Spec.Top.PWList
module M = GC.Spec.Top.Heap
module PWK = GC.Spec.Top.PWMark
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module RA = GC.Spec.Top.RunApp
module PWS = GC.Spec.Top.PWSweep
module PWM = GC.Spec.Top.PWMinor
module PWP = GC.Spec.Top.PWPages
module PSw = GC.Spec.Top.PagesSweep
module MS = GC.Spec.Pages.MidSweep
module PMP = GC.Spec.Pages.MarkPhase

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// A finished sweep leaves nothing unswept.
let done_unswept (p: GC.Spec.Top.PagesAlloc.pprog) (h: GC.Spec.Base.heap) (s: GC.Spec.Top.PagesAlloc.pst) (o: nat)
  : Lemma (requires GC.Spec.Top.PagesAlloc.pinv (T.Sweeping p) h s /\ PSw.pdone p == true)
          (ensures GC.Spec.Top.PagesAlloc.punswept p o == false)
  = PSw.swept_upto_iff p.GC.Spec.Top.PagesAlloc.ppm GC.Spec.Pages.Layout.n_pages;
    assert (PMP.all_swept s.GC.Spec.Top.PagesAlloc.ps);
    MS.uw_same p.GC.Spec.Top.PagesAlloc.ppm s.GC.Spec.Top.PagesAlloc.ps.GC.Spec.Pages.Inv.pm (GC.Spec.Top.Abs.pos o);
    GC.Spec.Top.PagesAlloc.all_swept_uw s.GC.Spec.Top.PagesAlloc.ps (GC.Spec.Top.Abs.pos o)

/// **The sweep has a step**: A is in use and unswept when it starts.
let ksw_pos () : Lemma (requires pw_room /\ cok) (ensures ksw () > 0)
  = c12 (); c13 (); c14 ();
    let x12 = x12 () in
    let d12 = ddv DM M.Black M.Black M.Black true [vA ()] 6 in
    hand_dd sq x12 true [vA ()] 6;
    distinct ();
    db_dd DM M.Black M.Black M.Black true [vA ()] 6 ms0 (M.empty_heap GC.Spec.Top.Word.ywords) (xA ());
    blk x12 d12 (xA ());
    assert (unsw (x13 ()) (xA ()) == true);
    assert ((x14 ()).ph == (x13 ()).ph);
    holds_elim (x14 ()) (ddv DS M.Black M.Black M.Black true [vA ()] 8);
    assert (unsw (x14 ()) (xA ()) == true);
    let T.Sweeping p = (x14 ()).ph in
    assert (GC.Spec.Top.PagesAlloc.punswept p (xA ()) == true);
    assert (ksw () == PWP.nsw p (x14 ()).w.cmaj (stx (x14 ())));
    assert (GC.Spec.Top.PagesAlloc.pinv (T.Sweeping p) (x14 ()).w.cmaj (stx (x14 ())));
    let k = ksw () in
    assert (k == ksw ());
    if k = 0 then begin
      assert (PWP.nsw p (x14 ()).w.cmaj (stx (x14 ())) == 0);
      PWP.nsw_done p (x14 ()).w.cmaj (stx (x14 ()));
      assert (PSw.pdone p == true);
      done_unswept p (x14 ()).w.cmaj (stx (x14 ())) (xA ());
      assert False
    end

/// ---------------------------------------------------------------------------
/// The run by index
/// ---------------------------------------------------------------------------

let es_is () : Lemma (es_seq () == es3 (pre14 ()) (ksw ()) (post ())) = ()

#push-options "--fuel 16"
let len_pre () : Lemma (L.length (pre14 ()) == 14 /\ L.length (post ()) == 6) = ()

let take_pre (i: nat)
  : Lemma (requires i <= 14)
          (ensures take i (es_seq ()) == take i (pre14 ()))
  = len_pre ();
    RA.take_app_le i (pre14 ()) (L.append (PWS.repl (ksw ())) (post ()))

let pre_take () : Lemma (take 7 (pre14 ()) == [e0; e1; e2 (); e3; e4 (); e5 (); e6 ()] /\
                         take 8 (pre14 ()) == [e0; e1; e2 (); e3; e4 (); e5 (); e6 (); EStart] /\
                         take 13 (pre14 ()) == [e0; e1; e2 (); e3; e4 (); e5 (); e6 (); EStart; EMinor; PWK.esl (x9 ()); PWK.esl (x10 ()); PWK.esl (x11 ()); EHandover])
  = ()
#pop-options

#push-options "--fuel 1"
let exec_cons (x: config pc) (e: event) (tl: list event) : Lemma (exec pc x (e :: tl) == exec pc (step pc x e) tl) = ()
let exec_nil (x: config pc) : Lemma (exec pc x [] == x) = ()
#pop-options

let exec13 () : Lemma (exec pc (x0 ()) [e0; e1; e2 (); e3; e4 (); e5 (); e6 ()] == x7 () /\
                       exec pc (x0 ()) [e0; e1; e2 (); e3; e4 (); e5 (); e6 (); EStart] == x8 () /\
                       exec pc (x0 ()) [e0; e1; e2 (); e3; e4 (); e5 (); e6 (); EStart; EMinor; PWK.esl (x9 ()); PWK.esl (x10 ()); PWK.esl (x11 ()); EHandover] == x13 ())
  = exec_nil (x7 ()); exec_nil (x8 ()); exec_nil (x13 ());
    exec_cons (x12 ()) EHandover [];
    exec_cons (x11 ()) (PWK.esl (x11 ())) [EHandover];
    exec_cons (x10 ()) (PWK.esl (x10 ())) [PWK.esl (x11 ()); EHandover];
    exec_cons (x9 ()) (PWK.esl (x9 ())) [PWK.esl (x10 ()); PWK.esl (x11 ()); EHandover];
    exec_cons (x8 ()) EMinor [PWK.esl (x9 ()); PWK.esl (x10 ()); PWK.esl (x11 ()); EHandover];
    exec_cons (x7 ()) EStart [EMinor; PWK.esl (x9 ()); PWK.esl (x10 ()); PWK.esl (x11 ()); EHandover];
    exec_cons (x7 ()) EStart [];
    let l13 = [EStart; EMinor; PWK.esl (x9 ()); PWK.esl (x10 ()); PWK.esl (x11 ()); EHandover] in
    exec_cons (x6 ()) (e6 ()) l13; exec_cons (x6 ()) (e6 ()) [EStart]; exec_cons (x6 ()) (e6 ()) [];
    exec_cons (x5 ()) (e5 ()) (e6 () :: l13); exec_cons (x5 ()) (e5 ()) [e6 (); EStart]; exec_cons (x5 ()) (e5 ()) [e6 ()];
    exec_cons (x4 ()) (e4 ()) [e5 (); e6 ()] ; exec_cons (x4 ()) (e4 ()) [e5 (); e6 (); EStart];
    exec_cons (x4 ()) (e4 ()) (e5 () :: e6 () :: l13);
    exec_cons (x3 ()) e3 [e4 (); e5 (); e6 ()]; exec_cons (x3 ()) e3 [e4 (); e5 (); e6 (); EStart];
    exec_cons (x3 ()) e3 (e4 () :: e5 () :: e6 () :: l13);
    exec_cons (x2 ()) (e2 ()) [e3; e4 (); e5 (); e6 ()]; exec_cons (x2 ()) (e2 ()) [e3; e4 (); e5 (); e6 (); EStart];
    exec_cons (x2 ()) (e2 ()) (e3 :: e4 () :: e5 () :: e6 () :: l13);
    exec_cons (x1 ()) e1 [e2 (); e3; e4 (); e5 (); e6 ()]; exec_cons (x1 ()) e1 [e2 (); e3; e4 (); e5 (); e6 (); EStart];
    exec_cons (x1 ()) e1 (e2 () :: e3 :: e4 () :: e5 () :: e6 () :: l13);
    exec_cons (x0 ()) e0 [e1; e2 (); e3; e4 (); e5 (); e6 ()]; exec_cons (x0 ()) e0 [e1; e2 (); e3; e4 (); e5 (); e6 (); EStart];
    exec_cons (x0 ()) e0 (e1 :: e2 () :: e3 :: e4 () :: e5 () :: e6 () :: l13)

#push-options "--fuel 16"
let at7 () : Lemma (at pc GC.Spec.Top.Word.msize GC.Spec.Top.Word.ywords (es_seq ()) 7 == x7 () /\
                   at pc GC.Spec.Top.Word.msize GC.Spec.Top.Word.ywords (es_seq ()) 8 == x8 () /\
                   at pc GC.Spec.Top.Word.msize GC.Spec.Top.Word.ywords (es_seq ()) 13 == x13 ())
  = take_pre 7; take_pre 8; take_pre 13; pre_take (); exec13 ()
#pop-options

#push-options "--fuel 8"
let post_take () : Lemma (take 1 (post ()) == [EEnd] /\ take 5 (post ()) == [EEnd; e16 (); e17 (); e18; e19 ()]) = ()
#pop-options

let exec_post () : Lemma (exec pc (x15 ()) [EEnd] == x16 () /\ exec pc (x15 ()) [EEnd; e16 (); e17 (); e18; e19 ()] == x20 ())
  = exec_nil (x16 ()); exec_nil (x20 ());
    exec_cons (x15 ()) EEnd [];
    exec_cons (x19 ()) (e19 ()) [];
    exec_cons (x18 ()) e18 [e19 ()];
    exec_cons (x17 ()) (e17 ()) [e18; e19 ()];
    exec_cons (x16 ()) (e16 ()) [e17 (); e18; e19 ()];
    exec_cons (x15 ()) EEnd [e16 (); e17 (); e18; e19 ()]

#push-options "--fuel 8"
let at_post () : Lemma (requires pw_room /\ cok)
  (ensures at pc GC.Spec.Top.Word.msize GC.Spec.Top.Word.ywords (es_seq ()) (15 + ksw ()) == x16 () /\
           at pc GC.Spec.Top.Word.msize GC.Spec.Top.Word.ywords (es_seq ()) (19 + ksw ()) == x20 ())
  = pre_ok (); len_pre (); post_take (); exec_post ();
    at_q pc GC.Spec.Top.Word.msize GC.Spec.Top.Word.ywords (pre14 ()) (ksw ()) (post ()) 1;
    at_q pc GC.Spec.Top.Word.msize GC.Spec.Top.Word.ywords (pre14 ()) (ksw ()) (post ()) 5
#pop-options

/// ---------------------------------------------------------------------------
/// The cycle
/// ---------------------------------------------------------------------------

#push-options "--fuel 16"
let ev_pre (i: nat)
  : Lemma (requires i < 14) (ensures i < L.length (es_seq ()) /\ ev (es_seq ()) i == L.index (pre14 ()) i)
  = len_pre (); ev_p (pre14 ()) (ksw ()) (post ()) i

/// Positions in lists of 14 and 6 events, over variables (the slices'
/// events are then not unfolded).
let idx14 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13: event)
  : Lemma (let l = [a0; a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11; a12; a13] in
           L.index l 7 == a7 /\ L.index l 8 == a8 /\ L.index l 9 == a9 /\ L.index l 10 == a10 /\
           L.index l 11 == a11 /\ L.index l 12 == a12 /\ L.index l 13 == a13)
  = ()

let idx6 (a0 a1 a2 a3 a4 a5: event)
  : Lemma (let l = [a0; a1; a2; a3; a4; a5] in L.index l 0 == a0 /\ L.index l 5 == a5)
  = ()

let pre_events () : Lemma (L.index (pre14 ()) 7 == EStart /\ L.index (pre14 ()) 8 == EMinor /\
                           L.index (pre14 ()) 9 == PWK.esl (x9 ()) /\ L.index (pre14 ()) 10 == PWK.esl (x10 ()) /\
                           L.index (pre14 ()) 11 == PWK.esl (x11 ()) /\ L.index (pre14 ()) 12 == EHandover /\
                           L.index (pre14 ()) 13 == EMinor /\
                           L.index (post ()) 0 == EEnd /\ L.index (post ()) 5 == EMinor)
  = idx14 e0 e1 (e2 ()) e3 (e4 ()) (e5 ()) (e6 ()) EStart EMinor (PWK.esl (x9 ())) (PWK.esl (x10 ())) (PWK.esl (x11 ()))
          EHandover EMinor;
    idx6 EEnd (e16 ()) (e17 ()) e18 (e19 ()) EMinor
#pop-options

let pre7 () : GTot (list event) = [e0; e1; e2 (); e3; e4 (); e5 (); e6 ()]
let midl () : GTot (list event) = [EStart; EMinor; PWK.esl (x9 ()); PWK.esl (x10 ()); PWK.esl (x11 ()); EHandover; EMinor]

#push-options "--fuel 16"
let pre_split () : Lemma (pre14 () == L.append (pre7 ()) (midl ()) /\ L.length (pre7 ()) == 7 /\ L.length (midl ()) == 7) = ()

let mid7 (b c e: event) (i: nat)
  : Lemma (requires ESlice? b /\ ESlice? c /\ ESlice? e /\ 0 < i /\ i < 7)
          (ensures (let l = [EStart; EMinor; b; c; e; EHandover; EMinor] in
                    ~(L.index l i == EStart) /\ ~(L.index l i == EEnd)))
  = ()

let midl_ev (i: nat)
  : Lemma (requires 0 < i /\ i < 7) (ensures ~(L.index (midl ()) i == EStart) /\ ~(L.index (midl ()) i == EEnd))
  = mid7 (PWK.esl (x9 ())) (PWK.esl (x10 ())) (PWK.esl (x11 ())) i
#pop-options

let pre_mid (t: nat)
  : Lemma (requires 7 < t /\ t < 14)
          (ensures t < L.length (pre14 ()) /\ ~(L.index (pre14 ()) t == EStart) /\ ~(L.index (pre14 ()) t == EEnd))
  = pre_split ();
    RA.index_app_ge (pre7 ()) (midl ()) (t - 7);
    midl_ev (t - 7)

/// Between 7 and 14 + k: no start, no end.
let mid_ev (t: nat)
  : Lemma (requires 7 < t /\ t < 14 + ksw ())
          (ensures t < L.length (es_seq ()) /\ ~(ev (es_seq ()) t == EStart) /\ ~(ev (es_seq ()) t == EEnd))
  = es_is (); len_pre (); pre_events ();
    len3 (pre14 ()) (ksw ()) (post ());
    if t < 14 then (ev_pre t; pre_mid t)
    else ev_r (pre14 ()) (ksw ()) (post ()) (t - 14)

/// **Events 7 to 14 + k are a cycle.**
let seq_cycle () : Lemma (requires pw_room /\ cok) (ensures is_cycle (es_seq ()) 7 (14 + ksw ()))
  = es_is (); len_pre (); pre_events ();
    len3 (pre14 ()) (ksw ()) (post ());
    ev_pre 7;
    ev_q (pre14 ()) (ksw ()) (post ()) 0;
    FStar.Classical.forall_intro (FStar.Classical.move_requires mid_ev)

/// **Every kind of event occurs.**
#push-options "--fuel 24 --ifuel 2"
let every_flat () : Lemma (every_event (L.append (pre14 ()) (ESweep :: post ())))
  = ()
#pop-options

let seq_every_event () : Lemma (requires pw_room /\ cok) (ensures every_event (es_seq ()))
  = ksw_pos ();
    every3 (pre14 ()) (ksw ()) (post ());
    every_flat ()

/// ---------------------------------------------------------------------------
/// What the run shows
/// ---------------------------------------------------------------------------

let w7 () : GTot M.world = wd (x7 ()) (d7c ())

/// **At the cycle's start**: A is the only outside reference; A, B and K are
/// reachable (K only through B's infix pointer), C is in use and is not.
let seq_start () : Lemma (requires pw_room /\ cok)
  (ensures at pc GC.Spec.Top.Word.msize GC.Spec.Top.Word.ywords (es_seq ()) 7 == x7 () /\
           7 < L.length (es_seq ()) /\ ev (es_seq ()) 7 == EStart /\
           (forall (o: nat). M.outside_ref (w7 ()) o <==> o == xA ()) /\
           M.reachable (w7 ()) (xA ()) /\ M.reachable (w7 ()) (xB ()) /\ M.reachable (w7 ()) (xK ()) /\
           (forall (o: nat). M.reachable (w7 ()) o ==> o == xA () \/ o == xB () \/ o == xK ()) /\
           iu (x7 ()) (xC ()) == true /\ ~(M.reachable (w7 ()) (xC ())) /\
           M.field (mx (x7 ())) (xB ()) 0 == vK2 () /\ M.field (mx (x7 ())) (xK ()) 1 == iw)
  = at7 (); start7 (); len_pre (); pre_events (); ev_pre 7; es_is (); len3 (pre14 ()) (ksw ()) (post ());
    distinct ();
    let x = x7 () in
    let d = d7c () in
    db_dd DI M.White M.White M.White true [vA ()] 4 ms0 (M.empty_heap GC.Spec.Top.Word.ywords) (xB ());
    db_dd DI M.White M.White M.White true [vA ()] 4 ms0 (M.empty_heap GC.Spec.Top.Word.ywords) (xK ());
    blk x d (xB ()); blk x d (xK ());
    l1 (vK2 ()); l3 i1 iw i1

/// **Minor collections in every phase**: at 8 (marking), 13 (sweeping),
/// 19 + k (idle).
let seq_minor_phases () : Lemma (requires pw_room /\ cok)
  (ensures 19 + ksw () < L.length (es_seq ()) /\ ev (es_seq ()) 8 == EMinor /\ T.Marking? (at pc GC.Spec.Top.Word.msize GC.Spec.Top.Word.ywords (es_seq ()) 8).ph /\
           ev (es_seq ()) 13 == EMinor /\ T.Sweeping? (at pc GC.Spec.Top.Word.msize GC.Spec.Top.Word.ywords (es_seq ()) 13).ph /\
           ev (es_seq ()) (19 + ksw ()) == EMinor /\
           T.Idle? (at pc GC.Spec.Top.Word.msize GC.Spec.Top.Word.ywords (es_seq ()) (19 + ksw ())).ph)
  = at7 (); at_post (); len_pre (); pre_events (); es_is (); len3 (pre14 ()) (ksw ()) (post ());
    ev_pre 8; ev_pre 13;
    ev_q (pre14 ()) (ksw ()) (post ()) 5;
    c8 (); c13 (); c20 ();
    holds_elim (x8 ()) (ddv DM M.Grey M.White M.White true [vA ()] 4);
    holds_elim (x13 ()) (ddv DS M.Black M.Black M.Black true [vA ()] 6);
    holds_elim (x20 ()) (d20 ())

/// **The cycle frees C.**
let seq_freed () : Lemma (requires pw_room /\ cok)
  (ensures iu (at pc GC.Spec.Top.Word.msize GC.Spec.Top.Word.ywords (es_seq ()) (15 + ksw ())) (xC ()) == false)
  = at_post (); c16 (); distinct ();
    not_iu (x16 ()) (ddv DI M.White M.White M.White false [vA ()] 8) (xC ())

/// **The last collection promotes Y1 (an infix pointer into K) and Y2 (an
/// integer that reads as an infix header).**
let seq_promotes () : Lemma (requires pw_room /\ cok)
  (ensures (let x = at pc GC.Spec.Top.Word.msize GC.Spec.Top.Word.ywords (es_seq ()) (19 + ksw ()) in
            T.Done? (PWM.mres x) /\ Some? (PWM.mfwd x 0) /\ Some? (PWM.mfwd x 2) /\
            M.field (wd x (d20 ())).M.yng 0 0 == vK2 () /\ M.field (wd x (d20 ())).M.yng 2 0 == iw /\
            Some? (M.infix_hdr iw)))
  = at_post (); c21 (); nice_y ();
    PWM.ym2_ok (xK ()) (vK2 ()) iw;
    st_vals ();
    assert_norm (M.infix_hdr (M.VInt 2297) == Some 2)
