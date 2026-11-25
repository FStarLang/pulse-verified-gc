/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PWIncF - what the pages incremental witness run shows
/// ---------------------------------------------------------------------------
///
/// Design doc §17.  On the run `PWIncB.es_inc` (the sweep has `k = ksw () > 0`
/// steps, from event 21):
///   - `inc_cycle`: events 7 to 21 + k are a cycle;
///   - `inc_every_event`: every kind of event occurs;
///   - `inc_darkens`: the write at 9 runs while marking, overwrites A.0 (B,
///     white), and B is grey after it;
///   - `inc_promotes`: the minor collections at 12 (marking) and 19
///     (sweeping) are `Done` and promote both young blocks, Y1 holding K + 2
///     and Y2 an integer that reads as an infix header; the last, at
///     23 + k, runs idle;
///   - `inc_interleaves`: the program allocates, writes and allocates young
///     while marking (8-11), allocates young and changes the roots while
///     sweeping (17, 18, 20);
///   - `inc_freed`: C is free after the cycle.

module GC.Spec.Top.PWIncF

open GC.Spec.Top.Run
open GC.Spec.Top.PWDesc
open GC.Spec.Top.PWRun
open GC.Spec.Top.PWPre
open GC.Spec.Top.PWIncA
open GC.Spec.Top.PWInc
open GC.Spec.Top.PWIncB
open GC.Spec.Top.PWList
module M = GC.Spec.Top.Heap
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module RA = GC.Spec.Top.RunApp
module PWS = GC.Spec.Top.PWSweep
module PWM = GC.Spec.Top.PWMinor
module PWMu = GC.Spec.Top.PWMut
module PWP = GC.Spec.Top.PWPages
module SF = GC.Spec.Top.PWSeqF
module W = GC.Spec.Top.Word

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// **The sweep has a step**: A is in use and unswept when it starts.
let ksw_pos () : Lemma (requires pw_room /\ cok) (ensures ksw () > 0)
  = c16 (); c17 (); c21 (); distinct ();
    holds_elim (x16 ()) (dM M.Black M.Black M.Black);
    holds_blk (x16 ()) (dM M.Black M.Black M.Black) (xA ());
    assert (unsw (x17 ()) (xA ()) == true);
    assert ((x21 ()).ph == (x17 ()).ph);
    holds_elim (x21 ()) (d21 ());
    assert (unsw (x21 ()) (xA ()) == true);
    let T.Sweeping p = (x21 ()).ph in
    assert (GC.Spec.Top.PagesAlloc.punswept p (xA ()) == true);
    assert (ksw () == PWP.nsw p (x21 ()).w.cmaj (stx (x21 ())));
    let k = ksw () in
    assert (k == ksw ());
    if k = 0 then begin
      PWP.nsw_done p (x21 ()).w.cmaj (stx (x21 ()));
      SF.done_unswept p (x21 ()).w.cmaj (stx (x21 ())) (xA ());
      assert False
    end

/// ---------------------------------------------------------------------------
/// The run by index
/// ---------------------------------------------------------------------------

let es_is () : Lemma (es_inc () == es3 (pre21 ()) (ksw ()) (post ())) = ()

let pre7 () : GTot (list event) = [e0; e1; e2 (); e3; e4 (); e5 (); e6 ()]
let mid14 () : GTot (list event) =
  [EStart; e8 (); e9 (); e10 (); e11; EMinor; ESlice; ESlice; ESlice; EHandover; e10 (); e11; EMinor; e20 ()]

#push-options "--fuel 24"
let shape () : Lemma (pre21 () == L.append (pre7 ()) (mid14 ()) /\ L.length (pre7 ()) == 7 /\
                      L.length (mid14 ()) == 14 /\ L.length (pre21 ()) == 21 /\ L.length (post ()) == 3)
  = ()

let nse (e: event) : bool = not (EStart? e) && not (EEnd? e)

let mid_all () : Lemma (L.for_all nse (L.tl (mid14 ())) == true /\ mid14 () == EStart :: L.tl (mid14 ())) = ()
#pop-options

#push-options "--fuel 1"
let rec all_idx (l: list event) (i: nat)
  : Lemma (requires L.for_all nse l == true /\ i < L.length l) (ensures nse (L.index l i) == true) (decreases l)
  = match l with _ :: tl -> if i = 0 then () else all_idx tl (i - 1)

let mid_ev (i: nat) : Lemma (requires 0 < i /\ i < 14 /\ L.length (mid14 ()) == 14)
  (ensures ~(L.index (mid14 ()) i == EStart) /\ ~(L.index (mid14 ()) i == EEnd))
  = mid_all (); shape ();
    all_idx (L.tl (mid14 ())) (i - 1)
#pop-options

#push-options "--fuel 24"

let mid_known () : Lemma (L.index (mid14 ()) 0 == EStart /\ L.index (mid14 ()) 2 == e9 () /\
                          L.index (mid14 ()) 5 == EMinor /\ L.index (mid14 ()) 12 == EMinor /\
                          L.index (post ()) 0 == EEnd /\ L.index (post ()) 2 == EMinor)
  = ()
#pop-options

let ev_pre (i: nat) : Lemma (requires 7 <= i /\ i < 21 /\ L.length (mid14 ()) == 14)
  (ensures i < L.length (es_inc ()) /\ ev (es_inc ()) i == L.index (mid14 ()) (i - 7))
  = es_is (); shape ();
    ev_p (pre21 ()) (ksw ()) (post ()) i;
    RA.index_app_ge (pre7 ()) (mid14 ()) (i - 7)

let inc_mid (t: nat) : Lemma (requires 7 < t /\ t < 21 + ksw ())
  (ensures t < L.length (es_inc ()) /\ ~(ev (es_inc ()) t == EStart) /\ ~(ev (es_inc ()) t == EEnd))
  = es_is (); shape ();
    len3 (pre21 ()) (ksw ()) (post ());
    if t < 21 then (ev_pre t; mid_ev (t - 7))
    else ev_r (pre21 ()) (ksw ()) (post ()) (t - 21)

/// **Events 7 to 21 + k are a cycle.**
let inc_cycle () : Lemma (requires pw_room /\ cok) (ensures is_cycle (es_inc ()) 7 (21 + ksw ()))
  = es_is (); shape (); mid_known ();
    len3 (pre21 ()) (ksw ()) (post ());
    ev_pre 7;
    ev_q (pre21 ()) (ksw ()) (post ()) 0;
    FStar.Classical.forall_intro (FStar.Classical.move_requires inc_mid)

/// **Every kind of event occurs.**
#push-options "--fuel 30 --ifuel 2"
let every_flat () : Lemma (every_event (L.append (pre21 ()) (ESweep :: post ()))) = ()
#pop-options

let inc_every_event () : Lemma (requires pw_room /\ cok) (ensures every_event (es_inc ()))
  = ksw_pos ();
    every3 (pre21 ()) (ksw ()) (post ());
    every_flat ()

/// ---------------------------------------------------------------------------
/// The configurations by index
/// ---------------------------------------------------------------------------

let mid_a () : GTot (list event) = [EStart; e8 (); e9 (); e10 (); e11; EMinor; ESlice]
let mid_b () : GTot (list event) = [ESlice; ESlice; EHandover; e10 (); e11; EMinor; e20 ()]

#push-options "--fuel 16"
let mid_split () : Lemma (mid14 () == L.append (mid_a ()) (mid_b ()) /\ L.length (mid_a ()) == 7 /\ L.length (mid_b ()) == 7) = ()
#pop-options

#push-options "--fuel 9"
let idx7 () : Lemma (L.index (pre7 ()) 0 == e0 /\ L.index (pre7 ()) 1 == e1 /\ L.index (pre7 ()) 2 == e2 () /\
                     L.index (pre7 ()) 3 == e3 /\ L.index (pre7 ()) 4 == e4 () /\ L.index (pre7 ()) 5 == e5 () /\
                     L.index (pre7 ()) 6 == e6 () /\
                     L.index (mid_a ()) 0 == EStart /\ L.index (mid_a ()) 1 == e8 () /\ L.index (mid_a ()) 2 == e9 () /\
                     L.index (mid_a ()) 3 == e10 () /\ L.index (mid_a ()) 4 == e11 /\ L.index (mid_a ()) 5 == EMinor /\
                     L.index (mid_a ()) 6 == ESlice /\
                     L.index (mid_b ()) 0 == ESlice /\ L.index (mid_b ()) 1 == ESlice /\ L.index (mid_b ()) 2 == EHandover /\
                     L.index (mid_b ()) 3 == e10 () /\ L.index (mid_b ()) 4 == e11 /\ L.index (mid_b ()) 5 == EMinor /\
                     L.index (mid_b ()) 6 == e20 ())
  = ()
#pop-options

/// Event `i` of the prefix.
let pidx (i: nat) : Lemma (requires i < 21 /\ L.length (pre7 ()) == 7 /\ L.length (mid_a ()) == 7 /\ L.length (mid_b ()) == 7)
  (ensures i < L.length (pre21 ()) /\
           L.index (pre21 ()) i == (if i < 7 then L.index (pre7 ()) i
                                    else if i < 14 then L.index (mid_a ()) (i - 7)
                                    else L.index (mid_b ()) (i - 14)))
  = shape (); mid_split ();
    L.append_length (pre7 ()) (mid14 ());
    if i < 7 then RA.index_app_lt (pre7 ()) (mid14 ()) i
    else begin
      RA.index_app_ge (pre7 ()) (mid14 ()) (i - 7);
      if i < 14 then RA.index_app_lt (mid_a ()) (mid_b ()) (i - 7)
      else RA.index_app_ge (mid_a ()) (mid_b ()) (i - 14)
    end

let pre_idx () : Lemma (requires L.length (pre21 ()) == 21) (ensures L.index (pre21 ()) 0 == e0 /\ L.index (pre21 ()) 1 == e1 /\ L.index (pre21 ()) 2 == e2 () /\
                        L.index (pre21 ()) 3 == e3 /\ L.index (pre21 ()) 4 == e4 () /\ L.index (pre21 ()) 5 == e5 () /\
                        L.index (pre21 ()) 6 == e6 () /\ L.index (pre21 ()) 7 == EStart /\ L.index (pre21 ()) 8 == e8 () /\
                        L.index (pre21 ()) 9 == e9 () /\ L.index (pre21 ()) 10 == e10 () /\ L.index (pre21 ()) 11 == e11 /\
                        L.index (pre21 ()) 12 == EMinor /\ L.index (pre21 ()) 13 == ESlice /\ L.index (pre21 ()) 14 == ESlice /\
                        L.index (pre21 ()) 15 == ESlice /\ L.index (pre21 ()) 16 == EHandover /\
                        L.index (pre21 ()) 17 == e10 () /\ L.index (pre21 ()) 18 == e11 /\
                        L.index (pre21 ()) 19 == EMinor /\ L.index (pre21 ()) 20 == e20 ())
  = idx7 (); shape (); mid_split ();
    pidx 0; pidx 1; pidx 2; pidx 3; pidx 4; pidx 5; pidx 6; pidx 7; pidx 8; pidx 9; pidx 10;
    pidx 11; pidx 12; pidx 13; pidx 14; pidx 15; pidx 16; pidx 17; pidx 18; pidx 19; pidx 20

let atn (i: nat) : GTot (config pc) = at pc W.msize W.ywords (es_inc ()) i

let ev21 (i: nat) : Lemma (requires i < 21 /\ L.length (pre21 ()) == 21) (ensures i < L.length (es_inc ()) /\ ev (es_inc ()) i == L.index (pre21 ()) i)
  = es_is (); shape (); ev_p (pre21 ()) (ksw ()) (post ()) i

let succ (i: nat) : Lemma (requires i < 21 /\ L.length (pre21 ()) == 21) (ensures atn (i + 1) == step pc (atn i) (L.index (pre21 ()) i))
  = ev21 i;
    GC.Spec.Top.RunFacts.at_succ pc W.msize W.ywords (es_inc ()) i

let at_chain () : Lemma (atn 7 == x7 () /\ atn 8 == x8 () /\ atn 9 == x9 () /\ atn 10 == x10 () /\
                         atn 11 == x11 () /\ atn 12 == x12 () /\ atn 13 == x13 () /\ atn 17 == x17 () /\
                         atn 18 == x18 () /\ atn 19 == x19 () /\ atn 20 == x20 () /\ atn 21 == x21 ())
  = shape (); pre_idx ();
    GC.Spec.Top.RunFacts.at_zero pc W.msize W.ywords (es_inc ());
    succ 0; succ 1; succ 2; succ 3; succ 4; succ 5; succ 6; succ 7; succ 8; succ 9; succ 10;
    succ 11; succ 12; succ 13; succ 14; succ 15; succ 16; succ 17; succ 18; succ 19; succ 20

#push-options "--fuel 4"
let post_take () : Lemma (take 1 (post ()) == [EEnd] /\ take 2 (post ()) == [EEnd; e23 ()]) = ()
#pop-options

let at_post () : Lemma (requires pw_room /\ cok)
  (ensures atn (22 + ksw ()) == x23 () /\ atn (23 + ksw ()) == x24 ())
  = pre_ok (); shape (); post_take ();
    SF.exec_nil (x23 ()); SF.exec_nil (x24 ());
    SF.exec_cons (x22 ()) EEnd [];
    SF.exec_cons (x23 ()) (e23 ()) [];
    SF.exec_cons (x22 ()) EEnd [e23 ()];
    at_q pc W.msize W.ywords (pre21 ()) (ksw ()) (post ()) 1;
    at_q pc W.msize W.ywords (pre21 ()) (ksw ()) (post ()) 2

/// ---------------------------------------------------------------------------
/// What the run shows
/// ---------------------------------------------------------------------------

/// **The barrier darkens**: at 9, while marking, A.0 (B, white) is
/// overwritten; B is grey after it.
let inc_darkens () : Lemma (requires pw_room /\ cok)
  (ensures 9 < L.length (es_inc ()) /\ ev (es_inc ()) 9 == EWrite (M.Major (xA ())) 0 i1 /\
           T.Marking? (atn 9).ph /\ M.field (mx (atn 9)) (xA ()) 0 == vB () /\
           M.col_of (mx (atn 9)) (xB ()) == M.White /\ M.col_of (mx (atn 10)) (xB ()) == M.Grey)
  = at_chain (); shape (); pre_idx (); ev21 9;
    c9 (); c10 (); distinct (); distD ();
    holds_elim (x9 ()) (d9 ()); holds_elim (x10 ()) (d10 ());
    db_dx DM M.Grey M.White M.White true (vB ()) (exD M.Black (vB ())) [vD (); vA ()] 5 ms0 (M.empty_heap W.ywords) (xA ());
    db_dx DM M.Grey M.White M.White true (vB ()) (exD M.Black (vB ())) [vD (); vA ()] 5 ms0 (M.empty_heap W.ywords) (xB ());
    db_dx DM M.Grey M.Grey M.White true i1 (exD M.Black (vB ())) [vD (); vA ()] 5 ms0 (M.empty_heap W.ywords) (xB ());
    blk (x9 ()) (d9 ()) (xA ()); blk (x9 ()) (d9 ()) (xB ()); blk (x10 ()) (d10 ()) (xB ());
    l2 (vB ()) i1

/// **The minor collections inside the cycle promote**, at 12 while marking
/// and at 19 while sweeping: Y1 (an infix pointer into K) and Y2 (an
/// integer that reads as an infix header); the last one runs idle.
let inc_promotes () : Lemma (requires pw_room /\ cok)
  (ensures 23 + ksw () < L.length (es_inc ()) /\
           ev (es_inc ()) 12 == EMinor /\ T.Marking? (atn 12).ph /\
           T.Done? (PWM.mres (atn 12)) /\ Some? (PWM.mfwd (atn 12) 0) /\ Some? (PWM.mfwd (atn 12) 2) /\
           ev (es_inc ()) 19 == EMinor /\ T.Sweeping? (atn 19).ph /\
           T.Done? (PWM.mres (atn 19)) /\ Some? (PWM.mfwd (atn 19) 0) /\ Some? (PWM.mfwd (atn 19) 2) /\
           M.field (PWMu.ym2 (vK2 ()) iw) 0 0 == vK2 () /\ M.field (PWMu.ym2 (vK2 ()) iw) 2 0 == iw /\
           Some? (M.infix_hdr iw) /\
           (atn 12).w.cyng == PWMu.ms2 (vK2 ()) iw /\ (atn 19).w.cyng == PWMu.ms2 (vK2 ()) iw /\
           ev (es_inc ()) (23 + ksw ()) == EMinor /\ T.Idle? (atn (23 + ksw ())).ph)
  = at_chain (); at_post (); shape (); pre_idx (); ev21 12; ev21 19;
    es_is (); shape (); mid_known ();
    len3 (pre21 ()) (ksw ()) (post ());
    ev_q (pre21 ()) (ksw ()) (post ()) 2;
    c12 (); c13 (); c19 (); c20 (); c24 (); nice12 ();
    holds_elim (x12 ()) (d12 ()); holds_elim (x19 ()) (d19 ()); holds_elim (x24 ()) (d24 ());
    st_vals ();
    assert_norm (M.infix_hdr (M.VInt 2297) == Some 2)

let sweeping_17_20 () : Lemma (requires pw_room /\ cok)
  (ensures T.Sweeping? (atn 17).ph /\ T.Sweeping? (atn 20).ph)
  = at_chain (); c17 (); c20 ();
    holds_elim (x17 ()) (dS ()); holds_elim (x20 ()) (d20 ())

let marking_8_10 () : Lemma (requires pw_room /\ cok)
  (ensures T.Marking? (atn 8).ph /\ T.Marking? (atn 9).ph /\ T.Marking? (atn 10).ph)
  = at_chain (); c8 (); c9 (); c10 ();
    holds_elim (x8 ()) (d8 ()); holds_elim (x9 ()) (d9 ()); holds_elim (x10 ()) (d10 ())

/// **The program runs inside the cycle**: an allocation, a write and young
/// allocations while marking (8-10), young allocations and a root change
/// while sweeping (17, 20).
let inc_interleaves () : Lemma (requires pw_room /\ cok)
  (ensures 20 < L.length (es_inc ()) /\
           EAlloc? (ev (es_inc ()) 8) /\ T.Marking? (atn 8).ph /\
           EWrite? (ev (es_inc ()) 9) /\ T.Marking? (atn 9).ph /\
           EYoungAlloc? (ev (es_inc ()) 10) /\ T.Marking? (atn 10).ph /\
           EYoungAlloc? (ev (es_inc ()) 17) /\ T.Sweeping? (atn 17).ph /\
           ERoots? (ev (es_inc ()) 20) /\ T.Sweeping? (atn 20).ph)
  = shape (); pre_idx (); ev21 8; ev21 9; ev21 10; ev21 17; ev21 20;
    sweeping_17_20 (); marking_8_10 ()

/// **The cycle frees C**, which was in use and unreachable at its start.
let inc_freed () : Lemma (requires pw_room /\ cok)
  (ensures atn 7 == x7 () /\ iu (x7 ()) (xC ()) == true /\ iu (atn (22 + ksw ())) (xC ()) == false)
  = at_chain (); at_post (); c23 (); distinct ();
    GC.Spec.Top.PWCyc.start7 ();
    not_iu (x23 ()) (d23 ()) (xC ())
