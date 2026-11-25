/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PWNamesS - the pages sequential run names only what it reaches
/// ---------------------------------------------------------------------------
///
/// Design doc §17.  Every program event of `PWSeq.es_seq` names only blocks
/// reached from the roots, or young roots (`seq_named`).

module GC.Spec.Top.PWNamesS

open GC.Spec.Top.Run
open GC.Spec.Top.PWDesc
open GC.Spec.Top.PWRun
open GC.Spec.Top.PWPre
open GC.Spec.Top.PWCyc
open GC.Spec.Top.PWSeq
open GC.Spec.Top.PWSeqF
open GC.Spec.Top.PWList
open GC.Spec.Top.TrNames
open GC.Spec.Top.PWNames
module M = GC.Spec.Top.Heap
module L = FStar.List.Tot
module RA = GC.Spec.Top.RunApp
module RF = GC.Spec.Top.RunFacts
module PWMu = GC.Spec.Top.PWMut
module W = GC.Spec.Top.Word

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let atn (i: nat) : GTot (config pc) = at pc W.msize W.ywords (es_seq ()) i

/// ---------------------------------------------------------------------------
/// After the cycle: a read, two young blocks, the roots
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let names_16 () : Lemma (requires pw_room /\ cok) (ensures enamed (wv (x16 ())) (e16 ()))
  = c16 (); distinct ();
    let x = x16 () in
    let d = ddv DI M.White M.White M.White false [vA ()] 8 in
    holds_elim x d;
    db_dd DI M.White M.White M.White false [vA ()] 8 ms0 (M.empty_heap W.ywords) (xA ());
    blk x d (xA ());
    mem_hd (vA ()) [];
    rooted_r x d (xA ());
    enamed_wd x d (e16 ())

let names_17 () : Lemma (requires pw_room /\ cok) (ensures enamed (wv (x17 ())) (e17 ()))
  = c17 (); distinct ();
    let x = x17 () in
    let d = d17 () in
    holds_elim x d;
    db_dd DI M.White M.White M.White false [vB (); vA ()] 8 ms0 (M.empty_heap W.ywords) (xB ());
    db_dd DI M.White M.White M.White false [vB (); vA ()] 8 ms0 (M.empty_heap W.ywords) (xK ());
    blk x d (xB ()); blk x d (xK ());
    st_vals (); l1 (vK2 ()); l3 i1 iw i1;
    mem_hd (vB ()) [vA ()];
    rooted_r x d (xB ());
    res_infix (mx x) (xK ());
    rooted_f x d (xB ()) 0 (xK () + 2) (xK ());
    en_l1 (wd x d) (vK2 ());
    enamed_wd x d (e17 ())

let names_18 () : Lemma (requires pw_room /\ cok) (ensures enamed (wv (x18 ())) e18)
  = c18 (); st_vals ();
    en_l1 (wd (x18 ()) (d18 ())) iw;
    enamed_wd (x18 ()) (d18 ()) e18

let names_19 () : Lemma (requires pw_room /\ cok) (ensures enamed (wv (x19 ())) (e19 ()))
  = c19 (); nice_y (); distinct ();
    let x = x19 () in
    let d = d19 () in
    holds_elim x d;
    GC.Spec.Top.PWMinor.ym2_ok (xK ()) (vK2 ()) iw;
    db_dd DI M.White M.White M.White false [vY2; vY1; vB (); vA ()] 8 (PWMu.ms2 (vK2 ()) iw) (PWMu.ym2 (vK2 ()) iw) (xA ());
    blk x d (xA ());
    mem_hd (vA ()) [];
    mem_tl (vB ()) (vA ()) [vA ()];
    mem_tl vY1 (vA ()) [vB (); vA ()];
    mem_tl vY2 (vA ()) [vY1; vB (); vA ()];
    mem_hd vY2 [vY1; vB (); vA ()];
    mem_hd vY1 [vB (); vA ()];
    mem_tl vY2 vY1 [vY1; vB (); vA ()];
    rooted_r x d (xA ());
    res_iu x (xA ());
    vn_young (wd x d) 0; vn_young (wd x d) 2;
    en_l3 (wd x d) (vA ()) vY1 vY2;
    enamed_wd x d (e19 ())
#pop-options

/// ---------------------------------------------------------------------------
/// Every program event
/// ---------------------------------------------------------------------------

#push-options "--fuel 9"
let idx7 () : Lemma (L.index (pre7 ()) 0 == e0 /\ L.index (pre7 ()) 1 == e1 /\ L.index (pre7 ()) 2 == e2 () /\
                     L.index (pre7 ()) 3 == e3 /\ L.index (pre7 ()) 4 == e4 () /\ L.index (pre7 ()) 5 == e5 () /\
                     L.index (pre7 ()) 6 == e6 ())
  = ()
#pop-options

let ev7 (i: nat) : Lemma (requires i < 7 /\ L.length (pre7 ()) == 7)
  (ensures i < L.length (es_seq ()) /\ ev (es_seq ()) i == L.index (pre7 ()) i)
  = es_is (); len_pre (); pre_split ();
    ev_pre i;
    RA.index_app_lt (pre7 ()) midl i

let succ (i: nat) : Lemma (requires i < 7 /\ L.length (pre7 ()) == 7)
  (ensures atn (i + 1) == step pc (atn i) (L.index (pre7 ()) i))
  = ev7 i;
    RF.at_succ pc W.msize W.ywords (es_seq ()) i

let at_0_6 () : Lemma (atn 0 == x0 () /\ atn 1 == x1 () /\ atn 2 == x2 () /\ atn 3 == x3 () /\
                       atn 4 == x4 () /\ atn 5 == x5 () /\ atn 6 == x6 ())
  = idx7 (); pre_split ();
    RF.at_zero pc W.msize W.ywords (es_seq ());
    succ 0; succ 1; succ 2; succ 3; succ 4; succ 5

#push-options "--fuel 8"
let post_idx () : Lemma (L.index (post ()) 1 == e16 () /\ L.index (post ()) 2 == e17 () /\
                         L.index (post ()) 3 == e18 /\ L.index (post ()) 4 == e19 () /\
                         take 2 (post ()) == [EEnd; e16 ()] /\ take 3 (post ()) == [EEnd; e16 (); e17 ()] /\
                         take 4 (post ()) == [EEnd; e16 (); e17 (); e18])
  = ()
#pop-options

let at_post2 () : Lemma (requires pw_room /\ cok)
  (ensures atn (15 + ksw ()) == x16 () /\ atn (16 + ksw ()) == x17 () /\ atn (17 + ksw ()) == x18 () /\
           atn (18 + ksw ()) == x19 ())
  = at_post (); pre_ok (); len_pre (); post_idx ();
    exec_nil (x17 ()); exec_nil (x18 ()); exec_nil (x19 ());
    exec_cons (x15 ()) EEnd [e16 ()]; exec_cons (x16 ()) (e16 ()) [];
    exec_cons (x15 ()) EEnd [e16 (); e17 ()]; exec_cons (x16 ()) (e16 ()) [e17 ()]; exec_cons (x17 ()) (e17 ()) [];
    exec_cons (x15 ()) EEnd [e16 (); e17 (); e18]; exec_cons (x16 ()) (e16 ()) [e17 (); e18];
    exec_cons (x17 ()) (e17 ()) [e18]; exec_cons (x18 ()) e18 [];
    at_q pc W.msize W.ywords (pre14 ()) (ksw ()) (post ()) 2;
    at_q pc W.msize W.ywords (pre14 ()) (ksw ()) (post ()) 3;
    at_q pc W.msize W.ywords (pre14 ()) (ksw ()) (post ()) 4

#push-options "--fuel 8"
let pre_mid' (j: nat) : Lemma (requires j < 7) (ensures j < L.length midl /\ not (is_mutator_event (L.index midl j)))
  = ()
#pop-options

let cases7 (i: nat) : Lemma (requires i < 7) (ensures i == 0 \/ i == 1 \/ i == 2 \/ i == 3 \/ i == 4 \/ i == 5 \/ i == 6)
  = ()

let named_pre (i: nat) : Lemma (requires pw_room /\ cok /\ i < 7)
  (ensures i < L.length (es_seq ()) /\ enamed (wv (atn i)) (ev (es_seq ()) i))
  = cases7 i;
    pre_split ();
    ev7 i; idx7 (); at_0_6 (); names_pre ()

let cases4 (j: nat) : Lemma (requires 0 < j /\ j < 5) (ensures j == 1 \/ j == 2 \/ j == 3 \/ j == 4) = ()

let named_post (j: nat) : Lemma (requires pw_room /\ cok /\ 0 < j /\ j < 5)
  (ensures 14 + ksw () + j < L.length (es_seq ()) /\ enamed (wv (atn (14 + ksw () + j))) (ev (es_seq ()) (14 + ksw () + j)))
  = cases4 j;
    es_is (); len_pre ();
    ev_q (pre14 ()) (ksw ()) (post ()) j;
    post_idx (); at_post2 ();
    names_16 (); names_17 (); names_18 (); names_19 ()

let cases6 (j: nat) : Lemma (requires j < 6) (ensures j == 0 \/ j == 1 \/ j == 2 \/ j == 3 \/ j == 4 \/ j == 5) = ()

/// The suffix: the end, the read, two young blocks, the roots, the collection.
let named_tail (i: nat) : Lemma (requires pw_room /\ cok /\ 14 + ksw () <= i /\ i < L.length (es_seq ()) /\
                                          is_mutator_event (ev (es_seq ()) i))
  (ensures enamed (wv (atn i)) (ev (es_seq ()) i))
  = es_is (); len_pre ();
    len3 (pre14 ()) (ksw ()) (post ());
    let j : nat = i - 14 - ksw () in
    assert (j < 6);
    cases6 j;
    ev_q (pre14 ()) (ksw ()) (post ()) j;
    pre_events ();
    if j = 0 || j = 5 then ()
    else named_post j

/// One index of the run.
#push-options "--z3rlimit 40"
let named_at (i: nat) : Lemma (requires pw_room /\ cok /\ i < L.length (es_seq ()) /\ is_mutator_event (ev (es_seq ()) i))
  (ensures enamed (wv (atn i)) (ev (es_seq ()) i))
  = es_is (); len_pre (); pre_split ();
    len3 (pre14 ()) (ksw ()) (post ());
    if i < 7 then named_pre i
    else if i < 14 then begin
      ev_pre i;
      RA.index_app_ge (pre7 ()) midl (i - 7);
      pre_mid' (i - 7)
    end
    else if i < 14 + ksw () then ev_r (pre14 ()) (ksw ()) (post ()) (i - 14)
    else named_tail i
#pop-options

/// **Every program event of the sequential run names only what it reaches.**
let seq_named () : Lemma (requires pw_room /\ cok)
  (ensures forall (i: nat). i < L.length (es_seq ()) /\ is_mutator_event (ev (es_seq ()) i) ==>
                            enamed (wv (atn i)) (ev (es_seq ()) i))
  = let f (i: nat) : Lemma (i < L.length (es_seq ()) /\ is_mutator_event (ev (es_seq ()) i) ==>
                            enamed (wv (atn i)) (ev (es_seq ()) i))
      = if i < L.length (es_seq ()) then
          (if is_mutator_event (ev (es_seq ()) i) then named_at i) in
    FStar.Classical.forall_intro f
