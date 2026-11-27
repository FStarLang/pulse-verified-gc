/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PWNamesI - the pages incremental run names only what it reaches
/// ---------------------------------------------------------------------------
///
/// Design doc §17.  Every program event of `PWIncB.es_inc` names only blocks
/// reached from the roots, or young roots (`inc_named`).

module GC.Spec.Top.PWNamesI

open GC.Spec.Top.Run
open GC.Spec.Top.PWDesc
open GC.Spec.Top.PWRun
open GC.Spec.Top.PWPre
open GC.Spec.Top.PWIncA
open GC.Spec.Top.PWInc
open GC.Spec.Top.PWIncB
open GC.Spec.Top.PWIncF
open GC.Spec.Top.PWList
open GC.Spec.Top.TrNames
open GC.Spec.Top.PWNames
module M = GC.Spec.Top.Heap
module L = FStar.List.Tot
module RA = GC.Spec.Top.RunApp
module PWMu = GC.Spec.Top.PWMut
module W = GC.Spec.Top.Word

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// K, from D through B; D a root.
#push-options "--z3rlimit 40"
let rooted_K (x: config pc) (dk: phk) (cA cB cK: M.colour) (a0: M.value) (ex: exb) (rs: list M.value) (j: nat)
             (ys: GC.Gen.MinorHeap.minor_state) (ym: M.mheap)
  : Lemma (requires pw_room /\ cok /\ holds x (dx dk cA cB cK true a0 ex rs j ys ym) /\ L.memP (vD ()) rs /\
                    ex (xD ()) == Some (bD M.Black (vB ())))
          (ensures rooted (wd x (dx dk cA cB cK true a0 ex rs j ys ym)) (xK ()) /\
                   M.resolve (mx x) (xK () + 2) == Some (xK ()) /\
                   rooted (wd x (dx dk cA cB cK true a0 ex rs j ys ym)) (xD ()))
  = let d = dx dk cA cB cK true a0 ex rs j ys ym in
    l1 (vB ());
    reachK x dk cA cB cK a0 ex rs j ys ym;
    distinct (); distD ();
    holds_elim x d;
    db_ex dk cA cB cK true a0 ex rs j ys ym (xD ());
    db_dx dk cA cB cK true a0 ex rs j ys ym (xB ());
    db_dx dk cA cB cK true a0 ex rs j ys ym (xK ());
    blk x d (xD ()); blk x d (xB ()); blk x d (xK ());
    st_vals (); l1 (vK2 ()); l3 i1 iw i1;
    rooted_r x d (xD ());
    res_iu x (xB ());
    rooted_f x d (xD ()) 0 (xB ()) (xB ());
    res_infix (mx x) (xK ());
    rooted_f x d (xB ()) 0 (xK () + 2) (xK ())
#pop-options

let names_8 () : Lemma (requires pw_room /\ cok) (ensures enamed (wv (x8 ())) (e8 ()))
  = c8 (); distinct ();
    let x = x8 () in
    let d = d8 () in
    holds_elim x d;
    db_dx DM M.Grey M.White M.White true (vB ()) noex [vA ()] 4 ms0 (M.empty_heap W.ywords) (xA ());
    db_dx DM M.Grey M.White M.White true (vB ()) noex [vA ()] 4 ms0 (M.empty_heap W.ywords) (xB ());
    blk x d (xA ()); blk x d (xB ());
    l2 (vB ()) i1;
    mem_hd (vA ()) [];
    rooted_r x d (xA ());
    res_iu x (xB ());
    rooted_f x d (xA ()) 0 (xB ()) (xB ());
    en_l1 (wd x d) (vB ());
    enamed_wd x d (e8 ())

let names_9 () : Lemma (requires pw_room /\ cok) (ensures enamed (wv (x9 ())) (e9 ()))
  = c9 (); distinct ();
    let x = x9 () in
    let d = d9 () in
    holds_elim x d;
    db_dx DM M.Grey M.White M.White true (vB ()) (exD M.Black (vB ())) [vD (); vA ()] 5 ms0 (M.empty_heap W.ywords) (xA ());
    blk x d (xA ());
    mem_hd (vA ()) []; mem_tl (vD ()) (vA ()) [vA ()];
    rooted_r x d (xA ());
    enamed_wd x d (e9 ())

let names_10 () : Lemma (requires pw_room /\ cok) (ensures enamed (wv (x10 ())) (e10 ()))
  = c10 ();
    let x = x10 () in
    let d = d10 () in
    mem_hd (vD ()) [vA ()];
    rooted_K x DM M.Grey M.Grey M.White i1 (ex9 ()) [vD (); vA ()] 5 ms0 (M.empty_heap W.ywords);
    en_l1 (wd x d) (vK2 ());
    enamed_wd x d (e10 ())

let names_17 () : Lemma (requires pw_room /\ cok) (ensures enamed (wv (x17 ())) (e10 ()))
  = c17 (); mem_D13 (); ex13_D ();
    let x = x17 () in
    let d = dS () in
    rooted_K x DS M.Black M.Black M.Black i1 (ex13 ()) (rs13 ()) 7 ms0 (M.empty_heap W.ywords);
    en_l1 (wd x d) (vK2 ());
    enamed_wd x d (e10 ())

let names_11 () : Lemma (requires pw_room /\ cok) (ensures enamed (wv (x11 ())) e11 /\ enamed (wv (x18 ())) e11)
  = c11 (); c18 (); st_vals ();
    en_l1 (wd (x11 ()) (d11 ())) iw; enamed_wd (x11 ()) (d11 ()) e11;
    en_l1 (wd (x18 ()) (d18 ())) iw; enamed_wd (x18 ()) (d18 ()) e11

let names_20 () : Lemma (requires pw_room /\ cok) (ensures enamed (wv (x20 ())) (e20 ()))
  = c20 (); mem_20 (); ex20_D (); distinct ();
    let x = x20 () in
    let d = d20 () in
    rooted_K x DS M.Black M.Black M.Black i1 (ex20 ()) (rs20 ()) 9 ms0 (M.empty_heap W.ywords);
    holds_elim x d;
    db_dx DS M.Black M.Black M.Black true i1 (ex20 ()) (rs20 ()) 9 ms0 (M.empty_heap W.ywords) (xA ());
    blk x d (xA ());
    rooted_r x d (xA ());
    res_iu x (xA ());
    holds_elim x d;
    distD ();
    db_ex DS M.Black M.Black M.Black true i1 (ex20 ()) (rs20 ()) 9 ms0 (M.empty_heap W.ywords) (xD ());
    blk x d (xD ());
    res_iu x (xD ());
    en_l2 (wd x d) (vA ()) (vD ());
    enamed_wd x d (e20 ())

let en_read (w: M.world) (o i: nat) : Lemma (requires rooted w o) (ensures enamed w (ERead (M.Major o) i)) = ()

let names_23 () : Lemma (requires pw_room /\ cok) (ensures enamed (wv (x23 ())) (e23 ()))
  = c23 (); ex20_D (); distinct (); distD ();
    let x = x23 () in
    let d = d23 () in
    holds_elim x d;
    db_ex DI M.White M.White M.White false i1 (exw (ex20 ())) [vA (); vD ()] 9 ms0 (M.empty_heap W.ywords) (xD ());
    blk x d (xD ());
    mem_hd (vD ()) []; mem_tl (vA ()) (vD ()) [vD ()];
    assert (d.drt == [vA (); vD ()]);
    rooted_r x d (xD ());
    en_read (wd x d) (xD ()) 0;
    enamed_wd x d (e23 ())

/// ---------------------------------------------------------------------------
/// Every program event
/// ---------------------------------------------------------------------------

let at_0_6 () : Lemma (atn 0 == x0 () /\ atn 1 == x1 () /\ atn 2 == x2 () /\ atn 3 == x3 () /\
                       atn 4 == x4 () /\ atn 5 == x5 () /\ atn 6 == x6 ())
  = shape (); pre_idx ();
    GC.Spec.Top.RunFacts.at_zero pc W.msize W.ywords (es_inc ());
    succ 0; succ 1; succ 2; succ 3; succ 4; succ 5

let cases7 (i: nat) : Lemma (requires i < 7) (ensures i == 0 \/ i == 1 \/ i == 2 \/ i == 3 \/ i == 4 \/ i == 5 \/ i == 6)
  = ()

let cases14 (i: nat) : Lemma (requires 7 <= i /\ i < 21)
  (ensures i == 7 \/ i == 8 \/ i == 9 \/ i == 10 \/ i == 11 \/ i == 12 \/ i == 13 \/ i == 14 \/ i == 15 \/
           i == 16 \/ i == 17 \/ i == 18 \/ i == 19 \/ i == 20)
  = ()

let named_pre (i: nat) : Lemma (requires pw_room /\ cok /\ i < 7)
  (ensures i < L.length (es_inc ()) /\ enamed (wv (atn i)) (ev (es_inc ()) i))
  = cases7 i;
    shape (); pre_idx (); ev21 i; at_0_6 ();
    names_pre ()

let named_mid (i: nat) : Lemma (requires pw_room /\ cok /\ 7 <= i /\ i < 21 /\ i < L.length (es_inc ()) /\
                                         is_mutator_event (ev (es_inc ()) i))
  (ensures enamed (wv (atn i)) (ev (es_inc ()) i))
  = cases14 i;
    shape (); pre_idx (); ev21 i; at_chain ();
    names_8 (); names_9 (); names_10 (); names_11 (); names_17 (); names_20 ()

let cases3 (j: nat) : Lemma (requires j < 3) (ensures j == 0 \/ j == 1 \/ j == 2) = ()

#push-options "--fuel 4"
let post_idx' () : Lemma (L.index (post ()) 0 == EEnd /\ L.index (post ()) 1 == e23 () /\ L.index (post ()) 2 == EMinor) = ()
#pop-options

let named_post (j: nat) : Lemma (requires pw_room /\ cok /\ j < 3 /\ 21 + ksw () + j < L.length (es_inc ()) /\
                                          is_mutator_event (ev (es_inc ()) (21 + ksw () + j)))
  (ensures enamed (wv (atn (21 + ksw () + j))) (ev (es_inc ()) (21 + ksw () + j)))
  = cases3 j;
    es_is (); shape (); mid_known ();
    ev_q (pre21 ()) (ksw ()) (post ()) j;
    at_post ();
    post_idx' ();
    names_23 ();
    assert (21 + ksw () + 1 == 22 + ksw ())

let post_at (i k j: nat) : Lemma (requires i >= 21 + k /\ j == i - 21 - k) (ensures 21 + k + j == i) = ()

let named_at (i: nat) : Lemma (requires pw_room /\ cok /\ i < L.length (es_inc ()) /\ is_mutator_event (ev (es_inc ()) i))
  (ensures enamed (wv (atn i)) (ev (es_inc ()) i))
  = es_is (); shape ();
    len3 (pre21 ()) (ksw ()) (post ());
    if i < 7 then named_pre i
    else if i < 21 then named_mid i
    else if i < 21 + ksw () then ev_r (pre21 ()) (ksw ()) (post ()) (i - 21)
    else begin
      let j : nat = i - 21 - ksw () in
      post_at i (ksw ()) j;
      named_post j
    end

/// **Every program event of the incremental run names only what it reaches.**
let inc_named () : Lemma (requires pw_room /\ cok)
  (ensures forall (i: nat). i < L.length (es_inc ()) /\ is_mutator_event (ev (es_inc ()) i) ==>
                            enamed (wv (atn i)) (ev (es_inc ()) i))
  = let f (i: nat) : Lemma (i < L.length (es_inc ()) /\ is_mutator_event (ev (es_inc ()) i) ==>
                            enamed (wv (atn i)) (ev (es_inc ()) i))
      = if i < L.length (es_inc ()) then
          (if is_mutator_event (ev (es_inc ()) i) then named_at i) in
    FStar.Classical.forall_intro f
