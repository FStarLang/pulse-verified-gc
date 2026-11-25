/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PWInc - the pages collector's incremental witness run
/// ---------------------------------------------------------------------------
///
/// Design doc §17.  A run of the pages collector (`PagesComps.pc`), in the
/// incremental style, from the page allocator's initial heap, under
/// `PWPre.pw_room`:
///   0-6   as the sequential run (GC.Spec.Top.PWPre): A = [B; 1], B = [K + 2],
///         C = [B], K a closure, roots [A];
///   7     the cycle starts: A grey;
///   8     while marking: D allocated (black), D.0 = B;
///   9     while marking: A.0 := 1, the barrier darkens B (white to grey);
///   10-11 while marking: Y1 (holding K + 2) and Y2 (holding an integer that
///         reads as an infix header) allocated young;
///   12    a minor collection while marking: Y1 and Y2 promoted through the
///         page allocator (black copies), the roots rewritten;
///   13-15 three slices (A, B, K, in an order the mark chooses);
///   16    the hand-over;
///   17-18 while sweeping: Y3, Y4 allocated young, as Y1, Y2;
///   19    a minor collection while sweeping: promoted again;
///   20    the roots become [A; D];
///   21-   the sweep's steps; C freed;
///   then  the end; a read of D.0 into a root; a minor collection while idle.
/// Every event is allowed (`inc_run`), with every hypothesis of
/// `gc_correct`, T1 and T2 (GC.Spec.Top.PWHyps).

module GC.Spec.Top.PWInc

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Top.Word
open GC.Spec.Top.ByteRep
open GC.Spec.Top.PagesAlloc
open GC.Spec.Top.Run
open GC.Spec.Top.PWDesc
open GC.Spec.Top.PWRun
open GC.Spec.Top.PWPre
open GC.Spec.Top.PWIncA
module M = GC.Spec.Top.Heap
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module RA = GC.Spec.Top.RunApp
module TR = GC.Spec.Top.Transp
module PWK = GC.Spec.Top.PWMark
module PWM = GC.Spec.Top.PWMinor
module PWMu = GC.Spec.Top.PWMut
module PWA = GC.Spec.Top.PWAlloc
module PWS = GC.Spec.Top.PWSweep
module PWC = GC.Spec.Top.PWCyc
module FWS = GC.Spec.Top.FFWStep
module PWF = GC.Spec.Top.PWFold

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let ic = Incremental
let ok (x: config pc) (e: event) : prop = RA.conds pc ic x e /\ TR.alloc_succeeds x e

let noex : exb = fun _ -> None

/// ---------------------------------------------------------------------------
/// 7-12: marking
/// ---------------------------------------------------------------------------

let x8 () : GTot (config pc) = step pc (x7 ()) EStart

let d8 () : GTot dsc = dx DM M.Grey M.White M.White true (vB ()) noex [vA ()] 4 ms0 (M.empty_heap ywords)

let c8 () : Lemma (requires pw_room /\ cok) (ensures holds (x8 ()) (d8 ()) /\ ok (x7 ()) EStart)
  = PWC.s8 ic;
    distinct ();
    holds_ext (x8 ()) (PWC.d8c ()) (d8 ())

let e8 () : GTot event = EAlloc 1 0 [vB ()]
let xD () : GTot nat = PWA.aaddr (x8 ()) 1 0
let vD () : GTot M.value = M.VPtr (M.Major (xD ()))
let x9 () : GTot (config pc) = step pc (x8 ()) (e8 ())

let bD (c: M.colour) (v: M.value) : bd = { bw = 1; bt = 0; bc = c; blv = true; bf = [v] }
let exD (c: M.colour) (v: M.value) : exb = fun (y: nat) -> if y = xD () then Some (bD c v) else None

let d9 () : GTot dsc = dx DM M.Grey M.White M.White true (vB ()) (exD M.Black (vB ())) [vD (); vA ()] 5 ms0 (M.empty_heap ywords)

#push-options "--z3rlimit 40"
let c9a () : Lemma (requires pw_room /\ cok)
  (ensures holds (x9 ()) (PWA.dalloc (x8 ()) (d8 ()) 1 0 [vB ()]) /\ ok (x8 ()) (e8 ()) /\
           iu (x8 ()) (xD ()) == false)
  = c8 ();
    GC.Spec.Top.PWFold.smax ();
    distinct ();
    let x = x8 () in
    let d = d8 () in
    holds_elim x d;
    db_dx DM M.Grey M.White M.White true (vB ()) noex [vA ()] 4 ms0 (M.empty_heap ywords) (xA ());
    db_dx DM M.Grey M.White M.White true (vB ()) noex [vA ()] 4 ms0 (M.empty_heap ywords) (xB ());
    blk x d (xA ()); blk x d (xB ());
    l1 (vB ()); l2 (vB ()) i1; l1 (vA ());
    st_blk x (xB ());
    reach_r x d (xA ());
    reach_f x d (xA ()) 0 (xB ()) (xB ());
    sound_p x d (xB ()) (xB ());
    assert (PWA.apre x d 1 0 [vB ()]);
    assert (mutator_ok_w pc (wd x d) (e8 ()));
    GC.Spec.Top.PWPre.alloc_ev ic x d 1 0 [vB ()]
#pop-options

/// The blocks A, B, C, K are in use while marking.
let in_use8 () : Lemma (requires pw_room /\ cok)
  (ensures iu (x8 ()) (xA ()) /\ iu (x8 ()) (xB ()) /\ iu (x8 ()) (xC ()) /\ iu (x8 ()) (xK ()) /\ T.Marking? (x8 ()).ph)
  = c8 (); distinct ();
    let x = x8 () in
    let d = d8 () in
    holds_elim x d;
    holds_blk x d (xA ()); holds_blk x d (xB ()); holds_blk x d (xC ()); holds_blk x d (xK ())

let c9 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x9 ()) (d9 ()) /\ ok (x8 ()) (e8 ()))
  = c9a (); in_use8 (); distinct ();
    let d' = PWA.dalloc (x8 ()) (d8 ()) 1 0 [vB ()] in
    assert (xD () <> xA () /\ xD () <> xB () /\ xD () <> xC () /\ xD () <> xK ());
    assert (T.colour_at pk (x8 ()).ph (xD ()) == M.Black);
    let pt (y: nat) : Lemma ((d9 ()).db y == d'.db y) = () in
    FStar.Classical.forall_intro pt;
    holds_ext (x9 ()) d' (d9 ())

/// 9: A.0 := 1 while marking: the barrier darkens B.
let e9 () : GTot event = EWrite (M.Major (xA ())) 0 i1
let x10 () : GTot (config pc) = step pc (x9 ()) (e9 ())
let d10 () : GTot dsc = dx DM M.Grey M.Grey M.White true i1 (exD M.Black (vB ())) [vD (); vA ()] 5 ms0 (M.empty_heap ywords)

/// The old value's target is B, white.
let dt9 () : Lemma (requires pw_room /\ cok) (ensures PWMu.dt (x9 ()) (xA ()) 0 == Some (xB ()))
  = c9 (); distinct ();
    let x = x9 () in
    let d = d9 () in
    holds_elim x d;
    db_dx DM M.Grey M.White M.White true (vB ()) (exD M.Black (vB ())) [vD (); vA ()] 5 ms0 (M.empty_heap ywords) (xA ());
    db_dx DM M.Grey M.White M.White true (vB ()) (exD M.Black (vB ())) [vD (); vA ()] 5 ms0 (M.empty_heap ywords) (xB ());
    blk x d (xA ()); blk x d (xB ());
    l2 (vB ()) i1;
    res_iu x (xB ());
    assert (T.is_marking x.ph);
    assert (M.ptr_field (mx x) (xA ()) 0);
    assert (M.field (mx x) (xA ()) 0 == vB ());
    assert (T.old_target (mx x) (xA ()) 0 == Some (xB ()));
    assert (M.col_of (mx x) (xB ()) == M.White)

#push-options "--z3rlimit 40"
let c10a () : Lemma (requires pw_room /\ cok)
  (ensures holds (x10 ()) (PWMu.dwrite (x9 ()) (d9 ()) (xA ()) 0 i1) /\ ok (x9 ()) (e9 ()) /\
           PWMu.dt (x9 ()) (xA ()) 0 == Some (xB ()))
  = c9 (); dt9 (); distinct ();
    let x = x9 () in
    let d = d9 () in
    holds_elim x d;
    db_dx DM M.Grey M.White M.White true (vB ()) (exD M.Black (vB ())) [vD (); vA ()] 5 ms0 (M.empty_heap ywords) (xA ());
    db_dx DM M.Grey M.White M.White true (vB ()) (exD M.Black (vB ())) [vD (); vA ()] 5 ms0 (M.empty_heap ywords) (xB ());
    blk x d (xA ());
    st_vals (); l1 i1;
    mem_hd (vA ()) []; mem_tl (vD ()) (vA ()) [vA ()];
    reach_r x d (xA ());
    assert (PWMu.wpre x d (xA ()) 0 i1);
    mut_write x d (xA ()) 0 i1;
    write_ev ic x d (xA ()) 0 i1
#pop-options

let c10 () : Lemma (requires pw_room /\ cok) (ensures holds (x10 ()) (d10 ()) /\ ok (x9 ()) (e9 ()))
  = c10a (); in_use8 (); c9a (); distinct ();
    setv0 (vB ()) i1 i1;
    let d' = PWMu.dwrite (x9 ()) (d9 ()) (xA ()) 0 i1 in
    let pt (y: nat) : Lemma ((d10 ()).db y == d'.db y) = () in
    FStar.Classical.forall_intro pt;
    holds_ext (x10 ()) d' (d10 ())

/// ---------------------------------------------------------------------------
/// 10-12: two young blocks, and a minor collection while marking
/// ---------------------------------------------------------------------------

let vY1 : M.value = M.VPtr (M.Young 0)
let vY2 : M.value = M.VPtr (M.Young 2)

let e10 () : GTot event = EYoungAlloc 1 0 [vK2 ()]
let e11 : event = EYoungAlloc 1 0 [iw]
let x11 () : GTot (config pc) = step pc (x10 ()) (e10 ())
let x12 () : GTot (config pc) = step pc (x11 ()) e11
let x13 () : GTot (config pc) = step pc (x12 ()) EMinor

let ex9 () : GTot exb = exD M.Black (vB ())
let d11 () : GTot dsc = dx DM M.Grey M.Grey M.White true i1 (ex9 ()) [vY1; vD (); vA ()] 5 (PWMu.ms1 (vK2 ())) (PWMu.ym1 (vK2 ()))
let d12 () : GTot dsc = dx DM M.Grey M.Grey M.White true i1 (ex9 ()) [vY2; vY1; vD (); vA ()] 5
                           (PWMu.ms2 (vK2 ()) iw) (PWMu.ym2 (vK2 ()) iw)

/// D is none of A, B, C, K.
let distD () : Lemma (requires pw_room /\ cok)
  (ensures xD () <> xA () /\ xD () <> xB () /\ xD () <> xC () /\ xD () <> xK ())
  = c9a (); in_use8 ()

let ex9_ok () : Lemma (ex_ok (ex9 ()) /\ ex_ny (ex9 ()) /\ ex_ptr (ex9 ()) /\ ex_black (ex9 ()))
  = l1 (vB ())

/// K is reachable through D and B.
#push-options "--z3rlimit 40"
let reachK (x: config pc) (dk: phk) (cA cB cK: M.colour) (a0: M.value) (ex: exb) (rs: list M.value) (j: nat)
           (ys: GC.Gen.MinorHeap.minor_state) (ym: M.mheap)
  : Lemma (requires pw_room /\ cok /\ holds x (dx dk cA cB cK true a0 ex rs j ys ym) /\ L.memP (vD ()) rs /\
                    Some? (ex (xD ())) /\ (Some?.v (ex (xD ()))).blv == true /\
                    (Some?.v (ex (xD ()))).bt == 0 /\ (Some?.v (ex (xD ()))).bw == 1 /\
                    (Some?.v (ex (xD ()))).bf == [vB ()])
          (ensures M.reachable (wd x (dx dk cA cB cK true a0 ex rs j ys ym)) (xK ()) /\
                   M.resolve (mx x) (xK () + 2) == Some (xK ()) /\
                   M.reachable (wd x (dx dk cA cB cK true a0 ex rs j ys ym)) (xD ()) /\
                   iu x (xD ()) == true)
  = let d = dx dk cA cB cK true a0 ex rs j ys ym in
    distinct (); distD ();
    holds_elim x d;
    db_ex dk cA cB cK true a0 ex rs j ys ym (xD ());
    db_dx dk cA cB cK true a0 ex rs j ys ym (xB ());
    db_dx dk cA cB cK true a0 ex rs j ys ym (xK ());
    blk x d (xD ()); blk x d (xB ()); blk x d (xK ());
    st_vals (); l1 (vB ()); l1 (vK2 ()); l3 i1 iw i1;
    reach_r x d (xD ());
    res_iu x (xB ());
    reach_f x d (xD ()) 0 (xB ()) (xB ());
    res_infix (mx x) (xK ());
    reach_f x d (xB ()) 0 (xK () + 2) (xK ())
#pop-options

#push-options "--z3rlimit 40"
let c11 () : Lemma (requires pw_room /\ cok) (ensures holds (x11 ()) (d11 ()) /\ ok (x10 ()) (e10 ()))
  = c10 ();
    let x = x10 () in
    let d = d10 () in
    ex9_ok ();
    mem_hd (vD ()) [vA ()];
    reachK x DM M.Grey M.Grey M.White i1 (ex9 ()) [vD (); vA ()] 5 ms0 (M.empty_heap ywords);
    blocks_dx DM M.Grey M.Grey M.White true i1 (ex9 ()) [vD (); vA ()] 5 ms0 (M.empty_heap ywords);
    st_k2 x d (xK ());
    PWMu.yal1 (vK2 ());
    l1 (vK2 ());
    assert (mutator_ok_w pc (wd x d) (e10 ()));
    yalloc_ev ic x d 1 0 [vK2 ()] 0 (PWMu.ms1 (vK2 ()));
    let d' = { d with dys = PWMu.ms1 (vK2 ()); dym = M.young_alloc d.dym 0 1 0 [vK2 ()]; drt = vY1 :: d.drt } in
    holds_ext (x11 ()) d' (d11 ())

let c12 () : Lemma (requires pw_room /\ cok) (ensures holds (x12 ()) (d12 ()) /\ ok (x11 ()) e11)
  = c11 ();
    let x = x11 () in
    let d = d11 () in
    PWMu.yal2 (vK2 ()) iw;
    st_vals (); l1 iw;
    assert (mutator_ok_w pc (wd x d) e11);
    yalloc_ev ic x d 1 0 [iw] 2 (PWMu.ms2 (vK2 ()) iw);
    let d' = { d with dys = PWMu.ms2 (vK2 ()) iw; dym = M.young_alloc d.dym 2 1 0 [iw]; drt = vY2 :: d.drt } in
    holds_ext (x12 ()) d' (d12 ())
#pop-options

let ex13 () : GTot exb = exm (x12 ()) (d12 ()) (ex9 ())
let rs13 () : GTot (list M.value) = L.map (T.fwdv (PWMu.ym2 (vK2 ()) iw) (PWM.mfwd (x12 ()))) [vY2; vY1; vD (); vA ()]
let dM (cA cB cK: M.colour) : GTot dsc = dx DM cA cB cK true i1 (ex13 ()) (rs13 ()) 7 ms0 (M.empty_heap ywords)

/// The nursery's two blocks, nice.
let nice12 () : Lemma (requires pw_room /\ cok)
  (ensures PWM.nice_v (xK ()) (vK2 ()) /\ PWM.nice_v (xK ()) iw /\
           M.young_ok (PWMu.ym2 (vK2 ()) iw) /\ T.young_follow_ok (PWMu.ym2 (vK2 ()) iw) /\
           PWF.ynice (xK ()) (PWMu.ym2 (vK2 ()) iw) /\
           M.is_block (PWMu.ym2 (vK2 ()) iw) 0 /\ M.field (PWMu.ym2 (vK2 ()) iw) 0 0 == vK2 () /\
           M.is_block (PWMu.ym2 (vK2 ()) iw) 2 /\ M.field (PWMu.ym2 (vK2 ()) iw) 2 0 == iw)
  = c10 (); ex9_ok ();
    blocks_dx DM M.Grey M.Grey M.White true i1 (ex9 ()) [vD (); vA ()] 5 ms0 (M.empty_heap ywords);
    st_k2 (x10 ()) (d10 ()) (xK ());
    st_vals ();
    PWM.ym2_ok (xK ()) (vK2 ()) iw

/// **12: a minor collection while marking promotes Y1 and Y2.**
#push-options "--z3rlimit 40"
let c13 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x13 ()) (dM M.Grey M.Grey M.White) /\ ok (x12 ()) EMinor /\
           T.Done? (PWM.mres (x12 ())) /\ Some? (PWM.mfwd (x12 ()) 0) /\ Some? (PWM.mfwd (x12 ()) 2))
  = c12 (); nice12 (); ex9_ok (); distinct ();
    let x = x12 () in
    let d = d12 () in
    holds_elim x d;
    holds_blk x d (xC ());
    blocks_dx DM M.Grey M.Grey M.White true i1 (ex9 ()) [vY2; vY1; vD (); vA ()] 5 (PWMu.ms2 (vK2 ()) iw) (PWMu.ym2 (vK2 ()) iw);
    assert (PWM.mstep_pre x d (xK ()));
    minor_dx ic x DM M.Grey M.Grey M.White true i1 (ex9 ()) [vY2; vY1; vD (); vA ()] 5 (PWMu.ms2 (vK2 ()) iw) (PWMu.ym2 (vK2 ()) iw);
    mem_hd vY2 [vY1; vD (); vA ()];
    mem_hd vY1 [vD (); vA ()];
    mem_tl vY2 vY1 [vY1; vD (); vA ()];
    PWM.live_root (wd x d) 0 0;
    PWM.live_root (wd x d) 2 2
#pop-options

/// The extra blocks after 12: D and the two black copies.
let ex13_y (y: nat) : Lemma (requires pw_room /\ cok)
  (ensures Some? (ex13 () y) ==>
           (Some?.v (ex13 () y)).bc == M.Black /\ (Some?.v (ex13 () y)).blv == true /\
           (Some?.v (ex13 () y)).bw == 1 /\ (Some?.v (ex13 () y)).bt == 0 /\
           ((Some?.v (ex13 () y)).bf == [vB ()] \/ (Some?.v (ex13 () y)).bf == [vK2 ()] \/ (Some?.v (ex13 () y)).bf == [iw]))
  = c12 (); nice12 ();
    let x = x12 () in
    let d = d12 () in
    holds_elim x d;
    assert (T.Marking? x.ph);
    assert (ex13 () y == exm x d (ex9 ()) y);
    assert (d.dym == PWMu.ym2 (vK2 ()) iw);
    if PWM.is_cp x d 0 y then begin
      assert (ex13 () y == Some (PWM.cpy x d 0));
      assert ((PWM.cpy x d 0).bf == [vK2 ()])
    end
    else if PWM.is_cp x d 2 y then begin
      assert (ex13 () y == Some (PWM.cpy x d 2));
      assert ((PWM.cpy x d 2).bf == [iw])
    end
    else assert (ex13 () y == ex9 () y)

let ex13_ok () : Lemma (requires pw_room /\ cok)
  (ensures ex_ok (ex13 ()) /\ ex_ny (ex13 ()) /\ ex_ptr (ex13 ()) /\ ex_black (ex13 ()))
  = FStar.Classical.forall_intro (FStar.Classical.move_requires ex13_y);
    st_vals ();
    l1 (vB ()); l1 (vK2 ()); l1 iw;
    let pt (y i a: nat) : Lemma (Some? (ex13 () y) /\ i < (Some?.v (ex13 () y)).bw /\
                                 vi (Some?.v (ex13 () y)).bf i == M.VPtr (M.Major a) ==> a == xB () \/ a == xK () + 2)
      = if Some? (ex13 () y) then ex13_y y in
    FStar.Classical.forall_intro_3 pt;
    let ny (y: nat) : Lemma (Some? (ex13 () y) ==> FWS.no_young (Some?.v (ex13 () y)).bf == true)
      = if Some? (ex13 () y) then ex13_y y in
    FStar.Classical.forall_intro ny

/// ---------------------------------------------------------------------------
/// 13-15: three slices, in the order the mark chooses
/// ---------------------------------------------------------------------------

let x14 () : GTot (config pc) = step pc (x13 ()) ESlice
let x15 () : GTot (config pc) = step pc (x14 ()) ESlice
let x16 () : GTot (config pc) = step pc (x15 ()) ESlice

let sl (x: config pc) (cA cB cK: M.colour)
  : Lemma (requires pw_room /\ cok /\ holds x (dM cA cB cK) /\ anygrey cA cB cK)
          (ensures (let t = PWK.fg x in
                    ((t == xA () /\ cA == M.Grey) \/ (t == xB () /\ cB == M.Grey) \/ (t == xK () /\ cK == M.Grey)) /\
                    holds (step pc x ESlice) (dM (ngA t cA) (ngB t cB) (ngK t cK)) /\ ok x ESlice))
  = ex13_ok ();
    slice_dx ic x cA cB cK true 1 (ex13 ()) (rs13 ()) 7 ms0 (M.empty_heap ywords)

let c14 () : Lemma (requires pw_room /\ cok)
  (ensures (holds (x14 ()) (dM M.Black M.Grey M.White) \/ holds (x14 ()) (dM M.Grey M.Black M.Grey)) /\
           ok (x13 ()) ESlice)
  = c13 (); distinct ();
    sl (x13 ()) M.Grey M.Grey M.White

let c15 () : Lemma (requires pw_room /\ cok)
  (ensures (holds (x15 ()) (dM M.Black M.Black M.Grey) \/ holds (x15 ()) (dM M.Grey M.Black M.Black)) /\
           ok (x14 ()) ESlice)
  = c14 (); distinct ();
    FStar.Classical.move_requires (sl (x14 ()) M.Black M.Grey) M.White;
    FStar.Classical.move_requires (sl (x14 ()) M.Grey M.Black) M.Grey

let c16 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x16 ()) (dM M.Black M.Black M.Black) /\ ok (x15 ()) ESlice)
  = c15 (); distinct ();
    FStar.Classical.move_requires (sl (x15 ()) M.Black M.Black) M.Grey;
    FStar.Classical.move_requires (sl (x15 ()) M.Grey M.Black) M.Black


/// ---------------------------------------------------------------------------
/// 16-20: the hand-over; while sweeping, Y3 and Y4, a minor collection, roots
/// ---------------------------------------------------------------------------

let x17 () : GTot (config pc) = step pc (x16 ()) EHandover
let dS () : GTot dsc = dx DS M.Black M.Black M.Black true i1 (ex13 ()) (rs13 ()) 7 ms0 (M.empty_heap ywords)

let c17 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x17 ()) (dS ()) /\ ok (x16 ()) EHandover /\
           (forall (y: nat). iu (x16 ()) y == true ==> unsw (x17 ()) y == true) /\
           (forall (y: nat). iu (x17 ()) y == iu (x16 ()) y))
  = c16 (); ex13_ok ();
    hand_dx ic (x16 ()) 1 (ex13 ()) (rs13 ()) 7 ms0 (M.empty_heap ywords)

/// D stays D through the first collection: no copy is at a block in use.
let ex13_D () : Lemma (requires pw_room /\ cok) (ensures ex13 () (xD ()) == Some (bD M.Black (vB ())))
  = c12 (); nice12 (); ex9_ok (); distinct (); distD ();
    let x = x12 () in
    let d = d12 () in
    holds_elim x d;
    db_ex DM M.Grey M.Grey M.White true i1 (ex9 ()) [vY2; vY1; vD (); vA ()] 5 (PWMu.ms2 (vK2 ()) iw) (PWMu.ym2 (vK2 ()) iw) (xD ());
    holds_blk x d (xD ());
    blocks_dx DM M.Grey M.Grey M.White true i1 (ex9 ()) [vY2; vY1; vD (); vA ()] 5 (PWMu.ms2 (vK2 ()) iw) (PWMu.ym2 (vK2 ()) iw);
    assert (PWM.mstep_pre x d (xK ()));
    if PWM.is_cp x d 0 (xD ()) then cp_fresh x d (xK ()) 0 (xD ());
    if PWM.is_cp x d 2 (xD ()) then cp_fresh x d (xK ()) 2 (xD ())

/// D is among the roots after 12.
let mem_D13 () : Lemma (L.memP (vD ()) (rs13 ()) /\ L.memP (vA ()) (rs13 ()))
  = let f = T.fwdv (PWMu.ym2 (vK2 ()) iw) (PWM.mfwd (x12 ())) in
    mem_hd (vA ()) [];
    mem_tl (vD ()) (vA ()) [vA ()];
    mem_hd (vD ()) [vA ()];
    mem_tl vY1 (vD ()) [vD (); vA ()];
    mem_tl vY1 (vA ()) [vD (); vA ()];
    mem_tl vY2 (vD ()) [vY1; vD (); vA ()];
    mem_tl vY2 (vA ()) [vY1; vD (); vA ()];
    L.memP_map_intro f (vD ()) [vY2; vY1; vD (); vA ()];
    L.memP_map_intro f (vA ()) [vY2; vY1; vD (); vA ()]

let x18 () : GTot (config pc) = step pc (x17 ()) (e10 ())
let x19 () : GTot (config pc) = step pc (x18 ()) e11
let x20 () : GTot (config pc) = step pc (x19 ()) EMinor

let d18 () : GTot dsc = dx DS M.Black M.Black M.Black true i1 (ex13 ()) (vY1 :: rs13 ()) 7 (PWMu.ms1 (vK2 ())) (PWMu.ym1 (vK2 ()))
let d19 () : GTot dsc = dx DS M.Black M.Black M.Black true i1 (ex13 ()) (vY2 :: vY1 :: rs13 ()) 7
                           (PWMu.ms2 (vK2 ()) iw) (PWMu.ym2 (vK2 ()) iw)

/// A young allocation leaves the major heap and the allocator alone.
let iu_young (x: config pc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value) (y: nat)
  : Lemma (iu (step pc x (EYoungAlloc sz tag vs)) y == iu x y)
  = ()

/// The program's obligations for a young block holding one value.
let mut_y (w: M.world) (v: M.value)
  : Lemma (requires value_ok w v /\ storable_w v) (ensures mutator_ok_w pc w (EYoungAlloc 1 0 [v]))
  = l1 v

#push-options "--z3rlimit 40"
let c18 () : Lemma (requires pw_room /\ cok) (ensures holds (x18 ()) (d18 ()) /\ ok (x17 ()) (e10 ()))
  = c17 (); ex13_ok (); ex13_D (); mem_D13 (); l1 (vB ());
    let x = x17 () in
    let d = dS () in
    reachK x DS M.Black M.Black M.Black i1 (ex13 ()) (rs13 ()) 7 ms0 (M.empty_heap ywords);
    blocks_dx DS M.Black M.Black M.Black true i1 (ex13 ()) (rs13 ()) 7 ms0 (M.empty_heap ywords);
    st_k2 x d (xK ());
    PWMu.yal1 (vK2 ());
    l1 (vK2 ());
    assert (value_ok (wd x d) (vK2 ()));
    mut_y (wd x d) (vK2 ());
    yalloc_ev ic x d 1 0 [vK2 ()] 0 (PWMu.ms1 (vK2 ()));
    let d' = { d with dys = PWMu.ms1 (vK2 ()); dym = M.young_alloc d.dym 0 1 0 [vK2 ()]; drt = vY1 :: d.drt } in
    holds_ext (x18 ()) d' (d18 ())

let c19 () : Lemma (requires pw_room /\ cok) (ensures holds (x19 ()) (d19 ()) /\ ok (x18 ()) e11)
  = c18 ();
    let x = x18 () in
    let d = d18 () in
    PWMu.yal2 (vK2 ()) iw;
    st_vals (); l1 iw;
    assert (mutator_ok_w pc (wd x d) e11);
    yalloc_ev ic x d 1 0 [iw] 2 (PWMu.ms2 (vK2 ()) iw);
    let d' = { d with dys = PWMu.ms2 (vK2 ()) iw; dym = M.young_alloc d.dym 2 1 0 [iw]; drt = vY2 :: d.drt } in
    holds_ext (x19 ()) d' (d19 ())
#pop-options

/// C is in use until the sweep starts.
let iu_C19 () : Lemma (requires pw_room /\ cok) (ensures iu (x19 ()) (xC ()) == true)
  = c16 (); c17 (); distinct ();
    holds_elim (x16 ()) (dM M.Black M.Black M.Black);
    holds_blk (x16 ()) (dM M.Black M.Black M.Black) (xC ());
    iu_young (x17 ()) 1 0 [vK2 ()] (xC ());
    iu_young (x18 ()) 1 0 [iw] (xC ())

let ex20 () : GTot exb = exm (x19 ()) (d19 ()) (ex13 ())
let rs20 () : GTot (list M.value) = L.map (T.fwdv (PWMu.ym2 (vK2 ()) iw) (PWM.mfwd (x19 ()))) (vY2 :: vY1 :: rs13 ())
let d20 () : GTot dsc = dx DS M.Black M.Black M.Black true i1 (ex20 ()) (rs20 ()) 9 ms0 (M.empty_heap ywords)

let st_young () : Lemma (requires pw_room /\ cok)
  (ensures forall (o: nat). M.is_block (PWMu.ym2 (vK2 ()) iw) o ==> storable_w (M.field (PWMu.ym2 (vK2 ()) iw) o 0))
  = nice12 ()

let mpre19 () : Lemma (requires pw_room /\ cok) (ensures PWM.mstep_pre (x19 ()) (d19 ()) (xK ()))
  = c19 (); nice12 (); ex13_ok (); st_young ();
    holds_elim (x19 ()) (d19 ());
    blocks_dx DS M.Black M.Black M.Black true i1 (ex13 ()) (vY2 :: vY1 :: rs13 ()) 7 (PWMu.ms2 (vK2 ()) iw) (PWMu.ym2 (vK2 ()) iw)

/// **19: a minor collection while sweeping promotes Y3 and Y4.**
#push-options "--z3rlimit 40"
let c20 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x20 ()) (d20 ()) /\ ok (x19 ()) EMinor /\
           T.Done? (PWM.mres (x19 ())) /\ Some? (PWM.mfwd (x19 ()) 0) /\ Some? (PWM.mfwd (x19 ()) 2))
  = c19 (); nice12 (); ex13_ok (); iu_C19 ();
    let x = x19 () in
    let d = d19 () in
    holds_elim x d;
    blocks_dx DS M.Black M.Black M.Black true i1 (ex13 ()) (vY2 :: vY1 :: rs13 ()) 7 (PWMu.ms2 (vK2 ()) iw) (PWMu.ym2 (vK2 ()) iw);
    assert (PWM.mstep_pre x d (xK ()));
    minor_dx ic x DS M.Black M.Black M.Black true i1 (ex13 ()) (vY2 :: vY1 :: rs13 ()) 7 (PWMu.ms2 (vK2 ()) iw) (PWMu.ym2 (vK2 ()) iw);
    mem_hd vY2 (vY1 :: rs13 ());
    mem_hd vY1 (rs13 ());
    mem_tl vY2 vY1 (vY1 :: rs13 ());
    PWM.live_root (wd x d) 0 0;
    PWM.live_root (wd x d) 2 2
#pop-options

/// D stays D through the second collection.
let ex20_D () : Lemma (requires pw_room /\ cok) (ensures ex20 () (xD ()) == Some (bD M.Black (vB ())))
  = c19 (); nice12 (); ex13_ok (); ex13_D (); iu_C19 (); mem_D13 (); l1 (vB ());
    let x = x19 () in
    let d = d19 () in
    holds_elim x d;
    mem_tl vY1 (vD ()) (rs13 ()); mem_tl vY2 (vD ()) (vY1 :: rs13 ());
    reachK x DS M.Black M.Black M.Black i1 (ex13 ()) (vY2 :: vY1 :: rs13 ()) 7 (PWMu.ms2 (vK2 ()) iw) (PWMu.ym2 (vK2 ()) iw);
    mpre19 ();
    if PWM.is_cp x d 0 (xD ()) then cp_fresh x d (xK ()) 0 (xD ());
    if PWM.is_cp x d 2 (xD ()) then cp_fresh x d (xK ()) 2 (xD ())

let mem_20 () : Lemma (L.memP (vD ()) (rs20 ()) /\ L.memP (vA ()) (rs20 ()))
  = mem_D13 ();
    let f = T.fwdv (PWMu.ym2 (vK2 ()) iw) (PWM.mfwd (x19 ())) in
    mem_tl vY1 (vD ()) (rs13 ()); mem_tl vY1 (vA ()) (rs13 ());
    mem_tl vY2 (vD ()) (vY1 :: rs13 ()); mem_tl vY2 (vA ()) (vY1 :: rs13 ());
    L.memP_map_intro f (vD ()) (vY2 :: vY1 :: rs13 ());
    L.memP_map_intro f (vA ()) (vY2 :: vY1 :: rs13 ())

let e20 () : GTot event = ERoots [vA (); vD ()]
let x21 () : GTot (config pc) = step pc (x20 ()) (e20 ())
let d21 () : GTot dsc = dx DS M.Black M.Black M.Black true i1 (ex20 ()) [vA (); vD ()] 9 ms0 (M.empty_heap ywords)

let mut_roots2 (w: M.world) (u v: M.value)
  : Lemma (requires value_ok w u /\ value_ok w v /\ storable_w u /\ storable_w v)
          (ensures mutator_ok_w pc w (ERoots [u; v]))
  = l2 u v

#push-options "--z3rlimit 40"
let c21 () : Lemma (requires pw_room /\ cok) (ensures holds (x21 ()) (d21 ()) /\ ok (x20 ()) (e20 ()))
  = c20 (); ex20_D (); mem_20 (); l1 (vB ()); distinct ();
    let x = x20 () in
    let d = d20 () in
    holds_elim x d;
    reachK x DS M.Black M.Black M.Black i1 (ex20 ()) (rs20 ()) 9 ms0 (M.empty_heap ywords);
    db_dx DS M.Black M.Black M.Black true i1 (ex20 ()) (rs20 ()) 9 ms0 (M.empty_heap ywords) (xA ());
    blk x d (xA ());
    reach_r x d (xA ());
    res_iu x (xA ()); res_iu x (xD ());
    distD ();
    db_ex DS M.Black M.Black M.Black true i1 (ex20 ()) (rs20 ()) 9 ms0 (M.empty_heap ywords) (xD ());
    blk x d (xD ());
    st_blk x (xA ()); st_blk x (xD ());
    mut_roots2 (wd x d) (vA ()) (vD ());
    roots_ev ic x d [vA (); vD ()];
    holds_ext (x21 ()) ({ d with drt = [vA (); vD ()] }) (d21 ())
#pop-options

/// The extra blocks after 19: D, the black copies, the copies made sweeping.
let ex20_y (y: nat) : Lemma (requires pw_room /\ cok)
  (ensures Some? (ex20 () y) ==>
           (Some?.v (ex20 () y)).bc =!= M.Grey /\ (Some?.v (ex20 () y)).blv == true /\
           (Some?.v (ex20 () y)).bw == 1 /\ (Some?.v (ex20 () y)).bt == 0 /\
           ((Some?.v (ex20 () y)).bf == [vB ()] \/ (Some?.v (ex20 () y)).bf == [vK2 ()] \/ (Some?.v (ex20 () y)).bf == [iw]))
  = c19 (); ex13_y y;
    let x = x19 () in
    let d = d19 () in
    holds_elim x d;
    assert (ex20 () y == exm x d (ex13 ()) y);
    assert (d.dym == PWMu.ym2 (vK2 ()) iw);
    nice12 ();
    if PWM.is_cp x d 0 y then begin
      assert (ex20 () y == Some (PWM.cpy x d 0));
      assert ((PWM.cpy x d 0).bf == [vK2 ()])
    end
    else if PWM.is_cp x d 2 y then begin
      assert (ex20 () y == Some (PWM.cpy x d 2));
      assert ((PWM.cpy x d 2).bf == [iw])
    end
    else assert (ex20 () y == ex13 () y)

let ex20_ok () : Lemma (requires pw_room /\ cok) (ensures ex_ok (ex20 ()) /\ ex_ny (exw (ex20 ())))
  = FStar.Classical.forall_intro (FStar.Classical.move_requires ex20_y);
    st_vals ();
    l1 (vB ()); l1 (vK2 ()); l1 iw;
    let ny (y: nat) : Lemma (Some? (exw (ex20 ()) y) ==> FWS.no_young (Some?.v (exw (ex20 ()) y)).bf == true)
      = if Some? (ex20 () y) then ex20_y y in
    FStar.Classical.forall_intro ny
