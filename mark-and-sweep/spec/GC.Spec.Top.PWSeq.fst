/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PWSeq - the pages collector's sequential witness run
/// ---------------------------------------------------------------------------
///
/// Design doc §17.  A run of the pages collector (`PagesComps.pc`), in the
/// sequential style, from the page allocator's initial heap, under
/// `PWPre.pw_room`:
///   0-6   A, B, C (holding B), K (a closure, its second field an infix
///         header), A.0 := B, B.0 := K + 2, roots [A] (GC.Spec.Top.PWPre);
///   7     the cycle starts: A grey; A, B, K reachable, C unreachable;
///   8     a minor collection while marking (empty nursery);
///   9-11  three slices: A (greys B), B (greys K through the infix
///         pointer), K;
///   12    the hand-over;
///   13    a minor collection while sweeping (empty nursery);
///   14-   the sweep's steps, one per unit: `nsw` of them (PWPages); C freed;
///   then  the end; a read of A.0 into a root; Y1 (holding K + 2) and Y2
///         (holding an integer that reads as an infix header) allocated
///         young; the roots become [A; Y1; Y2]; a minor collection while
///         idle, promoting Y1 and Y2.
/// Every event is allowed (`seq_run_ok`), with every hypothesis of
/// `gc_correct`, T1 and T2 (GC.Spec.Top.PWHyps).

module GC.Spec.Top.PWSeq

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
open GC.Spec.Top.PWCyc
module M = GC.Spec.Top.Heap
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module RA = GC.Spec.Top.RunApp
module TR = GC.Spec.Top.Transp
module PWK = GC.Spec.Top.PWMark
module PWM = GC.Spec.Top.PWMinor
module PWMu = GC.Spec.Top.PWMut
module PWS = GC.Spec.Top.PWSweep
module FWS = GC.Spec.Top.FFWStep
module Y = GC.Spec.Top.Young

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let sq = Sequential

/// The conditions and no failed allocation, at one step.
let ok (x: config pc) (e: event) : prop = RA.conds pc sq x e /\ TR.alloc_succeeds x e

/// ---------------------------------------------------------------------------
/// The cycle
/// ---------------------------------------------------------------------------

let x8 () : GTot (config pc) = step pc (x7 ()) EStart
let x9 () : GTot (config pc) = step pc (x8 ()) EMinor
let x10 () : GTot (config pc) = step pc (x9 ()) ESlice
let x11 () : GTot (config pc) = step pc (x10 ()) ESlice
let x12 () : GTot (config pc) = step pc (x11 ()) ESlice
let x13 () : GTot (config pc) = step pc (x12 ()) EHandover
let x14 () : GTot (config pc) = step pc (x13 ()) EMinor

let rA : list M.value -> prop = fun rs -> rs == [vA ()]

let nyA () : Lemma (FWS.no_young [vA ()] == true) = l1 (vA ())

let c8 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x8 ()) (ddv DM M.Grey M.White M.White true [vA ()] 4) /\ ok (x7 ()) EStart)
  = s8 sq

let c9 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x9 ()) (ddv DM M.Grey M.White M.White true [vA ()] 6) /\ ok (x8 ()) EMinor)
  = c8 (); nyA ();
    minor_empty sq (x8 ()) DM M.Grey M.White M.White true [vA ()] 4

let c10 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x10 ()) (ddv DM M.Black M.Grey M.White true [vA ()] 6) /\ ok (x9 ()) ESlice)
  = c9 (); distinct ();
    slice_dd sq (x9 ()) M.Grey M.White M.White true [vA ()] 6

let c11 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x11 ()) (ddv DM M.Black M.Black M.Grey true [vA ()] 6) /\ ok (x10 ()) ESlice)
  = c10 (); distinct ();
    slice_dd sq (x10 ()) M.Black M.Grey M.White true [vA ()] 6

let c12 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x12 ()) (ddv DM M.Black M.Black M.Black true [vA ()] 6) /\ ok (x11 ()) ESlice)
  = c11 (); distinct ();
    slice_dd sq (x11 ()) M.Black M.Black M.Grey true [vA ()] 6

let c13 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x13 ()) (ddv DS M.Black M.Black M.Black true [vA ()] 6) /\ ok (x12 ()) EHandover)
  = c12 ();
    hand_dd sq (x12 ()) true [vA ()] 6

let c14 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x14 ()) (ddv DS M.Black M.Black M.Black true [vA ()] 8) /\ ok (x13 ()) EMinor)
  = c13 (); nyA ();
    minor_empty sq (x13 ()) DS M.Black M.Black M.Black true [vA ()] 6

/// ---------------------------------------------------------------------------
/// The sweep and the end
/// ---------------------------------------------------------------------------

let ksw () : GTot nat = PWS.nsx (x14 ())
let x15 () : GTot (config pc) = exec pc (x14 ()) (PWS.repl (ksw ()))
let x16 () : GTot (config pc) = step pc (x15 ()) EEnd

let c15 () : Lemma (requires pw_room /\ cok)
  (ensures RA.tail_ok pc sq (x14 ()) (PWS.repl (ksw ())) /\ nf_tail (x14 ()) (PWS.repl (ksw ())) /\
           holds (x15 ()) (ddv DS M.Black M.Black M.Black true [vA ()] 8) /\ PWS.nsx (x15 ()) == 0)
  = c14 ();
    PWS.sweeps sq (x14 ()) (ddv DS M.Black M.Black M.Black true [vA ()] 8);
    nf_repl (x14 ()) (ksw ())

let c16 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x16 ()) (ddv DI M.White M.White M.White false [vA ()] 8) /\ ok (x15 ()) EEnd)
  = c15 ();
    end_dd sq (x15 ()) true [vA ()] 8

/// ---------------------------------------------------------------------------
/// Idle again: a read, two young blocks, the roots, a minor collection
/// ---------------------------------------------------------------------------

let vY1 : M.value = M.VPtr (M.Young 0)
let vY2 : M.value = M.VPtr (M.Young 2)

let e16 () : GTot event = ERead (M.Major (xA ())) 0
let e17 () : GTot event = EYoungAlloc 1 0 [vK2 ()]
let e18 : event = EYoungAlloc 1 0 [iw]
let e19 () : GTot event = ERoots [vA (); vY1; vY2]

let x17 () : GTot (config pc) = step pc (x16 ()) (e16 ())
let x18 () : GTot (config pc) = step pc (x17 ()) (e17 ())
let x19 () : GTot (config pc) = step pc (x18 ()) e18
let x20 () : GTot (config pc) = step pc (x19 ()) (e19 ())
let x21 () : GTot (config pc) = step pc (x20 ()) EMinor

let d17 () : GTot dsc = ddv DI M.White M.White M.White false [vB (); vA ()] 8
let d18 () : GTot dsc = dd DI M.White M.White M.White false [vY1; vB (); vA ()] 8 (PWMu.ms1 (vK2 ())) (PWMu.ym1 (vK2 ()))
let d19 () : GTot dsc = dd DI M.White M.White M.White false [vY2; vY1; vB (); vA ()] 8
                           (PWMu.ms2 (vK2 ()) iw) (PWMu.ym2 (vK2 ()) iw)
let d20 () : GTot dsc = dd DI M.White M.White M.White false [vA (); vY1; vY2] 8
                           (PWMu.ms2 (vK2 ()) iw) (PWMu.ym2 (vK2 ()) iw)

/// The blocks are in use and their fields known.
let at16 () : Lemma (requires pw_room /\ cok)
  (ensures (let x = x16 () in let d = ddv DI M.White M.White M.White false [vA ()] 8 in
            iu x (xA ()) /\ iu x (xB ()) /\ iu x (xK ()) /\
            d.db (xA ()) == Some (bof M.White M.White M.White (xA ())) /\
            d.db (xB ()) == Some (bof M.White M.White M.White (xB ())) /\
            d.db (xK ()) == Some (bof M.White M.White M.White (xK ()))))
  = c16 ();
    let d = ddv DI M.White M.White M.White false [vA ()] 8 in
    db_dd DI M.White M.White M.White false [vA ()] 8 ms0 (M.empty_heap ywords) (xA ());
    db_dd DI M.White M.White M.White false [vA ()] 8 ms0 (M.empty_heap ywords) (xB ());
    db_dd DI M.White M.White M.White false [vA ()] 8 ms0 (M.empty_heap ywords) (xK ());
    blk (x16 ()) d (xA ()); blk (x16 ()) d (xB ()); blk (x16 ()) d (xK ())

#push-options "--z3rlimit 40"
let c17 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x17 ()) (d17 ()) /\ ok (x16 ()) (e16 ()))
  = c16 (); at16 (); distinct ();
    let x = x16 () in
    let d = ddv DI M.White M.White M.White false [vA ()] 8 in
    st_vals (); l2 (vB ()) i1; l1 (vA ());
    reach_r x d (xA ());
    blk x d (xA ());
    assert (mutator_ok_w pc (wd x d) (e16 ()));
    read_ev sq x d (xA ()) 0;
    let d' = { d with drt = vi (Some?.v (d.db (xA ()))).bf 0 :: d.drt } in
    holds_ext (step pc x (e16 ())) d' (d17 ())
#pop-options

/// K is reachable from the root B.
let reachK17 () : Lemma (requires pw_room /\ cok)
  (ensures M.reachable (wd (x17 ()) (d17 ())) (xK ()) /\ M.resolve (mx (x17 ())) (xK () + 2) == Some (xK ()))
  = c17 (); distinct ();
    let x = x17 () in
    let d = d17 () in
    holds_elim x d;
    db_dd DI M.White M.White M.White false [vB (); vA ()] 8 ms0 (M.empty_heap ywords) (xB ());
    db_dd DI M.White M.White M.White false [vB (); vA ()] 8 ms0 (M.empty_heap ywords) (xK ());
    blk x d (xB ()); blk x d (xK ());
    st_vals (); l1 (vK2 ()); l3 i1 iw i1;
    mem_hd (vB ()) [vA ()];
    reach_r x d (xB ());
    res_infix (mx x) (xK ());
    reach_f x d (xB ()) 0 (xK () + 2) (xK ())

#push-options "--z3rlimit 40"
let c18 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x18 ()) (d18 ()) /\ ok (x17 ()) (e17 ()))
  = c17 (); reachK17 ();
    let x = x17 () in
    let d = d17 () in
    PWMu.yal1 (vK2 ());
    blocks_ok DI M.White M.White M.White false [vB (); vA ()] 8 ms0 (M.empty_heap ywords);
    st_k2 x d (xK ());
    l1 (vK2 ());
    assert (mutator_ok_w pc (wd x d) (e17 ()));
    yalloc_ev sq x d 1 0 [vK2 ()] 0 (PWMu.ms1 (vK2 ()));
    let d' = { d with dys = PWMu.ms1 (vK2 ()); dym = M.young_alloc d.dym 0 1 0 [vK2 ()]; drt = vY1 :: d.drt } in
    holds_ext (step pc x (e17 ())) d' (d18 ())

let c19 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x19 ()) (d19 ()) /\ ok (x18 ()) e18)
  = c18 ();
    let x = x18 () in
    let d = d18 () in
    PWMu.yal2 (vK2 ()) iw;
    st_vals ();
    l1 iw;
    assert (mutator_ok_w pc (wd x d) e18);
    yalloc_ev sq x d 1 0 [iw] 2 (PWMu.ms2 (vK2 ()) iw);
    let d' = { d with dys = PWMu.ms2 (vK2 ()) iw; dym = M.young_alloc d.dym 2 1 0 [iw]; drt = vY2 :: d.drt } in
    holds_ext (step pc x e18) d' (d19 ())
#pop-options

/// A young root is young-reachable.
let yreach_root (w: M.world) (a o: nat)
  : Lemma (requires L.memP (M.VPtr (M.Young a)) w.M.roots /\ M.resolve w.M.yng a == Some o)
          (ensures M.yreachable w o)
  = let r : M.yreach w o = M.YRoot o a () in
    assert (M.yreachable w o)

let nice_y () : Lemma (requires pw_room /\ cok)
  (ensures PWM.nice_v (xK ()) (vK2 ()) /\ PWM.nice_v (xK ()) iw)
  = c17 ();
    blocks_ok DI M.White M.White M.White false [vB (); vA ()] 8 ms0 (M.empty_heap ywords);
    st_k2 (x17 ()) (d17 ()) (xK ());
    st_vals ()

/// The program's obligations for three roots.
let mut_roots3 (w: M.world) (u v z: M.value)
  : Lemma (requires value_ok w u /\ value_ok w v /\ value_ok w z /\ storable_w u /\ storable_w v /\ storable_w z)
          (ensures mutator_ok_w pc w (ERoots [u; v; z]))
  = l3 u v z

#push-options "--z3rlimit 40"
let c20 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x20 ()) (d20 ()) /\ ok (x19 ()) (e19 ()))
  = c19 (); nice_y (); distinct ();
    let x = x19 () in
    let d = d19 () in
    holds_elim x d;
    PWM.ym2_ok (xK ()) (vK2 ()) iw;
    db_dd DI M.White M.White M.White false [vY2; vY1; vB (); vA ()] 8 (PWMu.ms2 (vK2 ()) iw) (PWMu.ym2 (vK2 ()) iw) (xA ());
    blk x d (xA ());
    st_blk x (xA ());
    young_storable 0; young_storable 2;
    mem_hd (vA ()) [];
    mem_tl (vB ()) (vA ()) [vA ()];
    mem_tl vY1 (vA ()) [vB (); vA ()];
    mem_tl vY2 (vA ()) [vY1; vB (); vA ()];
    mem_hd vY2 [vY1; vB (); vA ()];
    mem_hd vY1 [vB (); vA ()];
    mem_tl vY2 vY1 [vY1; vB (); vA ()];
    reach_r x d (xA ());
    yreach_root (wd x d) 0 0;
    yreach_root (wd x d) 2 2;
    l3 (vA ()) vY1 vY2;
    res_iu x (xA ());
    assert (M.resolve (wd x d).M.yng 0 == Some 0 /\ M.resolve (wd x d).M.yng 2 == Some 2);
    assert (value_ok (wd x d) (vA ()));
    assert (value_ok (wd x d) vY1);
    assert (value_ok (wd x d) vY2);
    assert (storable_w (vA ()) /\ storable_w vY1 /\ storable_w vY2);
    mut_roots3 (wd x d) (vA ()) vY1 vY2;
    roots_ev sq x d [vA (); vY1; vY2];
    holds_ext (step pc x (e19 ())) ({ d with drt = [vA (); vY1; vY2] }) (d20 ())

/// **The last event: a minor collection while idle, promoting Y1 and Y2.**
let c21 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x21 ()) (PWM.dminor (x20 ()) (d20 ())) /\ ok (x20 ()) EMinor /\
           T.Done? (PWM.mres (x20 ())) /\ Some? (PWM.mfwd (x20 ()) 0) /\ Some? (PWM.mfwd (x20 ()) 2))
  = c20 (); nice_y ();
    let x = x20 () in
    let d = d20 () in
    PWM.ym2_ok (xK ()) (vK2 ()) iw;
    blocks_ok DI M.White M.White M.White false [vA (); vY1; vY2] 8 (PWMu.ms2 (vK2 ()) iw) (PWMu.ym2 (vK2 ()) iw);
    assert (PWM.mstep_pre x d (xK ()));
    PWM.step_minor x d (xK ());
    l3 (vA ()) vY1 vY2;
    mem_hd vY2 [];
    mem_tl vY1 vY2 [vY2];
    mem_hd vY1 [vY2];
    mem_tl (vA ()) vY1 [vY1; vY2];
    mem_tl (vA ()) vY2 [vY1; vY2];
    PWM.live_root (wd x d) 0 0;
    PWM.live_root (wd x d) 2 2;
    enabled_plain x d EMinor;
    conds_of sq x d EMinor
#pop-options

/// ---------------------------------------------------------------------------
/// The run
/// ---------------------------------------------------------------------------

let pre14 () : GTot (list event) =
  [e0; e1; e2 (); e3; e4 (); e5 (); e6 (); EStart; EMinor; ESlice; ESlice; ESlice; EHandover; EMinor]

let post () : GTot (list event) = [EEnd; e16 (); e17 (); e18; e19 (); EMinor]

/// **The sequential run.**
let es_seq () : GTot (list event) = L.append (pre14 ()) (L.append (PWS.repl (ksw ())) (post ()))

#push-options "--fuel 1"
let nf_nil (x: config pc) : Lemma (nf_tail x []) = ()
#pop-options

/// One step of a tail, both properties.
let tl_cons (x: config pc) (e: event) (tl: list event)
  : Lemma (requires ok x e /\ RA.tail_ok pc sq (step pc x e) tl /\ nf_tail (step pc x e) tl)
          (ensures RA.tail_ok pc sq x (e :: tl) /\ nf_tail x (e :: tl) /\ exec pc x (e :: tl) == exec pc (step pc x e) tl)
  = tail_cons sq x e tl; nf_cons x e tl

let pre_ok () : Lemma (requires pw_room /\ cok)
  (ensures RA.tail_ok pc sq (x0 ()) (pre14 ()) /\ nf_tail (x0 ()) (pre14 ()) /\ exec pc (x0 ()) (pre14 ()) == x14 ())
  = h1 (); h2 (); h3 (); h4 (); h5 (); h6 (); h7 ();
    c8 (); c9 (); c10 (); c11 (); c12 (); c13 (); c14 ();
    tail_nil sq (x14 ()); nf_nil (x14 ());
    tl_cons (x13 ()) EMinor [];
    tl_cons (x12 ()) EHandover [EMinor];
    tl_cons (x11 ()) ESlice [EHandover; EMinor];
    tl_cons (x10 ()) ESlice [ESlice; EHandover; EMinor];
    tl_cons (x9 ()) ESlice [ESlice; ESlice; EHandover; EMinor];
    tl_cons (x8 ()) EMinor [ESlice; ESlice; ESlice; EHandover; EMinor];
    tl_cons (x7 ()) EStart [EMinor; ESlice; ESlice; ESlice; EHandover; EMinor];
    tl_cons (x6 ()) (e6 ()) [EStart; EMinor; ESlice; ESlice; ESlice; EHandover; EMinor];
    tl_cons (x5 ()) (e5 ()) [e6 (); EStart; EMinor; ESlice; ESlice; ESlice; EHandover; EMinor];
    tl_cons (x4 ()) (e4 ()) [e5 (); e6 (); EStart; EMinor; ESlice; ESlice; ESlice; EHandover; EMinor];
    tl_cons (x3 ()) e3 [e4 (); e5 (); e6 (); EStart; EMinor; ESlice; ESlice; ESlice; EHandover; EMinor];
    tl_cons (x2 ()) (e2 ()) [e3; e4 (); e5 (); e6 (); EStart; EMinor; ESlice; ESlice; ESlice; EHandover; EMinor];
    tl_cons (x1 ()) e1 [e2 (); e3; e4 (); e5 (); e6 (); EStart; EMinor; ESlice; ESlice; ESlice; EHandover; EMinor];
    tl_cons (x0 ()) e0 [e1; e2 (); e3; e4 (); e5 (); e6 (); EStart; EMinor; ESlice; ESlice; ESlice; EHandover; EMinor]

let post_ok () : Lemma (requires pw_room /\ cok)
  (ensures RA.tail_ok pc sq (x15 ()) (post ()) /\ nf_tail (x15 ()) (post ()))
  = c16 (); c17 (); c18 (); c19 (); c20 (); c21 ();
    tail_nil sq (x21 ()); nf_nil (x21 ());
    tl_cons (x20 ()) EMinor [];
    tl_cons (x19 ()) (e19 ()) [EMinor];
    tl_cons (x18 ()) e18 [e19 (); EMinor];
    tl_cons (x17 ()) (e17 ()) [e18; e19 (); EMinor];
    tl_cons (x16 ()) (e16 ()) [e17 (); e18; e19 (); EMinor];
    tl_cons (x15 ()) EEnd [e16 (); e17 (); e18; e19 (); EMinor]

/// **The sequential run is a run, with the contracts at every step, and
/// no allocation fails.**
let seq_run () : Lemma (requires pw_room /\ cok)
  (ensures run_ok pc Sequential msize ywords (es_seq ()) /\ run_hyps pc msize ywords (es_seq ()) /\
           TR.no_fail pc msize ywords (es_seq ()))
  = pre_ok (); post_ok (); c15 ();
    tail_app sq (x14 ()) (PWS.repl (ksw ())) (post ());
    nf_app (x14 ()) (PWS.repl (ksw ())) (post ());
    tail_app sq (x0 ()) (pre14 ()) (L.append (PWS.repl (ksw ())) (post ()));
    nf_app (x0 ()) (pre14 ()) (L.append (PWS.repl (ksw ())) (post ()));
    run_of sq (es_seq ());
    no_fail_of (es_seq ())
