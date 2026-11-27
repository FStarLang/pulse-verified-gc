/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PWIncB - the pages incremental witness run, from the sweep
/// ---------------------------------------------------------------------------
///
/// Design doc §17.  The incremental run (GC.Spec.Top.PWInc) after its
/// event 20: the sweep's `nsw` steps (C freed), the end, a read of D.0 into
/// a root, a minor collection while idle (empty nursery); and the run as a
/// whole (`inc_run`).

module GC.Spec.Top.PWIncB

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
open GC.Spec.Top.PWInc
module M = GC.Spec.Top.Heap
module PWK = GC.Spec.Top.PWMark
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module RA = GC.Spec.Top.RunApp
module TR = GC.Spec.Top.Transp
module PWM = GC.Spec.Top.PWMinor
module PWMu = GC.Spec.Top.PWMut
module PWS = GC.Spec.Top.PWSweep
module PWC = GC.Spec.Top.PWCyc
module FWS = GC.Spec.Top.FFWStep

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The sweep, the end, a read, a minor collection while idle
/// ---------------------------------------------------------------------------

let ksw () : GTot nat = PWS.nsx (x21 ())
let x22 () : GTot (config pc) = exec pc (x21 ()) (PWS.repl (ksw ()))
let x23 () : GTot (config pc) = step pc (x22 ()) EEnd
let e23 () : GTot event = ERead (M.Major (xD ())) 0
let x24 () : GTot (config pc) = step pc (x23 ()) (e23 ())
let x25 () : GTot (config pc) = step pc (x24 ()) EMinor

let d23 () : GTot dsc = dx DI M.White M.White M.White false i1 (exw (ex20 ())) [vA (); vD ()] 9 ms0 (M.empty_heap ywords)
let d24 () : GTot dsc = dx DI M.White M.White M.White false i1 (exw (ex20 ())) [vB (); vA (); vD ()] 9 ms0 (M.empty_heap ywords)

let c22 () : Lemma (requires pw_room /\ cok)
  (ensures RA.tail_ok pc ic (x21 ()) (PWS.repl (ksw ())) /\ nf_tail (x21 ()) (PWS.repl (ksw ())) /\
           holds (x22 ()) (d21 ()) /\ PWS.nsx (x22 ()) == 0 /\
           (forall (y: nat). iu (x22 ()) y == true ==> iu (x21 ()) y == true))
  = c21 ();
    PWS.sweeps ic (x21 ()) (d21 ());
    PWC.nf_repl (x21 ()) (ksw ())

let c23 () : Lemma (requires pw_room /\ cok) (ensures holds (x23 ()) (d23 ()) /\ ok (x22 ()) EEnd)
  = c22 (); ex20_ok ();
    end_dx ic (x22 ()) i1 (ex20 ()) [vA (); vD ()] 9 ms0 (M.empty_heap ywords)

/// `D`'s one field is a pointer field.
let ptr_D (x: config pc) (d: dsc)
  : Lemma (requires holds x d /\ d.db (xD ()) == Some ({ bD M.Black (vB ()) with bc = M.White }))
          (ensures M.ptr_field (wd x d).M.maj (xD ()) 0)
  = blk x d (xD ());
    assert_norm (M.scannable 0)

#push-options "--z3rlimit 40"
let c24 () : Lemma (requires pw_room /\ cok) (ensures holds (x24 ()) (d24 ()) /\ ok (x23 ()) (e23 ()))
  = c23 (); ex20_D (); distinct (); distD ();
    let x = x23 () in
    let d = d23 () in
    holds_elim x d;
    db_ex DI M.White M.White M.White false i1 (exw (ex20 ())) [vA (); vD ()] 9 ms0 (M.empty_heap ywords) (xD ());
    assert (d.db (xD ()) == Some ({ bD M.Black (vB ()) with bc = M.White }));
    blk x d (xD ());
    l1 (vB ()); l2 (vA ()) (vD ());
    mem_hd (vD ()) []; mem_tl (vA ()) (vD ()) [vD ()];
    reach_r x d (xD ());
    ptr_D x d;
    assert (mutator_ok_w pc (wd x d) (e23 ()));
    read_ev ic x d (xD ()) 0;
    holds_ext (x24 ()) ({ d with drt = vi (Some?.v (d.db (xD ()))).bf 0 :: d.drt }) (d24 ())

let c25 () : Lemma (requires pw_room /\ cok) (ensures ok (x24 ()) EMinor /\ T.Done? (PWM.mres (x24 ())))
  = c24 (); ex20_ok ();
    let x = x24 () in
    let d = d24 () in
    holds_elim x d;
    PWM.ym0_ok (xK ());
    blocks_dx DI M.White M.White M.White false i1 (exw (ex20 ())) [vB (); vA (); vD ()] 9 ms0 (M.empty_heap ywords);
    assert (PWM.mstep_pre x d (xK ()));
    minor_dx ic x DI M.White M.White M.White false i1 (exw (ex20 ())) [vB (); vA (); vD ()] 9 ms0 (M.empty_heap ywords)
#pop-options

/// ---------------------------------------------------------------------------
/// The run
/// ---------------------------------------------------------------------------

let pre21 () : GTot (list event) =
  [e0; e1; e2 (); e3; e4 (); e5 (); e6 (); EStart; e8 (); e9 (); e10 (); e11; EMinor; PWK.esl (x13 ()); PWK.esl (x14 ()); PWK.esl (x15 ()); EHandover; e10 (); e11; EMinor; e20 ()]

let post () : GTot (list event) = [EEnd; e23 (); EMinor]

/// **The incremental run.**
let es_inc () : GTot (list event) = L.append (pre21 ()) (L.append (PWS.repl (ksw ())) (post ()))

#push-options "--fuel 1"
let nf_nil (x: config pc) : Lemma (nf_tail x []) = ()
#pop-options

let tl_cons (x: config pc) (e: event) (tl: list event)
  : Lemma (requires ok x e /\ RA.tail_ok pc ic (step pc x e) tl /\ nf_tail (step pc x e) tl)
          (ensures RA.tail_ok pc ic x (e :: tl) /\ nf_tail x (e :: tl) /\ exec pc x (e :: tl) == exec pc (step pc x e) tl)
  = tail_cons ic x e tl; nf_cons x e tl

let pre_ok () : Lemma (requires pw_room /\ cok)
  (ensures RA.tail_ok pc ic (x0 ()) (pre21 ()) /\ nf_tail (x0 ()) (pre21 ()) /\ exec pc (x0 ()) (pre21 ()) == x21 ())
  = h1 (); h2 (); h3 (); h4 (); h5 (); h6 (); h7 ();
    c8 (); c9 (); c10 (); c11 (); c12 (); c13 (); c14 (); c15 (); c16 (); c17 (); c18 (); c19 (); c20 (); c21 ();
    tail_nil ic (x21 ()); nf_nil (x21 ());
    tl_cons (x20 ()) (e20 ()) [];
    tl_cons (x19 ()) EMinor [e20 ()];
    tl_cons (x18 ()) e11 [EMinor; e20 ()];
    tl_cons (x17 ()) (e10 ()) [e11; EMinor; e20 ()];
    tl_cons (x16 ()) EHandover [e10 (); e11; EMinor; e20 ()];
    tl_cons (x15 ()) (PWK.esl (x15 ())) [EHandover; e10 (); e11; EMinor; e20 ()];
    tl_cons (x14 ()) (PWK.esl (x14 ())) [PWK.esl (x15 ()); EHandover; e10 (); e11; EMinor; e20 ()];
    tl_cons (x13 ()) (PWK.esl (x13 ())) [PWK.esl (x14 ()); PWK.esl (x15 ()); EHandover; e10 (); e11; EMinor; e20 ()];
    tl_cons (x12 ()) EMinor [PWK.esl (x13 ()); PWK.esl (x14 ()); PWK.esl (x15 ()); EHandover; e10 (); e11; EMinor; e20 ()];
    tl_cons (x11 ()) e11 [EMinor; PWK.esl (x13 ()); PWK.esl (x14 ()); PWK.esl (x15 ()); EHandover; e10 (); e11; EMinor; e20 ()];
    tl_cons (x10 ()) (e10 ()) [e11; EMinor; PWK.esl (x13 ()); PWK.esl (x14 ()); PWK.esl (x15 ()); EHandover; e10 (); e11; EMinor; e20 ()];
    tl_cons (x9 ()) (e9 ()) [e10 (); e11; EMinor; PWK.esl (x13 ()); PWK.esl (x14 ()); PWK.esl (x15 ()); EHandover; e10 (); e11; EMinor; e20 ()];
    tl_cons (x8 ()) (e8 ()) [e9 (); e10 (); e11; EMinor; PWK.esl (x13 ()); PWK.esl (x14 ()); PWK.esl (x15 ()); EHandover; e10 (); e11; EMinor; e20 ()];
    tl_cons (x7 ()) EStart [e8 (); e9 (); e10 (); e11; EMinor; PWK.esl (x13 ()); PWK.esl (x14 ()); PWK.esl (x15 ()); EHandover; e10 (); e11; EMinor; e20 ()];
    tl_cons (x6 ()) (e6 ()) [EStart; e8 (); e9 (); e10 (); e11; EMinor; PWK.esl (x13 ()); PWK.esl (x14 ()); PWK.esl (x15 ()); EHandover; e10 (); e11; EMinor; e20 ()];
    tl_cons (x5 ()) (e5 ()) [e6 (); EStart; e8 (); e9 (); e10 (); e11; EMinor; PWK.esl (x13 ()); PWK.esl (x14 ()); PWK.esl (x15 ()); EHandover; e10 (); e11; EMinor; e20 ()];
    tl_cons (x4 ()) (e4 ()) [e5 (); e6 (); EStart; e8 (); e9 (); e10 (); e11; EMinor; PWK.esl (x13 ()); PWK.esl (x14 ()); PWK.esl (x15 ()); EHandover; e10 (); e11; EMinor; e20 ()];
    tl_cons (x3 ()) e3 [e4 (); e5 (); e6 (); EStart; e8 (); e9 (); e10 (); e11; EMinor; PWK.esl (x13 ()); PWK.esl (x14 ()); PWK.esl (x15 ()); EHandover; e10 (); e11; EMinor; e20 ()];
    tl_cons (x2 ()) (e2 ()) [e3; e4 (); e5 (); e6 (); EStart; e8 (); e9 (); e10 (); e11; EMinor; PWK.esl (x13 ()); PWK.esl (x14 ()); PWK.esl (x15 ()); EHandover; e10 (); e11; EMinor; e20 ()];
    tl_cons (x1 ()) e1 [e2 (); e3; e4 (); e5 (); e6 (); EStart; e8 (); e9 (); e10 (); e11; EMinor; PWK.esl (x13 ()); PWK.esl (x14 ()); PWK.esl (x15 ()); EHandover; e10 (); e11; EMinor; e20 ()];
    tl_cons (x0 ()) e0 [e1; e2 (); e3; e4 (); e5 (); e6 (); EStart; e8 (); e9 (); e10 (); e11; EMinor; PWK.esl (x13 ()); PWK.esl (x14 ()); PWK.esl (x15 ()); EHandover; e10 (); e11; EMinor; e20 ()]

let post_ok () : Lemma (requires pw_room /\ cok)
  (ensures RA.tail_ok pc ic (x22 ()) (post ()) /\ nf_tail (x22 ()) (post ()))
  = c23 (); c24 (); c25 ();
    tail_nil ic (x25 ()); nf_nil (x25 ());
    tl_cons (x24 ()) EMinor [];
    tl_cons (x23 ()) (e23 ()) [EMinor];
    tl_cons (x22 ()) EEnd [e23 (); EMinor]

/// **The incremental run is a run, with the contracts at every step, and no
/// allocation fails.**
let inc_run () : Lemma (requires pw_room /\ cok)
  (ensures run_ok pc Incremental msize ywords (es_inc ()) /\ run_hyps pc msize ywords (es_inc ()) /\
           TR.no_fail pc msize ywords (es_inc ()))
  = pre_ok (); post_ok (); c22 ();
    tail_app ic (x21 ()) (PWS.repl (ksw ())) (post ());
    nf_app (x21 ()) (PWS.repl (ksw ())) (post ());
    tail_app ic (x0 ()) (pre21 ()) (L.append (PWS.repl (ksw ())) (post ()));
    nf_app (x0 ()) (pre21 ()) (L.append (PWS.repl (ksw ())) (post ()));
    run_of ic (es_inc ());
    no_fail_of (es_inc ())
