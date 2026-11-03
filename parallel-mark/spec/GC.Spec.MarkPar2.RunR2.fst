/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.RunR2 — run R2 on g5
///
/// Two ranges, cut at B's header (A is worker 0's, B worker 1's); S = 1,
/// Q = 1; root A.
///   s0  setup: A pushed on stack 0
///   s1  W0 pops A                      s2  W0 scans B: sends it to 1
///   s3  W0 scans field 2               s4  W0 subtracts
///   s5  W1 takes B                     s6  W1 accepts B: greys, pushes
///   s7  W1 subtracts                   s8  W1 pops B
///   s8i W0 finds its inbox empty (a spin step: the counter is 1)
///   s9  W1 scans A: sends it to 0, which is idle
///   s10 W1 subtracts
///   s10i W0 reads 1: back to Loop, with A waiting (a message that came
///       in between its take and its read)
///   s11 W0 takes A                     s12 W0 accepts A: black, nothing
///   s13 W0 subtracts
///   s13i W0 finds its inbox empty      s14 W0 reads 0 and stops
///   s14i W1 finds its inbox empty      s15 W1 reads 0 and stops
///   s16 Main: no flag: done
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.RunR2

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.MarkPar.Exec
open GC.Spec.MarkPar.Recolour
open GC.Spec.MarkPar.Witness
open GC.Spec.MarkPar2.Witness
open GC.Spec.MarkPar2.Model
open GC.Spec.MarkPar2.Runs

module HeapGraph = GC.Spec.HeapGraph
module M1 = GC.Spec.MarkPar.Model

let cut (_: squash big) : nat = za + 24
let k2 (_: squash big) : cfg = { cs = [cut ()]; cap_s = 1; cap_q = 1 }
let rootsA : list obj_addr = [vA]

let own2 (_: squash big)
  : Lemma (own (k2 ()) vA == 0 /\ own (k2 ()) (obj_B ()) == 1 /\ nr (k2 ()) == 2 /\ valid_cfg (k2 ()))
  = hd_address_spec vA; hd_address_spec (obj_B ())

/// ---------------------------------------------------------------------------
/// Heaps: A grey; A black; then B grey; then B black
/// ---------------------------------------------------------------------------

let hA1 (_: squash big) : heap = makeGray_x vA (g5 ())
let hA2 (_: squash big) : heap = makeBlack_x vA (hA1 ())
let hA3 (_: squash big) : heap = makeGray_x (obj_B ()) (hA2 ())
let hA4 (_: squash big) : heap = makeBlack_x (obj_B ()) (hA3 ())

let heapsA (_: squash big)
  : Lemma (let b = obj_B () in
           ab () (hA1 ()) /\ ab () (hA2 ()) /\ ab () (hA3 ()) /\ ab () (hA4 ()) /\
           color_of_object vA (g5 ()) == White /\ color_of_object b (g5 ()) == White /\
           color_of_object vA (hA1 ()) == Gray /\ color_of_object b (hA1 ()) == White /\
           color_of_object vA (hA2 ()) == Black /\ color_of_object b (hA2 ()) == White /\
           color_of_object vA (hA3 ()) == Black /\ color_of_object b (hA3 ()) == Gray /\
           color_of_object vA (hA4 ()) == Black /\ color_of_object b (hA4 ()) == Black)
  = let b = obj_B () in
    ab_g5 ();
    objects_g5 ();
    facts_g5 () vA; facts_g5 () b;
    makeGray_eq vA (g5 ()); makeBlack_eq vA (hA1 ());
    makeGray_eq b (hA2 ()); makeBlack_eq b (hA3 ());
    paint () (g5 ()) vA Gray;
    paint () (hA1 ()) vA Black;
    paint () (hA2 ()) b Gray;
    paint () (hA3 ()) b Black

/// ---------------------------------------------------------------------------
/// States
/// ---------------------------------------------------------------------------

let w (st ib: list obj_addr) (p: pc) : wk = { stack = st; inbox = ib; pc = p; ovf = false }

let scA1 : M1.scanning = { M1.sobj = vA; M1.snext = 1UL; M1.sws = 2UL }
let scA2 : M1.scanning = { M1.sobj = vA; M1.snext = 2UL; M1.sws = 2UL }
let scB1 (_: squash big) : M1.scanning = { M1.sobj = obj_B (); M1.snext = 1UL; M1.sws = 1UL }

let st (h: heap) (ws: list wk) (n: nat) : state =
  { heap = h; wks = ws; count = n; ovf_main = false; finished = false }

let t0 (_: squash big) : state = init (k2 ()) (g5 ()) rootsA
let t1 (_: squash big) : state = step (k2 ()) (t0 ()) (W 0)
let t2 (_: squash big) : state = step (k2 ()) (t1 ()) (W 0)
let t3 (_: squash big) : state = step (k2 ()) (t2 ()) (W 0)
let t4 (_: squash big) : state = step (k2 ()) (t3 ()) (W 0)
let t5 (_: squash big) : state = step (k2 ()) (t4 ()) (W 1)
let t6 (_: squash big) : state = step (k2 ()) (t5 ()) (W 1)
let t7 (_: squash big) : state = step (k2 ()) (t6 ()) (W 1)
let t8 (_: squash big) : state = step (k2 ()) (t7 ()) (W 1)
let t8i (_: squash big) : state = step (k2 ()) (t8 ()) (W 0)
let t9 (_: squash big) : state = step (k2 ()) (t8i ()) (W 1)
let t10 (_: squash big) : state = step (k2 ()) (t9 ()) (W 1)
let t10i (_: squash big) : state = step (k2 ()) (t10 ()) (W 0)
let t11 (_: squash big) : state = step (k2 ()) (t10i ()) (W 0)
let t12 (_: squash big) : state = step (k2 ()) (t11 ()) (W 0)
let t13 (_: squash big) : state = step (k2 ()) (t12 ()) (W 0)
let t13i (_: squash big) : state = step (k2 ()) (t13 ()) (W 0)
let t14 (_: squash big) : state = step (k2 ()) (t13i ()) (W 0)
let t14i (_: squash big) : state = step (k2 ()) (t14 ()) (W 1)
let t15 (_: squash big) : state = step (k2 ()) (t14i ()) (W 1)
let t16 (_: squash big) : state = step (k2 ()) (t15 ()) Main

let blank0 : wk = w [] [] Loop

#push-options "--z3rlimit 40 --fuel 4 --ifuel 2"
let t0_eq (_: squash big)
  : Lemma (t0 () == st (hA1 ()) [w [vA] [] Loop; blank0] 1)
  = heapsA (); own2 (); ab_g5 ();
    view () (g5 ());
    colors_of (g5 ()) vA White;
    assert (blanks (nr (k2 ())) == [blank; blank]);
    let f0 : fx = { fh = g5 (); fws = [blank; blank]; fom = false; fn = 0 } in
    let f1 : fx = { fh = hA1 (); fws = [w [vA] [] Loop; blank0]; fom = false; fn = 1 } in
    assert (darken (k2 ()) f0 vA == f1);
    assert (setup (k2 ()) f0 rootsA == f1)
#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let t1_eq (_: squash big) : Lemma (t1 () == st (hA2 ()) [w [] [] (Scan scA1); blank0] 1)
  = heapsA (); own2 (); view () (hA1 ()); t0_eq ()

let t2_eq (_: squash big) : Lemma (t2 () == st (hA2 ()) [w [] [] (Scan scA2); w [] [obj_B ()] Loop] 2)
  = heapsA (); own2 (); view () (hA2 ()); t1_eq ();
    let s0' = st (hA2 ()) [w [] [] (Scan scA2); blank0] 1 in
    assert (send (k2 ()) s0' 0 1 (obj_B ()) == st (hA2 ()) [w [] [] (Scan scA2); w [] [obj_B ()] Loop] 2);
    assert (route (k2 ()) s0' 0 vB == send (k2 ()) s0' 0 1 (obj_B ()))

let t3_eq (_: squash big) : Lemma (t3 () == st (hA2 ()) [w [] [] Finish; w [] [obj_B ()] Loop] 2)
  = heapsA (); view () (hA2 ()); t2_eq ()

let t4_eq (_: squash big) : Lemma (t4 () == st (hA2 ()) [w [] [] Loop; w [] [obj_B ()] Loop] 1)
  = t3_eq ()

let t5_eq (_: squash big) : Lemma (t5 () == st (hA2 ()) [w [] [] Loop; w [] [] (Got (obj_B ()))] 1)
  = t4_eq ()

let t6_eq (_: squash big) : Lemma (t6 () == st (hA3 ()) [w [] [] Loop; w [obj_B ()] [] Finish] 2)
  = heapsA (); own2 (); view () (hA2 ()); t5_eq ();
    colors_of (hA2 ()) (obj_B ()) White;
    let s0' = st (hA2 ()) [w [] [] Loop; w [] [] Finish] 1 in
    assert (grey_push (k2 ()) s0' 1 (obj_B ()) == st (hA3 ()) [w [] [] Loop; w [obj_B ()] [] Finish] 2);
    assert (accept (k2 ()) s0' 1 (obj_B ()) == grey_push (k2 ()) s0' 1 (obj_B ()))

let t7_eq (_: squash big) : Lemma (t7 () == st (hA3 ()) [w [] [] Loop; w [obj_B ()] [] Loop] 1)
  = t6_eq ()

let t8_eq (_: squash big) : Lemma (t8 () == st (hA4 ()) [w [] [] Loop; w [] [] (Scan (scB1 ()))] 1)
  = heapsA (); view () (hA3 ()); t7_eq ()

let t8i_eq (_: squash big) : Lemma (t8i () == st (hA4 ()) [w [] [] Idle; w [] [] (Scan (scB1 ()))] 1)
  = t8_eq ()

let send9 (_: squash big)
  : Lemma (send (k2 ()) (st (hA4 ()) [w [] [] Idle; w [] [] Finish] 1) 1 0 vA ==
           st (hA4 ()) [w [] [vA] Idle; w [] [] Finish] 2)
  = ()

let t9_eq (_: squash big) : Lemma (t9 () == st (hA4 ()) [w [] [vA] Idle; w [] [] Finish] 2)
  = heapsA (); own2 (); view () (hA4 ()); t8i_eq ();
    let s0' = st (hA4 ()) [w [] [] Idle; w [] [] Finish] 1 in
    assert (M1.next_field (scB1 ()) == None);
    send9 ();
    assert (route (k2 ()) s0' 1 vA == send (k2 ()) s0' 1 0 vA)

let t10_eq (_: squash big) : Lemma (t10 () == st (hA4 ()) [w [] [vA] Idle; w [] [] Loop] 1)
  = t9_eq ()

let t10i_eq (_: squash big) : Lemma (t10i () == st (hA4 ()) [w [] [vA] Loop; w [] [] Loop] 1)
  = t10_eq ()

let t11_eq (_: squash big) : Lemma (t11 () == st (hA4 ()) [w [] [] (Got vA); w [] [] Loop] 1)
  = t10i_eq ()

let t12_eq (_: squash big) : Lemma (t12 () == st (hA4 ()) [w [] [] Finish; w [] [] Loop] 1)
  = heapsA (); own2 (); view () (hA4 ()); t11_eq ();
    colors_of (hA4 ()) vA Black;
    let s0' = st (hA4 ()) [w [] [] Finish; w [] [] Loop] 1 in
    assert (grey_push (k2 ()) s0' 0 vA == s0');
    assert (accept (k2 ()) s0' 0 vA == s0')

let t13_eq (_: squash big) : Lemma (t13 () == st (hA4 ()) [w [] [] Loop; w [] [] Loop] 0)
  = t12_eq ()

let t13i_eq (_: squash big) : Lemma (t13i () == st (hA4 ()) [w [] [] Idle; w [] [] Loop] 0)
  = t13_eq ()

let t14_eq (_: squash big) : Lemma (t14 () == st (hA4 ()) [w [] [] Stopped; w [] [] Loop] 0)
  = t13i_eq ()

let t14i_eq (_: squash big) : Lemma (t14i () == st (hA4 ()) [w [] [] Stopped; w [] [] Idle] 0)
  = t14_eq ()

let t15_eq (_: squash big) : Lemma (t15 () == st (hA4 ()) [w [] [] Stopped; w [] [] Stopped] 0)
  = t14i_eq ()

#pop-options

#push-options "--z3rlimit 40 --fuel 3 --ifuel 2"
let t16_eq (_: squash big)
  : Lemma (t16 () == { st (hA4 ()) [w [] [] Stopped; w [] [] Stopped] 0 with finished = true })
  = t15_eq ();
    let s15 = st (hA4 ()) [w [] [] Stopped; w [] [] Stopped] 0 in
    assert (all_stopped s15.wks);
    assert (flagged s15 == false);
    assert (main_step (k2 ()) s15 == { s15 with finished = true })
#pop-options
