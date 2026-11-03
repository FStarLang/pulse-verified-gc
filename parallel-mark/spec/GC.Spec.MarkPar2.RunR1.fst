/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.RunR1 — run R1 on g5
///
/// One range, S = 1, Q = 0, roots [A; B].
///   s0  setup: A pushed; B greyed, the stack full: overflow_main
///   s1  W0 pops A (black)            s2  W0 scans A's field 1, B: grey
///   s3  W0 scans field 2, not a pointer                s4  W0 subtracts
///   s4i W0 finds its inbox empty       s5  W0 reads 0 and stops
///   s6  Main: overflow_main set; the fix-up pushes B; a new round
///   s7  W0 pops B (black)            s8  W0 scans B's field, A: black
///   s9  W0 subtracts                 s9i W0 finds its inbox empty
///   s10 W0 reads 0 and stops
///   s11 Main: no flag: done
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.RunR1

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

let k1 : cfg = { cs = []; cap_s = 1; cap_q = 0 }
let roots1 (_: squash big) : list obj_addr = [vA; obj_B ()]

let own1 (x: obj_addr) : Lemma (own k1 x == 0 /\ nr k1 == 1 /\ valid_cfg k1) = ()

/// ---------------------------------------------------------------------------
/// Heaps
/// ---------------------------------------------------------------------------

let h1 (_: squash big) : heap = makeGray_x vA (g5 ())
let h2 (_: squash big) : heap = makeGray_x (obj_B ()) (h1 ())
let h3 (_: squash big) : heap = makeBlack_x vA (h2 ())
let h4 (_: squash big) : heap = makeBlack_x (obj_B ()) (h3 ())

let heaps (_: squash big)
  : Lemma (let b = obj_B () in
           ab () (g5 ()) /\ ab () (h1 ()) /\ ab () (h2 ()) /\ ab () (h3 ()) /\ ab () (h4 ()) /\
           color_of_object vA (g5 ()) == White /\ color_of_object b (g5 ()) == White /\
           color_of_object vA (h1 ()) == Gray /\ color_of_object b (h1 ()) == White /\
           color_of_object vA (h2 ()) == Gray /\ color_of_object b (h2 ()) == Gray /\
           color_of_object vA (h3 ()) == Black /\ color_of_object b (h3 ()) == Gray /\
           color_of_object vA (h4 ()) == Black /\ color_of_object b (h4 ()) == Black)
  = let b = obj_B () in
    ab_g5 ();
    objects_g5 ();
    facts_g5 () vA; facts_g5 () b;
    makeGray_eq vA (g5 ()); makeGray_eq b (h1 ());
    makeBlack_eq vA (h2 ()); makeBlack_eq b (h3 ());
    paint () (g5 ()) vA Gray;
    paint () (h1 ()) b Gray;
    paint () (h2 ()) vA Black;
    paint () (h3 ()) b Black

/// ---------------------------------------------------------------------------
/// States
/// ---------------------------------------------------------------------------

let wk_of_l (st: list obj_addr) (p: pc) : wk = { stack = st; inbox = []; pc = p; ovf = false }

let scA1 : M1.scanning = { M1.sobj = vA; M1.snext = 1UL; M1.sws = 2UL }
let scA2 : M1.scanning = { M1.sobj = vA; M1.snext = 2UL; M1.sws = 2UL }
let scB1 (_: squash big) : M1.scanning = { M1.sobj = obj_B (); M1.snext = 1UL; M1.sws = 1UL }

let s0 (_: squash big) : state = init k1 (g5 ()) (roots1 ())
let s1 (_: squash big) : state = step k1 (s0 ()) (W 0)
let s2 (_: squash big) : state = step k1 (s1 ()) (W 0)
let s3 (_: squash big) : state = step k1 (s2 ()) (W 0)
let s4 (_: squash big) : state = step k1 (s3 ()) (W 0)
let s4i (_: squash big) : state = step k1 (s4 ()) (W 0)
let s5 (_: squash big) : state = step k1 (s4i ()) (W 0)
let s6 (_: squash big) : state = step k1 (s5 ()) Main
let s7 (_: squash big) : state = step k1 (s6 ()) (W 0)
let s8 (_: squash big) : state = step k1 (s7 ()) (W 0)
let s9 (_: squash big) : state = step k1 (s8 ()) (W 0)
let s9i (_: squash big) : state = step k1 (s9 ()) (W 0)
let s10 (_: squash big) : state = step k1 (s9i ()) (W 0)
let s11 (_: squash big) : state = step k1 (s10 ()) Main

let sched1 : list event = [W 0; W 0; W 0; W 0; W 0; W 0; Main; W 0; W 0; W 0; W 0; W 0; Main]

#push-options "--z3rlimit 40 --fuel 4 --ifuel 2"
let s0_eq (_: squash big)
  : Lemma (s0 () == { heap = h2 (); wks = [wk_of_l [vA] Loop]; count = 1; ovf_main = true; finished = false })
  = let b = obj_B () in
    heaps ();
    view () (g5 ()); view () (h1 ());
    colors_of (g5 ()) vA White; colors_of (h1 ()) b White;
    assert (blanks (nr k1) == [blank]);
    let f0 : fx = { fh = g5 (); fws = [blank]; fom = false; fn = 0 } in
    let f1 : fx = { fh = h1 (); fws = [wk_of_l [vA] Loop]; fom = false; fn = 1 } in
    let f2 : fx = { fh = h2 (); fws = [wk_of_l [vA] Loop]; fom = true; fn = 1 } in
    assert (darken k1 f0 vA == f1);
    assert (darken k1 f1 b == f2);
    assert (setup k1 f0 (roots1 ()) == f2)
#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let s1_eq (_: squash big)
  : Lemma (s1 () == { heap = h3 (); wks = [wk_of_l [] (Scan scA1)]; count = 1; ovf_main = true; finished = false })
  = heaps (); view () (h2 ()); s0_eq ()

let s2_eq (_: squash big)
  : Lemma (s2 () == { heap = h3 (); wks = [wk_of_l [] (Scan scA2)]; count = 1; ovf_main = true; finished = false })
  = heaps (); view () (h3 ()); s1_eq ();
    colors_of (h3 ()) (obj_B ()) Gray

let s3_eq (_: squash big)
  : Lemma (s3 () == { heap = h3 (); wks = [wk_of_l [] Finish]; count = 1; ovf_main = true; finished = false })
  = heaps (); view () (h3 ()); s2_eq ()

let s4_eq (_: squash big)
  : Lemma (s4 () == { heap = h3 (); wks = [wk_of_l [] Loop]; count = 0; ovf_main = true; finished = false })
  = s3_eq ()

let s4i_eq (_: squash big)
  : Lemma (s4i () == { heap = h3 (); wks = [wk_of_l [] Idle]; count = 0; ovf_main = true; finished = false })
  = s4_eq ()

let s5_eq (_: squash big)
  : Lemma (s5 () == { heap = h3 (); wks = [wk_of_l [] Stopped]; count = 0; ovf_main = true; finished = false })
  = s4i_eq ()
#pop-options

/// The fix-up of the first Main.
let f6_0 (_: squash big) : fx = { fh = h3 (); fws = [wk_of_l [] Stopped]; fom = false; fn = 0 }
let f6_2 (_: squash big) : fx = { fh = h3 (); fws = [wk_of_l [obj_B ()] Stopped]; fom = false; fn = 1 }

#push-options "--z3rlimit 40 --fuel 3 --ifuel 2"
let f6_walk (_: squash big)
  : Lemma (fix_obj k1 (f6_0 ()) vA == f6_0 () /\
           fix_obj k1 (f6_0 ()) (obj_B ()) == f6_2 () /\
           fix_walk k1 (f6_0 ()) (objs_list (h3 ())) == f6_2 ())
  = let b = obj_B () in
    heaps (); view () (h3 ());
    colors_of (h3 ()) vA Black; colors_of (h3 ()) b Gray;
    assert (fix_child k1 vA (f6_0 ()) vB == f6_0 ());
    assert (fix_child k1 vA (f6_0 ()) 0UL == f6_0 ());
    assert (fix_fields k1 vA 2UL 2UL (f6_0 ()) == f6_0 ());
    assert (fix_fields k1 vA 1UL 2UL (f6_0 ()) == f6_0 ());
    walk_tl_ab () k1 (f6_2 ())
#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let s6_eq (_: squash big)
  : Lemma (s6 () == { heap = h3 (); wks = [wk_of_l [obj_B ()] Loop]; count = 1; ovf_main = false; finished = false })
  = s5_eq (); f6_walk ();
    assert (clear_ovf [wk_of_l [] Stopped] == [wk_of_l [] Stopped]);
    assert (restart [wk_of_l [obj_B ()] Stopped] == [wk_of_l [obj_B ()] Loop])

let s7_eq (_: squash big)
  : Lemma (s7 () == { heap = h4 (); wks = [wk_of_l [] (Scan (scB1 ()))]; count = 1; ovf_main = false; finished = false })
  = heaps (); view () (h3 ()); s6_eq ()

let s8_eq (_: squash big)
  : Lemma (s8 () == { heap = h4 (); wks = [wk_of_l [] Finish]; count = 1; ovf_main = false; finished = false })
  = heaps (); view () (h4 ()); s7_eq ();
    colors_of (h4 ()) vA Black;
    let t : state = { heap = h4 (); wks = [wk_of_l [] Finish]; count = 1; ovf_main = false; finished = false } in
    assert (grey_push k1 t 0 vA == t);
    assert (accept k1 t 0 vA == t);
    assert (route k1 t 0 vA == t);
    assert (M1.next_field (scB1 ()) == None)

let s9_eq (_: squash big)
  : Lemma (s9 () == { heap = h4 (); wks = [wk_of_l [] Loop]; count = 0; ovf_main = false; finished = false })
  = s8_eq ()

let s9i_eq (_: squash big)
  : Lemma (s9i () == { heap = h4 (); wks = [wk_of_l [] Idle]; count = 0; ovf_main = false; finished = false })
  = s9_eq ()

let s10_eq (_: squash big)
  : Lemma (s10 () == { heap = h4 (); wks = [wk_of_l [] Stopped]; count = 0; ovf_main = false; finished = false })
  = s9i_eq ()

let s11_eq (_: squash big)
  : Lemma (s11 () == { heap = h4 (); wks = [wk_of_l [] Stopped]; count = 0; ovf_main = false; finished = true })
  = s10_eq ()
#pop-options

let run1_eq (_: squash big)
  : Lemma (run k1 (g5 ()) (roots1 ()) sched1 == s11 ())
  = assert (run k1 (g5 ()) (roots1 ()) sched1 == s11 ())
      by (FStar.Tactics.V2.norm [delta_only [`%run; `%run_from; `%sched1; `%s0; `%s1; `%s2; `%s3; `%s4; `%s4i;
                                               `%s5; `%s6; `%s7; `%s8; `%s9; `%s9i; `%s10; `%s11];
                                  zeta; iota];
          FStar.Tactics.V2.trefl ())
