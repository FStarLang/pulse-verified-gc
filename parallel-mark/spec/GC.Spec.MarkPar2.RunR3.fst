/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.RunR3 — run R3 on g5
///
/// Two ranges, cut at B's header; S = 1, Q = 0; root A.
///   u0  setup: A pushed on stack 0
///   u1  W0 pops A           u2  W0 scans B: inbox 1 full, dropped, flag 0
///   u3  W0 scans field 2    u4  W0 subtracts
///   u4i, u5  W0 finds its inbox empty, reads 0, stops
///   u5i, u6  W1 the same
///   u7  Main: flag 0 set; the fix-up greys B (above A, so not pushed),
///       then reaches B and pushes it; a new round
///   u8  W1 pops B           u9  W1 scans A: inbox 0 full, dropped, flag 1
///   u10 W1 subtracts
///   u10i, u11  W1 finds its inbox empty, reads 0, stops
///   u11i, u12  W0 the same
///   u13 Main: flag 1 set; the fix-up finds nothing to push: done
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.RunR3

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
open GC.Spec.MarkPar2.RunR2

module HeapGraph = GC.Spec.HeapGraph
module M1 = GC.Spec.MarkPar.Model

let k3 (_: squash big) : cfg = { cs = [cut ()]; cap_s = 1; cap_q = 0 }

let own3 (_: squash big)
  : Lemma (own (k3 ()) vA == 0 /\ own (k3 ()) (obj_B ()) == 1 /\ nr (k3 ()) == 2 /\ valid_cfg (k3 ()))
  = hd_address_spec vA; hd_address_spec (obj_B ())

let wf (st ib: list obj_addr) (p: pc) (o: bool) : wk = { stack = st; inbox = ib; pc = p; ovf = o }

let u0 (_: squash big) : state = init (k3 ()) (g5 ()) rootsA
let u1 (_: squash big) : state = step (k3 ()) (u0 ()) (W 0)
let u2 (_: squash big) : state = step (k3 ()) (u1 ()) (W 0)
let u3 (_: squash big) : state = step (k3 ()) (u2 ()) (W 0)
let u4 (_: squash big) : state = step (k3 ()) (u3 ()) (W 0)
let u4i (_: squash big) : state = step (k3 ()) (u4 ()) (W 0)
let u5 (_: squash big) : state = step (k3 ()) (u4i ()) (W 0)
let u5i (_: squash big) : state = step (k3 ()) (u5 ()) (W 1)
let u6 (_: squash big) : state = step (k3 ()) (u5i ()) (W 1)
let u7 (_: squash big) : state = step (k3 ()) (u6 ()) Main
let u8 (_: squash big) : state = step (k3 ()) (u7 ()) (W 1)
let u9 (_: squash big) : state = step (k3 ()) (u8 ()) (W 1)
let u10 (_: squash big) : state = step (k3 ()) (u9 ()) (W 1)
let u10i (_: squash big) : state = step (k3 ()) (u10 ()) (W 1)
let u11 (_: squash big) : state = step (k3 ()) (u10i ()) (W 1)
let u11i (_: squash big) : state = step (k3 ()) (u11 ()) (W 0)
let u12 (_: squash big) : state = step (k3 ()) (u11i ()) (W 0)
let u13 (_: squash big) : state = step (k3 ()) (u12 ()) Main

#push-options "--z3rlimit 40 --fuel 4 --ifuel 2"
let u0_eq (_: squash big)
  : Lemma (u0 () == st (hA1 ()) [w [vA] [] Loop; blank0] 1)
  = heapsA (); own3 (); ab_g5 ();
    view () (g5 ());
    colors_of (g5 ()) vA White;
    assert (blanks (nr (k3 ())) == [blank; blank]);
    let f0 : fx = { fh = g5 (); fws = [blank; blank]; fom = false; fn = 0 } in
    let f1 : fx = { fh = hA1 (); fws = [w [vA] [] Loop; blank0]; fom = false; fn = 1 } in
    assert (darken (k3 ()) f0 vA == f1);
    assert (setup (k3 ()) f0 rootsA == f1)
#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let u1_eq (_: squash big) : Lemma (u1 () == st (hA2 ()) [w [] [] (Scan scA1); blank0] 1)
  = heapsA (); own3 (); view () (hA1 ()); u0_eq ()

let send2 (_: squash big)
  : Lemma (send (k3 ()) (st (hA2 ()) [w [] [] (Scan scA2); blank0] 1) 0 1 (obj_B ()) ==
           st (hA2 ()) [wf [] [] (Scan scA2) true; blank0] 1)
  = ()

let u2_eq (_: squash big) : Lemma (u2 () == st (hA2 ()) [wf [] [] (Scan scA2) true; blank0] 1)
  = heapsA (); own3 (); view () (hA2 ()); u1_eq ();
    let s0' = st (hA2 ()) [w [] [] (Scan scA2); blank0] 1 in
    send2 ();
    assert (route (k3 ()) s0' 0 vB == send (k3 ()) s0' 0 1 (obj_B ()))

let u3_eq (_: squash big) : Lemma (u3 () == st (hA2 ()) [wf [] [] Finish true; blank0] 1)
  = heapsA (); view () (hA2 ()); u2_eq ()

let u4_eq (_: squash big) : Lemma (u4 () == st (hA2 ()) [wf [] [] Loop true; blank0] 0)
  = u3_eq ()

let u4i_eq (_: squash big) : Lemma (u4i () == st (hA2 ()) [wf [] [] Idle true; blank0] 0)
  = u4_eq ()

let u5_eq (_: squash big) : Lemma (u5 () == st (hA2 ()) [wf [] [] Stopped true; blank0] 0)
  = u4i_eq ()

let u5i_eq (_: squash big) : Lemma (u5i () == st (hA2 ()) [wf [] [] Stopped true; w [] [] Idle] 0)
  = u5_eq ()

let u6_eq (_: squash big) : Lemma (u6 () == st (hA2 ()) [wf [] [] Stopped true; w [] [] Stopped] 0)
  = u5i_eq ()
#pop-options

/// The first fix-up: A is black and its first field names B, white and
/// above A: B is greyed, not pushed.  Then the walk reaches B, grey: pushed.
let ws_stop : list wk = [w [] [] Stopped; w [] [] Stopped]

let v7_0 (_: squash big) : fx = { fh = hA2 (); fws = ws_stop; fom = false; fn = 0 }
let v7_1 (_: squash big) : fx = { fh = hA3 (); fws = ws_stop; fom = false; fn = 0 }
let v7_2 (_: squash big) : fx = { fh = hA3 (); fws = [w [] [] Stopped; w [obj_B ()] [] Stopped]; fom = false; fn = 1 }

#push-options "--z3rlimit 40 --fuel 3 --ifuel 2"
let v7_child (_: squash big)
  : Lemma (fix_child (k3 ()) vA (v7_0 ()) vB == v7_1 ())
  = heapsA (); view () (hA2 ());
    colors_of (hA2 ()) (obj_B ()) White;
    hd_address_spec vA; hd_address_spec (obj_B ())

let v7_walk (_: squash big)
  : Lemma (fix_obj (k3 ()) (v7_0 ()) vA == v7_1 () /\
           fix_obj (k3 ()) (v7_1 ()) (obj_B ()) == v7_2 () /\
           fix_walk (k3 ()) (v7_0 ()) (objs_list (hA2 ())) == v7_2 ())
  = let b = obj_B () in
    heapsA (); own3 (); view () (hA2 ()); view () (hA3 ());
    colors_of (hA2 ()) vA Black; colors_of (hA3 ()) b Gray;
    v7_child ();
    assert (fix_child (k3 ()) vA (v7_1 ()) 0UL == v7_1 ());
    assert (fix_fields (k3 ()) vA 2UL 2UL (v7_1 ()) == v7_1 ());
    assert (fix_fields (k3 ()) vA 1UL 2UL (v7_0 ()) == v7_1 ());
    walk_tl_ab () (k3 ()) (v7_2 ())

let u7_eq (_: squash big)
  : Lemma (u7 () == st (hA3 ()) [w [] [] Loop; w [obj_B ()] [] Loop] 1)
  = u6_eq (); v7_walk ();
    assert (all_stopped [wf [] [] Stopped true; w [] [] Stopped]);
    assert (clear_ovf [wf [] [] Stopped true; w [] [] Stopped] == ws_stop);
    assert (restart [w [] [] Stopped; w [obj_B ()] [] Stopped] == [w [] [] Loop; w [obj_B ()] [] Loop])
#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let u8_eq (_: squash big) : Lemma (u8 () == st (hA4 ()) [w [] [] Loop; w [] [] (Scan (scB1 ()))] 1)
  = heapsA (); view () (hA3 ()); u7_eq ()

let send9 (_: squash big)
  : Lemma (send (k3 ()) (st (hA4 ()) [w [] [] Loop; w [] [] Finish] 1) 1 0 vA ==
           st (hA4 ()) [w [] [] Loop; wf [] [] Finish true] 1)
  = ()

let u9_eq (_: squash big) : Lemma (u9 () == st (hA4 ()) [w [] [] Loop; wf [] [] Finish true] 1)
  = heapsA (); own3 (); view () (hA4 ()); u8_eq ();
    let s0' = st (hA4 ()) [w [] [] Loop; w [] [] Finish] 1 in
    assert (M1.next_field (scB1 ()) == None);
    send9 ();
    assert (route (k3 ()) s0' 1 vA == send (k3 ()) s0' 1 0 vA)

let u10_eq (_: squash big) : Lemma (u10 () == st (hA4 ()) [w [] [] Loop; wf [] [] Loop true] 0)
  = u9_eq ()

let u10i_eq (_: squash big) : Lemma (u10i () == st (hA4 ()) [w [] [] Loop; wf [] [] Idle true] 0)
  = u10_eq ()

let u11_eq (_: squash big) : Lemma (u11 () == st (hA4 ()) [w [] [] Loop; wf [] [] Stopped true] 0)
  = u10i_eq ()

let u11i_eq (_: squash big) : Lemma (u11i () == st (hA4 ()) [w [] [] Idle; wf [] [] Stopped true] 0)
  = u11_eq ()

let u12_eq (_: squash big) : Lemma (u12 () == st (hA4 ()) [w [] [] Stopped; wf [] [] Stopped true] 0)
  = u11i_eq ()
#pop-options

/// The second fix-up: A and B are black and point to each other; nothing
/// to push.
let v13 (_: squash big) : fx = { fh = hA4 (); fws = ws_stop; fom = false; fn = 0 }

#push-options "--z3rlimit 40 --fuel 3 --ifuel 2"
let v13_walk (_: squash big)
  : Lemma (fix_obj (k3 ()) (v13 ()) vA == v13 () /\ fix_obj (k3 ()) (v13 ()) (obj_B ()) == v13 () /\
           fix_walk (k3 ()) (v13 ()) (objs_list (hA4 ())) == v13 ())
  = let b = obj_B () in
    heapsA (); view () (hA4 ());
    colors_of (hA4 ()) vA Black; colors_of (hA4 ()) b Black;
    assert (fix_child (k3 ()) vA (v13 ()) vB == v13 ());
    assert (fix_child (k3 ()) vA (v13 ()) 0UL == v13 ());
    assert (fix_fields (k3 ()) vA 2UL 2UL (v13 ()) == v13 ());
    assert (fix_fields (k3 ()) vA 1UL 2UL (v13 ()) == v13 ());
    assert (fix_child (k3 ()) b (v13 ()) vA == v13 ());
    assert (fix_fields (k3 ()) b 1UL 1UL (v13 ()) == v13 ());
    walk_tl_ab () (k3 ()) (v13 ())

let u13_eq (_: squash big)
  : Lemma (u13 () == { st (hA4 ()) ws_stop 0 with finished = true })
  = u12_eq (); v13_walk ();
    assert (all_stopped [w [] [] Stopped; wf [] [] Stopped true]);
    assert (clear_ovf [w [] [] Stopped; wf [] [] Stopped true] == ws_stop)
#pop-options
