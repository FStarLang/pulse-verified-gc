/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.RunR4 — run R4 on g5, to its first fix-up
///
/// Two ranges, cut at B's header; S = 1, Q = 0; root B.
///   z0  setup: B pushed on stack 1
///   z1  W1 pops B           z2  W1 scans A: inbox 0 full, dropped, flag 1
///   z3  W1 subtracts        z4  W1 stops        z5  W0 stops
///   z6  Main: flag 1 set; the walk passes A (white), reaches B (black),
///       whose field names A, white and below B: A is greyed and pushed
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.RunR4

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
open GC.Spec.MarkPar2.RunR3

module HeapGraph = GC.Spec.HeapGraph
module M1 = GC.Spec.MarkPar.Model

let rootsB (_: squash big) : list obj_addr = [obj_B ()]

let hB1 (_: squash big) : heap = makeGray_x (obj_B ()) (g5 ())
let hB2 (_: squash big) : heap = makeBlack_x (obj_B ()) (hB1 ())
let hB3 (_: squash big) : heap = makeGray_x vA (hB2 ())

let heapsB (_: squash big)
  : Lemma (let b = obj_B () in
           ab () (hB1 ()) /\ ab () (hB2 ()) /\ ab () (hB3 ()) /\
           color_of_object vA (g5 ()) == White /\ color_of_object b (g5 ()) == White /\
           color_of_object vA (hB1 ()) == White /\ color_of_object b (hB1 ()) == Gray /\
           color_of_object vA (hB2 ()) == White /\ color_of_object b (hB2 ()) == Black /\
           color_of_object vA (hB3 ()) == Gray /\ color_of_object b (hB3 ()) == Black)
  = let b = obj_B () in
    ab_g5 ();
    objects_g5 ();
    facts_g5 () vA; facts_g5 () b;
    makeGray_eq b (g5 ()); makeBlack_eq b (hB1 ()); makeGray_eq vA (hB2 ());
    paint () (g5 ()) b Gray;
    paint () (hB1 ()) b Black;
    paint () (hB2 ()) vA Gray

let z0 (_: squash big) : state = init (k3 ()) (g5 ()) (rootsB ())
let z1 (_: squash big) : state = step (k3 ()) (z0 ()) (W 1)
let z2 (_: squash big) : state = step (k3 ()) (z1 ()) (W 1)
let z3 (_: squash big) : state = step (k3 ()) (z2 ()) (W 1)
let z4 (_: squash big) : state = step (k3 ()) (z3 ()) (W 1)
let z5 (_: squash big) : state = step (k3 ()) (z4 ()) (W 0)
let z6 (_: squash big) : state = step (k3 ()) (z5 ()) Main

#push-options "--z3rlimit 40 --fuel 4 --ifuel 2"
let z0_eq (_: squash big)
  : Lemma (z0 () == st (hB1 ()) [blank0; w [obj_B ()] [] Loop] 1)
  = let b = obj_B () in
    heapsB (); own3 (); ab_g5 ();
    view () (g5 ());
    colors_of (g5 ()) b White;
    assert (blanks (nr (k3 ())) == [blank; blank]);
    let f0 : fx = { fh = g5 (); fws = [blank; blank]; fom = false; fn = 0 } in
    let f1 : fx = { fh = hB1 (); fws = [blank0; w [b] [] Loop]; fom = false; fn = 1 } in
    assert (darken (k3 ()) f0 b == f1);
    assert (setup (k3 ()) f0 (rootsB ()) == f1)
#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let z1_eq (_: squash big) : Lemma (z1 () == st (hB2 ()) [blank0; w [] [] (Scan (scB1 ()))] 1)
  = heapsB (); own3 (); view () (hB1 ()); z0_eq ()

let send2 (_: squash big)
  : Lemma (send (k3 ()) (st (hB2 ()) [blank0; w [] [] Finish] 1) 1 0 vA ==
           st (hB2 ()) [blank0; wf [] [] Finish true] 1)
  = ()

let z2_eq (_: squash big) : Lemma (z2 () == st (hB2 ()) [blank0; wf [] [] Finish true] 1)
  = heapsB (); own3 (); view () (hB2 ()); z1_eq ();
    let s0' = st (hB2 ()) [blank0; w [] [] Finish] 1 in
    assert (M1.next_field (scB1 ()) == None);
    send2 ();
    assert (route (k3 ()) s0' 1 vA == send (k3 ()) s0' 1 0 vA)

let z3_eq (_: squash big) : Lemma (z3 () == st (hB2 ()) [blank0; wf [] [] Loop true] 0)
  = z2_eq ()

let z4_eq (_: squash big) : Lemma (z4 () == st (hB2 ()) [blank0; wf [] [] Stopped true] 0)
  = z3_eq ()

let z5_eq (_: squash big) : Lemma (z5 () == st (hB2 ()) [w [] [] Stopped; wf [] [] Stopped true] 0)
  = z4_eq ()
#pop-options

/// The fix-up: A is white (passed), B is black and its field names A,
/// white and below B: greyed and pushed.
let y0 (_: squash big) : fx = { fh = hB2 (); fws = ws_stop; fom = false; fn = 0 }
let y1 (_: squash big) : fx = { fh = hB3 (); fws = ws_stop; fom = false; fn = 0 }
let y2 (_: squash big) : fx = { fh = hB3 (); fws = [w [vA] [] Stopped; w [] [] Stopped]; fom = false; fn = 1 }

#push-options "--z3rlimit 40 --fuel 3 --ifuel 2"
let y_child (_: squash big)
  : Lemma (fix_child (k3 ()) (obj_B ()) (y0 ()) vA == y2 ())
  = heapsB (); own3 (); view () (hB2 ());
    colors_of (hB2 ()) vA White;
    hd_address_spec vA; hd_address_spec (obj_B ());
    assert (push_fx (k3 ()) (y1 ()) vA == y2 ())

let y_walk (_: squash big)
  : Lemma (fix_obj (k3 ()) (y0 ()) vA == y0 () /\
           fix_obj (k3 ()) (y0 ()) (obj_B ()) == y2 () /\
           fix_walk (k3 ()) (y0 ()) (objs_list (hB2 ())) == y2 ())
  = let b = obj_B () in
    heapsB (); view () (hB2 ()); view () (hB3 ());
    colors_of (hB2 ()) vA White; colors_of (hB2 ()) b Black;
    y_child ();
    assert (fix_fields (k3 ()) b 1UL 1UL (y0 ()) == y2 ());
    walk_tl_ab () (k3 ()) (y2 ())

let z6_eq (_: squash big)
  : Lemma (z6 () == st (hB3 ()) [w [vA] [] Loop; w [] [] Loop] 1)
  = z5_eq (); y_walk ();
    assert (all_stopped [w [] [] Stopped; wf [] [] Stopped true]);
    assert (clear_ovf [w [] [] Stopped; wf [] [] Stopped true] == ws_stop);
    assert (restart [w [vA] [] Stopped; w [] [] Stopped] == [w [vA] [] Loop; w [] [] Loop])
#pop-options
