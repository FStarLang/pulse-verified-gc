/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.WitnessRun — concrete runs of the model on g2
///
/// Two ranges, cut at B's header, so A is worker 0's and B is worker 1's.
///
/// Run 1, root A:
///     Take 0; Pop 0; Scan 0; Scan 0; Deliver 0; Take 1; Pop 1; Scan 1
/// greys and blackens A, sends B to worker 1 when scanning A's first field,
/// passes A's second field (not a pointer), and greys, blackens and scans B
/// there.  It ends quiescent.
///
/// Run 2, roots A and B:
///     Take 0; Take 1; Pop 0; Pop 1; Scan 0; Deliver 0; Take 1
/// has both workers part-way through an object at once, and ends with a
/// Take that finds B already black.
///
/// Run 3, root A, one range:
///     Take 0; Pop 0; Scan 0
/// greys B in worker 0's own range when scanning A.
///
/// Each state is given with its shape, for the vacuity checks.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar.WitnessRun

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
open GC.Spec.MarkPar.Model
open GC.Spec.MarkPar.Recolour
open GC.Spec.MarkPar.Witness

module HeapGraph = GC.Spec.HeapGraph
module Own = GC.Spec.MarkPar.Own

let cut : nat = za + 24
let cs1 : list nat = [cut]
let cs0 : list nat = []
let roots1 : list obj_addr = [vA]
let roots2 (_: squash big) : list obj_addr = [vA; obj_B ()]

let owners (_: squash big)
  : Lemma (owner cs1 vA == 0 /\ owner cs1 (obj_B ()) == 1 /\ valid_cuts cs1 /\
           owner cs0 vA == 0 /\ owner cs0 (obj_B ()) == 0 /\ valid_cuts cs0)
  = hd_address_spec vA; hd_address_spec (obj_B ())

let idle_w : worker = { work = []; inbox = []; scan = None }

let scA1 : scanning = { sobj = vA; snext = 1UL; sws = 2UL }
let scA2 : scanning = { sobj = vA; snext = 2UL; sws = 2UL }
let scB1 (_: squash big) : scanning = { sobj = obj_B (); snext = 1UL; sws = 1UL }

/// ---------------------------------------------------------------------------
/// Heaps
/// ---------------------------------------------------------------------------

let h1 : heap = makeGray_x vA g2
let h2 : heap = makeBlack_x vA h1
let h6 (_: squash big) : heap = makeGray_x (obj_B ()) h2
let h7 (_: squash big) : heap = makeBlack_x (obj_B ()) (h6 ())
let hb2 (_: squash big) : heap = makeGray_x (obj_B ()) h1
let hb3 (_: squash big) : heap = makeBlack_x vA (hb2 ())
let hb4 (_: squash big) : heap = makeBlack_x (obj_B ()) (hb3 ())

/// One colour change on a recoloured heap: x gets c, y keeps its colour.
let paint (h: heap) (x y: obj_addr) (c: color)
  : Lemma (requires recoloured g2 h /\ Seq.mem x (objects zero_addr g2) /\ ~(is_blue x h) /\
                    c <> Blue /\ x <> y)
          (ensures recoloured g2 (set_object_color x h c) /\
                   color_of_object x (set_object_color x h c) == c /\
                   color_of_object y (set_object_color x h c) == color_of_object y h)
  = recoloured_set g2 h x c;
    color_of_object_spec x (set_object_color x h c);
    if c = Gray then begin makeGray_eq x h; makeGray_spec x h end
    else if c = Black then begin makeBlack_eq x h; makeBlack_spec x h end
    else begin makeWhite_eq x h; makeWhite_spec x h end;
    read_write_same h (hd_address x) (colorHeader (read_word h (hd_address x)) c);
    colorHeader_getColor (read_word h (hd_address x)) c;
    color_change_preserves_other_color x y h c

let col (x: obj_addr) (h: heap) (c: color)
  : Lemma (requires color_of_object x h == c)
          (ensures (is_white x h <==> c = White) /\ (is_gray x h <==> c = Gray) /\
                   (is_black x h <==> c = Black) /\ (is_blue x h <==> c = Blue))
  = is_white_iff x h; is_gray_iff x h; is_black_iff x h; is_blue_iff x h

#push-options "--z3rlimit 40"
let heaps (_: squash big)
  : Lemma (let b = obj_B () in
           recoloured g2 h1 /\ recoloured g2 h2 /\ recoloured g2 (h6 ()) /\ recoloured g2 (h7 ()) /\
           recoloured g2 (hb2 ()) /\ recoloured g2 (hb3 ()) /\ recoloured g2 (hb4 ()) /\
           color_of_object vA g2 == White /\ color_of_object b g2 == White /\
           color_of_object vA h1 == Gray /\ color_of_object b h1 == White /\
           color_of_object vA h2 == Black /\ color_of_object b h2 == White /\
           color_of_object vA (h6 ()) == Black /\ color_of_object b (h6 ()) == Gray /\
           color_of_object vA (h7 ()) == Black /\ color_of_object b (h7 ()) == Black /\
           color_of_object vA (hb2 ()) == Gray /\ color_of_object b (hb2 ()) == Gray /\
           color_of_object vA (hb3 ()) == Black /\ color_of_object b (hb3 ()) == Gray /\
           color_of_object vA (hb4 ()) == Black /\ color_of_object b (hb4 ()) == Black)
  = let b = obj_B () in
    g2_pre ();
    recoloured_refl g2;
    objects_g2 ();
    facts_g2 () vA; facts_g2 () b;
    makeGray_eq vA g2; makeBlack_eq vA h1;
    makeGray_eq b h2; makeBlack_eq b (h6 ());
    makeGray_eq b h1; makeBlack_eq vA (hb2 ()); makeBlack_eq b (hb3 ());
    paint g2 vA b Gray;        col vA h1 Gray;
    paint h1 vA b Black;
    paint h2 b vA Gray;        col b h2 White;
    paint (h6 ()) b vA Black;  col b (h6 ()) Gray;
    paint h1 b vA Gray;        col b h1 White;
    paint (hb2 ()) vA b Black; col vA (hb2 ()) Gray;
    paint (hb3 ()) b vA Black; col b (hb3 ()) Gray
#pop-options

/// Reads in any recoloured heap: A's fields and B's.
let reads (h: heap)
  : Lemma (requires big /\ recoloured g2 h)
          (ensures (let b = obj_B () in
                    get_field_x h vA 1UL == vB /\ get_field_x h vA 2UL == 0UL /\
                    get_field_x h b 1UL == 0UL /\
                    HeapGraph.is_pointer_field vB /\ ~(HeapGraph.is_pointer_field 0UL) /\
                    resolve_x b h == b /\ resolve_x vA h == vA /\
                    wosize_x vA h == 2UL /\ wosize_x b h == 1UL /\
                    is_no_scan_x vA h == false /\ is_no_scan_x b h == false))
  = let b = obj_B () in
    objects_g2 ();
    facts_g2 () vA; facts_g2 () b;
    fields_g2 ();
    resolve_non_infix b g2; resolve_non_infix vA g2;
    recoloured_wosize g2 h vA; recoloured_wosize g2 h b;
    recoloured_no_scan g2 h vA; recoloured_no_scan g2 h b

let col_facts (_: squash big) (h: heap) (ca cb: color)
  : Lemma (requires color_of_object vA h == ca /\ color_of_object (obj_B ()) h == cb)
          (ensures is_white_x vA h == (ca = White) /\ is_white_x (obj_B ()) h == (cb = White))
  = col vA h ca; col (obj_B ()) h cb

/// ---------------------------------------------------------------------------
/// Run 1
/// ---------------------------------------------------------------------------

let sched1 : list event = [Take 0; Pop 0; Scan 0; Scan 0; Deliver 0; Take 1; Pop 1; Scan 1]

let a0 = init cs1 g2 roots1
let a1 = step cs1 a0 (Take 0)
let a2 = step cs1 a1 (Pop 0)
let a3 = step cs1 a2 (Scan 0)
let a4 = step cs1 a3 (Scan 0)
let a5 = step cs1 a4 (Deliver 0)
let a6 = step cs1 a5 (Take 1)
let a7 = step cs1 a6 (Pop 1)
let a8 = step cs1 a7 (Scan 1)

#push-options "--z3rlimit 40 --fuel 3 --ifuel 1"
let a01 (_: squash big)
  : Lemma (a0.heap == g2 /\ a0.net == [] /\ a0.workers == [{ idle_w with inbox = [vA] }; idle_w] /\
           a1.heap == h1 /\ a1.net == [] /\ a1.workers == [{ idle_w with work = [vA] }; idle_w])
  = owners (); heaps (); objects_g2 (); facts_g2 () vA;
    resolve_non_infix vA g2;
    col_facts () g2 White White

let a23 (_: squash big)
  : Lemma (a2.heap == h2 /\ a2.net == [] /\ a2.workers == [{ idle_w with scan = Some scA1 }; idle_w] /\
           a3.heap == h2 /\ a3.net == [{ dest = 1; addr = obj_B () }] /\
           a3.workers == [{ idle_w with scan = Some scA2 }; idle_w])
  = a01 (); owners (); heaps (); reads h1; reads h2

let a45 (_: squash big)
  : Lemma (a4.heap == h2 /\ a4.net == [{ dest = 1; addr = obj_B () }] /\ a4.workers == [idle_w; idle_w] /\
           a5.heap == h2 /\ a5.net == [] /\ a5.workers == [idle_w; { idle_w with inbox = [obj_B ()] }])
  = a23 (); heaps (); reads h2

let a678 (_: squash big)
  : Lemma (a6.heap == h6 () /\ a6.net == [] /\ a6.workers == [idle_w; { idle_w with work = [obj_B ()] }] /\
           a7.heap == h7 () /\ a7.net == [] /\ a7.workers == [idle_w; { idle_w with scan = Some (scB1 ()) }] /\
           a8.heap == h7 () /\ a8.net == [] /\ a8.workers == [idle_w; idle_w])
  = a45 (); heaps (); col_facts () h2 Black White; reads (h6 ()); reads (h7 ())
#pop-options

#push-options "--fuel 9 --ifuel 1"
let run1_end (_: squash big)
  : Lemma (run cs1 g2 roots1 sched1 == a8 /\ quiescent a8)
  = a678 ();
    assert_norm (L.for_all idle [idle_w; idle_w] == true)
#pop-options

/// ---------------------------------------------------------------------------
/// Run 2
/// ---------------------------------------------------------------------------

let b0 (_: squash big) = init cs1 g2 (roots2 ())
let b1 (_: squash big) = step cs1 (b0 ()) (Take 0)
let b2 (_: squash big) = step cs1 (b1 ()) (Take 1)
let b3 (_: squash big) = step cs1 (b2 ()) (Pop 0)
let b4 (_: squash big) = step cs1 (b3 ()) (Pop 1)
let b5 (_: squash big) = step cs1 (b4 ()) (Scan 0)
let b6 (_: squash big) = step cs1 (b5 ()) (Deliver 0)
let b7 (_: squash big) = step cs1 (b6 ()) (Take 1)

#push-options "--z3rlimit 40 --fuel 3 --ifuel 1"
let b012 (_: squash big)
  : Lemma (let b = obj_B () in
           (b0 ()).heap == g2 /\ (b0 ()).net == [] /\
             (b0 ()).workers == [{ idle_w with inbox = [vA] }; { idle_w with inbox = [b] }] /\
           (b1 ()).heap == h1 /\ (b1 ()).net == [] /\
             (b1 ()).workers == [{ idle_w with work = [vA] }; { idle_w with inbox = [b] }] /\
           (b2 ()).heap == hb2 () /\ (b2 ()).net == [] /\
             (b2 ()).workers == [{ idle_w with work = [vA] }; { idle_w with work = [b] }])
  = let b = obj_B () in
    owners (); heaps (); objects_g2 (); facts_g2 () vA; facts_g2 () b;
    resolve_non_infix vA g2; resolve_non_infix b g2;
    col_facts () g2 White White;
    col_facts () h1 Gray White

let b345 (_: squash big)
  : Lemma (let b = obj_B () in
           (b3 ()).heap == hb3 () /\ (b3 ()).net == [] /\
             (b3 ()).workers == [{ idle_w with scan = Some scA1 }; { idle_w with work = [b] }] /\
           (b4 ()).heap == hb4 () /\ (b4 ()).net == [] /\
             (b4 ()).workers == [{ idle_w with scan = Some scA1 }; { idle_w with scan = Some (scB1 ()) }] /\
           (b5 ()).heap == hb4 () /\ (b5 ()).net == [{ dest = 1; addr = b }] /\
             (b5 ()).workers == [{ idle_w with scan = Some scA2 }; { idle_w with scan = Some (scB1 ()) }])
  = b012 (); owners (); heaps (); reads (hb2 ()); reads (hb3 ()); reads (hb4 ())

let b67 (_: squash big)
  : Lemma (let b = obj_B () in
           (b6 ()).heap == hb4 () /\ (b6 ()).net == [] /\
             (b6 ()).workers == [{ idle_w with scan = Some scA2 };
                                 { idle_w with scan = Some (scB1 ()); inbox = [b] }] /\
           (b7 ()).heap == hb4 () /\ (b7 ()).net == [] /\
             (b7 ()).workers == [{ idle_w with scan = Some scA2 }; { idle_w with scan = Some (scB1 ()) }])
  = b345 (); heaps (); col_facts () (hb4 ()) Black Black
#pop-options

/// ---------------------------------------------------------------------------
/// Run 3
/// ---------------------------------------------------------------------------

let c0 = init cs0 g2 roots1
let c1 = step cs0 c0 (Take 0)
let c2 = step cs0 c1 (Pop 0)
let c3 = step cs0 c2 (Scan 0)

#push-options "--z3rlimit 40 --fuel 3 --ifuel 1"
let run3_shapes (_: squash big)
  : Lemma (c0.heap == g2 /\ c0.net == [] /\ c0.workers == [{ idle_w with inbox = [vA] }] /\
           c1.heap == h1 /\ c1.net == [] /\ c1.workers == [{ idle_w with work = [vA] }] /\
           c2.heap == h2 /\ c2.net == [] /\ c2.workers == [{ idle_w with scan = Some scA1 }] /\
           c3.heap == h6 () /\ c3.net == [] /\
           c3.workers == [{ idle_w with scan = Some scA2; work = [obj_B ()] }])
  = owners (); heaps (); objects_g2 (); facts_g2 () vA;
    resolve_non_infix vA g2;
    col_facts () g2 White White;
    col_facts () h2 Black White;
    reads h1; reads h2
#pop-options
