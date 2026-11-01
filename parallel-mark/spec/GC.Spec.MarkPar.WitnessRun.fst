/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.WitnessRun — a concrete run of the model on g2
///
/// Two ranges, cut at B's header, so A is worker 0's and B is worker 1's.
/// The root A starts in worker 0's inbox.  The run
///
///     Take 0; Pop 0; Scan 0; Deliver 0; Take 1; Pop 1
///
/// greys and blackens A, sends B to worker 1 when scanning A's field, and
/// greys and blackens B there.  It passes through every kind of step, and
/// ends quiescent.  Each state is given with its shape, for the vacuity
/// checks.
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

let cut : nat = za + 16
let cs1 : list nat = [cut]
let roots1 : list obj_addr = [vA]

let owners (_: squash big)
  : Lemma (owner cs1 vA == 0 /\ owner cs1 (obj_B ()) == 1 /\ valid_cuts cs1)
  = hd_address_spec vA; hd_address_spec (obj_B ())

let sched1 : list event = [Take 0; Pop 0; Scan 0; Deliver 0; Take 1; Pop 1]

let s0 = init cs1 g2 roots1
let s1 = step cs1 s0 (Take 0)
let s2 = step cs1 s1 (Pop 0)
let s3 = step cs1 s2 (Scan 0)
let s4 = step cs1 s3 (Deliver 0)
let s5 = step cs1 s4 (Take 1)
let s6 = step cs1 s5 (Pop 1)

let idle_w : worker = { work = []; inbox = []; scan = None }

#push-options "--z3rlimit 40 --fuel 3 --ifuel 1"
let s0_shape (_: squash big)
  : Lemma (s0.heap == g2 /\ s0.net == [] /\
           s0.workers == [{ idle_w with inbox = [vA] }; idle_w])
  = owners ();
    objects_g2 ();
    facts_g2 () vA;
    resolve_non_infix vA g2
#pop-options


let h1 : heap = makeGray_x vA g2
let h2 : heap = makeBlack_x vA h1
let h5 (_: squash big) : heap = makeGray_x (obj_B ()) h2
let h6 (_: squash big) : heap = makeBlack_x (obj_B ()) (h5 ())

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let s1_shape (_: squash big)
  : Lemma (s1.heap == h1 /\ s1.net == [] /\
           s1.workers == [{ idle_w with work = [vA] }; idle_w])
  = s0_shape ();
    objects_g2 ();
    facts_g2 () vA
#pop-options

/// The heaps along the run are g2 recoloured.
let heaps_recoloured (_: squash big)
  : Lemma (recoloured g2 h1 /\ recoloured g2 h2 /\ recoloured g2 (h5 ()) /\ recoloured g2 (h6 ()) /\
           is_gray vA h1 /\ is_black vA h2 /\ is_white (obj_B ()) h2 /\
           is_gray (obj_B ()) (h5 ()) /\ is_black (obj_B ()) (h6 ()) /\ is_black vA (h6 ()))
  = let b = obj_B () in
    g2_pre ();
    recoloured_refl g2;
    objects_g2 ();
    facts_g2 () vA; facts_g2 () b;
    recoloured_makeGray g2 g2 vA;
    makeGray_is_gray vA g2;
    Own.colors_distinct vA h1;
    recoloured_makeBlack g2 h1 vA;
    makeBlack_is_black vA h1;
    makeBlack_eq vA h1; makeGray_eq vA g2;
    Own.other_color g2 vA b Gray;
    Own.other_color h1 vA b Black;
    Own.colors_distinct b h2;
    recoloured_makeGray g2 h2 b;
    makeGray_is_gray b h2;
    Own.colors_distinct b (h5 ());
    recoloured_makeBlack g2 (h5 ()) b;
    makeBlack_is_black b (h5 ());
    makeGray_eq b h2; makeBlack_eq b (h5 ());
    Own.other_color h2 b vA Gray;
    Own.other_color (h5 ()) b vA Black

let sc_A : scanning = { sobj = vA; snext = 1UL; sws = 1UL }

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let s2_shape (_: squash big)
  : Lemma (s2.heap == h2 /\ s2.net == [] /\
           s2.workers == [{ idle_w with scan = Some sc_A }; idle_w])
  = s1_shape ();
    heaps_recoloured ();
    objects_g2 ();
    facts_g2 () vA;
    recoloured_wosize g2 h1 vA;
    recoloured_no_scan g2 h1 vA
#pop-options

/// A's field, read in h2, is B.
let field_A (_: squash big)
  : Lemma (get_field_x h2 vA 1UL == vB /\ HeapGraph.is_pointer_field vB /\
           resolve_x (obj_B ()) h2 == obj_B ())
  = heaps_recoloured ();
    objects_g2 ();
    facts_g2 () vA; facts_g2 () (obj_B ());
    hd_address_spec vA;
    read_g2 vA;
    resolve_non_infix (obj_B ()) g2

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let s3_shape (_: squash big)
  : Lemma (s3.heap == h2 /\ s3.net == [{ dest = 1; addr = obj_B () }] /\
           s3.workers == [idle_w; idle_w])
  = s2_shape ();
    field_A ();
    owners ()
#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let s4_shape (_: squash big)
  : Lemma (s4.heap == h2 /\ s4.net == [] /\
           s4.workers == [idle_w; { idle_w with inbox = [obj_B ()] }])
  = s3_shape ()
#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let s5_shape (_: squash big)
  : Lemma (s5.heap == (h5 ()) /\ s5.net == [] /\
           s5.workers == [idle_w; { idle_w with work = [obj_B ()] }])
  = s4_shape ();
    heaps_recoloured ()
#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let s6_shape (_: squash big)
  : Lemma (s6.heap == (h6 ()) /\ s6.net == [] /\ s6.workers == [idle_w; idle_w] /\ quiescent s6)
  = s5_shape ();
    heaps_recoloured ();
    objects_g2 ();
    facts_g2 () (obj_B ());
    recoloured_wosize g2 (h5 ()) (obj_B ());
    recoloured_no_scan g2 (h5 ()) (obj_B ());
    assert_norm (L.for_all idle [idle_w; idle_w] == true)
#pop-options

/// s6 is the run of the whole schedule.
#push-options "--fuel 8 --ifuel 1"
let run1 () : Lemma (run cs1 g2 roots1 sched1 == s6) = ()
#pop-options
