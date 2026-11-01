/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.VacuityMark — the marking proof's preconditions can be met
///
/// As `GC.Spec.MarkPar.Vacuity`, for the modules behind
/// `mark_par_reachable`: `GC.Spec.MarkPar.Roots`, `.Inv` and `.End`.  The
/// arguments are the runs of `GC.Spec.MarkPar.WitnessRun`, and the empty
/// root list, whose start state is already quiescent and leaves A
/// unreachable.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar.VacuityMark

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Spec.HeapModel
open GC.Spec.DFS
open GC.Lib.Header
open GC.Spec.MarkPar.Exec
open GC.Spec.MarkPar.Model
open GC.Spec.MarkPar.Recolour
open GC.Spec.MarkPar.Witness
open GC.Spec.MarkPar.WitnessRun

module HeapGraph = GC.Spec.HeapGraph
module F = GC.Spec.MarkPar.Field
module Own = GC.Spec.MarkPar.Own
module R = GC.Spec.MarkPar.Roots
module I = GC.Spec.MarkPar.Inv
module E = GC.Spec.MarkPar.End
module MP = GC.Spec.MarkPar

/// ---------------------------------------------------------------------------
/// The settings
/// ---------------------------------------------------------------------------

#push-options "--fuel 2 --ifuel 1"
let root_objs_1 (_: squash big)
  : Lemma (root_objs g2 roots1 == [vA] /\ root_objs g2 (roots2 ()) == [vA; obj_B ()] /\
           root_objs g2 [] == [])
  = objects_g2 ();
    facts_g2 () vA; facts_g2 () (obj_B ());
    resolve_non_infix vA g2; resolve_non_infix (obj_B ()) g2
#pop-options

let ctxs (_: squash big)
  : Lemma (I.ctx cs1 g2 roots1 /\ I.ctx cs1 g2 (roots2 ()) /\ I.ctx cs0 g2 roots1 /\ I.ctx cs1 g2 [] /\
           graph_pre g2 roots1 /\ graph_pre g2 (roots2 ()) /\ graph_pre g2 [])
  = g2_pre (); g2_pre2 (); g2_pre_roots () [];
    R.graph_pre_holds g2 roots1;
    R.graph_pre_holds g2 (roots2 ());
    R.graph_pre_holds g2 [];
    reveal_opaque (`%I.ctx) (I.ctx cs1 g2 roots1);
    reveal_opaque (`%I.ctx) (I.ctx cs1 g2 (roots2 ()));
    reveal_opaque (`%I.ctx) (I.ctx cs0 g2 roots1);
    reveal_opaque (`%I.ctx) (I.ctx cs1 g2 [])

let marks_a (_: squash big)
  : Lemma (I.inv_mark cs1 g2 roots1 a0 /\ I.inv_mark cs1 g2 roots1 a1 /\ I.inv_mark cs1 g2 roots1 a2 /\
           I.inv_mark cs1 g2 roots1 a3 /\ I.inv_mark cs1 g2 roots1 a4 /\ I.inv_mark cs1 g2 roots1 a5 /\
           I.inv_mark cs1 g2 roots1 a6 /\ I.inv_mark cs1 g2 roots1 a7 /\ I.inv_mark cs1 g2 roots1 a8)
  = ctxs ();
    I.init_mark cs1 g2 roots1;
    I.step_mark cs1 g2 roots1 a0 (Take 0);
    I.step_mark cs1 g2 roots1 a1 (Pop 0);
    I.step_mark cs1 g2 roots1 a2 (Scan 0);
    I.step_mark cs1 g2 roots1 a3 (Scan 0);
    I.step_mark cs1 g2 roots1 a4 (Deliver 0);
    I.step_mark cs1 g2 roots1 a5 (Take 1);
    I.step_mark cs1 g2 roots1 a6 (Pop 1);
    I.step_mark cs1 g2 roots1 a7 (Scan 1)

let marks_b (_: squash big)
  : Lemma (let rs = roots2 () in
           I.inv_mark cs1 g2 rs (b4 ()) /\ I.inv_mark cs1 g2 rs (b5 ()) /\
           I.inv_mark cs1 g2 rs (b6 ()) /\ I.inv_mark cs1 g2 rs (b7 ()))
  = let rs = roots2 () in
    ctxs ();
    I.init_mark cs1 g2 rs;
    I.step_mark cs1 g2 rs (b0 ()) (Take 0);
    I.step_mark cs1 g2 rs (b1 ()) (Take 1);
    I.step_mark cs1 g2 rs (b2 ()) (Pop 0);
    I.step_mark cs1 g2 rs (b3 ()) (Pop 1);
    I.step_mark cs1 g2 rs (b4 ()) (Scan 0);
    I.step_mark cs1 g2 rs (b5 ()) (Deliver 0);
    I.step_mark cs1 g2 rs (b6 ()) (Take 1)

let marks_c (_: squash big)
  : Lemma (I.inv_mark cs0 g2 roots1 c2 /\ I.inv_mark cs0 g2 roots1 c3)
  = ctxs ();
    I.init_mark cs0 g2 roots1;
    I.step_mark cs0 g2 roots1 c0 (Take 0);
    I.step_mark cs0 g2 roots1 c1 (Pop 0);
    I.step_mark cs0 g2 roots1 c2 (Scan 0)

let own_of (cs: list nat) (g: heap) (roots: list obj_addr) (s: state)
  : Lemma (requires I.inv_mark cs g roots s) (ensures Own.inv_own cs g s /\ I.own cs g s)
  = reveal_opaque (`%I.own) (I.own cs g s)

/// ---------------------------------------------------------------------------
/// The step relations, on the runs
/// ---------------------------------------------------------------------------

let mB (_: squash big) : msg = { dest = 1; addr = obj_B () }

let targets (_: squash big)
  : Lemma (I.field_target g2 vA 1UL == obj_B () /\ I.is_field g2 vA 1UL /\
           ~(I.is_field g2 vA 2UL) /\ ~(I.is_field g2 (obj_B ()) 1UL))
  = objects_g2 ();
    facts_g2 () vA; facts_g2 () (obj_B ());
    fields_g2 ();
    resolve_non_infix (obj_B ()) g2

#push-options "--z3rlimit 40 --fuel 3 --ifuel 1"
let rel_a23 (_: squash big) : Lemma (I.scan_rel cs1 g2 a2 a3 0 scA1 2)
  = a23 (); targets (); owners ()

let rel_a34 (_: squash big) : Lemma (I.scan_rel cs1 g2 a3 a4 0 scA2 0)
  = a23 (); a45 (); targets ()

let rel_c23 (_: squash big) : Lemma (I.scan_rel cs0 g2 c2 c3 0 scA1 1)
  = run3_shapes (); targets (); owners (); heaps ();
    col (obj_B ()) h2 White;
    makeGray_eq (obj_B ()) h2

let rel_b45 (_: squash big) : Lemma (I.scan_rel cs1 g2 (b4 ()) (b5 ()) 0 scA1 2)
  = b345 (); targets (); owners ()

let rel_a56 (_: squash big) : Lemma (I.take_rel cs1 g2 a5 a6 1 (obj_B ()) [] 1)
  = let b = obj_B () in
    a45 (); a678 (); heaps ();
    col b h2 White;
    makeGray_eq b h2;
    let w' = { idle_w with work = [b] } in
    assert (a6.workers == set_nth a5.workers 1 w');
    I.accessors_upd a5 1 w' a6;
    assert (I.inbox_at a5 1 == [b]);
    assert (I.scan_at a5 1 == None)

let rel_b67 (_: squash big) : Lemma (I.take_rel cs1 g2 (b6 ()) (b7 ()) 1 (obj_B ()) [] 0)
  = let b = obj_B () in
    b67 (); heaps ();
    col b (hb4 ()) Black;
    let w' = { idle_w with scan = Some (scB1 ()) } in
    assert ((b7 ()).workers == set_nth (b6 ()).workers 1 w');
    I.accessors_upd (b6 ()) 1 w' (b7 ());
    assert (I.inbox_at (b6 ()) 1 == [b]);
    assert (I.scan_at (b6 ()) 1 == Some (scB1 ()))

let rel_a45 (_: squash big) : Lemma (I.deliver_rel cs1 g2 a4 a5 0 (mB ()))
  = a45 (); owners ()
#pop-options

/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.Roots
/// ---------------------------------------------------------------------------

let field_ok_A' (_: squash big) : Lemma (F.field_ok g2 vA 1UL)
  = wf_g2 (); objects_g2 (); facts_g2 () vA; fields_g2 ()

let reach_AB (_: squash big)
  : Lemma (reachable g2 roots1 vA /\ reachable g2 roots1 (obj_B ()))
  = ctxs (); root_objs_1 (); g2_pre ();
    field_ok_A' ();
    R.root_reachable g2 roots1 vA;
    F.field_child_facts g2 vA 1UL;
    targets ();
    R.edge_reachable g2 roots1 vA (obj_B ())

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let roots_lemmas (_: squash big) : unit =
  ctxs (); root_objs_1 (); g2_pre ();
  R.vertex_set_of_list [vA];
  R.root_obj_facts g2 roots1 vA;
  R.roots'_mem g2 roots1 vA;
  R.coerce_vertex (Seq.seq_of_list (root_objs g2 roots1)) vA;
  R.graph_pre_holds g2 roots1;
  R.root_reachable g2 roots1 vA;
  reach_AB ()
#pop-options

/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.Inv
/// ---------------------------------------------------------------------------

/// In run 2, worker 1 is part-way through B while worker 0 scans A.
#push-options "--fuel 3 --ifuel 1"
let unscanned_b4 (_: squash big) : Lemma (I.unscanned cs1 (b4 ()) (obj_B ()) 1)
  = b345 (); owners ()
#pop-options

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let inv_lemmas (_: squash big) : unit =
  let b = obj_B () in
  let m = mB () in
  ctxs (); root_objs_1 (); g2_pre (); owners (); heaps ();
  objects_g2 (); facts_g2 () vA; facts_g2 () b;
  marks_a (); marks_b (); marks_c ();
  own_of cs1 g2 roots1 a0; own_of cs1 g2 roots1 a1; own_of cs1 g2 roots1 a2;
  own_of cs1 g2 roots1 a4;
  a01 (); a23 (); a45 (); a678 (); b345 (); b67 (); run3_shapes ();
  targets (); reach_AB ();
  rel_a23 (); rel_a34 (); rel_c23 (); rel_b45 (); rel_a56 (); rel_b67 (); rel_a45 ();
  let w0A = { idle_w with inbox = [vA] } in
  let w1A = { idle_w with work = [vA] } in
  let w2A = { idle_w with scan = Some scA1 } in
  // the initial state
  I.owned_roots_has cs1 g2 roots1 vA;
  I.init_mark cs1 g2 roots1;
  I.field_in g2 h2 vA 1UL;
  assert (I.pending cs1 a4 b);
  I.pending_mono cs1 a4 a4 b;
  // Pop
  I.step_pop_rel cs1 g2 a1 0 w1A vA [];
  let sc' = (Own.pop_worker a1 w1A vA []).scan in
  I.pop_x cs1 g2 a1 0 vA [];
  I.pop_grey cs1 g2 roots1 a1 a2 0 vA [] sc';
  I.pop_sound cs1 g2 roots1 a1 a2 0 vA [] sc';
  I.pop_black cs1 g2 roots1 a1 a2 0 vA [] sc';
  // Scan
  I.step_scan_rel cs1 g2 a2 0 w2A scA1;
  I.scan_x cs1 g2 a2 0 scA1;
  I.target_facts cs1 g2 roots1 vA 1UL;
  I.scan_grey cs0 g2 roots1 c2 c3 0 scA1 1;
  I.scan_sound_grey cs0 g2 roots1 c2 c3 0 scA1;
  I.scan_sound_send cs1 g2 roots1 a2 a3 0 scA1;
  I.scan_sound_none cs1 g2 roots1 a3 a4 0 scA2;
  I.scan_net cs1 g2 a2 a3 0 scA1 2;
  I.scan_roots cs1 g2 roots1 a2 a3 0 scA1 2;
  I.scan_sound cs1 g2 roots1 a2 a3 0 scA1 2;
  I.black_ok_at cs1 g2 a2 vA 1UL;
  I.scan_keeps cs1 g2 a2 a3 0 scA1 2 vA;
  unscanned_b4 ();
  I.scan_other_field cs1 g2 (b4 ()) (b5 ()) 0 scA1 2 b 1;
  I.scan_this_field cs1 g2 a2 a3 0 scA1 2;
  I.scan_later_field cs1 g2 a2 a3 0 scA1 2 2;
  I.scan_black cs1 g2 roots1 a2 a3 0 scA1 2;
  // Take
  I.step_take_rel cs1 g2 a0 0 w0A vA [];
  I.take_keeps cs1 g2 a5 a6 1 b [] 1 b;
  I.take_grey cs1 g2 roots1 a5 a6 1 b [] 1;
  I.take_sound cs1 g2 roots1 a5 a6 1 b [] 1;
  I.take_roots cs1 g2 roots1 a5 a6 1 b [] 1;
  I.take_black cs1 g2 roots1 a5 a6 1 b [] 1;
  I.take_mark cs1 g2 roots1 a5 a6 1 b [] 1;
  I.take_mark cs1 g2 (roots2 ()) (b6 ()) (b7 ()) 1 b [] 0;
  // Deliver
  I.memP_remove_nth_or [m] 0 m;
  I.step_deliver_rel cs1 g2 a4 0 m idle_w;
  I.deliver_keeps cs1 g2 a4 a5 0 m b;
  I.inbox_append_reach g2 roots1 [] b b;
  I.net_append_reach g2 roots1 [] m;
  I.deliver_grey cs1 g2 roots1 a4 a5 0 m;
  I.deliver_sound cs1 g2 roots1 a4 a5 0 m;
  I.deliver_roots cs1 g2 roots1 a4 a5 0 m;
  I.deliver_black cs1 g2 roots1 a4 a5 0 m;
  I.deliver_mark cs1 g2 roots1 a4 a5 0 m;
  // the step function and runs
  I.accessors_upd a0 0 w1A a1;
  I.step_mark cs1 g2 roots1 a0 (Take 0);
  I.run_from_mark cs1 g2 roots1 a0 sched1;
  I.run_mark cs1 g2 roots1 sched1
#pop-options

/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.End, and mark_par_reachable
/// ---------------------------------------------------------------------------

let z0 = init cs1 g2 []

#push-options "--z3rlimit 20 --fuel 3 --ifuel 1"
let z0_quiet (_: squash big)
  : Lemma (z0.workers == [idle_w; idle_w] /\ z0.net == [] /\ quiescent z0 /\
           I.inv_mark cs1 g2 [] z0 /\ ~(reachable g2 [] vA))
  = ctxs (); root_objs_1 ();
    assert_norm (L.for_all idle [idle_w; idle_w] == true);
    I.init_mark cs1 g2 [];
    reachable_set_correct (create_graph g2) (HeapGraph.coerce_to_vertex_list (Seq.seq_of_list (root_objs g2 [])))
#pop-options

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let end_lemmas (_: squash big) : unit =
  let b = obj_B () in
  ctxs (); root_objs_1 (); g2_pre (); heaps ();
  objects_g2 (); facts_g2 () vA;
  marks_a (); a678 (); run1_end ();
  reach_AB ();
  z0_quiet ();
  E.for_all_nth [idle_w; idle_w] 0 idle_w;
  E.quiet a8 0;
  E.nothing_pending cs1 a8 b;
  E.nothing_unscanned cs1 a8 vA 1;
  E.end_recoloured cs1 g2 roots1 a8;
  E.end_ctx cs1 g2 roots1;
  E.end_no_grey cs1 g2 roots1 a8;
  E.end_roots_black cs1 g2 roots1 a8 vA;
  E.end_tri_color cs1 g2 roots1 a8;
  E.end_reachable_black cs1 g2 roots1 a8 vA;
  E.end_unreachable cs1 g2 [] z0 vA;
  E.end_marked cs1 g2 roots1 a8;
  E.run_end cs1 g2 roots1 sched1;
  MP.mark_par_reachable cs1 g2 roots1 sched1
#pop-options
