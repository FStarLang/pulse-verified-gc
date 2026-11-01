/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.Vacuity — every proof lemma's precondition can be met
///
/// Each check calls one lemma on arguments that meet its precondition: the
/// heap g2 and the run of `GC.Spec.MarkPar.WitnessRun`.  If a precondition
/// were contradictory, the call would not verify.  Lemmas without a
/// precondition need no witness.  `heap_size` is abstract, so the checks
/// assume it has room for g2's two objects (`big`).
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar.Vacuity

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
open GC.Spec.MarkPar.WitnessRun

module HeapGraph = GC.Spec.HeapGraph
module F = GC.Spec.MarkPar.Field
module Own = GC.Spec.MarkPar.Own
module MP = GC.Spec.MarkPar

/// ---------------------------------------------------------------------------
/// The witness itself
/// ---------------------------------------------------------------------------

let field_ok_A (_: squash big) : Lemma (F.field_ok g2 vA 1UL)
  = wf_g2 ();
    objects_g2 ();
    facts_g2 () vA;
    hd_address_spec vA;
    read_g2 vA

let witness_lemmas (_: squash big) : unit =
  let b = obj_B () in
  objects_g2 ();
  objects_above zero_addr g2 vA;
  header_g2 () vA;
  facts_g2 () vA;
  field_ok_A ();
  F.field_points_to g2 vA 1UL;
  efp_g2 () vA b;
  g2_pre ()

/// The states of the run meet the ownership invariant.
let invs (_: squash big)
  : Lemma (Own.inv_own cs1 g2 s0 /\ Own.inv_own cs1 g2 s1 /\ Own.inv_own cs1 g2 s2 /\
           Own.inv_own cs1 g2 s3 /\ Own.inv_own cs1 g2 s4 /\ Own.inv_own cs1 g2 s5 /\
           Own.inv_own cs1 g2 s6)
  = g2_pre ();
    Own.init_own cs1 g2 roots1;
    Own.step_own cs1 g2 s0 (Take 0);
    Own.step_own cs1 g2 s1 (Pop 0);
    Own.step_own cs1 g2 s2 (Scan 0);
    Own.step_own cs1 g2 s3 (Deliver 0);
    Own.step_own cs1 g2 s4 (Take 1);
    Own.step_own cs1 g2 s5 (Pop 1)

/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.Recolour
/// ---------------------------------------------------------------------------

let marked_p (x: obj_addr) : prop = x == vA \/ x == vB

let recolour_lemmas (_: squash big) : unit =
  let b = obj_B () in
  g2_pre ();
  objects_g2 ();
  facts_g2 () vA; facts_g2 () b;
  heaps_recoloured ();
  heap_ext g2 g2;
  header_eq hA hA;
  recoloured_refl g2;
  recoloured_wosize g2 h1 vA;
  recoloured_no_scan g2 h1 vA;
  recoloured_blue g2 h1 vA;
  set_color_blue vA vA g2 Gray;
  set_color_no_pointer_to_blue g2 vA Gray;
  recoloured_set g2 g2 vA Gray;
  recoloured_makeGray g2 g2 vA;
  recoloured_makeBlack g2 h1 vA;
  recoloured_header g2 h2 vA

/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.Field
/// ---------------------------------------------------------------------------

let field_lemmas (_: squash big) : unit =
  let b = obj_B () in
  g2_pre ();
  objects_g2 ();
  facts_g2 () vA;
  heaps_recoloured ();
  field_A ();
  hd_address_spec vA;
  read_g2 vA;
  field_ok_A ();
  F.field_points_to g2 vA 1UL;
  F.field_child_facts g2 vA 1UL;
  wosize_of_object_bound vA g2;
  let _ = F.efp_witness g2 vA 1UL b in
  ()

/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.Own
/// ---------------------------------------------------------------------------

let list_lemmas () : unit =
  Own.nth_memP [vA] 0 vA;
  Own.memP_remove_nth [vA; vA] 0 vA

let own_lemmas (_: squash big) : unit =
  let b = obj_B () in
  let m : msg = { dest = 1; addr = b } in
  g2_pre ();
  owners ();
  objects_g2 ();
  facts_g2 () vA; facts_g2 () b;
  heaps_recoloured ();
  invs ();
  s0_shape (); s1_shape (); s2_shape (); s3_shape (); s4_shape (); s5_shape ();
  let w0A = { idle_w with inbox = [vA] } in
  let w1A = { idle_w with work = [vA] } in
  let w2A = { idle_w with scan = Some sc_A } in
  Own.other_color g2 vA b Gray;
  Own.worker_ok_other cs1 g2 g2 1 idle_w vA Gray;
  Own.scan_next_ok cs1 g2 h2 0 sc_A;
  Own.upd_worker s0 0 idle_w 1;
  Own.replace_worker cs1 g2 s0 1 g2 idle_w [];
  Own.others_unaffected cs1 g2 s1 0 vA Black;
  Own.owned_roots_mem cs1 g2 0 roots1 vA;
  Own.init_own cs1 g2 roots1;
  Own.push_record cs1 g2 s0 0 w0A idle_w vA;
  Own.push_step cs1 g2 s0 0 w0A idle_w vA (Take 0);
  Own.set_color_writes g2 vA Gray zero_addr;
  makeGray_eq vA g2;
  Own.writes_at cs1 g2 s0 s1 (Take 0) vA;
  Own.pop_record cs1 g2 s1 0 w1A vA [];
  Own.scan_child cs1 g2 s2 0 w2A sc_A;
  Own.send_ok cs1 g2 [] m;
  Own.append_entry cs1 g2 [] 1 b b;
  Own.deliver_pre cs1 g2 s3 0 m idle_w;
  Own.move_step cs1 g2 s3 1 idle_w ({ idle_w with inbox = [b] }) [];
  Own.step_take cs1 g2 s0 0;
  Own.step_pop cs1 g2 s1 0;
  Own.step_scan cs1 g2 s2 0;
  Own.step_deliver cs1 g2 s3 0;
  Own.step_own cs1 g2 s4 (Take 1);
  Own.run_from_own cs1 g2 s0 sched1;
  Own.run_own cs1 g2 roots1 sched1

/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar
/// ---------------------------------------------------------------------------

/// The first step greys A: its header changes.
let step_writes_own_witness (_: squash big) : unit =
  g2_pre ();
  owners ();
  s0_shape (); s1_shape ();
  heaps_recoloured ();
  objects_g2 ();
  facts_g2 () vA;
  hd_address_spec vA;
  color_of_object_spec vA g2;
  color_of_object_spec vA h1;
  is_gray_iff vA h1;
  assert (run cs1 g2 roots1 [] == s0);
  assert (read_word (step cs1 s0 (Take 0)).heap (hd_address vA) <> read_word s0.heap (hd_address vA));
  MP.step_writes_own cs1 g2 roots1 [] (Take 0) (hd_address vA)
