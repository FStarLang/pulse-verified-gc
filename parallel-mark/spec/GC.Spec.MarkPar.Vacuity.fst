/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.Vacuity — every proof lemma's precondition can be met
///
/// Each check calls one lemma on arguments that meet its precondition: the
/// heap g2 and the runs of `GC.Spec.MarkPar.WitnessRun`.  If a precondition
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
    fields_g2 ()

let witness_lemmas (_: squash big) : unit =
  let b = obj_B () in
  objects_g2 ();
  objects_above zero_addr g2 vA;
  header_g2 () vA;
  facts_g2 () vA;
  field_ok_A ();
  F.field_points_to g2 vA 1UL;
  efp_g2 () vA b;
  g2_pre_roots () [];
  g2_pre ();
  g2_pre2 ()

/// The states of run 1 meet the ownership invariant.
let invs (_: squash big)
  : Lemma (Own.inv_own cs1 g2 a0 /\ Own.inv_own cs1 g2 a1 /\ Own.inv_own cs1 g2 a2 /\
           Own.inv_own cs1 g2 a3 /\ Own.inv_own cs1 g2 a4 /\ Own.inv_own cs1 g2 a5 /\
           Own.inv_own cs1 g2 a6 /\ Own.inv_own cs1 g2 a7 /\ Own.inv_own cs1 g2 a8)
  = g2_pre ();
    Own.init_own cs1 g2 roots1;
    Own.step_own cs1 g2 a0 (Take 0);
    Own.step_own cs1 g2 a1 (Pop 0);
    Own.step_own cs1 g2 a2 (Scan 0);
    Own.step_own cs1 g2 a3 (Scan 0);
    Own.step_own cs1 g2 a4 (Deliver 0);
    Own.step_own cs1 g2 a5 (Take 1);
    Own.step_own cs1 g2 a6 (Pop 1);
    Own.step_own cs1 g2 a7 (Scan 1)

/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.Recolour
/// ---------------------------------------------------------------------------

let recolour_lemmas (_: squash big) : unit =
  let b = obj_B () in
  g2_pre ();
  objects_g2 ();
  facts_g2 () vA; facts_g2 () b;
  heaps ();
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
  field_ok_A ();
  F.field_points_to g2 vA 1UL;
  F.field_child_facts g2 vA 1UL;
  wosize_of_object_bound vA g2;
  objects_g2 ();
  facts_g2 () vA;
  fields_g2 ();
  assert (points_to g2 vA b);
  let _ = F.efp_witness g2 vA (wosize_of_object vA g2) b in
  ()

/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.Own
/// ---------------------------------------------------------------------------

let list_lemmas () : unit =
  Own.nth_memP [vA] 0 vA;
  Own.memP_remove_nth [vA; vA] 0 vA

/// One worker's record, per the ownership invariant.
let worker_ok_at (cs: list nat) (g: heap) (s: state) (i: nat) (w: worker)
  : Lemma (requires Own.inv_own cs g s /\ nth s.workers i == Some w)
          (ensures Own.worker_ok cs g s.heap i w)
  = ()

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let own_lemmas (_: squash big) : unit =
  let b = obj_B () in
  let m : msg = { dest = 1; addr = b } in
  g2_pre ();
  owners ();
  objects_g2 ();
  facts_g2 () vA; facts_g2 () b;
  heaps ();
  invs ();
  a01 (); a23 (); a45 ();
  let w0A = { idle_w with inbox = [vA] } in
  let w1A = { idle_w with work = [vA] } in
  let w2A = { idle_w with scan = Some scA1 } in
  worker_ok_at cs1 g2 a2 0 w2A;
  worker_ok_at cs1 g2 a0 1 idle_w;
  Own.other_color g2 vA b Gray;
  Own.worker_ok_other cs1 g2 g2 1 idle_w vA Gray;
  Own.scan_next_ok cs1 g2 h2 0 scA1;
  Own.upd_worker a0 0 idle_w 1;
  Own.replace_worker cs1 g2 a0 1 g2 idle_w [];
  Own.others_unaffected cs1 g2 a1 0 vA Black;
  Own.owned_roots_mem cs1 g2 0 roots1 vA;
  Own.init_own cs1 g2 roots1;
  Own.push_record cs1 g2 a0 0 w0A idle_w vA;
  Own.push_step cs1 g2 a0 0 w0A idle_w vA (Take 0);
  Own.set_color_writes g2 vA Gray zero_addr;
  makeGray_eq vA g2;
  Own.writes_at cs1 g2 a0 a1 (Take 0) vA;
  Own.pop_record cs1 g2 a1 0 w1A vA [];
  Own.scan_child cs1 g2 a2 0 w2A scA1;
  Own.send_ok cs1 g2 [] m;
  Own.append_entry cs1 g2 [] 1 b b;
  Own.deliver_pre cs1 g2 a4 0 m idle_w;
  Own.move_step cs1 g2 a4 1 idle_w ({ idle_w with inbox = [b] }) [];
  Own.step_take cs1 g2 a0 0;
  Own.step_pop cs1 g2 a1 0;
  Own.step_scan cs1 g2 a2 0;
  Own.step_deliver cs1 g2 a4 0;
  Own.step_own cs1 g2 a5 (Take 1);
  Own.run_from_own cs1 g2 a0 sched1;
  Own.run_own cs1 g2 roots1 sched1
#pop-options

/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar: step_writes_own
/// ---------------------------------------------------------------------------

/// The first step greys A: its header changes.
let step_writes_own_witness (_: squash big) : unit =
  g2_pre ();
  owners ();
  a01 ();
  heaps ();
  objects_g2 ();
  facts_g2 () vA;
  hd_address_spec vA;
  color_of_object_spec vA g2;
  color_of_object_spec vA h1;
  assert (run cs1 g2 roots1 [] == a0);
  assert (read_word (step cs1 a0 (Take 0)).heap (hd_address vA) <> read_word a0.heap (hd_address vA));
  MP.step_writes_own cs1 g2 roots1 [] (Take 0) (hd_address vA)
