/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.VacuityTerm — vacuity checks for GC.Spec.MarkPar.Term
///
/// Each lemma of the Stage 1 termination proof that has a precondition is
/// called once on arguments that meet it: the heap g2 and the states of run 1
/// (`GC.Spec.MarkPar.WitnessRun`), whose invariants `GC.Spec.MarkPar.Vacuity`
/// and `.VacuityMark` already give.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar.VacuityTerm

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

module I = GC.Spec.MarkPar.Inv
module Own = GC.Spec.MarkPar.Own
module V = GC.Spec.MarkPar.Vacuity
module VM = GC.Spec.MarkPar.VacuityMark
module T = GC.Spec.MarkPar.Term

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let vac_term (_: squash big) : unit =
  let b = obj_B () in
  g2_pre (); VM.ctxs (); V.invs ();
  objects_g2 (); facts_g2 () vA; facts_g2 () b;
  recoloured_refl g2;
  T.fts_rec g2 g2 vA;
  T.work_weight_rec g2 g2 [];
  T.works_in_intro g2 [];
  T.workers_weight_rec g2 g2 [];
  T.inv_works cs1 g2 a0;
  T.measure_parts g2 a0;
  T.white_mono g2 g2 [];
  T.white_drop g2 g2 [vA] vA 0;
  recoloured_set g2 g2 vA Gray;
  T.wt_other g2 g2 vA b Gray;
  makeGray_eq vA g2; makeGray_is_gray vA g2; I.colors vA h1;
  T.white_after g2 g2 h1 vA Gray;
  a01 (); a23 (); a45 (); run1_end ();
  T.drop_take cs1 g2 roots1 a0 0 ({ idle_w with inbox = [vA] }) vA [];
  T.drop_pop cs1 g2 roots1 a1 0 ({ idle_w with work = [vA] }) vA [];
  T.drop_scan cs1 g2 roots1 a2 0 ({ idle_w with scan = Some scA1 }) scA1;
  T.length_remove_nth [1] 0;
  T.drop_deliver cs1 g2 roots1 a4 0 ({ dest = 1; addr = b }) idle_w;
  T.enabled_nil a8;
  T.disabled_same cs1 a8 (Pop 0);
  T.mem_enabled a0 (Take 0);
  T.enabled_drops cs1 g2 roots1 a0 (Take 0);
  T.effective_le cs1 g2 roots1 a0 []
#pop-options
