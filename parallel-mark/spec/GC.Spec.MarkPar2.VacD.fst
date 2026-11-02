/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.VacD — vacuity checks: End, Count, Term, and the
/// statements of GC.Spec.MarkPar2
///
/// The finished runs R1 (through a fix-up) and R0 (no roots, so A is
/// unreachable), R1's prefixes to s4 (counter 0) and s5 (a worker stopped),
/// and states of R1 and R2 for the measure.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.VacD

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
open GC.Spec.MarkPar2.Inv
open GC.Spec.MarkPar2.Runs
open GC.Spec.MarkPar2.RunR1
open GC.Spec.MarkPar2.RunR2
open GC.Spec.MarkPar2.VacBase

module M1 = GC.Spec.MarkPar.Model
module R = GC.Spec.MarkPar.Roots
module LS = GC.Spec.MarkPar2.Lists
module U = GC.Spec.MarkPar2.Upd
module St = GC.Spec.MarkPar2.Step
module FX = GC.Spec.MarkPar2.Fix
module Mn = GC.Spec.MarkPar2.Main
module E = GC.Spec.MarkPar2.End
module C = GC.Spec.MarkPar2.Count
module T = GC.Spec.MarkPar2.Term
module MP = GC.Spec.MarkPar2
module VB = GC.Spec.MarkPar2.VacB
module VC = GC.Spec.MarkPar2.VacC

let wA : wk = wk_of_l [vA] Loop

let sched4 : list event = [W 0; W 0; W 0; W 0]
let sched5 : list event = [W 0; W 0; W 0; W 0; W 0]

let run4_eq (_: squash big) : Lemma (run k1 (g5 ()) (roots1 ()) sched4 == s4 ())
  = assert (run k1 (g5 ()) (roots1 ()) sched4 == s4 ())
      by (FStar.Tactics.V2.norm [delta_only [`%run; `%run_from; `%sched4; `%s0; `%s1; `%s2; `%s3; `%s4];
                                  zeta; iota];
          FStar.Tactics.V2.trefl ())

let run5_eq (_: squash big) : Lemma (run k1 (g5 ()) (roots1 ()) sched5 == s5 ())
  = assert (run k1 (g5 ()) (roots1 ()) sched5 == s5 ())
      by (FStar.Tactics.V2.norm [delta_only [`%run; `%run_from; `%sched5; `%s0; `%s1; `%s2; `%s3; `%s4; `%s5];
                                  zeta; iota];
          FStar.Tactics.V2.trefl ())

let roots_A (_: squash big) : Lemma (L.memP vA (M1.root_objs (g5 ()) (roots1 ())))
  = VB.entry_B ();
    R.root_objs_mem (g5 ()) (roots1 ()) vA

/// ---------------------------------------------------------------------------
/// End
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let vac_end (_: squash big) : unit =
  let g = g5 () in let r = roots1 () in
  inv1 (); ctx1 (); s11_eq (); run1_eq ();
  E.step_inv k1 g r (s0 ()) (W 0);
  E.run_from_inv k1 g r (s0 ()) [];
  E.run_inv k1 g r [];
  let s = s11 () in
  E.quiet k1 g r s;
  E.end_no_grey k1 g r s;
  roots_A ();
  E.end_roots_black k1 g r s vA;
  E.end_tri_color k1 g r s;
  objects_g5 (); VB.reach_AB ();
  E.end_reachable_black k1 g r s vA;
  E.end_marked k1 g r s;
  ctx_elim k1 g r;
  E.run_end k1 g r sched1;
  // R0: A unreachable
  inv0 (); r0_eq (); unreachable0 ();
  E.end_unreachable k1 g [] (r0_2 ()) vA
#pop-options

/// ---------------------------------------------------------------------------
/// Count
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let vac_count (_: squash big) : unit =
  let g = g5 () in let r = roots1 () in
  inv1 (); ctx1 (); s4_eq (); s5_eq (); run4_eq (); run5_eq ();
  C.count_exact k1 g r [];
  U.own_len k1 g (s5 ());
  C.stopped_zero k1 g r sched5 0;
  C.zero_empty (s4 ()) 0 (wk_of_l [] Loop);
  C.zero_step k1 (s4 ()) 0;
  C.zero_final k1 g r sched4 0
#pop-options

/// ---------------------------------------------------------------------------
/// Term
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let vac_term1 (_: squash big) : unit =
  let g = g5 () in let r = roots1 () in
  inv1 (); ctx1 (); s0_eq (); s1_eq (); s3_eq (); s4_eq (); s5_eq (); s10_eq (); s11_eq ();
  T.disabled_same k1 (s11 ()) Main;
  T.counted_some [wA];
  T.busy_enabled k1 g (s0 ()) 0 wA;
  T.enabled_nil k1 g r (s0 ());
  T.measure_of k1 g r (s0 ());
  T.om_rec k1 g (s0 ()) 0 wA wA 1;
  U.own_len k1 g (s4 ()); U.old_eq (s4 ()) 0;
  assert (U.upd (s4 ()) 0 (wk_of_l [] Stopped) (h3 ()) 0 == s5 ());
  T.drop_rec k1 g r (s4 ()) 0 (wk_of_l [] Loop) (wk_of_l [] Stopped) 0;
  U.own_len k1 g (s0 ()); U.old_eq (s0 ()) 0;
  T.drop_pop k1 g r (s0 ()) 0 wA vA [];
  T.drop_stop k1 g r (s4 ()) 0 (wk_of_l [] Loop);
  U.own_len k1 g (s3 ()); U.old_eq (s3 ()) 0;
  T.drop_finish k1 g r (s3 ()) 0 (wk_of_l [] Finish);
  U.own_len k1 g (s1 ()); U.old_eq (s1 ()) 0;
  T.mid_parts k1 g r (s1 ()) 0 VB.wS1 (St.next_pc scA1);
  T.drop_scan k1 g r (s1 ()) 0 VB.wS1 scA1;
  T.mem_enabled (s0 ()) (W 0);
  T.wstep_drops k1 g r (s0 ()) 0;
  T.main_done_drops k1 g r (s10 ());
  T.enabled_drops k1 g r (s0 ()) (W 0);
  T.effective_le k1 g r (s0 ()) []
#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let vac_term2 (_: squash big) : unit =
  let g = g5 () in let k = k2 () in
  inv2 (); ctx2 (); own2 (); t4_eq (); t5_eq ();
  U.own_len k g (t4 ()); U.old_eq (t4 ()) 1;
  T.drop_take k g rootsA (t4 ()) 1 (w [] [obj_B ()] Loop) (obj_B ()) [];
  U.own_len k g (t5 ()); U.old_eq (t5 ()) 1;
  T.drop_got k g rootsA (t5 ()) 1 (VB.wGot ()) (obj_B ())
#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let vac_term3 (_: squash big) : unit =
  let g = g5 () in let r = roots1 () in
  inv1 (); ctx1 (); s5_eq (); VC.walk1 (); VC.starts ();
  Mn.stopped_empty k1 g (s5 ());
  T.empty_off k1 (s5 ()) vA;
  g5_pre_roots () []; recoloured_refl g; objects_g5 (); facts_g5 () vA;
  T.x_weight k1 g g [blank] [blank] vA;
  T.walk_weights k1 g r (s5 ()) (f6_2 ()) (f6_2 ()).fws;
  T.some_pushed k1 g r (f6_2 ());
  T.main_fix_drops k1 g r (s5 ());
  T.main_drops k1 g r (s5 ())
#pop-options

/// ---------------------------------------------------------------------------
/// The statements
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let vac_statements (_: squash big) : unit =
  let g = g5 () in let r = roots1 () in
  ctx1 (); inv1 (); s0_eq (); s1_eq (); s4_eq (); s11_eq (); run1_eq (); run4_eq (); heaps ();
  ctx_elim k1 g r;
  MP.ctx_of k1 g r;
  MP.mark_par_correct k1 g r sched1;
  MP.mark_par_reachable k1 g r sched1;
  // the first step writes A's header, grey to black
  color_of_object_spec vA (h2 ()); color_of_object_spec vA (h3 ());
  assert (run k1 g r [] == s0 ());
  assert (step k1 (s0 ()) (W 0) == s1 ());
  MP.step_writes_own k1 g r [] 0 (hd_address vA);
  MP.step_reads_own k1 g r [] 0 (s0 ()).heap;
  MP.main_at_barrier k1 (s0 ());
  MP.count_exact k1 g r [];
  MP.zero_final k1 g r sched4 0;
  MP.mark_par_terminates k1 g r [];
  // two workers: worker 0 writes A's header, which worker 1 may not read
  ctx2 (); inv2 (); own2 (); t0_eq (); t1_eq (); heapsA ();
  ctx_elim (k2 ()) g rootsA;
  color_of_object_spec vA (hA1 ()); color_of_object_spec vA (hA2 ());
  assert (run (k2 ()) g rootsA [] == t0 ());
  assert (step (k2 ()) (t0 ()) (W 0) == t1 ());
  MP.step_race_free (k2 ()) g rootsA [] 1 0 (hd_address vA)
#pop-options
