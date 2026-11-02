/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.VacB — vacuity checks: Act, Step, Foot
///
/// Each check calls one lemma on arguments that meet its precondition: the
/// states of runs R1 and R2, and the intermediate states inside a scan step
/// (R1 s1) and an accept step (R2 t5).
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.VacB

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
module I1 = GC.Spec.MarkPar.Inv
module Own = GC.Spec.MarkPar.Own
module LS = GC.Spec.MarkPar2.Lists
module U = GC.Spec.MarkPar2.Upd
module A = GC.Spec.MarkPar2.Act
module St = GC.Spec.MarkPar2.Step
module Ft = GC.Spec.MarkPar2.Foot

let wA : wk = wk_of_l [vA] Loop
let wS1 : wk = wk_of_l [] (Scan scA1)
let wGot (_: squash big) : wk = w [] [] (Got (obj_B ()))

/// Reachability of A and B: from R1's s0 (both grey) and R2's t6 (A
/// black, B grey), by `sound`.
let reach_AB (_: squash big)
  : Lemma (M1.reachable (g5 ()) (roots1 ()) vA /\ M1.reachable (g5 ()) (roots1 ()) (obj_B ()) /\
           M1.reachable (g5 ()) rootsA vA /\ M1.reachable (g5 ()) rootsA (obj_B ()))
  = let g = g5 () in
    inv1 (); inv2 (); heaps (); heapsA (); s0_eq (); t6_eq ();
    objects_g5 ();
    reveal_opaque (`%sound) (sound g (roots1 ()) (s0 ()));
    reveal_opaque (`%sound) (sound g rootsA (t6 ()));
    is_gray_iff vA (h2 ()); is_gray_iff (obj_B ()) (h2 ());
    is_black_iff vA (hA3 ()); is_gray_iff (obj_B ()) (hA3 ())

let entry_B (_: squash big)
  : Lemma (entry_ok k1 (g5 ()) 0 (obj_B ()) /\ entry_ok (k2 ()) (g5 ()) 1 (obj_B ()) /\
           resolve_object (obj_B ()) (g5 ()) == obj_B () /\ resolve_object vA (g5 ()) == vA /\
           entry_ok k1 (g5 ()) 0 vA)
  = objects_g5 (); facts_g5 () vA; facts_g5 () (obj_B ()); own2 ();
    resolve_non_infix vA (g5 ()); resolve_non_infix (obj_B ()) (g5 ())

/// ---------------------------------------------------------------------------
/// Act
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let vac_act1 (_: squash big) : unit =
  let g = g5 () in
  let r = roots1 () in
  inv1 (); ctx1 (); s0_eq (); s1_eq (); heaps ();
  reach_AB (); entry_B ();
  U.own_rec k1 g (s0 ()) 0 wA;
  A.wk_ok_recolour k1 g (h2 ()) 0 wA (obj_B ()) Gray;
  assert (pc_of (s1 ()) 0 == Scan scA1);
  A.send_full k1 g r (s1 ()) 0 None;
  A.send_lemma k1 g r (s1 ()) 0 0 (obj_B ()) None;
  objects_g5 (); facts_g5 () vA; facts_g5 () (obj_B ());
  A.entry_facts k1 g r (s1 ()) vA;
  black_weaken k1 g (s1 ()) (obj_B ());
  A.route_lemma k1 g r (s1 ()) 0 (obj_B ()) (obj_B ())
#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let vac_act2 (_: squash big) : unit =
  let g = g5 () in
  let k = k2 () in
  inv2 (); ctx2 (); own2 (); t1_eq (); t5_eq (); heapsA ();
  reach_AB (); entry_B ();
  objects_g5 (); facts_g5 () (obj_B ());
  assert (pc_of (t1 ()) 0 == Scan scA1);
  assert (wk_of (t1 ()) 1 == Some blank0);
  A.send_append k g rootsA (t1 ()) 0 1 (obj_B ()) None blank0;
  colors_of (hA2 ()) (obj_B ()) White;
  A.grey_records k g (t5 ()) (obj_B ());
  A.grey_heap k g (t5 ()) (obj_B ());
  colors_of (hA3 ()) (obj_B ()) Gray;
  makeGray_eq (obj_B ()) (hA2 ());
  A.push_record k g (hA3 ()) 1 blank0 (obj_B ());
  assert (pc_of (t5 ()) 1 == Got (obj_B ()));
  black_weaken k g (t5 ()) (obj_B ());
  A.grey_push_white k g rootsA (t5 ()) 1 (Some (obj_B ())) (obj_B ());
  A.grey_push_lemma k g rootsA (t5 ()) 1 (Some (obj_B ())) (obj_B ());
  U.own_len k g (t5 ());
  U.old_eq (t5 ()) 1;
  U.busy_count (t5 ()) 1;
  A.grey_push_case k g rootsA (t5 ()) 1 (Some (obj_B ())) (obj_B ()) (wGot ()) (hA3 ()) false;
  A.accept_lemma k g rootsA (t5 ()) 1 (obj_B ()) (obj_B ())
#pop-options

/// ---------------------------------------------------------------------------
/// Step
/// ---------------------------------------------------------------------------

let mid1 (_: squash big) : state = U.upd (s1 ()) 0 { wS1 with pc = St.next_pc scA1 } (h3 ()) 1
let mid5 (_: squash big) : state = U.upd (t5 ()) 1 { wGot () with pc = Finish } (hA2 ()) 1

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let vac_step1 (_: squash big) : unit =
  let g = g5 () in
  let r = roots1 () in
  inv1 (); ctx1 (); s0_eq (); s1_eq (); s3_eq (); s4_eq (); heaps ();
  objects_g5 (); facts_g5 () vA;
  colors_of (h2 ()) vA Gray;
  St.pop_heap k1 g (s0 ()) vA;
  St.pop_others k1 g (s0 ()) 0 vA;
  St.pop_record k1 g (s0 ()) 0 wA vA [];
  view () (h2 ());
  I1.others_keep (h2 ()) vA Black;
  makeBlack_eq vA (h2 ());
  colors_of (h3 ()) vA Black;
  assert (St.pop_pc (s0 ()) vA == Scan scA1);
  St.pop_black k1 g (s0 ()) (s1 ()) 0 vA [];
  U.own_len k1 g (s0 ());
  U.old_eq (s0 ()) 0;
  St.step_pop k1 g r (s0 ()) 0 wA vA [];
  U.own_rec k1 g (s0 ()) 0 wA;
  St.step_rec k1 g r (s0 ()) 0 wA wA 1;
  U.own_len k1 g (s4 ()); U.old_eq (s4 ()) 0;
  St.step_stop k1 g r (s4 ()) 0 (wk_of_l [] Loop);
  U.own_len k1 g (s3 ()); U.old_eq (s3 ()) 0;
  St.step_finish k1 g r (s3 ()) 0 (wk_of_l [] Finish)
#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let vac_step2 (_: squash big) : unit =
  let g = g5 () in
  let r = roots1 () in
  inv1 (); ctx1 (); s1_eq (); heaps (); view () (h3 ());
  objects_g5 (); facts_g5 () vA; fields_g5 ();
  VacA.field_A ();
  U.own_len k1 g (s1 ()); U.old_eq (s1 ()) 0;
  St.scan_field k1 g (s1 ()) 0 wS1 scA1;
  U.upd_wk (s1 ()) 0 { wS1 with pc = St.next_pc scA1 } (h3 ()) 1;
  assert (St.next_pc scA1 == Scan scA2);
  assert (pc_of (mid1 ()) 0 == Scan scA2);
  St.scan_unscanned k1 g (s1 ()) (mid1 ()) 0 scA1 vA 2UL;
  colors_of (h3 ()) (obj_B ()) Gray;
  St.scan_cover k1 g (s1 ()) (mid1 ()) 0 scA1 (Some (obj_B ())) vA 1UL;
  St.scan_black k1 g (s1 ()) (mid1 ()) 0 scA1 (Some (obj_B ()));
  St.scan_mid k1 g r (s1 ()) 0 wS1 scA1 (Some (obj_B ()));
  colors_of (h3 ()) vA Black;
  St.scan_target k1 g r (s1 ()) vA 1UL;
  St.step_scan k1 g r (s1 ()) 0 wS1 scA1;
  St.wstep_inv k1 g r (s0 ()) 0
#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let vac_step3 (_: squash big) : unit =
  let g = g5 () in
  let k = k2 () in
  inv2 (); ctx2 (); own2 (); t4_eq (); t5_eq (); heapsA ();
  U.own_len k g (t4 ()); U.old_eq (t4 ()) 1;
  St.step_take k g rootsA (t4 ()) 1 (w [] [obj_B ()] Loop) (obj_B ()) [];
  U.own_len k g (t5 ()); U.old_eq (t5 ()) 1;
  U.upd_wk (t5 ()) 1 { wGot () with pc = Finish } (hA2 ()) 1;
  St.got_black k g (t5 ()) (mid5 ()) 1 (obj_B ());
  St.step_got k g rootsA (t5 ()) 1 (wGot ()) (obj_B ())
#pop-options

/// ---------------------------------------------------------------------------
/// Foot
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let vac_foot1 (_: squash big) : unit =
  let g = g5 () in
  let r = roots1 () in
  let s = s0 () in
  inv1 (); ctx1 (); s0_eq (); s1_eq (); heaps ();
  objects_g5 (); entry_B ();
  Ft.writes_color k1 g 0 (h2 ()) vA Black;
  Ft.grey_push_writes k1 g s 0 vA;
  U.own_heap k1 g s;
  Ft.accept_writes k1 g s 0 (obj_B ());
  Ft.route_writes k1 g s 0 (obj_B ());
  Ft.wstep_writes k1 g r s 0;
  Ft.hd_reads vA g g;
  Ft.gray_rel vA g g;
  Ft.black_rel vA g g;
  Ft.send_reads k1 s s 0 0 vA;
  Ft.grey_push_reads k1 s s 0 vA;
  Ft.accept_reads k1 s s 0 vA;
  Ft.route_reads k1 s s 0 vA;
  Ft.field_reads (s1 ()) 0 wS1 scA1 (h3 ());
  Ft.wstep_reads k1 g r s 0 s.heap
#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let vac_foot2 (_: squash big) : unit =
  let g = g5 () in
  let k = k2 () in
  inv2 (); ctx2 (); own2 (); t0_eq (); t1_eq (); heapsA ();
  objects_g5 ();
  Ft.other_header k g (t1 ()) 0 (obj_B ());
  // worker 0's pop of A changes A's header (grey to black)
  color_of_object_spec vA (hA1 ());
  color_of_object_spec vA (hA2 ());
  assert (wstep k (t0 ()) 0 == t1 ());
  assert (read_word (wstep k (t0 ()) 0).heap (hd_address vA) <> read_word (t0 ()).heap (hd_address vA));
  Ft.race_free k g rootsA (t0 ()) 1 0 (hd_address vA)
#pop-options
