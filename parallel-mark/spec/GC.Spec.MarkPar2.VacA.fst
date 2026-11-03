/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.VacA — vacuity checks: Lists, Inv, Upd, Weight, Meas
///
/// Each check calls one lemma on arguments that meet its precondition.  If
/// a precondition were contradictory, the call would not verify.  The
/// arguments are small lists, the witness heap g5, and states of the runs
/// (`GC.Spec.MarkPar2.Runs`, `.RunR1`-`.RunR4`, `.VacBase`).
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.VacA

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
module LS = GC.Spec.MarkPar2.Lists
module U = GC.Spec.MarkPar2.Upd
module W = GC.Spec.MarkPar2.Weight
module Ms = GC.Spec.MarkPar2.Meas

let wA : wk = wk_of_l [vA] Loop
let wOv : wk = { blank with ovf = true }

/// ---------------------------------------------------------------------------
/// Lists
/// ---------------------------------------------------------------------------

#push-options "--fuel 2 --ifuel 1"
let vac_lists (_: squash big) : unit =
  LS.counted_zero [blank] 0 blank;
  LS.any_ovf_nth [wOv] 0 wOv;
  LS.all_stopped_nth [{ blank with pc = Stopped }] 0 { blank with pc = Stopped };
  LS.all_stopped_intro [];
  LS.any_ovf_elim [wOv];
  LS.counted_restart [];
  LS.nth_upd [blank] 0 wA 0;
  LS.above_mem 0 [vA] vA;
  LS.above_weaken 0 0 [];
  LS.above_norepeats 0 [];
  LS.objs_list_same (g5 ()) (g5 ())
#pop-options

/// ---------------------------------------------------------------------------
/// Inv
/// ---------------------------------------------------------------------------

let field_A (_: squash big) : Lemma (I1.is_field (g5 ()) vA 1UL /\ I1.field_target (g5 ()) vA 1UL == obj_B ())
  = objects_g5 (); facts_g5 () vA; fields_g5 (); facts_g5 () (obj_B ());
    resolve_non_infix (obj_B ()) (g5 ())

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let vac_inv (_: squash big) : unit =
  let g = g5 () in
  inv1 (); ctx1 (); inv2 (); ctx2 ();
  ctx_elim k1 g (roots1 ());
  ctx_elim k1 g (roots1 ());
  wf_g5 (); objects_g5 ();
  resolve_self g vA;
  g5_pre_roots () []; recoloured_refl g;
  resolve_recoloured g g vA;
  heaps (); s1_eq ();
  colors_of (h3 ()) vA Black;
  field_A ();
  black_ok_at k1 g (s1 ()) None vA 1UL;
  // pending: R2's t2 holds B in inbox 1
  t2_eq ();
  assert (holds (t2 ()) 1 (obj_B ()));
  facts_g5 () (obj_B ());
  resolve_non_infix (obj_B ()) g;
  assert (pending g (t2 ()) (obj_B ()));
  let kp () : Lemma (keeps (k2 ()) g (t2 ()) (t2 ())) = () in
  kp ();
  keeps_pending (k2 ()) g (t2 ()) (t2 ()) (obj_B ());
  let kp1 () : Lemma (keeps k1 g (s0 ()) (s0 ())) = () in
  kp1 ();
  black_keeps k1 g (s0 ()) (s0 ()) None;
  black_weaken k1 g (s1 ()) vA;
  black_cover k1 g (s1 ()) vA;
  black_weaken k1 g (s0 ()) vA
#pop-options

/// ---------------------------------------------------------------------------
/// Upd
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let vac_upd (_: squash big) : unit =
  let g = g5 () in
  let r = roots1 () in
  inv1 (); ctx1 ();
  s0_eq (); s1_eq ();
  let s = s0 () in
  U.upd_wk s 0 wA s.heap s.count;
  U.old_eq s 0;
  U.own_rec k1 g s 0 wA;
  U.own_others k1 g s 0;
  U.own_len k1 g s;
  U.own_heap k1 g s;
  assert (U.old s 0 == wA);
  U.own_upd k1 g s 0 wA s.heap s.count;
  U.own_upd_same k1 g s 0 wA s.count;
  U.count_upd s 0 wA s.heap s.count;
  assert (pc_of (s1 ()) 0 == Scan scA1);
  U.busy_count (s1 ()) 0;
  U.count_pos s 0;
  U.flagged_upd s 0 wA s.heap s.count;
  U.grey_upd k1 g s s;
  U.sound_upd g r s 0 wA s.heap s.count;
  U.roots_upd g r s s;
  U.fin_running s;
  assert (U.upd s 0 wA s.heap s.count == s);
  U.keeps_upd k1 g s 0 wA s.heap s.count
#pop-options

/// ---------------------------------------------------------------------------
/// Weight and Meas
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let vac_weight (_: squash big) : unit =
  let g = g5 () in
  g5_pre_roots () []; recoloured_refl g; objects_g5 ();
  W.entry_w_rec k1 g g vA;
  W.pc_w_rec k1 g g Loop;
  W.inbox_w_rec k1 g g [];
  W.wks_w_rec k1 g g 0 [];
  W.wks_w_restart k1 g 0 [];
  W.wks_w_stopped k1 g 0 [];
  W.fields_rec g g vA;
  W.objs_w_mono k1 g g [] [] [];
  W.objs_w_drop k1 g g [blank] [blank] [vA] vA 0

let vac_meas (_: squash big) : unit =
  let g = g5 () in
  inv1 (); ctx1 ();
  s0_eq (); s1_eq ();
  let s = s0 () in
  U.own_heap k1 g s;
  U.own_len k1 g s;
  Ms.measure_parts k1 g s;
  Ms.on_stack_same k1 [blank] [blank] vA;
  Ms.om_same k1 g s s;
  Ms.set_same_stacks [blank] 0 blank;
  U.own_len k1 g (s1 ());
  Ms.send_m k1 g (s1 ()) 0 0 (obj_B ());
  Ms.push_other k1 [blank] 0 blank vA (obj_B ());
  Ms.push_self k1 [blank] 0 blank vA;
  objects_g5 (); facts_g5 () vA; wf_g5 ();
  resolve_non_infix vA g;
  Ms.grey_push_m k1 g s 0 vA;
  Ms.accept_m k1 g s 0 vA;
  Ms.route_m k1 g s 0 vA
#pop-options
