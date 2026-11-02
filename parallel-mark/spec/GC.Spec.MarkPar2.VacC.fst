/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.VacC — vacuity checks: Fix, Main, Init
///
/// The walks: R1's first fix-up (A black, B grey and pushed), R3's first
/// (B white, above A, greyed) and second (nothing to push), and R4's (A
/// white, below B, greyed and pushed).  The setups: R1's (A pushed, B
/// left grey with overflow_main).
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.VacC

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
open GC.Spec.MarkPar2.RunR3
open GC.Spec.MarkPar2.RunR4
open GC.Spec.MarkPar2.VacBase

module M1 = GC.Spec.MarkPar.Model
module I1 = GC.Spec.MarkPar.Inv
module LS = GC.Spec.MarkPar2.Lists
module U = GC.Spec.MarkPar2.Upd
module FX = GC.Spec.MarkPar2.Fix
module Mn = GC.Spec.MarkPar2.Main
module In = GC.Spec.MarkPar2.Init
module VB = GC.Spec.MarkPar2.VacB

let za_i : int = U64.v zero_addr
let wS : wk = wk_of_l [] Stopped
let w2 (_: squash big) : wk = wk_of_l [obj_B ()] Stopped

/// Only A's first field is a pointer.
let fields_of_A (_: squash big) (j: U64.t{U64.v j >= 1})
  : Lemma (requires I1.is_field (g5 ()) vA j) (ensures j == 1UL)
  = objects_g5 (); facts_g5 () vA; fields_g5 ();
    if U64.v j = 2 then assert (j == 2UL) else ()

/// The walks start where Main.walk_start says.
let starts (_: squash big)
  : Lemma (Mn.start_fx (s5 ()) == f6_0 () /\ Mn.start_fx (u6 ()) == v7_0 () /\
           Mn.start_fx (u12 ()) == v13 () /\ Mn.start_fx (z5 ()) == y0 ())
  = s5_eq (); u6_eq (); u12_eq (); z5_eq ()

let empty_f6_0 (_: squash big) : Lemma (forall (i: nat). FX.fstack (f6_0 ()) i == [])
  = let aux (i: nat) : Lemma (FX.fstack (f6_0 ()) i == []) =
      if i = 0 then () else assert (M1.nth (f6_0 ()).fws i == None) in
    FStar.Classical.forall_intro aux

/// R1's walk: wbase and wvis at each position.
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let walk1 (_: squash big)
  : Lemma (let g = g5 () in let r = roots1 () in
           FX.wbase k1 g r (f6_0 ()) /\ FX.wvis k1 g (f6_0 ()) (vA :: obj_B () :: tl ()) za_i /\
           FX.wvis k1 g (f6_0 ()) (obj_B () :: tl ()) (U64.v vA) /\
           FX.wbase k1 g r (f6_2 ()) /\ FX.wvis k1 g (f6_2 ()) (tl ()) (U64.v (obj_B ())) /\
           FX.grows (f6_0 ()) (f6_2 ()) /\ (exists (lo: int). FX.wvis k1 g (f6_2 ()) [] lo))
  = let g = g5 () in let r = roots1 () in
    inv1 (); ctx1 (); s5_eq (); heaps (); view () (h3 ()); starts ();
    Mn.walk_start k1 g r (s5 ());
    f6_walk ();
    FX.obj_step k1 g r (f6_0 ()) vA (obj_B () :: tl ()) za_i;
    FX.obj_step k1 g r (f6_0 ()) (obj_B ()) (tl ()) (U64.v vA);
    FX.walk_step k1 g r (f6_2 ()) (tl ()) (U64.v (obj_B ()));
    walk_tl_ab () k1 (f6_2 ())
#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let walk3 (_: squash big)
  : Lemma (let g = g5 () in
           FX.wbase (k3 ()) g rootsA (v7_0 ()) /\ FX.wvis (k3 ()) g (v7_0 ()) (vA :: obj_B () :: tl ()) za_i /\
           FX.wbase (k3 ()) g rootsA (v13 ()) /\ FX.wvis (k3 ()) g (v13 ()) (vA :: obj_B () :: tl ()) za_i)
  = let g = g5 () in
    inv3 (); ctx3 (); u6_eq (); u12_eq (); heapsA (); view () (hA2 ()); view () (hA4 ()); starts ();
    Mn.walk_start (k3 ()) g rootsA (u6 ());
    Mn.walk_start (k3 ()) g rootsA (u12 ())
#pop-options

#push-options "--z3rlimit 40 --fuel 3 --ifuel 1"
let walk4 (_: squash big)
  : Lemma (let g = g5 () in
           FX.wbase (k3 ()) g (rootsB ()) (y0 ()) /\ FX.wvis (k3 ()) g (y0 ()) (vA :: obj_B () :: tl ()) za_i /\
           FX.wvis (k3 ()) g (y0 ()) (obj_B () :: tl ()) (U64.v vA))
  = let g = g5 () in
    inv4 (); ctx4 (); z5_eq (); heapsB (); view () (hB2 ()); starts ();
    Mn.walk_start (k3 ()) g (rootsB ()) (z5 ());
    y_walk ();
    FX.obj_step (k3 ()) g (rootsB ()) (y0 ()) vA (obj_B () :: tl ()) za_i
#pop-options

let reach_B4 (_: squash big) : Lemma (M1.reachable (g5 ()) (rootsB ()) vA)
  = let g = g5 () in
    inv4 (); z6_eq (); heapsB (); objects_g5 ();
    reveal_opaque (`%sound) (sound g (rootsB ()) (z6 ()));
    is_gray_iff vA (hB3 ())

/// ---------------------------------------------------------------------------
/// Fix
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let vac_fix1 (_: squash big) : unit =
  let g = g5 () in let r = roots1 () in
  walk1 (); ctx1 (); heaps (); view () (h3 ()); objects_g5 (); facts_g5 () vA; facts_g5 () (obj_B ());
  ctx_elim k1 g r;
  colors_of (h3 ()) vA Black; colors_of (h3 ()) (obj_B ()) Gray;
  FX.wbase_heap k1 g r (f6_0 ());
  FX.wbase_at k1 g r (f6_0 ()) 0 wS;
  FX.grows_refl (f6_0 ());
  FX.grows_trans (f6_0 ()) (f6_0 ()) (f6_0 ());
  FX.push_facts k1 (f6_0 ()) (obj_B ());
  FX.push_rec k1 g (f6_0 ()) (obj_B ()) wS;
  FX.push_facts k1 (f6_2 ()) (obj_B ());
  FX.push_full k1 g r (f6_2 ()) (obj_B ()) (w2 ());
  FX.push_room k1 g r (f6_0 ()) (obj_B ()) wS;
  empty_f6_0 ();
  FX.push_base k1 g r (f6_0 ()) (obj_B ());
  FX.field_now k1 g r (f6_0 ()) vA 1UL;
  VacA.field_A ();
  FX.child_facts k1 g r (f6_0 ()) vA (obj_B () :: tl ()) za_i 1UL;
  LS.objs_list_above (h3 ());
  FX.below_not_in (obj_B ()) (tl ()) (U64.v vA) vA;
  FX.wvis_grows k1 g (f6_0 ()) (f6_0 ()) (vA :: obj_B () :: tl ()) za_i;
  FX.child_step k1 g r (f6_0 ()) vA (obj_B () :: tl ()) za_i 1UL;
  FX.fields_step k1 g r (f6_0 ()) vA (obj_B () :: tl ()) za_i 1UL 2UL;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (fields_of_A ()));
  FX.advance k1 g (f6_0 ()) vA (obj_B () :: tl ()) za_i;
  f6_walk ();
  FX.push_base k1 g r (f6_0 ()) (obj_B ());
  FX.advance_push k1 g (f6_0 ()) (f6_2 ()) (obj_B ()) (tl ()) (U64.v vA);
  FX.obj_facts k1 g r (f6_0 ()) vA (obj_B () :: tl ()) za_i;
  FX.obj_black k1 g r (f6_0 ()) vA (obj_B () :: tl ()) za_i;
  FX.obj_grey k1 g r (f6_0 ()) (obj_B ()) (tl ()) (U64.v vA);
  FX.obj_step k1 g r (f6_0 ()) vA (obj_B () :: tl ()) za_i;
  FX.walk_step k1 g r (f6_0 ()) (vA :: obj_B () :: tl ()) za_i
#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let vac_fix3 (_: squash big) : unit =
  let g = g5 () in let k = k3 () in
  walk3 (); ctx3 (); heapsA (); view () (hA2 ()); objects_g5 (); facts_g5 () (obj_B ());
  VB.reach_AB (); VacA.field_A ();
  colors_of (hA2 ()) vA Black; colors_of (hA2 ()) (obj_B ()) White;
  FX.wbase_at k g rootsA (v7_0 ()) 0 wS;
  FX.wrec_recolour k g (hA2 ()) 0 wS (obj_B ());
  FX.white_unstacked k g rootsA (v7_0 ()) (obj_B ());
  recoloured_blue g (hA2 ()) (obj_B ());
  FX.grey_colors (v7_0 ()) (obj_B ());
  FX.grey_wbase k g rootsA (v7_0 ()) (obj_B ());
  FX.grey_base k g rootsA (v7_0 ()) (obj_B ());
  hd_address_spec vA; hd_address_spec (obj_B ());
  FX.above_in k g (v7_0 ()) vA (obj_B () :: tl ()) za_i (obj_B ());
  FX.fix_child_white k vA (v7_0 ()) vB (obj_B ());
  FX.child_above k g rootsA (v7_0 ()) vA (obj_B () :: tl ()) za_i (obj_B ());
  FX.child_white k g rootsA (v7_0 ()) vA (obj_B () :: tl ()) za_i 1UL
#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let vac_fix4 (_: squash big) : unit =
  let g = g5 () in let k = k3 () in
  walk4 (); ctx4 (); heapsB (); view () (hB2 ()); objects_g5 (); facts_g5 () vA;
  reach_B4 ();
  colors_of (hB2 ()) vA White;
  hd_address_spec vA; hd_address_spec (obj_B ());
  FX.child_below k g (rootsB ()) (y0 ()) (obj_B ()) (tl ()) (U64.v vA) vA;
  FX.obj_other k g (rootsB ()) (y0 ()) vA (obj_B () :: tl ()) za_i
#pop-options

/// ---------------------------------------------------------------------------
/// Main
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let vac_main1 (_: squash big) : unit =
  let g = g5 () in let r = roots1 () in
  inv1 (); ctx1 (); s5_eq (); s6_eq (); s10_eq (); heaps ();
  Mn.stopped_empty k1 g (s5 ());
  Mn.no_ovf [];
  let s = s10 () in
  Mn.own_fin k1 g s; Mn.count_fin s; Mn.grey_fin k1 g s; Mn.sound_fin g r s; Mn.roots_fin g r s;
  Mn.fin_fin s; Mn.black_fin k1 g s;
  Mn.main_done k1 g r s;
  Mn.start_recs k1 g (s5 ());
  Mn.wbase_start k1 g r (s5 ());
  Mn.wvis_start k1 g r (s5 ());
  Mn.walk_start k1 g r (s5 ());
  Mn.stopped_at k1 g (s5 ()) 0 wS;
  Mn.main_fix k1 g r (s5 ());
  Mn.main_inv k1 g r (s5 ())
#pop-options

let one_loop (x: wk) (i: nat) (w: wk)
  : Lemma (requires M1.nth [x] i == Some w /\ x.pc == Loop) (ensures w.pc == Loop)
  = if i = 0 then () else assert (M1.nth [x] i == M1.nth ([] #wk) (i - 1))

let s6_one (_: squash big) (i: nat) (w: wk)
  : Lemma (requires M1.nth (s6 ()).wks i == Some w) (ensures w.pc == Loop)
  = s6_eq ();
    one_loop (wk_of_l [obj_B ()] Loop) i w

let s6_loop (_: squash big)
  : Lemma (forall (i: nat) (w: wk). M1.nth (s6 ()).wks i == Some w ==> w.pc == Loop)
  = introduce forall (i: nat) (w: wk). M1.nth (s6 ()).wks i == Some w ==> w.pc == Loop
    with introduce _ ==> _ with s6_one () i w

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let vac_main2 (_: squash big) : unit =
  let g = g5 () in let r = roots1 () in
  walk1 (); inv1 (); ctx1 (); s5_eq (); s6_eq (); heaps ();
  let f = f6_2 () in
  Mn.walk_end k1 g r f;
  Mn.walked_black k1 g (s6 ()) f;
  Mn.wbase_recs k1 g r (f6_0 ());
  Mn.like_walk k1 g r f;
  Mn.like_restart k1 g r f;
  Mn.like_at k1 g f f.fws 0 (w2 ());
  assert ((s6 ()).wks == restart f.fws);
  Mn.like_flagged k1 g f (s6 ());
  Mn.like_own k1 g r f (s6 ());
  Mn.stopped_empty k1 g (s5 ());
  Mn.like_grey k1 g r (s5 ()) f (s6 ());
  Mn.like_sound k1 g r f (s6 ());
  s6_loop ();
  Mn.like_count k1 g f (s6 ());
  Mn.fix_round k1 g r (s5 ()) f
#pop-options

#push-options "--z3rlimit 40 --fuel 3 --ifuel 1"
let vac_main3 (_: squash big) : unit =
  let g = g5 () in let k = k3 () in
  walk3 (); inv3 (); ctx3 (); u12_eq (); heapsA (); view () (hA4 ());
  v13_walk (); starts ();
  Mn.walk_start k g rootsA (u12 ());
  FX.walk_step k g rootsA (v13 ()) (objs_list (hA4 ())) za_i;
  Mn.walk_end k g rootsA (v13 ());
  Mn.stopped_empty k g (u12 ());
  Mn.fix_done k g rootsA (u12 ()) (v13 ())
#pop-options

/// ---------------------------------------------------------------------------
/// Init
/// ---------------------------------------------------------------------------

let f0 (_: squash big) : fx = In.start_fx k1 (g5 ())
let f1 (_: squash big) : fx = { fh = h1 (); fws = [wk_of_l [vA] Loop]; fom = false; fn = 1 }
let f1g (_: squash big) : fx = { f1 () with fh = makeGray_x (obj_B ()) (h1 ()) }

#push-options "--z3rlimit 40 --fuel 4 --ifuel 2"
let f1_eq (_: squash big) : Lemma (darken k1 (f0 ()) vA == f1 ())
  = heaps (); ab_g5 (); view () (g5 ());
    colors_of (g5 ()) vA White;
    assert (blanks (nr k1) == [blank])
#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let vac_init (_: squash big) : unit =
  let g = g5 () in let r = roots1 () in
  ctx1 (); heaps (); ab_g5 (); objects_g5 (); facts_g5 () vA; facts_g5 () (obj_B ());
  VB.reach_AB (); VB.entry_B ();
  In.sinv_start k1 g r;
  colors_of (g5 ()) vA White;
  In.srec_recolour k1 g g 0 blank vA;
  In.sinv_grey k1 g r (f0 ()) [] vA;
  In.grey_pre_intro k1 g r (f0 ()) [] vA vA;
  In.sinv_push k1 g r (f0 ()) [] vA vA;
  In.root_facts k1 g r (f0 ()) [] vA;
  In.darken_step k1 g r (f0 ()) [] vA;
  f1_eq ();
  // the second root, B, finds the stack full
  colors_of (h1 ()) (obj_B ()) White;
  makeGray_eq (obj_B ()) (h1 ());
  In.grey_pre_intro k1 g r (f1 ()) [vA] (obj_B ()) (obj_B ());
  FX.push_facts k1 (f1g ()) (obj_B ());
  In.push_full_s k1 g r (f1g ()) [vA] (obj_B ()) (obj_B ()) (wk_of_l [vA] Loop);
  makeGray_eq vA g;
  FX.push_facts k1 ({ f0 () with fh = makeGray_x vA g }) vA;
  In.grey_pre_intro k1 g r (f0 ()) [] vA vA;
  In.push_room_s k1 g r ({ f0 () with fh = makeGray_x vA g }) [] vA vA blank;
  colors_of (h1 ()) vA Gray;
  In.sinv_skip k1 g r (f1 ()) [vA] vA;
  In.sinv_same k1 g r (f0 ()) [] [];
  In.setup_step k1 g r (f0 ()) [] r;
  In.sinv_recs k1 g r (f0 ()) [];
  In.init_own k1 g r (f0 ()) []; In.init_count k1 g r (f0 ()) []; In.init_flag k1 g r (f0 ()) [];
  In.init_grey k1 g r (f0 ()) []; In.init_sound k1 g r (f0 ()) [];
  In.init_core k1 g r (setup k1 (f0 ()) r);
  In.init_rest k1 g r (setup k1 (f0 ()) r);
  In.init_inv k1 g r
#pop-options
