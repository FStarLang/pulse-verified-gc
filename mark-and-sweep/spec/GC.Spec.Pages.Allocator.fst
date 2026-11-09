/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Allocator - proofs of the page allocator's interface
/// ---------------------------------------------------------------------------
///
/// Each lemma of the interface from the stage 1–3 theorems and
/// `GC.Spec.Pages.AllocPhase` / `GC.Spec.Pages.MarkPhase`.

module GC.Spec.Pages.Allocator

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map

module U64 = FStar.UInt64
module Seq = FStar.Seq
module I = GC.Spec.AllocIface
module Inv = GC.Spec.Pages.Inv
module Th = GC.Spec.Pages.Theorems
module AP = GC.Spec.Pages.AllocPhase
module MP = GC.Spec.Pages.MarkPhase
module SA = GC.Spec.Pages.SweepAll
module SU = GC.Spec.Pages.SweepUnits
module SO = GC.Spec.Pages.SweepOrder
module A = GC.Spec.Pages.Alloc
module Mark = GC.Spec.Mark

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Allocation
/// ---------------------------------------------------------------------------

let inv_mc (ph: I.phase) (g: heap) (st: pstate)
  : Lemma (requires inv ph g st) (ensures pages_ok_mc g st)
  = match ph with
    | I.Idle -> AP.mc_of_ok g st
    | _ -> ()

/// The words of unswept pages are kept.
let unswept_words (g g': heap) (st st': pstate)
  : Lemma (requires Th.unswept_unchanged g g' st st')
          (ensures forall (b: hp_addr). unswept st b ==> read_word g' b == read_word g b)
  = ()

/// Allocation meets `alloc_post` in one phase.
let alloc_post_at (ph: I.phase) (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires inv ph g st)
          (ensures (let (g', st', o) = alloc ph g st wz in
                    I.alloc_post pages_allocator ph g st wz g' st' o))
  = let col = I.new_colour ph in
    inv_mc ph g st;
    AP.alloc_col_correct col g st wz;
    let (g', st', o) = alloc ph g st wz in
    unswept_words g g' st st';
    match ph with
    | I.Idle ->
      AP.alloc_col_white g st wz;
      A.alloc_ok_at g st wz;
      MP.alloc_swept g st wz;
      if o <> 0UL then is_white_iff (o <: obj_addr) g'
    | I.Marking ->
      MP.mark_inv_alloc g st wz
    | I.Sweeping -> ()

let pages_allocator_ok () =
  let ok (ph: I.phase) (g: heap) (s: pstate) (wz: nat)
    : Lemma (inv ph g s ==>
             (let (g', s', obj) = alloc ph g s wz in I.alloc_post pages_allocator ph g s wz g' s' obj))
    = FStar.Classical.move_requires (alloc_post_at ph g s) wz
  in
  FStar.Classical.forall_intro_4 ok;
  let enter (g: heap) (s: pstate) : Lemma (inv I.Idle g s ==> inv I.Marking g s)
    = FStar.Classical.move_requires (MP.mark_inv_of_ok g) s
  in
  FStar.Classical.forall_intro_2 enter;
  let mark (g: heap) (s: pstate) (x: obj_addr) (c: color)
    : Lemma (inv I.Marking g s /\ I.live g x /\ c <> Blue ==> inv I.Marking (set_object_color x g c) s)
    = if FStar.IndefiniteDescription.strong_excluded_middle (inv I.Marking g s /\ I.live g x /\ c <> Blue)
      then MP.mark_inv_recolour g s x c
  in
  FStar.Classical.forall_intro_4 mark

let alloc_no_fit ph g st wz =
  inv_mc ph g st;
  AP.alloc_col_correct (I.new_colour ph) g st wz

let alloc_idle g st wz =
  AP.mc_of_ok g st;
  AP.alloc_col_white g st wz;
  A.alloc_ok_at g st wz


let alloc_col_correct col g st wz = AP.alloc_col_correct col g st wz

/// ---------------------------------------------------------------------------
/// The sweep
/// ---------------------------------------------------------------------------

let sweep_page_correct () = GC.Spec.Pages.SweepPage.sweep_page_correct ()

let sweep_run_correct () = GC.Spec.Pages.SweepRun.sweep_run_correct ()

let sweep_commute g pm i j fpi fpj = SO.sweep_commute g pm i j fpi fpj

let sweep_start g st = SA.inv_init g st

let sweep_step_inv g0 st0 g st p =
  SA.inv_step g0 g st0 st p;
  SA.inv_elim g0 st0 g st p

let sweep_end g0 st0 g st =
  SA.inv_elim g0 st0 g st n_pages;
  SA.no_blue_after g0 g st0 st;
  eliminate exists (cs: list obj_addr). GC.Spec.Pages.Cells.lview g st cs
  with GC.Spec.Pages.Cells.lview_large_ok g st cs;
  GC.Spec.Pages.Step.pages_ok_intro g st

let sweep_all_correct g st = SA.sweep_all_correct g st

/// ---------------------------------------------------------------------------
/// The collector's contract
/// ---------------------------------------------------------------------------

let mark_exact_done h_init h_mark roots = ()

/// ---------------------------------------------------------------------------
/// Vacuity
/// ---------------------------------------------------------------------------

/// The empty heap of pages satisfies the invariant of every phase.
let init_inv (g: heap) (ph: I.phase)
  : Lemma (inv ph (GC.Spec.Pages.Init.init_heap g) GC.Spec.Pages.Init.init_state)
  = A.init_alloc_pre g;
    AP.mc_of_ok (GC.Spec.Pages.Init.init_heap g) GC.Spec.Pages.Init.init_state

/// On it, a small allocation succeeds in every phase, with the phase's
/// colour: `allocator_ok` is not met by failing, nor by ignoring the phase.
let init_alloc_ok (g: heap) (ph: I.phase) (wz: nat)
  : Lemma (requires n_pages > 0 /\ wz + 1 <= small_max)
          (ensures (let (g', _, o) = alloc ph (GC.Spec.Pages.Init.init_heap g) GC.Spec.Pages.Init.init_state wz in
                    o =!= 0UL /\ U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
                    color_of_object (o <: obj_addr) g' == I.new_colour ph))
  = let g0 = GC.Spec.Pages.Init.init_heap g in
    let st0 = GC.Spec.Pages.Init.init_state in
    A.init_alloc_pre g;
    A.init_alloc_succeeds g wz;
    AP.mc_of_ok g0 st0;
    AP.alloc_col_white g0 st0 wz;
    AP.alloc_col_correct (I.new_colour ph) g0 st0 wz

/// The hypotheses of the guarantees are not refutable.
#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"
[@@expect_failure [19]]
let inv_not_false (ph: I.phase) (g: heap) (st: pstate)
  : Lemma (requires inv ph g st) (ensures False)
  = ()

[@@expect_failure [19]]
let sweep_hyps_not_false (g: heap) (st: pstate)
  : Lemma (requires sweep_ready g st /\ mark_done g) (ensures False)
  = ()

[@@expect_failure [19]]
let mark_exact_not_false (h_init h_mark: heap) (roots: Seq.seq obj_addr)
  : Lemma (requires mark_exact h_init h_mark roots) (ensures False)
  = ()
#pop-options
