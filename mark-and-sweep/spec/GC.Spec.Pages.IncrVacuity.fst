/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.IncrVacuity - witnesses for incremental mode
/// ---------------------------------------------------------------------------
///
/// Plan §28.  Every theorem of `GC.Spec.Pages.Incr` and
/// `GC.Spec.Pages.Cycle.Incr`, and the preconditions of the Pulse code of
/// incremental mode, on concrete states of the dark run
/// (`Cycle.VacuityDark`, plan §25.3) from the witness heap `W`:
///
///   * **a mid-sweep state with some pages swept and some not**
///     (`mixed_state`): after the sweep of A's page, that page is swept and
///     B's run is not.  The Pulse allocator's precondition holds there
///     (`Incr.phase_inv I.Sweeping`), and an allocation with any tag
///     succeeds, white, in a swept page: the colour rule (`alloc_mixed`).
///     The `Idle` and `Marking` invariants of `W` meet it too
///     (`alloc_other_phases`).
///   * **a run of the page cycle finished by the Pulse operations**
///     (`run_incr`): the carried cycle of §26 up to its write mid-sweep,
///     then B's run swept as one unit (`cyc_unit`), then one slice from
///     cursor 0 with a budget of every page (`cyc_slice`), which reaches
///     the end, and the end (`cyc_end`).  The run is idle again, and
///     `ccycle_correct` applies (`run_incr_theorems`).  B's run is unswept
///     before the unit step and swept after it (`run_incr_nontrivial`).

module GC.Spec.Pages.IncrVacuity

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Gen.MinorHeap
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv

module U64 = FStar.UInt64
module MP = GC.Spec.MarkPhase
module MStart = GC.Gen.MarkPhase.Start
module SPC = GC.Spec.SweepPhase.Completeness
module GC_ = GC.Gen.Cycle
module I = GC.Spec.AllocIface
module PA = GC.Spec.Pages.Allocator
module AT = GC.Spec.Pages.AllocTag
module SA = GC.Spec.Pages.SweepAll
module MS = GC.Spec.Pages.MidSweep
module MSA = GC.Spec.Pages.MidSweepAlloc
module Wt = GC.Spec.Pages.Witness
module PV = GC.Spec.Pages.Vacuity
module V = GC.Spec.Pages.Cycle.Vacuity
module D = GC.Spec.Pages.Cycle.VacuityDark
module C = GC.Spec.Pages.Cycle.Carried
module Inc = GC.Spec.Pages.Incr
module CI = GC.Spec.Pages.Cycle.Incr

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Allocation in every phase
/// ---------------------------------------------------------------------------

/// **A mid-sweep state with some pages swept and some not**, which meets
/// the Pulse allocator's precondition.
let mixed_state (g: heap)
  : Lemma (requires V.roomy)
          (ensures Inc.phase_inv I.Sweeping (D.g1 g) (D.s1 g) /\
                   (entry (D.s1 g).pm (D.jc g)).swept /\
                   V.i0 g < n_pages /\ D.jc g <> V.i0 g /\
                   (entry (D.s1 g).pm (V.i0 g)).kind == LargeHead Wt.kL /\
                   not (entry (D.s1 g).pm (V.i0 g)).swept)
  = D.step1 g;
    MS.pages_ok_sw_elim (D.g1 g) (D.s1 g)

/// **The colour rule mid-sweep**: from that state, an allocation with any
/// tag succeeds and hands out an object of the colour `colour_at`, white.
let alloc_mixed (g: heap) (tag: AT.tag_t)
  : Lemma (requires V.roomy)
          (ensures (let (g', st', o) = AT.alloc_tag I.Sweeping (D.g1 g) (D.s1 g) Wt.wzS tag in
                    o == (D.oo g <: U64.t) /\ st' == D.s2 g /\
                    color_of_object (D.oo g) g' == I.colour_at MSA.pages_allocator_sw (D.s1 g) I.Sweeping (D.oo g) /\
                    color_of_object (D.oo g) g' == White))
  = mixed_state g;
    D.alloc_ok g;
    Inc.alloc_tag_phase I.Sweeping (D.g1 g) (D.s1 g) Wt.wzS tag;
    Inc.tag_colour White tag (D.g1 g) (D.s1 g) Wt.wzS

/// The `Idle` and `Marking` invariants of `W` meet the allocator's
/// precondition in those phases.
let alloc_other_phases (g: heap)
  : Lemma (requires Wt.big_enough)
          (ensures Inc.phase_inv I.Idle (PV.h g) (PV.st g) /\ Inc.phase_inv I.Marking (PV.hm g) (PV.st g))
  = PV.interface_witness g

/// ---------------------------------------------------------------------------
/// A run finished by the Pulse operations
/// ---------------------------------------------------------------------------

/// The carried run of §26 (`CarriedVacuity.run_carried`) up to its write
/// mid-sweep: A's page swept, O allocated and written, B's run unswept.
#push-options "--fuel 1 --ifuel 1"
let run_sw (g: heap{V.roomy})
  : GTot (C.ccycle (D.h g) (D.rs g) (D.g3 g) (D.s2 g) I.Sweeping (D.since_d g)) =
  D.start_pre g;
  D.darkened_a g;
  D.gd_ok g;
  D.mal_ok g;
  D.gz_ok g;
  D.n1_storable g;
  D.write_ok g;
  D.gw_ok g;
  D.marks g;
  D.gh_no_grey g;
  D.alloc_ok g;
  D.swrite_ok g;
  let rm0 : C.cmarking (D.h g) (D.rs g) (MStart.darkened (D.h g) (D.rs g)) (D.st g) MP.scan_none SPC.nothing_new =
    C.CStart V.m0 (D.st g) () in
  let rm1 : C.cmarking (D.h g) (D.rs g) (D.gz g) (D.sb g) MP.scan_none (D.since_m g) =
    C.CAlloc rm0 V.m0 Wt.wzS (D.gb g) (D.sb g) (D.n1 g) () (D.gz g) (D.iw g) () in
  let rm2 : C.cmarking (D.h g) (D.rs g) (D.gw g) (D.sb g) MP.scan_none (D.since_m g) =
    C.CWrite rm1 V.m0 (D.oa g) (D.oa g <: hp_addr) (D.n1 g <: U64.t) () in
  let r0 : C.csweep (D.gh g) (D.gh g) (D.s0 g) I.Sweeping SPC.nothing_new = C.CSStart (D.s0 g) in
  let r1 : C.csweep (D.gh g) (D.g1 g) (D.s1 g) I.Sweeping SPC.nothing_new = C.CSStep r0 (D.jc g) in
  let r2 : C.csweep (D.gh g) (D.g2 g) (D.s2 g) I.Sweeping (SPC.with_new SPC.nothing_new (D.oo g <: U64.t)) =
    C.CSAlloc r1 Wt.wzS (D.ga g) (D.s2 g) (D.oo g) () (D.g2 g) () in
  let r3 : C.csweep (D.gh g) (D.g3 g) (D.s2 g) I.Sweeping (SPC.with_new SPC.nothing_new (D.oo g <: U64.t)) =
    C.CSWrite r2 (D.oa g) (D.oa g <: hp_addr) (D.oo g <: U64.t) () in
  assert (C.cstart_st r0 == D.s0 g);
  assert (C.cstart_st r1 == C.cstart_st r0);
  assert (C.cstart_st r2 == C.cstart_st r1);
  assert (C.cstart_st r3 == C.cstart_st r2);
  C.CSweep rm2 V.m0 (D.gh g) MP.scan_none () r3 ()
#pop-options

/// B's run, the unit the Pulse `sweep_unit` sweeps.
let i0 (g: heap{V.roomy}) : GTot (p: nat{p < n_pages}) = mixed_state g; V.i0 g

/// After it, and after one slice from cursor 0 with a budget of every page.
let g4 (g: heap{V.roomy}) : GTot heap = fst (SA.step (D.g3 g) (D.s2 g) (i0 g))
let s4 (g: heap{V.roomy}) : GTot pstate = snd (SA.step (D.g3 g) (D.s2 g) (i0 g))
let sl5 (g: heap{V.roomy}) : GTot (heap & pstate & nat) = Inc.slice_from (g4 g) (s4 g) 0 n_pages
let g5 (g: heap{V.roomy}) : GTot heap = let (a, _, _) = sl5 g in a
let s5 (g: heap{V.roomy}) : GTot pstate = let (_, b, _) = sl5 g in b
let p5 (g: heap{V.roomy}) : GTot nat = let (_, _, c) = sl5 g in c

/// The slice reaches the end of the pages, every page swept.
let slice_end (g: heap)
  : Lemma (requires V.roomy)
          (ensures MS.pages_ok_sw (g4 g) (s4 g) /\ MS.pages_ok_sw (g5 g) (s5 g) /\
                   Inc.swept_below (s5 g).pm (p5 g) /\ p5 g >= n_pages)
  = let r = run_sw g in
    let r4 = CI.cyc_unit r (i0 g) in
    C.ccycle_inv r4;
    Inc.cursor_start (s4 g).pm;
    Inc.slice_ok (g4 g) (s4 g) 0 n_pages;
    Inc.slice_full (g4 g) (s4 g) 0 n_pages

/// **The run**: the dark run to its write mid-sweep, then B's run swept as
/// one unit, then one slice to the end, then the end.
let run_incr (g: heap{V.roomy})
  : GTot (C.ccycle (D.h g) (D.rs g) (g5 g) (s5 g) I.Idle (D.since_d g)) =
  slice_end g;
  let r4 = CI.cyc_unit (run_sw g) (i0 g) in
  let r5 = CI.cyc_slice r4 0 n_pages (g5 g) (s5 g) in
  CI.cyc_end r5 (p5 g)

/// **Not trivial**: at the run's state before the unit step, the Pulse
/// code's preconditions hold, A's page is swept and B's run is not; the
/// unit step sweeps B's run; the slice ends with every page swept.
let run_incr_nontrivial (g: heap)
  : Lemma (requires V.roomy)
          (ensures Inc.phase_inv I.Sweeping (D.g3 g) (D.s2 g) /\ map_ok (D.s2 g).pm /\
                   (entry (D.s2 g).pm (i0 g)).kind == LargeHead Wt.kL /\
                   not (entry (D.s2 g).pm (i0 g)).swept /\
                   (entry (s4 g).pm (i0 g)).swept /\
                   GC.Spec.Pages.MarkPhase.all_swept (s5 g))
  = D.alloc_ok g;
    CI.run_pre (run_sw g);
    C.ccycle_inv (run_sw g);
    GC.Spec.Pages.MidSweepStep.step_sw (D.g3 g) (D.s2 g) (i0 g);
    slice_end g;
    Inc.cursor_end (s5 g) (p5 g)

/// **The theorems of the cycle hold of it**: the `Idle` invariant at the
/// end, and A and B survive.
let run_incr_theorems (g: heap)
  : Lemma (requires V.roomy)
          (ensures PA.inv I.Idle (g5 g) (s5 g) /\
                   (forall (x: obj_addr). GC.Gen.MarkPhase.Completeness.reachable_at_start (D.h g) (D.rs g) x ==>
                      Seq.mem x (objects zero_addr (g5 g)) /\ ~(is_blue x (g5 g))))
  = C.ccycle_correct (run_incr g)

/// **The cursor lemmas' hypotheses**, at the run's states: a step at the
/// cursor at the sweep's start (cursor 0), and an allocation and a step
/// with every page below the cursor swept, at the slice's end.
let cursor_witness (g: heap) (col: color) (tag: AT.tag_t) (wz: nat)
  : Lemma (requires V.roomy)
          (ensures MS.pages_ok_sw (D.g3 g) (D.s2 g) /\ Inc.swept_below (D.s2 g).pm 0 /\
                   MS.pages_ok_sw (g5 g) (s5 g) /\ map_ok (s5 g).pm /\
                   Inc.swept_below (s5 g).pm (p5 g) /\ p5 g >= n_pages /\
                   (let (_, st', _) = AT.alloc_col_tag col tag (g5 g) (s5 g) wz in
                    Inc.swept_below st'.pm (p5 g)) /\
                   Inc.swept_below (snd (SA.step (g5 g) (s5 g) (i0 g))).pm (p5 g))
  = C.ccycle_inv (run_sw g);
    Inc.cursor_start (D.s2 g).pm;
    Inc.cursor_step (D.g3 g) (D.s2 g) 0;
    slice_end g;
    MS.pages_ok_sw_elim (g5 g) (s5 g);
    Inc.alloc_cursor col tag (g5 g) (s5 g) wz (p5 g);
    Inc.step_cursor (g5 g) (s5 g) (i0 g) (p5 g)
