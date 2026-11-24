/// ---------------------------------------------------------------------------
/// GC.Spec.Top.Point - every step and every point of a run
/// ---------------------------------------------------------------------------
///
/// Design doc §16.6 (module 10).  `step_ok` dispatches each event to its
/// step lemma (GC.Spec.Top.Step*); `rinv_at` carries the run invariant along
/// the run, from `rinv_init`; `points_ok` gives clause (0), `concl_point` at
/// every point and `concl_step` at every step, and, for the cycle clauses,
/// `rback` and `cyc` at every step.

module GC.Spec.Top.Point

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.RInv
open GC.Spec.Top.StepBase
module L = FStar.List.Tot
module C = FStar.Classical
module RF = GC.Spec.Top.RunFacts
module SMu = GC.Spec.Top.StepMut
module SSw = GC.Spec.Top.StepSweep
module SMk = GC.Spec.Top.StepMark
module SAl = GC.Spec.Top.StepAlloc
module SWr = GC.Spec.Top.StepWrite
module SMi = GC.Spec.Top.StepMinor

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// What one step gives.
let step_post (#c: comps) (x: config c) (e: event) (x': config c) : prop =
  rinv x' /\ concl_step x e x' /\ rback x x' /\ cyc x x'

/// **One step, any event.**
let step_ok (#c: comps) (x: config c) (e: event)
  : Lemma (requires faithful c.r /\ rinv x /\ hyps_at c x e /\ enabled c x e /\ mutator_ok x e)
          (ensures step_post x e (step c x e))
  = match e with
    | EAlloc sz tag vs -> SAl.alloc_step x sz tag vs
    | EYoungAlloc sz tag vs -> SMu.yalloc_step x sz tag vs
    | EWrite (Major o) i v -> SWr.write_step x o i v
    | EWrite (Young o) i v -> SMu.ywrite_step x o i v
    | ERead (Major o) i -> SMu.read_major_step x o i
    | ERead (Young o) i -> SMu.read_young_step x o i
    | ERoots rs -> SMu.roots_step x rs
    | EMinor -> SMi.minor_step x
    | EStart -> SMk.start_step x
    | ESlice -> SMk.slice_step x
    | EHandover -> SSw.handover_step x
    | ESweep -> SSw.sweep_step x
    | EEnd -> SSw.end_step x

/// The hypotheses of a run (sealed: `at_i`, `run_start`).
[@@"opaque_to_smt"]
let run_pre (c: comps) (sty: style) (n ny: nat) (es: list event) : prop =
  faithful c.r /\ run_ok c sty n ny es /\ run_hyps c n ny es

let at_i (c: comps) (sty: style) (n ny: nat) (es: list event) (i: nat)
  : Lemma (requires run_pre c sty n ny es /\ i < L.length es)
          (ensures (let x = at c n ny es i in let e = ev es i in
                    enabled c x e /\ style_ok sty x e /\ mutator_ok x e /\ hyps_at c x e /\ faithful c.r))
  = reveal_opaque (`%run_pre) run_pre

let run_start (c: comps) (sty: style) (n ny: nat) (es: list event)
  : Lemma (requires run_pre c sty n ny es)
          (ensures faithful c.r /\ c.r.size_ok n /\ c.r.ysize_ok ny /\ init_at c.r c.a n /\ yinit_ok c.r ny)
  = reveal_opaque (`%run_pre) run_pre

/// **The invariant at every point of a run.**
let rec rinv_at (c: comps) (sty: style) (n ny: nat) (es: list event) (i: nat)
  : Lemma (requires run_pre c sty n ny es /\ i <= L.length es)
          (ensures rinv (at c n ny es i)) (decreases i)
  = if i = 0 then begin
      RF.at_zero c n ny es;
      run_start c sty n ny es;
      rinv_init c n ny
    end else begin
      rinv_at c sty n ny es (i - 1);
      at_i c sty n ny es (i - 1);
      RF.at_succ c n ny es (i - 1);
      step_ok (at c n ny es (i - 1)) (ev es (i - 1))
    end

/// **Every step of a run.**
let step_at (c: comps) (sty: style) (n ny: nat) (es: list event) (i: nat)
  : Lemma (requires run_pre c sty n ny es /\ i < L.length es)
          (ensures step_post (at c n ny es i) (ev es i) (at c n ny es (i + 1)))
  = rinv_at c sty n ny es i;
    at_i c sty n ny es i;
    RF.at_succ c n ny es i;
    step_ok (at c n ny es i) (ev es i)

let point_at (c: comps) (sty: style) (n ny: nat) (es: list event) (i: nat)
  : Lemma (requires run_pre c sty n ny es /\ i <= L.length es) (ensures concl_point (at c n ny es i))
  = rinv_at c sty n ny es i;
    run_start c sty n ny es;
    point_of_rinv (at c n ny es i)

/// **(0), (1a), (1b), (2), the read clause, (3d), (5) and (6).**
let points_ok (c: comps) (sty: style) (n ny: nat) (es: list event)
  : Lemma (requires run_pre c sty n ny es)
          (ensures (forall (o: nat). in_use_c (at c n ny es 0) o == false) /\
                   (forall (i: nat). i <= L.length es ==> concl_point (at c n ny es i)) /\
                   (forall (i: nat). i < L.length es ==> concl_step (at c n ny es i) (ev es i) (at c n ny es (i + 1))))
  = RF.at_zero c n ny es;
    run_start c sty n ny es;
    rinv_init c n ny;
    C.forall_intro (C.move_requires (point_at c sty n ny es));
    let f (i: nat) : Lemma (i < L.length es ==> concl_step (at c n ny es i) (ev es i) (at c n ny es (i + 1)))
      = if i < L.length es then step_at c sty n ny es i in
    C.forall_intro f
