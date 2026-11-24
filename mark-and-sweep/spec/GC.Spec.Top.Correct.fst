/// ---------------------------------------------------------------------------
/// GC.Spec.Top.Correct - the top-level theorem
/// ---------------------------------------------------------------------------
///
/// Design doc §16.6 (module 13).  `gc_correct_local` from `points_ok` ((0),
/// every point, every step), `cycle_ok` ((3a), (3b), (4)) and
/// `two_cycles_ok` ((3c)); `gc_correct` from it by
/// `gc_correct_local_implies`.  The style is never used, so both hold for
/// either style.

module GC.Spec.Top.Correct

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.Point
module L = FStar.List.Tot
module C = FStar.Classical
module Cy = GC.Spec.Top.Cycle
module TC = GC.Spec.Top.TwoCycles

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

let run_pre_intro (c: comps) (sty: style) (n ny: nat) (es: list event)
  : Lemma (requires faithful c.r /\ run_ok c sty n ny es /\ run_hyps c n ny es)
          (ensures run_pre c sty n ny es)
  = reveal_opaque (`%run_pre) run_pre

/// **Every run meets (0)-(6).**
let run_correct (c: comps) (sty: style) (n ny: nat) (es: list event)
  : Lemma (requires faithful c.r /\ run_ok c sty n ny es /\ run_hyps c n ny es)
          (ensures conclusions c n ny es)
  = run_pre_intro c sty n ny es;
    points_ok c sty n ny es;
    let f (s j: nat) : Lemma (is_cycle es s j ==> concl_cycle c n ny es s j)
      = C.move_requires (Cy.cycle_ok c sty n ny es s) j in
    C.forall_intro_2 f;
    let g (s1 j1 s2 j2: nat)
      : Lemma (is_cycle es s1 j1 /\ is_cycle es s2 j2 /\ j1 < s2 /\
               (forall (t: nat). j1 < t /\ t < s2 ==> ~(ev es t == EStart)) ==>
               concl_two_cycles c n ny es s1 j1 s2 j2)
      = C.move_requires (TC.two_cycles_ok c sty n ny es s1 j1 s2) j2 in
    C.forall_intro_4 g

/// **gc_correct_local**, for any components and either style.
let gc_correct_local_ok (c: comps) (sty: style) : Lemma (gc_correct_local c sty)
  = let f (n ny: nat) (es: list event)
      : Lemma (faithful c.r ==> (run_ok c sty n ny es /\ run_hyps c n ny es ==> conclusions c n ny es))
      = C.move_requires (run_correct c sty n ny) es in
    C.forall_intro_3 f

/// **gc_correct**, for any components and either style.
let gc_correct_ok (c: comps) (sty: style) : Lemma (gc_correct_local c sty /\ gc_correct c sty)
  = gc_correct_local_ok c sty;
    gc_correct_local_implies c sty

/// Both styles, by name.
let gc_correct_both (c: comps)
  : Lemma (gc_correct_local c Sequential /\ gc_correct_local c Incremental /\
           gc_correct c Sequential /\ gc_correct c Incremental)
  = gc_correct_ok c Sequential;
    gc_correct_ok c Incremental
