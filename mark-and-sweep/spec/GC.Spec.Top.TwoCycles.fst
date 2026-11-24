/// ---------------------------------------------------------------------------
/// GC.Spec.Top.TwoCycles - clause (3c)
/// ---------------------------------------------------------------------------
///
/// Design doc §16.6 (module 12).  An object in use and unreachable at `t`
/// stays unreachable while it stays in use (`rback`, from every step lemma).
/// So if it is still in use at the start `s2` of the next cycle, it is in the
/// stop-the-world set at `s2`, and by (4) the cycle `s2..j2` frees it.

module GC.Spec.Top.TwoCycles

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.StepBase
open GC.Spec.Top.Point
module L = FStar.List.Tot
module C = FStar.Classical
module Cy = GC.Spec.Top.Cycle

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// Unreachable and in use at `t`, in use through `t'`: unreachable at `t'`.
let rec unreach_at (c: comps) (sty: style) (n ny: nat) (es: list event) (t o t': nat)
  : Lemma (requires run_pre c sty n ny es /\ t <= t' /\ t' <= L.length es /\
                    ~(reachable (wv (at c n ny es t)) o) /\
                    (forall (u: nat). t <= u /\ u <= t' ==> in_use_c (at c n ny es u) o == true))
          (ensures ~(reachable (wv (at c n ny es t')) o))
          (decreases t')
  = if t' = t then ()
    else begin
      unreach_at c sty n ny es t o (t' - 1);
      Cy.step_to c sty n ny es t';
      assert (in_use_c (at c n ny es (t' - 1)) o == true)
    end

/// **(3c) for one object.**
let two_obj (c: comps) (sty: style) (n ny: nat) (es: list event) (s1 j1 s2 j2 t o: nat)
  : Lemma (requires run_pre c sty n ny es /\ is_cycle es s1 j1 /\ is_cycle es s2 j2 /\ j1 < s2 /\
                    s1 <= t /\ t <= j1 /\
                    in_use_c (at c n ny es t) o == true /\ ~(reachable (wv (at c n ny es t)) o))
          (ensures exists (t': nat). t < t' /\ t' <= j2 + 1 /\ in_use_c (at c n ny es t') o == false)
  = if FStar.IndefiniteDescription.strong_excluded_middle
         (forall (u: nat). t <= u /\ u <= s2 ==> in_use_c (at c n ny es u) o == true) then begin
      unreach_at c sty n ny es t o s2;
      Cy.cycle_ok c sty n ny es s2 j2;
      assert (stw_freed (at c n ny es s2) o);
      assert (freed_in c n ny es s2 j2 o);
      eliminate exists (u: nat). s2 <= u /\ u <= j2 /\ in_use_c (at c n ny es (u + 1)) o == false
      with assert (t < u + 1 /\ u + 1 <= j2 + 1)
    end else
      eliminate exists (u: nat). ~(t <= u /\ u <= s2 ==> in_use_c (at c n ny es u) o == true)
      with assert (t < u /\ u <= j2 + 1)

/// **(3c) for every pair of cycles.**  (The hypothesis that no cycle starts
/// between the two is not needed.)
let two_cycles_ok (c: comps) (sty: style) (n ny: nat) (es: list event) (s1 j1 s2 j2: nat)
  : Lemma (requires run_pre c sty n ny es /\ is_cycle es s1 j1 /\ is_cycle es s2 j2 /\ j1 < s2)
          (ensures concl_two_cycles c n ny es s1 j1 s2 j2)
  = let f (t o: nat)
      : Lemma ((s1 <= t /\ t <= j1 /\
                in_use_c (at c n ny es t) o == true /\ ~(reachable (wv (at c n ny es t)) o)) ==>
               (exists (t': nat). t < t' /\ t' <= j2 + 1 /\ in_use_c (at c n ny es t') o == false))
      = C.move_requires (two_obj c sty n ny es s1 j1 s2 j2 t) o in
    C.forall_intro_2 f
