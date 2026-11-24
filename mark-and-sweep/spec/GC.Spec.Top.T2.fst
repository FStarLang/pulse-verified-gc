/// ---------------------------------------------------------------------------
/// GC.Spec.Top.T2 - a cycle frees what stop-the-world at its start frees
/// ---------------------------------------------------------------------------
///
/// Design doc §16.7 (T2, parts 2 and 3).  The two runs agree up to `s`
/// (`RunApp.at_pre`), so (4) of each says it frees `stw_freed (at s)`.  By
/// (3b) each keeps its snapshot and what it allocated in the cycle; the
/// snapshots are both what was reachable at `s`, and the stop-the-world
/// run allocates nothing (`stw_allocd`).  `t2_local_ok` and `t2_ok`, for
/// any components and either style.

module GC.Spec.Top.T2

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.RInv
open GC.Spec.Top.StepBase
open GC.Spec.Top.Point
open GC.Spec.Top.Stw
open GC.Spec.Top.RunApp
open GC.Spec.Top.StwBuild
module L = FStar.List.Tot
module C = FStar.Classical
module RF = GC.Spec.Top.RunFacts
module Cy = GC.Spec.Top.Cycle

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

let run_pre_intro (c: comps) (sty: style) (n ny: nat) (es: list event)
  : Lemma (requires faithful c.r /\ run_ok c sty n ny es /\ run_hyps c n ny es)
          (ensures run_pre c sty n ny es)
  = reveal_opaque (`%run_pre) run_pre

let run_pre_elim (c: comps) (sty: style) (n ny: nat) (es: list event)
  : Lemma (requires run_pre c sty n ny es)
          (ensures faithful c.r /\ run_ok c sty n ny es /\ run_hyps c n ny es)
  = reveal_opaque (`%run_pre) run_pre

/// ---------------------------------------------------------------------------
/// The stop-the-world run's cycle
/// ---------------------------------------------------------------------------

let es2 (es: list event) (s a b: nat) : list event = L.append (take s es) (stw_tail a b)

let stw_ev (es: list event) (s a b k: nat)
  : Lemma (requires s <= L.length es /\ k <= a + b + 2)
          (ensures L.length (es2 es s a b) == s + a + b + 3 /\ last (es2 es s a b) == s + a + b + 2 /\
                   s + k < L.length (es2 es s a b) /\
                   (k = 0 ==> ev (es2 es s a b) (s + k) == EStart) /\
                   (0 < k /\ k < a + b + 2 ==> coll (ev (es2 es s a b) (s + k))) /\
                   (k = a + b + 2 ==> ev (es2 es s a b) (s + k) == EEnd))
  = tail_shape a b k;
    len_app es s (stw_tail a b);
    ev_tail es s (stw_tail a b) k

/// The same, by the run's index.
let stw_mid (es: list event) (s a b t: nat)
  : Lemma (requires s <= L.length es /\ s < t /\ t < s + a + b + 2)
          (ensures t < L.length (es2 es s a b) /\ coll (ev (es2 es s a b) t))
  = let k = t - s in
    assert (s + k == t);
    stw_ev es s a b k

let stw_cycle (es: list event) (s a b: nat)
  : Lemma (requires s <= L.length es)
          (ensures is_cycle (es2 es s a b) s (s + a + b + 2) /\ last (es2 es s a b) == s + a + b + 2)
  = stw_ev es s a b 0;
    stw_ev es s a b (a + b + 2);
    let f (t: nat) : Lemma (s < t /\ t < s + a + b + 2 ==>
                            ~(ev (es2 es s a b) t == EStart) /\ ~(ev (es2 es s a b) t == EEnd))
      = if s < t && t < s + a + b + 2 then stw_ev es s a b (t - s) in
    C.forall_intro f

let coll_allocd (#c: comps) (x: config c) (e: event)
  : Lemma (requires coll e) (ensures (step c x e).allocd == x.allocd)
  = match e with
    | ESweep -> (match x.ph with Sweeping p -> () | _ -> ())
    | _ -> ()

/// The stop-the-world run allocates nothing.
let rec stw_allocd (c: comps) (sty: style) (n ny: nat) (es: list event) (s a b t o: nat)
  : Lemma (requires run_pre c sty n ny (es2 es s a b) /\ s <= L.length es /\ s + 1 <= t /\ t <= s + a + b + 2)
          (ensures ~((at c n ny (es2 es s a b) t).allocd o))
          (decreases t)
  = let es' = es2 es s a b in
    stw_cycle es s a b;
    Cy.cyc_intro c sty n ny es' s (s + a + b + 2);
    if t = s + 1 then Cy.cycle_start c sty n ny es' s (s + a + b + 2)
    else begin
      stw_allocd c sty n ny es s a b (t - 1) o;
      stw_mid es s a b (t - 1);
      Cy.step_to c sty n ny es' t;
      coll_allocd (at c n ny es' (t - 1)) (ev es' (t - 1))
    end

/// What a cycle keeps: its snapshot (what was reachable at its start) and
/// what it allocated.
let keeps (c: comps) (sty: style) (n ny: nat) (es: list event) (s j o: nat)
  : Lemma (requires run_pre c sty n ny es /\ is_cycle es s j)
          (ensures in_use_c (at c n ny es (j + 1)) o == true <==>
                   (reachable (wv (at c n ny es s)) o \/ (at c n ny es j).allocd o))
  = Cy.cycle_ok c sty n ny es s j;
    Cy.cyc_intro c sty n ny es s j;
    Cy.in_cycle c sty n ny es s j j;
    Cy.cycle_start c sty n ny es s j

/// ---------------------------------------------------------------------------
/// The equivalence
/// ---------------------------------------------------------------------------

let equiv_ab (c: comps) (sty: style) (n ny: nat) (es: list event) (s j a b: nat)
  : Lemma (requires run_pre c sty n ny es /\ is_cycle es s j /\ run_pre c sty n ny (es2 es s a b))
          (ensures stw_equiv c n ny es s j (es2 es s a b))
  = let es' = es2 es s a b in
    let j' = s + a + b + 2 in
    stw_cycle es s a b;
    let pre (i: nat) : Lemma (i <= s ==> at c n ny es' i == at c n ny es i)
      = if i <= s then at_pre c n ny es s (stw_tail a b) i in
    C.forall_intro pre;
    Cy.cycle_ok c sty n ny es s j;
    Cy.cycle_ok c sty n ny es' s j';
    C.forall_intro (keeps c sty n ny es s j);
    C.forall_intro (keeps c sty n ny es' s j');
    C.forall_intro (stw_allocd c sty n ny es s a b j')

let equiv_of (c: comps) (sty: style) (n ny: nat) (es es': list event) (s j: nat)
  : Lemma (requires run_pre c sty n ny es /\ is_cycle es s j /\ stw_run es s es' /\ run_pre c sty n ny es')
          (ensures stw_equiv c n ny es s j es')
  = eliminate exists (a b: nat). es' == L.append (take s es) (stw_tail a b)
    with equiv_ab c sty n ny es s j a b

/// **T2, with the contracts at the steps of both runs.**
let t2_local_ok (c: comps) (sty: style) : Lemma (t2_local c sty)
  = let f (n ny: nat) (es es': list event) (s j: nat)
      : Lemma (requires faithful c.r /\ run_ok c sty n ny es /\ run_hyps c n ny es /\ is_cycle es s j /\
                        stw_run es s es' /\ run_ok c sty n ny es' /\ run_hyps c n ny es')
              (ensures stw_equiv c n ny es s j es')
      = run_pre_intro c sty n ny es;
        run_pre_intro c sty n ny es';
        equiv_of c sty n ny es es' s j in
    let g (n ny: nat) (es es': list event) (s j: nat)
      : Lemma (faithful c.r ==>
               (run_ok c sty n ny es /\ run_hyps c n ny es /\ is_cycle es s j /\
                stw_run es s es' /\ run_ok c sty n ny es' /\ run_hyps c n ny es' ==>
                stw_equiv c n ny es s j es'))
      = C.move_requires (f n ny es es' s) j in
    let h (n ny: nat) (es es': list event)
      : Lemma (forall (s j: nat). faithful c.r ==>
               (run_ok c sty n ny es /\ run_hyps c n ny es /\ is_cycle es s j /\
                stw_run es s es' /\ run_ok c sty n ny es' /\ run_hyps c n ny es' ==>
                stw_equiv c n ny es s j es'))
      = C.forall_intro_2 (g n ny es es') in
    C.forall_intro_4 h

/// **The stop-the-world run exists, and is a run.**
let stw_exists (c: comps) (sty: style) (n ny: nat) (es: list event) (s j: nat)
  : Lemma (requires components_ok c /\ run_ok c sty n ny es /\ is_cycle es s j)
          (ensures exists (a b: nat). run_pre c sty n ny (es2 es s a b) /\ run_pre c sty n ny es)
  = RF.run_hyps_of_ok c n ny es;
    run_pre_intro c sty n ny es;
    Cy.cyc_intro c sty n ny es s j;
    Cy.cycle_start c sty n ny es s j;
    rinv_at c sty n ny es s;
    at_i c sty n ny es s;
    stw_build sty (at c n ny es s);
    eliminate exists (a b: nat). tail_ok c sty (at c n ny es s) (stw_tail a b)
    with begin
      run_of_tail c sty n ny es s (stw_tail a b);
      run_pre_intro c sty n ny (es2 es s a b)
    end

let t2_run (c: comps) (sty: style) (n ny: nat) (es: list event) (s j: nat)
  : Lemma (requires components_ok c /\ run_ok c sty n ny es /\ is_cycle es s j)
          (ensures exists (es': list event). stw_run es s es' /\ run_ok c sty n ny es' /\ stw_equiv c n ny es s j es')
  = stw_exists c sty n ny es s j;
    eliminate exists (a b: nat). run_pre c sty n ny (es2 es s a b) /\ run_pre c sty n ny es
    with begin
      let es' = es2 es s a b in
      run_pre_elim c sty n ny es';
      equiv_ab c sty n ny es s j a b;
      assert (stw_run es s es')
    end

/// **T2.**
let t2_ok (c: comps) (sty: style) : Lemma (t2 c sty)
  = let f (n ny: nat) (es: list event) (s j: nat)
      : Lemma (components_ok c ==> run_ok c sty n ny es /\ is_cycle es s j ==>
               (exists (es': list event). stw_run es s es' /\ run_ok c sty n ny es' /\ stw_equiv c n ny es s j es'))
      = C.move_requires (t2_run c sty n ny es s) j in
    let g (n ny: nat) (es: list event)
      : Lemma (forall (s j: nat). components_ok c ==> run_ok c sty n ny es /\ is_cycle es s j ==>
               (exists (es': list event). stw_run es s es' /\ run_ok c sty n ny es' /\ stw_equiv c n ny es s j es'))
      = C.forall_intro_2 (f n ny es) in
    C.forall_intro_3 g

/// Both styles, by name.
let t2_both (c: comps)
  : Lemma (t2_local c Sequential /\ t2_local c Incremental /\ t2 c Sequential /\ t2 c Incremental)
  = t2_local_ok c Sequential; t2_local_ok c Incremental;
    t2_ok c Sequential; t2_ok c Incremental
