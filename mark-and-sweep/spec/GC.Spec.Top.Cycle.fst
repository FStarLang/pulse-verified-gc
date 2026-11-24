/// ---------------------------------------------------------------------------
/// GC.Spec.Top.Cycle - the clauses of one cycle: (3a), (3b), (4)
/// ---------------------------------------------------------------------------
///
/// Design doc §16.5, §16.6 (module 11).  A cycle runs from `EStart` at `s`
/// to `EEnd` at `j`, with no other start or end between.  Inside it the
/// snapshot is fixed and the phase is not idle (`in_cycle`); the allocated
/// set only grows, and only by blocks that were not in use (`cyc`, from the
/// step lemmas).  At `j` the sweep is done: everything in use is swept, so
/// live (`done_live`).
///   - (3b): in use at the end is live, and live is in use (R6).
///   - (4): an object in use at `s` and not in the snapshot stays out of the
///     live set while it stays in use (`never_allocd`), so the sweep frees
///     it; an object of the snapshot stays in use.
///   - (3a): each word of such an object is, at every point of the cycle, a
///     word of the pending object, a free word, or a word of a block
///     allocated in the cycle and in use (`word_at`).

module GC.Spec.Top.Cycle

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.Views
open GC.Spec.Top.Words
open GC.Spec.Top.RInv
open GC.Spec.Top.StepBase
open GC.Spec.Top.Point
module L = FStar.List.Tot
module C = FStar.Classical
module RF = GC.Spec.Top.RunFacts

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// What one step does to the bookkeeping
/// ---------------------------------------------------------------------------

let step_book (#c: comps) (x: config c) (e: event)
  : Lemma (requires ~(EStart? e))
          (ensures (step c x e).snap == x.snap /\
                   (forall (p: nat). x.allocd p ==> (step c x e).allocd p) /\
                   (~(EEnd? e) /\ ~(Idle? x.ph) ==> ~(Idle? (step c x e).ph)))
  = match e with
    | EAlloc sz tag vs ->
      let (h', st', r) = c.a.alloc x.ph x.w.cmaj x.ast sz tag in
      (match r with NoRoom -> () | Ok o -> ())
    | EYoungAlloc sz tag vs -> (match c.r.yalloc x.w.cyng sz tag vs with Some _ -> () | None -> ())
    | EMinor -> (match c.n.collect x.ph x.ast x.w with OutOfRoom -> () | Done _ _ _ _ -> ())
    | ESweep -> (match x.ph with Sweeping p -> () | _ -> ())
    | _ -> ()

let step_start (#c: comps) (x: config c)
  : Lemma (ensures (step c x EStart).snap == reachable (vw x) /\ (forall (p: nat). ~((step c x EStart).allocd p)) /\
                   (step c x EStart).ph == Marking)
  = ()

/// The end of a cycle changes the phase only.
let step_end (#c: comps) (x: config c) (o n: nat)
  : Lemma (requires faithful c.r /\ has_view x)
          (ensures (let x' = step c x EEnd in
                    x'.snap == x.snap /\ x'.allocd == x.allocd /\
                    in_use_c x' o == in_use_c x o /\ (free_word_c x' n <==> free_word_c x n) /\
                    covers (mj x') o n == covers (mj x) o n))
  = let x' = step c x EEnd in
    vw_views x;
    assert (views x' (vw x));
    vw_agree x' (vw x);
    ag_in_use c.a x.ast x.w.cmaj (mj x) (mj x') o;
    ag_free_word c.a x.ast x.w.cmaj (mj x) (mj x') n;
    ag_covers (mj x) (mj x') o n

/// While marking or sweeping, live is in use.
let live_iu (#c: comps) (x: config c) (o: nat)
  : Lemma (requires rinv x /\ ~(Idle? x.ph) /\ live x o) (ensures in_use_c x o)
  = reveal_opaque (`%r_live) (r_live #c)

/// When the sweep is done, in use is live.
let done_live (#c: comps) (x: config c) (o: nat)
  : Lemma (requires rinv x /\ hyps_at c x EEnd /\ enabled c x EEnd /\ in_use_c x o) (ensures live x o)
  = let Sweeping p = x.ph in
    vw_views x;
    reveal_opaque (`%r_heap) (r_heap #c);
    reveal_opaque (`%r_live) (r_live #c);
    assert (sweep_done_m c.s p x.w.cmaj x.ast (mj x))

/// ---------------------------------------------------------------------------
/// A cycle
/// ---------------------------------------------------------------------------

[@@"opaque_to_smt"]
let cyc_pre (c: comps) (sty: style) (n ny: nat) (es: list event) (s j: nat) : prop =
  run_pre c sty n ny es /\ is_cycle es s j

let cyc_facts (c: comps) (sty: style) (n ny: nat) (es: list event) (s j: nat)
  : Lemma (requires cyc_pre c sty n ny es s j)
          (ensures run_pre c sty n ny es /\ s < j /\ j < L.length es /\ ev es s == EStart /\ ev es j == EEnd)
  = reveal_opaque (`%cyc_pre) cyc_pre

let cyc_mid (c: comps) (sty: style) (n ny: nat) (es: list event) (s j t: nat)
  : Lemma (requires cyc_pre c sty n ny es s j /\ s < t /\ t < j)
          (ensures t < L.length es /\ ~(EStart? (ev es t)) /\ ~(EEnd? (ev es t)))
  = reveal_opaque (`%cyc_pre) cyc_pre

let xa (c: comps) (n ny: nat) (es: list event) (t: nat) : GTot (config c) = at c n ny es t

/// One step of the run.
let step_i (c: comps) (sty: style) (n ny: nat) (es: list event) (t: nat)
  : Lemma (requires run_pre c sty n ny es /\ t < L.length es)
          (ensures at c n ny es (t + 1) == step c (at c n ny es t) (ev es t) /\
                   step_post (at c n ny es t) (ev es t) (at c n ny es (t + 1)) /\
                   rinv (at c n ny es t) /\ concl_point (at c n ny es t) /\ concl_point (at c n ny es (t + 1)) /\
                   hyps_at c (at c n ny es t) (ev es t) /\ enabled c (at c n ny es t) (ev es t))
  = RF.at_succ c n ny es t;
    at_i c sty n ny es t;
    step_at c sty n ny es t;
    rinv_at c sty n ny es t;
    point_at c sty n ny es t;
    point_at c sty n ny es (t + 1)

/// The same, by the later point.
let step_to (c: comps) (sty: style) (n ny: nat) (es: list event) (t: nat)
  : Lemma (requires run_pre c sty n ny es /\ 0 < t /\ t <= L.length es)
          (ensures at c n ny es t == step c (at c n ny es (t - 1)) (ev es (t - 1)) /\
                   step_post (at c n ny es (t - 1)) (ev es (t - 1)) (at c n ny es t) /\
                   rinv (at c n ny es (t - 1)) /\ concl_point (at c n ny es (t - 1)) /\ concl_point (at c n ny es t))
  = step_i c sty n ny es (t - 1)

/// Inside the cycle: the snapshot of `s + 1`, not idle.
let rec in_cycle (c: comps) (sty: style) (n ny: nat) (es: list event) (s j t: nat)
  : Lemma (requires cyc_pre c sty n ny es s j /\ s + 1 <= t /\ t <= j)
          (ensures (at c n ny es t).snap == (at c n ny es (s + 1)).snap /\ ~(Idle? (at c n ny es t).ph))
          (decreases t)
  = cyc_facts c sty n ny es s j;
    if t = s + 1 then begin
      step_i c sty n ny es s;
      step_start (at c n ny es s)
    end else begin
      in_cycle c sty n ny es s j (t - 1);
      cyc_mid c sty n ny es s j (t - 1);
      step_to c sty n ny es t;
      step_book (at c n ny es (t - 1)) (ev es (t - 1))
    end

/// The snapshot is what was reachable at `s`, and it starts empty-handed.
let cycle_start (c: comps) (sty: style) (n ny: nat) (es: list event) (s j: nat)
  : Lemma (requires cyc_pre c sty n ny es s j)
          (ensures (at c n ny es (s + 1)).snap == reachable (vw (at c n ny es s)) /\
                   (forall (p: nat). ~((at c n ny es (s + 1)).allocd p)) /\
                   Idle? (at c n ny es s).ph)
  = cyc_facts c sty n ny es s j;
    step_i c sty n ny es s;
    step_start (at c n ny es s)

/// The end: what `xf` reads is what `xe` reads.
let cycle_end (c: comps) (sty: style) (n ny: nat) (es: list event) (s j: nat) (o w: nat)
  : Lemma (requires cyc_pre c sty n ny es s j)
          (ensures (let xe = at c n ny es j in let xf = at c n ny es (j + 1) in
                    xf.snap == xe.snap /\ xf.allocd == xe.allocd /\
                    in_use_c xf o == in_use_c xe o /\ (free_word_c xf w <==> free_word_c xe w) /\
                    covers (mj xf) o w == covers (mj xe) o w /\
                    (in_use_c xe o ==> live xe o)))
  = cyc_facts c sty n ny es s j;
    step_i c sty n ny es j;
    run_start c sty n ny es;
    let xe = at c n ny es j in
    step_end xe o w;
    if in_use_c xe o then done_live xe o

/// ---------------------------------------------------------------------------
/// (3b)
/// ---------------------------------------------------------------------------

let survivors (c: comps) (sty: style) (n ny: nat) (es: list event) (s j o: nat)
  : Lemma (requires cyc_pre c sty n ny es s j)
          (ensures in_use_c (at c n ny es (j + 1)) o == true <==>
                   ((at c n ny es j).snap o \/ (at c n ny es j).allocd o))
  = cyc_facts c sty n ny es s j;
    cycle_end c sty n ny es s j o 0;
    in_cycle c sty n ny es s j j;
    rinv_at c sty n ny es j;
    if FStar.IndefiniteDescription.strong_excluded_middle (live (at c n ny es j) o) then
      live_iu (at c n ny es j) o

/// ---------------------------------------------------------------------------
/// (4)
/// ---------------------------------------------------------------------------

/// Out of the snapshot and in use throughout: never allocated in the cycle.
let rec never_allocd (c: comps) (sty: style) (n ny: nat) (es: list event) (s j o t: nat)
  : Lemma (requires cyc_pre c sty n ny es s j /\ s + 1 <= t /\ t <= j /\
                    (forall (t': nat). s + 1 <= t' /\ t' <= j ==> in_use_c (at c n ny es t') o == true))
          (ensures ~((at c n ny es t).allocd o))
          (decreases t)
  = cyc_facts c sty n ny es s j;
    if t = s + 1 then cycle_start c sty n ny es s j
    else begin
      never_allocd c sty n ny es s j o (t - 1);
      cyc_mid c sty n ny es s j (t - 1);
      step_to c sty n ny es t
    end

/// A snapshot object is in use throughout the cycle.
let snap_in_use (c: comps) (sty: style) (n ny: nat) (es: list event) (s j o t: nat)
  : Lemma (requires cyc_pre c sty n ny es s j /\ (at c n ny es (s + 1)).snap o /\ s + 1 <= t /\ t <= j + 1)
          (ensures in_use_c (at c n ny es t) o == true)
  = cyc_facts c sty n ny es s j;
    if t = j + 1 then begin
      cycle_end c sty n ny es s j o 0;
      in_cycle c sty n ny es s j j;
      rinv_at c sty n ny es j;
      live_iu (at c n ny es j) o
    end else begin
      in_cycle c sty n ny es s j t;
      rinv_at c sty n ny es t;
      live_iu (at c n ny es t) o
    end

let freed_stw (c: comps) (sty: style) (n ny: nat) (es: list event) (s j o: nat)
  : Lemma (requires cyc_pre c sty n ny es s j /\ freed_in c n ny es s j o)
          (ensures stw_freed (at c n ny es s) o)
  = cyc_facts c sty n ny es s j;
    cycle_start c sty n ny es s j;
    if FStar.IndefiniteDescription.strong_excluded_middle (reachable (vw (at c n ny es s)) o) then
      eliminate exists (t: nat). s <= t /\ t <= j /\ in_use_c (at c n ny es (t + 1)) o == false
      with snap_in_use c sty n ny es s j o (t + 1)

let stw_freed_in (c: comps) (sty: style) (n ny: nat) (es: list event) (s j o: nat)
  : Lemma (requires cyc_pre c sty n ny es s j /\ stw_freed (at c n ny es s) o)
          (ensures freed_in c n ny es s j o)
  = cyc_facts c sty n ny es s j;
    cycle_start c sty n ny es s j;
    if FStar.IndefiniteDescription.strong_excluded_middle
         (forall (t': nat). s + 1 <= t' /\ t' <= j ==> in_use_c (at c n ny es t') o == true) then begin
      never_allocd c sty n ny es s j o j;
      in_cycle c sty n ny es s j j;
      cycle_end c sty n ny es s j o 0
    end else begin
      eliminate exists (t': nat). ~(s + 1 <= t' /\ t' <= j ==> in_use_c (at c n ny es t') o == true)
      with assert (s <= t' - 1 /\ t' - 1 <= j /\ in_use_c (at c n ny es ((t' - 1) + 1)) o == false)
    end

let freed_iff (c: comps) (sty: style) (n ny: nat) (es: list event) (s j o: nat)
  : Lemma (requires cyc_pre c sty n ny es s j)
          (ensures freed_in c n ny es s j o <==> stw_freed (at c n ny es s) o)
  = C.move_requires (freed_stw c sty n ny es s j) o;
    C.move_requires (stw_freed_in c sty n ny es s j) o

/// ---------------------------------------------------------------------------
/// (3a)
/// ---------------------------------------------------------------------------

/// The fate of word `w` of object `o` at point `t` of the cycle.
let word_ok (#c: comps) (x: config c) (o w: nat) : prop =
  (in_use_c x o == true /\ covers (mj x) o w /\ ~(live x o)) \/
  free_word_c x w \/
  (exists (y: nat). x.allocd y /\ in_use_c x y == true /\ covers (mj x) y w)

let in_use_covers (#c: comps) (x x': config c) (y w: nat)
  : Lemma (requires cyc x x' /\ in_use_c x y == true /\ in_use_c x' y == true /\ covers (mj x') y w)
          (ensures covers (mj x) y w)
  = ()

/// One step of the cycle keeps `word_ok`.
let word_step (#c: comps) (x x': config c) (o w: nat)
  : Lemma (requires rinv x' /\ concl_point x /\ concl_point x' /\ cyc x x' /\
                    x'.snap == x.snap /\ (forall (p: nat). x.allocd p ==> x'.allocd p) /\ ~(Idle? x'.ph) /\
                    word_ok x o w)
          (ensures word_ok x' o w)
  = if FStar.IndefiniteDescription.strong_excluded_middle (in_use_c x o == true /\ covers (mj x) o w /\ ~(live x o))
    then begin
      if in_use_c x' o then () else ()
    end
    else if FStar.IndefiniteDescription.strong_excluded_middle (free_word_c x w) then begin
      word_xor c.a x'.ast x'.w.cmaj (mj x') w;
      word_xor c.a x.ast x.w.cmaj (mj x) w;
      if FStar.IndefiniteDescription.strong_excluded_middle (free_word_c x' w) then ()
      else
        eliminate exists (y: nat). covers (mj x') y w /\ in_use c.a x'.ast x'.w.cmaj (mj x') y
        with begin
          if in_use_c x y then begin
            in_use_covers x x' y w;
            in_use_not_free c.a x.ast x.w.cmaj (mj x) y w
          end
        end
    end else begin
      eliminate exists (y: nat). x.allocd y /\ in_use_c x y == true /\ covers (mj x) y w
      with begin
        live_iu x' y;
        assert (covers (mj x') y w)
      end
    end

let rec word_at (c: comps) (sty: style) (n ny: nat) (es: list event) (s j o w t: nat)
  : Lemma (requires cyc_pre c sty n ny es s j /\ s + 1 <= t /\ t <= j /\
                    in_use_c (at c n ny es s) o == true /\ ~((at c n ny es (s + 1)).snap o) /\
                    covers (mj (at c n ny es s)) o w)
          (ensures word_ok (at c n ny es t) o w)
          (decreases t)
  = cyc_facts c sty n ny es s j;
    if t = s + 1 then begin
      step_i c sty n ny es s;
      cycle_start c sty n ny es s j;
      let x0 = at c n ny es s in
      assert (kept x0 o)
    end else begin
      word_at c sty n ny es s j o w (t - 1);
      cyc_mid c sty n ny es s j (t - 1);
      step_to c sty n ny es t;
      in_cycle c sty n ny es s j t;
      in_cycle c sty n ny es s j (t - 1);
      step_book (at c n ny es (t - 1)) (ev es (t - 1));
      rinv_at c sty n ny es t;
      word_step (at c n ny es (t - 1)) (at c n ny es t) o w
    end

let word_end (c: comps) (sty: style) (n ny: nat) (es: list event) (s j o w: nat)
  : Lemma (requires cyc_pre c sty n ny es s j /\ in_use_c (at c n ny es s) o == true /\
                    ~((at c n ny es (s + 1)).snap o) /\ covers (mj (at c n ny es s)) o w)
          (ensures free_word_c (at c n ny es (j + 1)) w \/
                   (exists (y: nat). (at c n ny es j).allocd y /\ in_use_c (at c n ny es (j + 1)) y == true /\
                                     covers (mj (at c n ny es (j + 1))) y w))
  = cyc_facts c sty n ny es s j;
    word_at c sty n ny es s j o w j;
    let xe = at c n ny es j in
    cycle_end c sty n ny es s j o w;
    if FStar.IndefiniteDescription.strong_excluded_middle (free_word_c xe w) then ()
    else if FStar.IndefiniteDescription.strong_excluded_middle (in_use_c xe o == true /\ covers (mj xe) o w /\ ~(live xe o))
    then ()
    else
      eliminate exists (y: nat). xe.allocd y /\ in_use_c xe y == true /\ covers (mj xe) y w
      with cycle_end c sty n ny es s j y w

let cyc_intro (c: comps) (sty: style) (n ny: nat) (es: list event) (s j: nat)
  : Lemma (requires run_pre c sty n ny es /\ is_cycle es s j) (ensures cyc_pre c sty n ny es s j)
  = reveal_opaque (`%cyc_pre) cyc_pre

/// **(3a), (3b) and (4) for every cycle of a run.**
let cycle_ok (c: comps) (sty: style) (n ny: nat) (es: list event) (s j: nat)
  : Lemma (requires run_pre c sty n ny es /\ is_cycle es s j) (ensures concl_cycle c n ny es s j)
  = cyc_intro c sty n ny es s j;
    C.forall_intro_2 (fun o w -> C.move_requires (word_end c sty n ny es s j o) w);
    C.forall_intro (survivors c sty n ny es s j);
    C.forall_intro (freed_iff c sty n ny es s j)
