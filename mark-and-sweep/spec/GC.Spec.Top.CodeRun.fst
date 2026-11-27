/// ---------------------------------------------------------------------------
/// GC.Spec.Top.CodeRun - the runs the code makes, one event at a time
/// ---------------------------------------------------------------------------
///
/// Design doc §18.1.  The code keeps, as ghost state, the list of events it
/// has performed (`es`); its concrete state represents `cur c n ny es`, the
/// configuration after them.  A run grows one event at a time (`snoc`): when
/// the event is allowed at `cur es` (enabled, in the style, the program's
/// obligations), `es @ [e]` is a run and its configuration is `step` of the
/// previous one.  At every point of a run the conclusions of `gc_correct`
/// hold (`point`); among them the allocator's invariant, which the code's
/// preconditions need.  For any collector (`comps`); the pages and first-fit
/// wrappers instantiate it.

module GC.Spec.Top.CodeRun

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
module L = FStar.List.Tot
module RA = GC.Spec.Top.RunApp
module RF = GC.Spec.Top.RunFacts

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The configuration after the events `es`.
let cur (c: comps) (n ny: nat) (es: list event) : GTot (config c) = at c n ny es (L.length es)

/// What one event asks of the configuration it runs from.
let allowed (c: comps) (sty: style) (x: config c) (e: event) : prop =
  enabled c x e /\ style_ok sty x e /\ mutator_ok x e

#push-options "--fuel 1"
let rec take_all (#t: Type) (l: list t) : Lemma (ensures take (L.length l) l == l) (decreases l)
  = match l with [] -> () | _ :: tl -> take_all tl
#pop-options

let cur_exec (c: comps) (n ny: nat) (es: list event)
  : Lemma (cur c n ny es == exec c (init_config c n ny) es)
  = take_all es

/// **No event yet**: the initial configuration, a run.
#push-options "--fuel 1"
let nil_run (c: comps) (sty: style) (n ny: nat)
  : Lemma (requires c.r.size_ok n /\ c.r.ysize_ok ny)
          (ensures run_ok c sty n ny [] /\ cur c n ny [] == init_config c n ny)
  = ()
#pop-options

/// **One more event.**
#push-options "--fuel 1"
let snoc (c: comps) (sty: style) (n ny: nat) (es: list event) (e: event)
  : Lemma (requires components_ok c /\ run_ok c sty n ny es /\ allowed c sty (cur c n ny es) e)
          (ensures run_ok c sty n ny (L.append es [e]) /\
                   cur c n ny (L.append es [e]) == step c (cur c n ny es) e)
  = RF.run_hyps_of_ok c n ny es;
    hyps_of_ok c (cur c n ny es) e;
    assert (RA.tail_ok c sty (step c (cur c n ny es) e) []);
    assert (RA.tail_ok c sty (cur c n ny es) [e]);
    take_all es;
    assert (at c n ny es (L.length es) == cur c n ny es);
    RA.run_of_tail c sty n ny es (L.length es) [e];
    assert (L.append (take (L.length es) es) [e] == L.append es [e]);
    L.append_length es [e];
    cur_exec c n ny (L.append es [e]);
    cur_exec c n ny es;
    RF.exec_append c (init_config c n ny) es [e];
    assert (exec c (cur c n ny es) [e] == exec c (step c (cur c n ny es) e) []);
    assert (exec c (step c (cur c n ny es) e) [] == step c (cur c n ny es) e)
#pop-options

/// **At every point of a run**, the conclusions' facts of a point: among
/// them the allocator's invariant.
let point (c: comps) (sty: style) (n ny: nat) (es: list event)
  : Lemma (requires components_ok c /\ run_ok c sty n ny es)
          (ensures concl_point (cur c n ny es) /\ c.a.inv (cur c n ny es).ph (cur c n ny es).w.cmaj (cur c n ny es).ast)
  = GC.Spec.Top.Correct.gc_correct_ok c sty;
    assert (conclusions c n ny es)

/// **The run invariant at every point of a run**, and what one more step
/// keeps (`Point.step_post`: among others, every kept block stays in use
/// with its size and tag, clause (1a)).
let rinv_cur (c: comps) (sty: style) (n ny: nat) (es: list event)
  : Lemma (requires components_ok c /\ run_ok c sty n ny es)
          (ensures GC.Spec.Top.RInv.rinv (cur c n ny es))
  = RF.run_hyps_of_ok c n ny es;
    GC.Spec.Top.Correct.run_pre_intro c sty n ny es;
    GC.Spec.Top.Point.rinv_at c sty n ny es (L.length es)

let step_facts (c: comps) (sty: style) (n ny: nat) (es: list event) (e: event)
  : Lemma (requires components_ok c /\ run_ok c sty n ny es /\ allowed c sty (cur c n ny es) e)
          (ensures GC.Spec.Top.RInv.rinv (cur c n ny es) /\
                   GC.Spec.Top.Point.step_post (cur c n ny es) e (step c (cur c n ny es) e))
  = rinv_cur c sty n ny es;
    hyps_of_ok c (cur c n ny es) e;
    GC.Spec.Top.Point.step_ok (cur c n ny es) e
