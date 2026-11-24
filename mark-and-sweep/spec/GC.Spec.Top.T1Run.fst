/// ---------------------------------------------------------------------------
/// GC.Spec.Top.T1Run - T1, part 1: every run without a failed allocation is
/// transparent
/// ---------------------------------------------------------------------------
///
/// Design doc §16.15.  `sim_step` dispatches each event to its lemma
/// (GC.Spec.Top.TrEv*, TrMin*).  Along the run the reference program grows
/// by one event at each program event, and the renaming follows the step
/// (`tr_upto`, `tr_ext`); at the end it is `transparent` (`t1_run`), so
/// `t1_local` holds for any components and either style.

module GC.Spec.Top.T1Run

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.RInv
open GC.Spec.Top.Point
open GC.Spec.Top.Transp
open GC.Spec.Top.TrRef
open GC.Spec.Top.TrVis
open GC.Spec.Top.TrIP
open GC.Spec.Top.TrEvA
module L = FStar.List.Tot
module C = FStar.Classical
module ID = FStar.IndefiniteDescription
module RF = GC.Spec.Top.RunFacts
module RA = GC.Spec.Top.RunApp
module EB = GC.Spec.Top.TrEvB
module EC = GC.Spec.Top.TrEvC
module ED = GC.Spec.Top.TrEvD
module MB = GC.Spec.Top.TrMinB

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// One step, any event
/// ---------------------------------------------------------------------------

let sim_step (#c: comps) (x: config c) (e: event) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x e rn r) (ensures sim_post x e rn r)
  = match e with
    | EAlloc sz tag vs -> ED.sim_malloc x sz tag vs rn r
    | EYoungAlloc sz tag vs -> ED.sim_yalloc x sz tag vs rn r
    | EWrite (Major o) i v -> EC.sim_mwrite x o i v rn r
    | EWrite (Young o) i v -> EC.sim_ywrite x o i v rn r
    | ERead p i -> EB.sim_read x p i rn r
    | ERoots rs -> EB.sim_roots x rs rn r
    | EMinor -> MB.sim_minor x rn r
    | _ -> EB.sim_coll x e rn r

/// ---------------------------------------------------------------------------
/// The run so far
/// ---------------------------------------------------------------------------

[@@"opaque_to_smt"]
let tu_pt (c: comps) (n ny: nat) (es: list event) (prog: list revent) (io: nat -> renaming) (i: nat) : prop =
  scorr (io i) (at c n ny es i) (rat prog (mc es i)) /\ clean (io i) (wv (at c n ny es i)) (rat prog (mc es i))

[@@"opaque_to_smt"]
let tu_ev (c: comps) (n ny: nat) (es: list event) (prog: list revent) (io: nat -> renaming) (i: nat) : prop =
  i < L.length es /\ is_mutator_event (ev es i) ==>
    rok (rat prog (mc es i)) (rev_at prog (mc es i)) /\
    ev_corr (io i) (wv (at c n ny es i)) (rat prog (mc es i)) (ev es i) (rev_at prog (mc es i))

[@@"opaque_to_smt"]
let tu_rd (c: comps) (n ny: nat) (es: list event) (prog: list revent) (io: nat -> renaming) (i: nat) : prop =
  i < L.length es /\ ERead? (ev es i) ==>
    vcorr (io (i + 1)) (wv (at c n ny es (i + 1))) true
      (head_or (VInt 0) (wv (at c n ny es (i + 1))).roots)
      (head_or (RWord (VInt 0)) (rat prog (mc es (i + 1))).rroots)

let tr_upto (c: comps) (n ny: nat) (es: list event) (t: nat) (prog: list revent) (io: nat -> renaming) : prop =
  t <= L.length es /\ L.length prog == mc es t /\
  (forall (i: nat). i <= t ==> tu_pt c n ny es prog io i) /\
  (forall (i: nat). i < t ==> tu_ev c n ny es prog io i) /\
  (forall (i: nat). i < t ==> tu_rd c n ny es prog io i)

let rec mc_mono (es: list event) (i j: nat)
  : Lemma (requires i <= j /\ j <= L.length es) (ensures mc es i <= mc es j) (decreases j)
  = if i = j then () else begin mc_mono es i (j - 1); mc_succ es (j - 1) end

/// ---------------------------------------------------------------------------
/// The start
/// ---------------------------------------------------------------------------

let nothing (_: ptr) : prop = False
let no_names : renaming = fun _ -> None

let init_corr (#c: comps) (x: config c)
  : Lemma (requires rinv x /\ (vw x).roots == [] /\ (forall (y: nat). ~(is_block (vw x).yng y)))
          (ensures scorr no_names x rinit /\ clean no_names (wv x) rinit)
  = let w = vw x in
    vis_sub w nothing;
    scorr_intro no_names w rinit;
    scorr_eq no_names x rinit

let init_world (c: comps) (sty: style) (n ny: nat) (es: list event)
  : Lemma (requires run_pre c sty n ny es)
          (ensures rinv (at c n ny es 0) /\ (vw (at c n ny es 0)).roots == [] /\
                   (forall (y: nat). ~(is_block (vw (at c n ny es 0)).yng y)))
  = rinv_at c sty n ny es 0;
    RF.at_zero c n ny es;
    run_start c sty n ny es;
    let x = at c n ny es 0 in
    vw_views x;
    assert (c.r.yrepr (empty_heap ny) x.w.cyng);
    GC.Spec.Top.Views.yrepr_agree c.r (empty_heap ny) (vw x).yng x.w.cyng;
    let f (y: nat) : Lemma (~(is_block (vw x).yng y))
      = agree_sym (empty_heap ny) (vw x).yng;
        if is_block (vw x).yng y then GC.Spec.Top.Views.ag_hd (vw x).yng (empty_heap ny) y in
    C.forall_intro f

let tr_zero (c: comps) (sty: style) (n ny: nat) (es: list event)
  : Lemma (requires run_pre c sty n ny es) (ensures tr_upto c n ny es 0 [] (fun _ -> no_names))
  = reveal_opaque (`%tu_pt) tu_pt; reveal_opaque (`%tu_ev) tu_ev; reveal_opaque (`%tu_rd) tu_rd;
    init_world c sty n ny es;
    init_corr (at c n ny es 0);
    mc_zero es;
    assert (rat [] 0 == rinit)

/// ---------------------------------------------------------------------------
/// One more step
/// ---------------------------------------------------------------------------

let ext_io (io: nat -> renaming) (t: nat) (rn': renaming) : nat -> renaming =
  fun (i: nat) -> if i <= t then io i else rn'

/// The step's precondition, from the run.
let pre_at (c: comps) (sty: style) (n ny: nat) (es: list event) (t: nat) (prog: list revent) (io: nat -> renaming)
  : Lemma (requires run_pre c sty n ny es /\ no_fail c n ny es /\ tr_upto c n ny es t prog io /\ t < L.length es)
          (ensures sim_pre (at c n ny es t) (ev es t) (io t) (rat prog (mc es t)) /\
                   at c n ny es (t + 1) == step c (at c n ny es t) (ev es t))
  = reveal_opaque (`%tu_pt) tu_pt; reveal_opaque (`%tu_ev) tu_ev; reveal_opaque (`%tu_rd) tu_rd;
    rinv_at c sty n ny es t;
    at_i c sty n ny es t;
    assert (tu_pt c n ny es prog io t);
    rwf_rat prog (mc es t);
    RF.at_succ c n ny es t

/// The old points, with the longer program.
let old_pt (c: comps) (n ny: nat) (es: list event) (t: nat) (prog: list revent) (io: nat -> renaming)
    (re: revent) (rn': renaming) (i: nat)
  : Lemma (requires tr_upto c n ny es t prog io /\ i <= t)
          (ensures tu_pt c n ny es (L.append prog [re]) (ext_io io t rn') i)
  = reveal_opaque (`%tu_pt) tu_pt; reveal_opaque (`%tu_ev) tu_ev; reveal_opaque (`%tu_rd) tu_rd;
    mc_mono es i t;
    rat_snoc_pre prog re (mc es i)

let rev_old (prog: list revent) (re: revent) (m: nat)
  : Lemma (requires m < L.length prog) (ensures rev_at (L.append prog [re]) m == rev_at prog m)
  = RA.index_app_lt prog [re] m

let old_ev (c: comps) (n ny: nat) (es: list event) (t: nat) (prog: list revent) (io: nat -> renaming)
    (re: revent) (rn': renaming) (i: nat)
  : Lemma (requires tr_upto c n ny es t prog io /\ t < L.length es /\ i < t)
          (ensures tu_ev c n ny es (L.append prog [re]) (ext_io io t rn') i /\
                   tu_rd c n ny es (L.append prog [re]) (ext_io io t rn') i)
  = reveal_opaque (`%tu_pt) tu_pt; reveal_opaque (`%tu_ev) tu_ev; reveal_opaque (`%tu_rd) tu_rd;
    mc_mono es i t;
    mc_mono es (i + 1) t;
    mc_succ es i;
    rat_snoc_pre prog re (mc es i);
    rat_snoc_pre prog re (mc es (i + 1));
    assert (tu_ev c n ny es prog io i /\ tu_rd c n ny es prog io i);
    if is_mutator_event (ev es i) then rev_old prog re (mc es i)

let mut_hyps (c: comps) (n ny: nat) (es: list event) (t: nat) (prog: list revent) (io: nat -> renaming)
    (re: revent) (rn': renaming) : prop =
  t < L.length es /\ is_mutator_event (ev es t) /\ L.length prog == mc es t /\
  rok (rat prog (mc es t)) re /\
  ev_corr (io t) (wv (at c n ny es t)) (rat prog (mc es t)) (ev es t) re /\
  scorr rn' (at c n ny es (t + 1)) (rstep (rat prog (mc es t)) re) /\
  clean rn' (wv (at c n ny es (t + 1))) (rstep (rat prog (mc es t)) re)

let new_ev (c: comps) (n ny: nat) (es: list event) (t: nat) (prog: list revent) (io: nat -> renaming)
    (re: revent) (rn': renaming)
  : Lemma (requires mut_hyps c n ny es t prog io re rn')
          (ensures tu_ev c n ny es (L.append prog [re]) (ext_io io t rn') t)
  = reveal_opaque (`%tu_pt) tu_pt; reveal_opaque (`%tu_ev) tu_ev; reveal_opaque (`%tu_rd) tu_rd;
    rev_at_snoc prog re;
    rat_snoc_pre prog re (mc es t)

let new_pt (c: comps) (n ny: nat) (es: list event) (t: nat) (prog: list revent) (io: nat -> renaming)
    (re: revent) (rn': renaming)
  : Lemma (requires mut_hyps c n ny es t prog io re rn')
          (ensures tu_pt c n ny es (L.append prog [re]) (ext_io io t rn') (t + 1))
  = reveal_opaque (`%tu_pt) tu_pt; reveal_opaque (`%tu_ev) tu_ev; reveal_opaque (`%tu_rd) tu_rd;
    mc_succ es t;
    rat_snoc_last prog re

let new_rd (c: comps) (n ny: nat) (es: list event) (t: nat) (prog: list revent) (io: nat -> renaming)
    (re: revent) (rn': renaming)
  : Lemma (requires mut_hyps c n ny es t prog io re rn')
          (ensures tu_rd c n ny es (L.append prog [re]) (ext_io io t rn') t)
  = reveal_opaque (`%tu_pt) tu_pt; reveal_opaque (`%tu_ev) tu_ev; reveal_opaque (`%tu_rd) tu_rd;
    mc_succ es t;
    rat_snoc_last prog re;
    scorr_eq rn' (at c n ny es (t + 1)) (rstep (rat prog (mc es t)) re);
    head_corr rn' (wv (at c n ny es (t + 1))) (rstep (rat prog (mc es t)) re)

let tr_intro (c: comps) (n ny: nat) (es: list event) (t: nat) (prog: list revent) (io: nat -> renaming)
  : Lemma (requires t <= L.length es /\ L.length prog == mc es t /\
                    (forall (i: nat). i <= t ==> tu_pt c n ny es prog io i) /\
                    (forall (i: nat). i < t ==> tu_ev c n ny es prog io i) /\
                    (forall (i: nat). i < t ==> tu_rd c n ny es prog io i))
          (ensures tr_upto c n ny es t prog io)
  = ()

/// **A program event extends the program.**
let tr_ext_mut (c: comps) (n ny: nat) (es: list event) (t: nat) (prog: list revent) (io: nat -> renaming)
    (re: revent) (rn': renaming)
  : Lemma (requires tr_upto c n ny es t prog io /\ mut_hyps c n ny es t prog io re rn')
          (ensures tr_upto c n ny es (t + 1) (L.append prog [re]) (ext_io io t rn'))
  = let prog' = L.append prog [re] in
    let io' = ext_io io t rn' in
    mc_succ es t;
    rev_at_snoc prog re;
    new_ev c n ny es t prog io re rn';
    new_rd c n ny es t prog io re rn';
    new_pt c n ny es t prog io re rn';
    let fp (i: nat) : Lemma (i <= t + 1 ==> tu_pt c n ny es prog' io' i)
      = if i <= t then old_pt c n ny es t prog io re rn' i in
    let fe (i: nat) : Lemma (i < t + 1 ==> tu_ev c n ny es prog' io' i /\ tu_rd c n ny es prog' io' i)
      = if i < t then old_ev c n ny es t prog io re rn' i in
    C.forall_intro fp;
    C.forall_intro fe;
    tr_intro c n ny es (t + 1) prog' io'

let old_pt0 (c: comps) (n ny: nat) (es: list event) (t: nat) (prog: list revent) (io: nat -> renaming)
    (rn': renaming) (i: nat)
  : Lemma (requires tr_upto c n ny es t prog io /\ i <= t)
          (ensures tu_pt c n ny es prog (ext_io io t rn') i /\
                   (i < t ==> tu_ev c n ny es prog (ext_io io t rn') i /\ tu_rd c n ny es prog (ext_io io t rn') i))
  = reveal_opaque (`%tu_pt) tu_pt; reveal_opaque (`%tu_ev) tu_ev; reveal_opaque (`%tu_rd) tu_rd;
    assert (tu_pt c n ny es prog io i);
    if i < t then assert (tu_ev c n ny es prog io i /\ tu_rd c n ny es prog io i)

let coll_new (c: comps) (n ny: nat) (es: list event) (t: nat) (prog: list revent) (io: nat -> renaming)
    (rn': renaming)
  : Lemma (requires t < L.length es /\ ~(is_mutator_event (ev es t)) /\
                    scorr rn' (at c n ny es (t + 1)) (rat prog (mc es t)) /\
                    clean rn' (wv (at c n ny es (t + 1))) (rat prog (mc es t)))
          (ensures tu_pt c n ny es prog (ext_io io t rn') (t + 1) /\
                   tu_ev c n ny es prog (ext_io io t rn') t /\ tu_rd c n ny es prog (ext_io io t rn') t)
  = reveal_opaque (`%tu_pt) tu_pt; reveal_opaque (`%tu_ev) tu_ev; reveal_opaque (`%tu_rd) tu_rd;
    mc_succ es t

/// **A collector event keeps the program.**
let tr_ext_coll (c: comps) (n ny: nat) (es: list event) (t: nat) (prog: list revent) (io: nat -> renaming)
    (rn': renaming)
  : Lemma (requires tr_upto c n ny es t prog io /\ t < L.length es /\ ~(is_mutator_event (ev es t)) /\
                    scorr rn' (at c n ny es (t + 1)) (rat prog (mc es t)) /\
                    clean rn' (wv (at c n ny es (t + 1))) (rat prog (mc es t)))
          (ensures tr_upto c n ny es (t + 1) prog (ext_io io t rn'))
  = let io' = ext_io io t rn' in
    mc_succ es t;
    coll_new c n ny es t prog io rn';
    let fp (i: nat) : Lemma (i <= t + 1 ==> tu_pt c n ny es prog io' i)
      = if i <= t then old_pt0 c n ny es t prog io rn' i in
    let fe (i: nat) : Lemma (i < t + 1 ==> tu_ev c n ny es prog io' i /\ tu_rd c n ny es prog io' i)
      = if i < t then old_pt0 c n ny es t prog io rn' i in
    C.forall_intro fp;
    C.forall_intro fe;
    tr_intro c n ny es (t + 1) prog io'

/// **One more step of the run.**
let tr_step (c: comps) (sty: style) (n ny: nat) (es: list event) (t: nat) (prog: list revent) (io: nat -> renaming)
  : Lemma (requires run_pre c sty n ny es /\ no_fail c n ny es /\ tr_upto c n ny es t prog io /\ t < L.length es)
          (ensures exists (prog': list revent) (io': nat -> renaming). tr_upto c n ny es (t + 1) prog' io')
  = let x = at c n ny es t in
    let e = ev es t in
    let r = rat prog (mc es t) in
    pre_at c sty n ny es t prog io;
    sim_step x e (io t) r;
    if is_mutator_event e then
      eliminate exists (re: revent) (rn': renaming).
        rok r re /\ ev_corr (io t) (wv x) r e re /\ scorr rn' (step c x e) (rstep r re) /\ clean rn' (wv (step c x e)) (rstep r re)
      with begin
        assert (mut_hyps c n ny es t prog io re rn');
        tr_ext_mut c n ny es t prog io re rn'
      end
    else
      eliminate exists (rn': renaming). scorr rn' (step c x e) r /\ clean rn' (wv (step c x e)) r
      with tr_ext_coll c n ny es t prog io rn'

let rec tr_all (c: comps) (sty: style) (n ny: nat) (es: list event) (t: nat)
  : Lemma (requires run_pre c sty n ny es /\ no_fail c n ny es /\ t <= L.length es)
          (ensures exists (prog: list revent) (io: nat -> renaming). tr_upto c n ny es t prog io) (decreases t)
  = if t = 0 then tr_zero c sty n ny es
    else begin
      tr_all c sty n ny es (t - 1);
      eliminate exists (prog: list revent) (io: nat -> renaming). tr_upto c n ny es (t - 1) prog io
      with tr_step c sty n ny es (t - 1) prog io
    end

/// ---------------------------------------------------------------------------
/// T1, part 1
/// ---------------------------------------------------------------------------

let tr_done (c: comps) (n ny: nat) (es: list event) (prog: list revent) (io: nat -> renaming)
  : Lemma (requires tr_upto c n ny es (L.length es) prog io) (ensures transparent c n ny es prog io)
  = reveal_opaque (`%tu_pt) tu_pt; reveal_opaque (`%tu_ev) tu_ev; reveal_opaque (`%tu_rd) tu_rd;
    let t = L.length es in
    let f (i: nat) : Lemma (i <= t ==> scorr (io i) (at c n ny es i) (rat prog (mc es i)))
      = if i <= t then assert (tu_pt c n ny es prog io i) in
    let g (i: nat) : Lemma (i < t /\ is_mutator_event (ev es i) ==>
                            rok (rat prog (mc es i)) (rev_at prog (mc es i)) /\
                            ev_corr (io i) (wv (at c n ny es i)) (rat prog (mc es i)) (ev es i) (rev_at prog (mc es i)))
      = if i < t then assert (tu_ev c n ny es prog io i) in
    let h (i: nat) : Lemma (i < t /\ ERead? (ev es i) ==>
                            vcorr (io (i + 1)) (wv (at c n ny es (i + 1))) true
                              (head_or (VInt 0) (wv (at c n ny es (i + 1))).roots)
                              (head_or (RWord (VInt 0)) (rat prog (mc es (i + 1))).rroots))
      = if i < t then assert (tu_rd c n ny es prog io i) in
    C.forall_intro f;
    C.forall_intro g;
    C.forall_intro h

let run_pre_intro (c: comps) (sty: style) (n ny: nat) (es: list event)
  : Lemma (requires faithful c.r /\ run_ok c sty n ny es /\ run_hyps c n ny es)
          (ensures run_pre c sty n ny es)
  = reveal_opaque (`%run_pre) run_pre

/// **Every run without a failed allocation is transparent.**
let t1_run (c: comps) (sty: style) (n ny: nat) (es: list event)
  : Lemma (requires faithful c.r /\ run_ok c sty n ny es /\ run_hyps c n ny es /\ no_fail c n ny es)
          (ensures exists (prog: list revent) (io: nat -> renaming). transparent c n ny es prog io)
  = run_pre_intro c sty n ny es;
    tr_all c sty n ny es (L.length es);
    eliminate exists (prog: list revent) (io: nat -> renaming). tr_upto c n ny es (L.length es) prog io
    with tr_done c n ny es prog io

/// **T1, part 1**, for any components and either style.
let t1_local_ok (c: comps) (sty: style) : Lemma (t1_local c sty)
  = let f (n ny: nat) (es: list event)
      : Lemma (faithful c.r ==>
               (run_ok c sty n ny es /\ run_hyps c n ny es /\ no_fail c n ny es ==>
                (exists (prog: list revent) (io: nat -> renaming). transparent c n ny es prog io)))
      = C.move_requires (t1_run c sty n ny) es in
    C.forall_intro_3 f

let t1_local_both (c: comps) : Lemma (t1_local c Sequential /\ t1_local c Incremental)
  = t1_local_ok c Sequential; t1_local_ok c Incremental
