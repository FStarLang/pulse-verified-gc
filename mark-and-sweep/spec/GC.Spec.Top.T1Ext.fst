/// ---------------------------------------------------------------------------
/// GC.Spec.Top.T1Ext - T1, part 2: extending a transparent run
/// ---------------------------------------------------------------------------
///
/// Design doc §16.18.  `core E P io`: `E` is a run with no failed
/// allocation that runs the reference program `P` (part 1's `tr_upto`, to
/// its end).  A prefix of a transparent run is transparent, with the prefix
/// of the program (`tr_cut`, `tr_pre`).  The run extends by collector
/// events, keeping the program (`tr_coll_run`), and by a program event that
/// is the next reference event renamed, adding it (`tr_mut_step`).  The
/// replay's chunks: a whole stop-the-world cycle from an idle configuration
/// (`cyc_chunk`), a minor collection (`min_chunk`), a program event
/// (`prog_chunk`); and the event it would perform next (`trans_at`).

module GC.Spec.Top.T1Ext

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.RInv
open GC.Spec.Top.Point
open GC.Spec.Top.Stw
open GC.Spec.Top.Transp
open GC.Spec.Top.TrRef
open GC.Spec.Top.TrVis
open GC.Spec.Top.TrGen
open GC.Spec.Top.TrEvA
open GC.Spec.Top.T1Run
open GC.Spec.Top.T1Re
open GC.Spec.Top.T1Tr
module L = FStar.List.Tot
module C = FStar.Classical
module RF = GC.Spec.Top.RunFacts
module RA = GC.Spec.Top.RunApp
module T2 = GC.Spec.Top.T2
module SB = GC.Spec.Top.StwBuild

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Prefixes
/// ---------------------------------------------------------------------------

let mc_pre (es: list event) (s: nat) (tl: list event) (i: nat)
  : Lemma (requires s <= L.length es /\ i <= s) (ensures mc (L.append (take s es) tl) i == mc es i)
  = RA.take_len s es;
    RA.take_app_le i (take s es) tl;
    RA.take_take i s es

/// **The run so far, cut at `t`, runs the program so far.**
let tr_cut (c: comps) (n ny: nat) (es: list event) (tt: nat) (prog: list revent) (io: nat -> renaming) (t: nat)
  : Lemma (requires tr_upto c n ny es tt prog io /\ t <= tt)
          (ensures tr_upto c n ny es t (take (mc es t) prog) io)
  = reveal_opaque (`%tu_pt) tu_pt; reveal_opaque (`%tu_ev) tu_ev; reveal_opaque (`%tu_rd) tu_rd;
    let k = mc es t in
    mc_mono es t tt;
    RA.take_len k prog;
    let fp (i: nat) : Lemma (i <= t ==> tu_pt c n ny es (take k prog) io i)
      = if i <= t then begin
          mc_mono es i t;
          rat_take prog k (mc es i);
          assert (tu_pt c n ny es prog io i)
        end in
    let fe (i: nat) : Lemma (i < t ==> tu_ev c n ny es (take k prog) io i /\ tu_rd c n ny es (take k prog) io i)
      = if i < t then begin
          mc_mono es (i + 1) t;
          mc_succ es i;
          rat_take prog k (mc es i);
          rat_take prog k (mc es (i + 1));
          assert (tu_ev c n ny es prog io i /\ tu_rd c n ny es prog io i);
          if is_mutator_event (ev es i) then rev_take prog k (mc es i)
        end in
    C.forall_intro fp;
    C.forall_intro fe

let pre_pt (c: comps) (n ny: nat) (es: list event) (s: nat) (tl: list event) (prog: list revent) (io: nat -> renaming) (i: nat)
  : Lemma (requires s <= L.length es /\ i <= s /\ tu_pt c n ny es prog io i)
          (ensures tu_pt c n ny (L.append (take s es) tl) prog io i)
  = reveal_opaque (`%tu_pt) tu_pt;
    RA.at_pre c n ny es s tl i;
    mc_pre es s tl i

let pre_ev (c: comps) (n ny: nat) (es: list event) (s: nat) (tl: list event) (prog: list revent) (io: nat -> renaming) (i: nat)
  : Lemma (requires s <= L.length es /\ i < s /\ tu_ev c n ny es prog io i /\ tu_rd c n ny es prog io i)
          (ensures tu_ev c n ny (L.append (take s es) tl) prog io i /\ tu_rd c n ny (L.append (take s es) tl) prog io i)
  = reveal_opaque (`%tu_ev) tu_ev; reveal_opaque (`%tu_rd) tu_rd;
    RA.at_pre c n ny es s tl i;
    RA.at_pre c n ny es s tl (i + 1);
    mc_pre es s tl i;
    mc_pre es s tl (i + 1);
    RA.ev_pre es s tl i;
    RA.len_app es s tl

/// **A transparent prefix stays transparent in a longer run.**
let tr_pre (c: comps) (n ny: nat) (es: list event) (s: nat) (tl: list event) (t: nat) (prog: list revent) (io: nat -> renaming)
  : Lemma (requires tr_upto c n ny es t prog io /\ t <= s /\ s <= L.length es)
          (ensures tr_upto c n ny (L.append (take s es) tl) t prog io)
  = RA.len_app es s tl;
    mc_pre es s tl t;
    let fp (i: nat) : Lemma (i <= t ==> tu_pt c n ny (L.append (take s es) tl) prog io i)
      = if i <= t then pre_pt c n ny es s tl prog io i in
    let fe (i: nat) : Lemma (i < t ==> tu_ev c n ny (L.append (take s es) tl) prog io i /\
                                       tu_rd c n ny (L.append (take s es) tl) prog io i)
      = if i < t then pre_ev c n ny es s tl prog io i in
    C.forall_intro fp;
    C.forall_intro fe;
    tr_intro c n ny (L.append (take s es) tl) t prog io

/// ---------------------------------------------------------------------------
/// One more event
/// ---------------------------------------------------------------------------

/// **A collector event keeps the program.**
let tr_coll_step (c: comps) (sty: style) (n ny: nat) (es: list event) (t: nat) (prog: list revent) (io: nat -> renaming)
  : Lemma (requires run_pre c sty n ny es /\ no_fail c n ny es /\ tr_upto c n ny es t prog io /\ t < L.length es /\
                    ~(is_mutator_event (ev es t)))
          (ensures exists (io': nat -> renaming). tr_upto c n ny es (t + 1) prog io')
  = let x = at c n ny es t in
    let e = ev es t in
    let r = rat prog (mc es t) in
    pre_at c sty n ny es t prog io;
    sim_step x e (io t) r;
    eliminate exists (rn': renaming). scorr rn' (step c x e) r /\ clean rn' (wv (step c x e)) r
    with tr_ext_coll c n ny es t prog io rn'

/// **A program event that is `re`, renamed, adds `re`.**
let tr_mut_step (c: comps) (sty: style) (n ny: nat) (es: list event) (t: nat) (prog: list revent) (io: nat -> renaming)
    (re: revent)
  : Lemma (requires run_pre c sty n ny es /\ no_fail c n ny es /\ tr_upto c n ny es t prog io /\ t < L.length es /\
                    is_mutator_event (ev es t) /\ rok (rat prog (mc es t)) re /\
                    ev_corr (io t) (wv (at c n ny es t)) (rat prog (mc es t)) (ev es t) re)
          (ensures exists (io': nat -> renaming). tr_upto c n ny es (t + 1) (L.append prog [re]) io')
  = let x = at c n ny es t in
    let e = ev es t in
    let r = rat prog (mc es t) in
    pre_at c sty n ny es t prog io;
    sim_step x e (io t) r;
    eliminate exists (re': revent) (rn': renaming).
      rok r re' /\ ev_corr (io t) (wv x) r e re' /\ scorr rn' (step c x e) (rstep r re') /\ clean rn' (wv (step c x e)) (rstep r re')
    with begin
      scorr_eq (io t) x r;
      ev_unique (io t) (wv x) r e re re';
      assert (mut_hyps c n ny es t prog io re rn');
      tr_ext_mut c n ny es t prog io re rn'
    end

/// **Collector events keep the program.**
let rec tr_coll_run (c: comps) (sty: style) (n ny: nat) (es: list event) (t u: nat) (prog: list revent) (io: nat -> renaming)
  : Lemma (requires run_pre c sty n ny es /\ no_fail c n ny es /\ tr_upto c n ny es t prog io /\
                    t <= u /\ u <= L.length es /\ (forall (i: nat). t <= i /\ i < u ==> ~(is_mutator_event (ev es i))))
          (ensures exists (io': nat -> renaming). tr_upto c n ny es u prog io')
          (decreases (u - t))
  = if t = u then ()
    else begin
      tr_coll_step c sty n ny es t prog io;
      eliminate exists (io1: nat -> renaming). tr_upto c n ny es (t + 1) prog io1
      with tr_coll_run c sty n ny es (t + 1) u prog io1
    end

/// ---------------------------------------------------------------------------
/// Appending to a run
/// ---------------------------------------------------------------------------

/// `E` is a run with no failed allocation, running `P` to its end.
let core (c: comps) (sty: style) (n ny: nat) (es: list event) (prog: list revent) (io: nat -> renaming) : prop =
  run_pre c sty n ny es /\ no_fail c n ny es /\ tr_upto c n ny es (L.length es) prog io

let app_run (c: comps) (sty: style) (n ny: nat) (es tl: list event)
  : Lemma (requires run_pre c sty n ny es /\ RA.tail_ok c sty (at c n ny es (L.length es)) tl)
          (ensures run_pre c sty n ny (L.append es tl))
  = T2.run_pre_elim c sty n ny es;
    take_all es;
    RA.run_of_tail c sty n ny es (L.length es) tl;
    T2.run_pre_intro c sty n ny (L.append es tl)

/// No allocation fails, if none of the new events does.
let app_nofail (c: comps) (n ny: nat) (es tl: list event)
  : Lemma (requires no_fail c n ny es /\
                    (forall (k: nat). k < L.length tl ==> alloc_succeeds (at c n ny (L.append es tl) (L.length es + k)) (L.index tl k)))
          (ensures no_fail c n ny (L.append es tl))
  = take_all es;
    RA.len_app es (L.length es) tl;
    let f (i: nat) : Lemma (i < L.length (L.append es tl) ==> alloc_succeeds (at c n ny (L.append es tl) i) (ev (L.append es tl) i))
      = if i < L.length (L.append es tl) then begin
          if i < L.length es then begin
            RA.at_pre c n ny es (L.length es) tl i;
            RA.ev_pre es (L.length es) tl i
          end else begin
            let k = i - L.length es in
            RA.ev_tail es (L.length es) tl k
          end
        end in
    C.forall_intro f

let app_tr (c: comps) (n ny: nat) (es tl: list event) (prog: list revent) (io: nat -> renaming)
  : Lemma (requires tr_upto c n ny es (L.length es) prog io)
          (ensures tr_upto c n ny (L.append es tl) (L.length es) prog io)
  = take_all es;
    tr_pre c n ny es (L.length es) tl (L.length es) prog io

let app_ev (es tl: list event) (k: nat)
  : Lemma (requires k < L.length tl)
          (ensures L.length (L.append es tl) == L.length es + L.length tl /\
                   ev (L.append es tl) (L.length es + k) == L.index tl k)
  = take_all es;
    L.append_length es tl;
    RA.ev_tail es (L.length es) tl k;
    assert (L.append (take (L.length es) es) tl == L.append es tl)

let app_coll (es tl: list event)
  : Lemma (requires forall (k: nat). k < L.length tl ==> ~(is_mutator_event (L.index tl k)))
          (ensures forall (i: nat). L.length es <= i /\ i < L.length (L.append es tl) ==>
                     ~(is_mutator_event (ev (L.append es tl) i)))
  = let f (i: nat) : Lemma (L.length es <= i /\ i < L.length (L.append es tl) ==>
                            ~(is_mutator_event (ev (L.append es tl) i)))
      = L.append_length es tl;
        if L.length es <= i && i < L.length (L.append es tl) then app_ev es tl (i - L.length es) in
    C.forall_intro f

let app_at (c: comps) (n ny: nat) (es tl: list event) (i: nat)
  : Lemma (requires i <= L.length es) (ensures at c n ny (L.append es tl) i == at c n ny es i)
  = take_all es;
    RA.at_pre c n ny es (L.length es) tl i

let one_idx (e: event) : Lemma (L.length [e] == 1 /\ (forall (k: nat). k < L.length [e] ==> L.index [e] k == e))
  = assert_norm (L.length [e] == 1);
    assert_norm (L.index [e] 0 == e)

let tail_one (c: comps) (sty: style) (x: config c) (e: event)
  : Lemma (requires RA.conds c sty x e) (ensures RA.tail_ok c sty x [e])
  = SB.tail_cons c sty x e [];
    assert_norm (RA.tail_ok c sty (step c x e) [] == True)

/// **Collector events extend a transparent run.**
let ext_coll (c: comps) (sty: style) (n ny: nat) (es tl: list event) (prog: list revent) (io: nat -> renaming)
  : Lemma (requires core c sty n ny es prog io /\ RA.tail_ok c sty (at c n ny es (L.length es)) tl /\
                    (forall (k: nat). k < L.length tl ==> ~(is_mutator_event (L.index tl k)) /\ ~(EAlloc? (L.index tl k))))
          (ensures exists (io': nat -> renaming). core c sty n ny (L.append es tl) prog io')
  = let es' = L.append es tl in
    app_run c sty n ny es tl;
    let fa (k: nat) : Lemma (k < L.length tl ==> alloc_succeeds (at c n ny es' (L.length es + k)) (L.index tl k)) = () in
    C.forall_intro fa;
    app_nofail c n ny es tl;
    app_tr c n ny es tl prog io;
    app_coll es tl;
    L.append_length es tl;
    tr_coll_run c sty n ny es' (L.length es) (L.length es') prog io

/// **A program event extends a transparent run, and its program.**
let ext_mut (c: comps) (sty: style) (n ny: nat) (es: list event) (e: event) (prog: list revent) (io: nat -> renaming)
    (re: revent)
  : Lemma (requires core c sty n ny es prog io /\ RA.conds c sty (at c n ny es (L.length es)) e /\
                    alloc_succeeds (at c n ny es (L.length es)) e /\ is_mutator_event e /\
                    rok (rat prog (L.length prog)) re /\
                    ev_corr (io (L.length es)) (wv (at c n ny es (L.length es))) (rat prog (L.length prog)) e re)
          (ensures exists (io': nat -> renaming). core c sty n ny (L.append es [e]) (L.append prog [re]) io')
  = let es' = L.append es [e] in
    let t = L.length es in
    tail_one c sty (at c n ny es t) e;
    app_run c sty n ny es [e];
    app_at c n ny es [e] t;
    app_ev es [e] 0;
    one_idx e;
    app_nofail c n ny es [e];
    app_tr c n ny es [e] prog io;
    mc_pre es t [e] t;
    take_all es;
    assert (L.length es' == t + 1);
    tr_mut_step c sty n ny es' t prog io re;
    eliminate exists (io': nat -> renaming). tr_upto c n ny es' (t + 1) (L.append prog [re]) io'
    with assert (core c sty n ny es' (L.append prog [re]) io')

/// ---------------------------------------------------------------------------
/// The configuration at the end
/// ---------------------------------------------------------------------------

let last_x (c: comps) (n ny: nat) (es: list event) : GTot (config c) = at c n ny es (L.length es)

let last_snoc (c: comps) (n ny: nat) (es: list event) (e: event)
  : Lemma (last_x c n ny (L.append es [e]) == step c (last_x c n ny es) e)
  = let es' = L.append es [e] in
    assert_norm (L.length [e] == 1);
    assert_norm (L.index [e] 0 == e);
    app_ev es [e] 0;
    app_at c n ny es [e] (L.length es);
    RF.at_succ c n ny es' (L.length es)

/// What the end of a transparent run gives.
let core_end (c: comps) (sty: style) (n ny: nat) (es: list event) (prog: list revent) (io: nat -> renaming)
  : Lemma (requires core c sty n ny es prog io)
          (ensures (let x = last_x c n ny es in
                    faithful c.r /\ rinv x /\ L.length prog == mc es (L.length es) /\
                    scorr_w (io (L.length es)) (wv x) (rat prog (L.length prog)) /\
                    clean (io (L.length es)) (wv x) (rat prog (L.length prog))))
  = reveal_opaque (`%tu_pt) tu_pt;
    let x = last_x c n ny es in
    assert (tu_pt c n ny es prog io (L.length es));
    scorr_eq (io (L.length es)) x (rat prog (L.length prog));
    rinv_at c sty n ny es (L.length es);
    run_start c sty n ny es

let wfacts (#c: comps) (x: config c)
  : Lemma (requires faithful c.r /\ rinv x) (ensures wbound c.r (wv x) /\ uc (wv x).maj /\ uc (wv x).yng)
  = reveal_opaque (`%r_heap) (r_heap #c);
    vw_views x;
    uc_wf (vw x).maj;
    uc_young (vw x).yng

/// **The replay can perform the program's event `m`.**
let trans_at (c: comps) (sty: style) (n ny: nat) (es: list event) (prog: list revent) (m: nat) (io: nat -> renaming)
  : Lemma (requires core c sty n ny es (take m prog) io /\ m < L.length prog /\ rok_all prog /\
                    wit c (rat prog m) (rev_at prog m) /\ names_reach (rat prog m) (rev_at prog m))
          (ensures (let x = last_x c n ny es in
                    exists (e: event). is_mutator_event e /\ mutator_ok x e /\
                      ev_corr (io (L.length es)) (wv x) (rat prog m) e (rev_at prog m)))
  = let x = last_x c n ny es in
    let rn = io (L.length es) in
    RA.take_len m prog;
    rat_take prog m m;
    core_end c sty n ny es (take m prog) io;
    wfacts x;
    rpos_at prog m;
    assert (dst rn (wv x) (rat prog m));
    tev_exists c rn (wv x) (rat prog m) (rev_at prog m)

/// ---------------------------------------------------------------------------
/// The chunks
/// ---------------------------------------------------------------------------

let idle_ok (#c: comps) (x: config c) : prop = Idle? x.ph /\ x.stopped == false

/// The end of a whole cycle is idle.
let cyc_end (c: comps) (sty: style) (n ny: nat) (es: list event) (s: nat) (a: slices) (b: nat)
  : Lemma (requires run_pre c sty n ny (L.append (take s es) (stw_tail a b)) /\ s <= L.length es)
          (ensures idle_ok (last_x c n ny (L.append (take s es) (stw_tail a b))))
  = let es' = L.append (take s es) (stw_tail a b) in
    let j = s + L.length a + b + 2 in
    T2.stw_ev es s a b (L.length a + b + 2);
    at_i c sty n ny es' j;
    RF.at_succ c n ny es' j

/// Its events are collector events, none an allocation.
let cyc_shape (es: list event) (a: slices) (b: nat)
  : Lemma (forall (k: nat). k < L.length (stw_tail a b) ==>
             ~(is_mutator_event (L.index (stw_tail a b) k)) /\ ~(EAlloc? (L.index (stw_tail a b) k)))
  = let f (k: nat) : Lemma (k < L.length (stw_tail a b) ==>
                            ~(is_mutator_event (L.index (stw_tail a b) k)) /\ ~(EAlloc? (L.index (stw_tail a b) k)))
      = SB.tail_shape a b 0;
        if k < L.length (stw_tail a b) then SB.tail_shape a b k in
    C.forall_intro f

/// **A whole stop-the-world cycle.**
let cyc_chunk (c: comps) (sty: style) (n ny: nat) (es: list event) (prog: list revent) (io: nat -> renaming)
  : Lemma (requires components_ok c /\ core c sty n ny es prog io /\ idle_ok (last_x c n ny es))
          (ensures exists (a: slices) (b: nat) (io': nat -> renaming).
                     core c sty n ny (L.append es (stw_tail a b)) prog io' /\
                     idle_ok (last_x c n ny (L.append es (stw_tail a b))))
  = let x = last_x c n ny es in
    rinv_at c sty n ny es (L.length es);
    SB.stw_build sty x;
    eliminate exists (a: slices) (b: nat). RA.tail_ok c sty x (stw_tail a b)
    with begin
      cyc_shape es a b;
      ext_coll c sty n ny es (stw_tail a b) prog io;
      take_all es;
      cyc_end c sty n ny es (L.length es) a b
    end

let minor_conds (c: comps) (sty: style) (x: config c)
  : Lemma (requires components_ok c /\ rinv x /\ x.stopped == false) (ensures RA.conds c sty x EMinor)
  = hyps_of_ok c x EMinor

/// **A minor collection** (it may run out of room).
let min_chunk (c: comps) (sty: style) (n ny: nat) (es: list event) (prog: list revent) (io: nat -> renaming)
  : Lemma (requires components_ok c /\ core c sty n ny es prog io /\ idle_ok (last_x c n ny es))
          (ensures exists (io': nat -> renaming).
                     core c sty n ny (L.append es [EMinor]) prog io' /\
                     Idle? (last_x c n ny (L.append es [EMinor])).ph)
  = let x = last_x c n ny es in
    let es' = L.append es [EMinor] in
    rinv_at c sty n ny es (L.length es);
    minor_conds c sty x;
    tail_one c sty x EMinor;
    assert_norm (L.length [EMinor] == 1);
    assert_norm (L.index [EMinor] 0 == EMinor);
    one_idx EMinor;
    ext_coll c sty n ny es [EMinor] prog io;
    last_snoc c n ny es EMinor

let mut_keeps (#c: comps) (x: config c) (e: event)
  : Lemma (requires is_mutator_event e)
          (ensures (step c x e).ph == x.ph /\ (step c x e).stopped == x.stopped)
  = match e with
    | EAlloc sz tag vs -> let (_, _, r) = c.a.alloc x.ph x.w.cmaj x.ast sz tag in (match r with Ok _ -> () | NoRoom -> ())
    | EYoungAlloc sz tag vs -> (match c.r.yalloc x.w.cyng sz tag vs with Some _ -> () | None -> ())
    | EWrite (Major _) _ _ | EWrite (Young _) _ _ -> ()
    | ERead (Major _) _ | ERead (Young _) _ -> ()
    | ERoots _ -> ()

/// **A program event, the next reference event renamed.**
let prog_chunk (c: comps) (sty: style) (n ny: nat) (es: list event) (prog: list revent) (m: nat) (io: nat -> renaming)
    (e: event)
  : Lemma (requires (let x = last_x c n ny es in
                     components_ok c /\ core c sty n ny es (take m prog) io /\ idle_ok x /\
                     m < L.length prog /\ rok (rat prog m) (rev_at prog m) /\
                     is_mutator_event e /\ mutator_ok x e /\ enabled c x e /\ alloc_succeeds x e /\
                     ev_corr (io (L.length es)) (wv x) (rat prog m) e (rev_at prog m)))
          (ensures exists (io': nat -> renaming).
                     core c sty n ny (L.append es [e]) (take (m + 1) prog) io' /\
                     idle_ok (last_x c n ny (L.append es [e])))
  = let x = last_x c n ny es in
    let es' = L.append es [e] in
    hyps_of_ok c x e;
    assert (RA.conds c sty x e);
    RA.take_len m prog;
    rat_take prog m m;
    take_succ_rev prog m;
    last_snoc c n ny es e;
    mut_keeps x e;
    assert (idle_ok (last_x c n ny es'));
    ext_mut c sty n ny es e (take m prog) io (rev_at prog m)
