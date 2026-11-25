/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PWHyps - the pages witness runs meet every hypothesis
/// ---------------------------------------------------------------------------
///
/// Design doc §17.  Under `PWPre.pw_room` (at least 12 pages, a nursery of
/// at least 4 words), for each pages witness run (sequential `PWSeq.es_seq`,
/// incremental `PWIncB.es_inc`) and its cycle:
///   - `seq_hyps`, `inc_hyps`: every hypothesis of `gc_correct` and
///     `gc_correct_local` (`components_ok`, `run_ok`, `run_hyps`), of T1
///     (`no_fail`; for part 2, `is_cycle` and, of every reference program
///     the run is transparent with, `names_reachable`), of T2 (`is_cycle`)
///     and of `t2_local` (a stop-the-world run, itself a run with the
///     contracts at its steps);
///   - `seq_concl`, `inc_concl`: so the theorems' conclusions hold of the
///     runs, none of them vacuously: (0)-(6), the stop-the-world replay of
///     the cycle (T1), and the equivalence with stop-the-world (T2).

module GC.Spec.Top.PWHyps

open GC.Spec.Top.Heap
open GC.Spec.Top.Run
open GC.Spec.Top.Stw
open GC.Spec.Top.Transp
open GC.Spec.Top.PWDesc
open GC.Spec.Top.PWPre
module L = FStar.List.Tot
module M = GC.Spec.Top.Heap
module T = GC.Spec.Top.Iface
module W = GC.Spec.Top.Word
module PC = GC.Spec.Top.PagesComps
module RF = GC.Spec.Top.RunFacts
module TN = GC.Spec.Top.TrNames
module SQ = GC.Spec.Top.PWSeq
module SF = GC.Spec.Top.PWSeqF
module SN = GC.Spec.Top.PWNamesS
module IB = GC.Spec.Top.PWIncB
module IF = GC.Spec.Top.PWIncF
module IN = GC.Spec.Top.PWNamesI

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The pages collector's contracts hold: there is a page.
let room_ok () : Lemma (requires pw_room) (ensures components_ok pc /\ cok)
  = assert (GC.Spec.Pages.Layout.n_pages > 0);
    PC.pages_components_ok ();
    cok_intro ()

/// Every hypothesis of the theorems, for a run and its cycle `s..j`.
let all_hyps (sty: style) (es: list event) (s j: nat) : prop =
  components_ok pc /\ run_ok pc sty W.msize W.ywords es /\ run_hyps pc W.msize W.ywords es /\
  no_fail pc W.msize W.ywords es /\ is_cycle es s j /\
  (forall (prog: list revent) (io: nat -> renaming).
     transparent pc W.msize W.ywords es prog io ==> names_reachable prog) /\
  (exists (es': list event). stw_run es s es' /\ run_ok pc sty W.msize W.ywords es' /\ run_hyps pc W.msize W.ywords es')

/// What the theorems then give, for the run.
let c_t1 (sty: style) (es: list event) (s: nat) : prop =
  exists (prog: list revent) (io: nat -> renaming).
    transparent pc W.msize W.ywords es prog io /\ names_reachable prog /\ stw_replay pc sty W.msize W.ywords es s prog

let c_t2 (sty: style) (es: list event) (s j: nat) : prop =
  exists (es': list event). stw_run es s es' /\ run_ok pc sty W.msize W.ywords es' /\ stw_equiv pc W.msize W.ywords es s j es'

let all_concl (sty: style) (es: list event) (s j: nat) : prop =
  conclusions pc W.msize W.ywords es /\ c_t1 sty es s /\ c_t2 sty es s j

/// From the run's facts to every hypothesis.
let hyps_of (sty: style) (es: list event) (s j: nat)
  : Lemma (requires components_ok pc /\ run_ok pc sty W.msize W.ywords es /\ run_hyps pc W.msize W.ywords es /\
                    no_fail pc W.msize W.ywords es /\ is_cycle es s j /\
                    (forall (i: nat). i < L.length es /\ is_mutator_event (ev es i) ==>
                       TN.enamed (wv (at pc W.msize W.ywords es i)) (ev es i)))
          (ensures all_hyps sty es s j)
  = let nm (prog: list revent) (io: nat -> renaming)
      : Lemma (transparent pc W.msize W.ywords es prog io ==> names_reachable prog)
      = if FStar.IndefiniteDescription.strong_excluded_middle (transparent pc W.msize W.ywords es prog io)
        then TN.names_of pc W.msize W.ywords es prog io in
    FStar.Classical.forall_intro_2 nm;
    let ex () : Lemma (exists (es': list event). stw_run es s es' /\ run_ok pc sty W.msize W.ywords es' /\
                                                run_hyps pc W.msize W.ywords es')
      = GC.Spec.Top.T2.t2_run pc sty W.msize W.ywords es s j;
        eliminate exists (es': list event). stw_run es s es' /\ run_ok pc sty W.msize W.ywords es' /\
                                           stw_equiv pc W.msize W.ywords es s j es'
        with begin
          RF.run_hyps_of_ok pc W.msize W.ywords es';
          assert (stw_run es s es' /\ run_ok pc sty W.msize W.ywords es' /\ run_hyps pc W.msize W.ywords es')
        end in
    ex ()

/// From every hypothesis to the conclusions.
let concl_of (sty: style) (es: list event) (s j: nat)
  : Lemma (requires all_hyps sty es s j) (ensures all_concl sty es s j)
  = GC.Spec.Top.Correct.gc_correct_ok pc sty;
    assert (conclusions pc W.msize W.ywords es);
    let t2p () : Lemma (c_t2 sty es s j)
      = GC.Spec.Top.T2.t2_run pc sty W.msize W.ywords es s j;
        eliminate exists (es': list event). stw_run es s es' /\ run_ok pc sty W.msize W.ywords es' /\
                                           stw_equiv pc W.msize W.ywords es s j es'
        with introduce exists (es2: list event). stw_run es s es2 /\ run_ok pc sty W.msize W.ywords es2 /\
                                                 stw_equiv pc W.msize W.ywords es s j es2
             with es' and () in
    let t1p () : Lemma (c_t1 sty es s)
      = GC.Spec.Top.T1.t1_ok pc sty;
        assert (t1 pc sty);
        eliminate exists (prog: list revent) (io: nat -> renaming).
                    transparent pc W.msize W.ywords es prog io /\
                    (names_reachable prog ==> (forall (s j: nat). is_cycle es s j ==> stw_replay pc sty W.msize W.ywords es s prog))
        with begin
          assert (names_reachable prog);
          assert (stw_replay pc sty W.msize W.ywords es s prog);
          introduce exists (p2: list revent) (i2: nat -> renaming).
            transparent pc W.msize W.ywords es p2 i2 /\ names_reachable p2 /\ stw_replay pc sty W.msize W.ywords es s p2
          with prog io and ()
        end in
    t1p (); t2p ()

/// ---------------------------------------------------------------------------
/// The two runs
/// ---------------------------------------------------------------------------

/// **The sequential run meets every hypothesis**, its cycle from 7 to 14 + k.
let seq_hyps () : Lemma (requires pw_room)
  (ensures all_hyps Sequential (SQ.es_seq ()) 7 (14 + SQ.ksw ()) /\
           GC.Spec.Top.PWList.every_event (SQ.es_seq ()) /\ SQ.ksw () > 0)
  = room_ok ();
    SQ.seq_run ();
    SF.seq_cycle ();
    SF.seq_every_event ();
    SF.ksw_pos ();
    SN.seq_named ();
    hyps_of Sequential (SQ.es_seq ()) 7 (14 + SQ.ksw ())

/// **The incremental run meets every hypothesis**, its cycle from 7 to 21 + k.
let inc_hyps () : Lemma (requires pw_room)
  (ensures all_hyps Incremental (IB.es_inc ()) 7 (21 + IB.ksw ()) /\
           GC.Spec.Top.PWList.every_event (IB.es_inc ()) /\ IB.ksw () > 0)
  = room_ok ();
    IB.inc_run ();
    IF.inc_cycle ();
    IF.inc_every_event ();
    IF.ksw_pos ();
    IN.inc_named ();
    hyps_of Incremental (IB.es_inc ()) 7 (21 + IB.ksw ())

/// **So the theorems say something of both runs.**
let seq_concl () : Lemma (requires pw_room) (ensures all_concl Sequential (SQ.es_seq ()) 7 (14 + SQ.ksw ()))
  = seq_hyps (); concl_of Sequential (SQ.es_seq ()) 7 (14 + SQ.ksw ())

let inc_concl () : Lemma (requires pw_room) (ensures all_concl Incremental (IB.es_inc ()) 7 (21 + IB.ksw ()))
  = inc_hyps (); concl_of Incremental (IB.es_inc ()) 7 (21 + IB.ksw ())

/// What the runs show, beyond the hypotheses (GC.Spec.Top.PWSeqF, PWIncF).
let nontrivial () : Lemma (requires pw_room)
  (ensures (* the cycle's start: A, B, K reachable, C in use and unreachable *)
           M.reachable (SF.w7 ()) (xA ()) /\ M.reachable (SF.w7 ()) (xB ()) /\ M.reachable (SF.w7 ()) (xK ()) /\
           iu (x7 ()) (xC ()) == true /\ ~(M.reachable (SF.w7 ()) (xC ())) /\
           (* freed by the cycle, in both runs *)
           iu (SN.atn (15 + SQ.ksw ())) (xC ()) == false /\ iu (IF.atn (22 + IB.ksw ())) (xC ()) == false /\
           (* the barrier darkens, while marking *)
           M.col_of (mx (IF.atn 9)) (xB ()) == M.White /\ M.col_of (mx (IF.atn 10)) (xB ()) == M.Grey /\
           (* the minor collections inside the cycle promote both young blocks *)
           T.Marking? (IF.atn 12).ph /\ T.Done? (GC.Spec.Top.PWMinor.mres (IF.atn 12)) /\
           Some? (GC.Spec.Top.PWMinor.mfwd (IF.atn 12) 0) /\ Some? (GC.Spec.Top.PWMinor.mfwd (IF.atn 12) 2) /\
           T.Sweeping? (IF.atn 19).ph /\ T.Done? (GC.Spec.Top.PWMinor.mres (IF.atn 19)) /\
           Some? (GC.Spec.Top.PWMinor.mfwd (IF.atn 19) 0) /\ Some? (GC.Spec.Top.PWMinor.mfwd (IF.atn 19) 2))
  = room_ok ();
    SF.seq_start (); SF.seq_freed ();
    IF.inc_freed (); IF.inc_darkens (); IF.inc_promotes ()
