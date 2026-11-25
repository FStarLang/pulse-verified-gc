/// ---------------------------------------------------------------------------
/// GC.Spec.Top.T1 - T1: the collector is invisible to the program
/// ---------------------------------------------------------------------------
///
/// Design doc §16.7, §16.15-§16.18.  `t1_ok`: T1 (`Transp.t1`), for any
/// components and either style, from both parts for one run
/// (`T1Rep.t1_run2`); `t1_both` adds part 1 with the contracts at the steps
/// taken (`T1Run.t1_local_ok`).

module GC.Spec.Top.T1

open GC.Spec.Top.Heap
open GC.Spec.Top.Run
open GC.Spec.Top.Transp
module L = FStar.List.Tot
module R = GC.Spec.Top.T1Rep
module TR = GC.Spec.Top.T1Run

/// `t1`, word for word.  (The solver does not unfold `t1` against the
/// conclusion as stated; the two are equal by definition, `t1_eq`.)
let t1_body (c: comps) (sty: style) : prop =
  components_ok c ==>
  (forall (n ny: nat) (es: list event).
     run_ok c sty n ny es /\ no_fail c n ny es ==>
     (exists (prog: list revent) (io: nat -> renaming).
        transparent c n ny es prog io /\
        (names_reachable prog ==>
           (forall (s j: nat). is_cycle es s j ==> stw_replay c sty n ny es s prog))))

let t1_eq (c: comps) (sty: style) : Lemma (t1 c sty == t1_body c sty)
  = assert (t1 c sty == t1_body c sty) by (FStar.Tactics.V2.trefl ())

/// The statement, proved from both parts for one run.
let t1_form (c: comps) (sty: style)
  : Lemma (components_ok c ==>
            (forall (n ny: nat) (es: list event).
               run_ok c sty n ny es /\ no_fail c n ny es ==>
               (exists (prog: list revent) (io: nat -> renaming).
                  transparent c n ny es prog io /\
                  (names_reachable prog ==>
                     (forall (s j: nat). is_cycle es s j ==> stw_replay c sty n ny es s prog)))))
  = introduce components_ok c ==>
      (forall (n ny: nat) (es: list event).
         run_ok c sty n ny es /\ no_fail c n ny es ==>
         (exists (prog: list revent) (io: nat -> renaming).
            transparent c n ny es prog io /\
            (names_reachable prog ==>
               (forall (s j: nat). is_cycle es s j ==> stw_replay c sty n ny es s prog))))
    with introduce forall (n ny: nat) (es: list event).
              run_ok c sty n ny es /\ no_fail c n ny es ==>
              (exists (prog: list revent) (io: nat -> renaming).
                 transparent c n ny es prog io /\
                 (names_reachable prog ==>
                    (forall (s j: nat). is_cycle es s j ==> stw_replay c sty n ny es s prog)))
    with introduce _ ==> _
    with R.t1_run2 c sty n ny es

let t1_body_of (c: comps) (sty: style)
  : Lemma (requires components_ok c ==>
            (forall (n ny: nat) (es: list event).
               run_ok c sty n ny es /\ no_fail c n ny es ==>
               (exists (prog: list revent) (io: nat -> renaming).
                  transparent c n ny es prog io /\
                  (names_reachable prog ==>
                     (forall (s j: nat). is_cycle es s j ==> stw_replay c sty n ny es s prog)))))
          (ensures t1_body c sty)
  = ()

/// **T1**, for any components and either style.
let t1_ok (c: comps) (sty: style) : Lemma (t1 c sty)
  = t1_form c sty;
    t1_body_of c sty;
    t1_eq c sty

/// Both parts, both styles, by name.
let t1_both (c: comps)
  : Lemma (t1_local c Sequential /\ t1_local c Incremental /\ t1 c Sequential /\ t1 c Incremental)
  = TR.t1_local_both c;
    t1_ok c Sequential;
    t1_ok c Incremental
