module GC.Gen.Run.Snapshot

open FStar.List.Tot
open GC.Gen.Run.Step
open GC.Model.Represents
open GC.Gen.Run.Simulation
open GC.Gen.Run.FloatingGarbage
open GC.Gen.Run.IdAccounting

module Ph = GC.Spec.Phase
module I = GC.Model.Ideal
module H = GC.Gen.Run.Hoisted
module LP = FStar.List.Tot.Properties
module Cl = FStar.Classical

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// Lists
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 1"
/// No cycle start among the kinds.
let rec no_start (ks: list kind) : bool =
  match ks with
  | [] -> true
  | k :: t -> not (KStart? k) && no_start t

let rec no_start_kinds (es: list event)
  : Lemma (ensures no_start (kinds es) == not (starts_a_cycle es)) (decreases es)
  = match es with [] -> () | _ :: t -> no_start_kinds t

#push-options "--fuel 4 --ifuel 2"
let rec hoist_append_aux (ks1 ks2: list kind)
  : Lemma (ensures hoist (ks1 @ ks2) == hoist ks1 @ hoist ks2) (decreases ks1)
  = match ks1 with [] -> () | _ :: t -> hoist_append_aux t ks2
#pop-options

let rec wf_prefix (m: I.ideal_memory) (ps1 ps2: list I.program_event)
  : Lemma (requires I.wf_program_from m (ps1 @ ps2)) (ensures I.wf_program_from m ps1) (decreases ps1)
  = match ps1 with [] -> () | e :: t -> wf_prefix (I.ideal_step m e) t ps2

/// The accounting of a schedule cut in two, the first part consuming the
/// first part of the program.
let rec account_append (a: acc) (ks1 ks2: list kind) (ps1 ps2: list I.program_event)
  : Lemma (requires n_program ks1 == length ps1)
          (ensures account a (ks1 @ ks2) (ps1 @ ps2) == account (account a ks1 ps1) ks2 ps2)
          (decreases ks1)
  = match ks1 with
    | [] -> ()
    | k :: ks1' ->
        if is_program_kind k
        then (match ps1 with pe :: ps1' -> account_append (kind_step a k (Some pe)) ks1' ks2 ps1' ps2)
        else account_append (kind_step a k None) ks1' ks2 ps1 ps2
#pop-options

/// ---------------------------------------------------------------------------
/// The kept set grows until another cycle starts
/// ---------------------------------------------------------------------------

#push-options "--ifuel 2"
let kept_step (a: acc) (k: kind) (pe: option I.program_event) (id: I.obj_id)
  : Lemma (requires ~(KStart? k) /\ a.kept id) (ensures (kind_step a k pe).kept id)
  = ()
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec kept_grows (a: acc) (ks: list kind) (ps: list I.program_event) (id: I.obj_id)
  : Lemma (requires no_start ks /\ a.kept id) (ensures (account a ks ps).kept id) (decreases ks)
  = match ks with
    | [] -> ()
    | k :: ks' ->
        if is_program_kind k
        then (match ps with
              | [] -> ()
              | pe :: ps' -> kept_step a k (Some pe) id; kept_grows (kind_step a k (Some pe)) ks' ps' id)
        else (kept_step a k None id; kept_grows (kind_step a k None) ks' ps id)
#pop-options

/// **At the end of the cycle, the accounting keeps what was reachable at its
/// start.**
#push-options "--fuel 1 --ifuel 1"
let kept_at_end (es1: list event) (roots: Seq.seq FStar.UInt64.t) (rest: list event)
                (ps1 ps2: list I.program_event) (id: I.obj_id)
  : Lemma (requires n_program (kinds es1) == length ps1 /\ not (starts_a_cycle rest) /\
                    I.reachable (I.ideal_run ps1) id)
          (ensures (account empty_acc (kinds (es1 @ (StartCycle roots :: rest))) (ps1 @ ps2)).kept id)
  = let es2 = StartCycle roots :: rest in
    LP.map_append kind_of es1 es2;
    account_append empty_acc (kinds es1) (kinds es2) ps1 ps2;
    let a1 = account empty_acc (kinds es1) ps1 in
    account_mem empty_acc (kinds es1) ps1;
    assert (kinds es2 == KStart :: kinds rest);
    assert (account a1 (kinds es2) ps2 == account (start_acc a1) (kinds rest) ps2);
    no_start_kinds rest;
    kept_grows (start_acc a1) (kinds rest) ps2 id
#pop-options

/// ---------------------------------------------------------------------------
/// The theorems
/// ---------------------------------------------------------------------------

/// The snapshot direction (`reachable_at_start_survives`).
#push-options "--ifuel 1"
let survives (#es1: list event) (#r1: real_state) (rn1: run (initial_state ()) es1 r1)
             (#es2: list event) (#r2: real_state) (rn2: run r1 es2 r2)
             (ps1 ps2: list I.program_event) (id: I.obj_id)
  : Lemma (requires I.wf_program (ps1 @ ps2) /\ executes rn1 ps1 /\ executes (run_append rn1 rn2) (ps1 @ ps2) /\
                    one_cycle es2 /\ r2.phase == Ph.Idle /\ I.reachable (I.ideal_run ps1) id)
          (ensures ~(no_block (run_append rn1 rn2) id))
  = let StartCycle roots :: rest = es2 in
    executes_length rn1 ps1;
    kept_at_end es1 roots rest ps1 ps2 id;
    H.step_hyps_hold ();
    H.ids_at_idle (run_append rn1 rn2) (ps1 @ ps2)
#pop-options

/// A block at the point: its object exists after the program's events.
let block_valid (#es1: list event) (#r1: real_state) (rn1: run (initial_state ()) es1 r1)
                (ps1 ps2: list I.program_event) (id: I.obj_id)
  : Lemma (requires I.wf_program (ps1 @ ps2) /\ executes rn1 ps1 /\ ~(no_block rn1 id))
          (ensures I.valid_id (I.ideal_run ps1) id)
  = wf_prefix I.empty_ideal ps1 ps2;
    simulation rn1 ps1;
    eliminate exists (b: block_addr). ids_of_run rn1 b == Some id
    with GC.Gen.Run.Simulation.Program.copies_faithful_elim r1.memory (GC.Gen.Run.History.history_of_run rn1)
                                                             (I.ideal_run ps1) (ids_of_run rn1) b id

#push-options "--fuel 1 --ifuel 1"
let snapshot_at_the_beginning #es1 #r1 rn1 #es2 #r2 rn2 ps1 ps2 id =
  assert (starts_a_cycle es2);
  block_valid rn1 ps1 ps2 id;
  Cl.move_requires (survives rn1 rn2 ps1 ps2) id;
  Cl.move_requires (floating_garbage_freed rn1 rn2 ps1 ps2) id
#pop-options

let reachable_at_start_survives #es1 #r1 rn1 #es2 #r2 rn2 ps1 ps2 id = survives rn1 rn2 ps1 ps2 id

let hoist_append ks1 ks2 = hoist_append_aux ks1 ks2

/// The run is idle where the cycle starts.
#push-options "--fuel 1 --ifuel 1"
let rec idle_at_start (#r1: real_state) (#es2: list event) (#r2: real_state) (rn2: run r1 es2 r2)
  : Lemma (requires Cons? es2 /\ StartCycle? (hd es2)) (ensures r1.phase == Ph.Idle) (decreases rn2)
  = match rn2 with
    | Step #_ #es' #_ rn' e _ _ ->
        (match es' with
         | [] -> ()
         | _ :: _ -> idle_at_start rn')
#pop-options

let snapshot_hoisted #es1 #r1 rn1 #es2 #r2 rn2 #eh1 #sh1 rnh1 #eh2 #sh2 rnh2 ps1 ps2 id =
  wf_prefix I.empty_ideal ps1 ps2;
  idle_at_start rn2;
  idle_at_start rnh2;
  H.step_hyps_hold ();
  H.ids_at_idle rn1 ps1;
  H.ids_at_idle rnh1 ps1;
  GC.Gen.Run.IdAccounting.live_ids_hoist ps1 (kinds es1) id;
  snapshot_at_the_beginning rn1 rn2 ps1 ps2 id;
  snapshot_at_the_beginning rnh1 rnh2 ps1 ps2 id
