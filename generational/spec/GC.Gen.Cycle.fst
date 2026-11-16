module GC.Gen.Cycle

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module Mark = GC.Spec.Mark
module MP = GC.Spec.MarkPhase
module GI = GC.Gen.Incremental
module MPC = GC.Spec.MarkPhase.Completeness
module GMC = GC.Gen.MarkPhase.Completeness
module SPC = GC.Spec.SweepPhase.Completeness
module SPI = GC.Spec.SweepPhase.Intrinsic
module FSI = GC.Spec.FusedSweep.Inv
module FSE = GC.Spec.FusedSweep.End
module MC = GC.Gen.MarkPhase.Cycle
module SC = GC.Gen.SweepPhase.Cycle
module GMM = GC.Gen.MarkPhase.Minor
module GenInv = GC.Gen.HeapInvariant

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

let handover_sweep_start minor g sp fp budget gh sp' =
  GI.mark_steps_shape minor g gh fp sp sp';
  GI.phase_shape_marking minor gh fp sp';
  GenInv.collection_shape_with_elim Ph.Marking free_stw minor gh fp;
  GenInv.major_shape_with_elim Ph.Marking free_stw gh fp;
  MP.marking_done_sweep_start gh (GMM.nursery_refs minor) sp' fp

/// What the two runs give once the sweep has started: from marking, the
/// black objects of the heap it handed over are the snapshot's, and
/// everything reachable at the start is among them; from the sweep, its
/// account and converse.
#push-options "--ifuel 1"
let sweep_parts (#g0: heap) (#rs: seq U64.t) (#g: heap) (#fp: U64.t) (#ph: Ph.gc_phase)
                (#since: obj_addr -> prop) (r: major_cycle g0 rs g fp ph since)
  : Lemma (requires ~(Ph.Marking? ph))
          (ensures exists (gh: heap) (sm ss: obj_addr -> prop).
                     (forall (x: obj_addr). since x <==> sm x \/ ss x) /\
                     (forall (x: obj_addr). GMC.reachable_at_start g0 rs x ==>
                        SPC.survived_mark gh x /\ wosize_of_object x gh == wosize_of_object x g0) /\
                     (forall (x: obj_addr). SPC.survived_mark gh x ==> MC.snapshot g0 rs sm x) /\
                     (forall (x: obj_addr). sm x ==> ~(GMC.reachable_at_start g0 rs x)) /\
                     SC.cycle_inv gh ss g ph)
  = match r with
    | Sweep #_ #_ #gm #fpm #sp #sm rm minor budget gh sp' _ #_ #_ #_ #ss sr _ ->
        MC.handover rm minor budget gh sp';
        SC.cycle_account sr
#pop-options

#push-options "--ifuel 1"
let cycle_account #g0 #rs #g #fp #ph #since r =
  let s = MC.snapshot g0 rs since in
  match r with
  | Mark rm ->
      MC.mark_run_account rm;
      assert (MPC.cycle_account s g ph)
  | Sweep _ _ _ _ _ _ _ _ ->
      sweep_parts r;
      eliminate exists (gh: heap) (sm ss: obj_addr -> prop).
        (forall (x: obj_addr). since x <==> sm x \/ ss x) /\
        (forall (x: obj_addr). GMC.reachable_at_start g0 rs x ==>
           SPC.survived_mark gh x /\ wosize_of_object x gh == wosize_of_object x g0) /\
        (forall (x: obj_addr). SPC.survived_mark gh x ==> MC.snapshot g0 rs sm x) /\
        (forall (x: obj_addr). sm x ==> ~(GMC.reachable_at_start g0 rs x)) /\
        SC.cycle_inv gh ss g ph
      with ()
#pop-options

let cycle_complete #g0 #rs #g #fp #since r =
  cycle_account r;
  MPC.cycle_complete (MC.snapshot g0 rs since) g

let cycle_frees_unreachable #g0 #rs #g #fp #since r =
  cycle_complete r

let cycle_survives #g0 #rs #g #fp #since r =
  sweep_parts r;
  eliminate exists (gh: heap) (sm ss: obj_addr -> prop).
    (forall (x: obj_addr). since x <==> sm x \/ ss x) /\
    (forall (x: obj_addr). GMC.reachable_at_start g0 rs x ==>
       SPC.survived_mark gh x /\ wosize_of_object x gh == wosize_of_object x g0) /\
    (forall (x: obj_addr). SPC.survived_mark gh x ==> MC.snapshot g0 rs sm x) /\
    (forall (x: obj_addr). sm x ==> ~(GMC.reachable_at_start g0 rs x)) /\
    SC.cycle_inv gh ss g Ph.Idle
  with begin
    let one (x: obj_addr)
      : Lemma (requires GMC.reachable_at_start g0 rs x)
              (ensures Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\
                       wosize_of_object x g == wosize_of_object x g0 /\ ~(since x))
      = SPC.survived_at_idle gh ss g x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)
  end

let cycle_lossless #g0 #rs #g #fp #since r =
  cycle_complete r;
  cycle_survives r
