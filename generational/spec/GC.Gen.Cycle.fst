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
module LL = GC.Spec.FusedSweep.Lossless
module W = GC.Spec.Walk

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

let cycle_addresses_lossless #g0 #rs #g #fp #since r =
  cycle_complete r;
  cycle_survives r

/// ---------------------------------------------------------------------------
/// Word by word
/// ---------------------------------------------------------------------------

/// What the two runs give at the end, word by word: from marking, the
/// hand-over heap `gh` (its black blocks are the objects reachable at the
/// start, at their sizes, and the blocks marking handed out, `sm`; its walk
/// ends where the start heap's did); from the sweep, its account and its
/// converse to `g`.
let parts (g0: heap) (rs: seq U64.t) (gh g: heap) (sm ss: obj_addr -> prop) : prop =
  (forall (x: obj_addr). GMC.reachable_at_start g0 rs x ==>
     Seq.mem x (objects zero_addr g0) /\
     SPC.survived_mark gh x /\ wosize_of_object x gh == wosize_of_object x g0) /\
  (forall (x: obj_addr). SPC.survived_mark gh x ==> MC.snapshot g0 rs sm x) /\
  (forall (x: obj_addr). sm x ==> ~(GMC.reachable_at_start g0 rs x)) /\
  (forall (x: obj_addr). sm x ==> SPC.survived_mark gh x) /\
  W.walk_end g0 zero_addr + 8 >= heap_size /\
  W.walk_end gh zero_addr == W.walk_end g0 zero_addr /\
  SPC.idle_account gh ss g /\ SPC.reclaimed_was_dead gh ss free_stw g

/// `p` lies in a block reachable at the start, in `h`.
let reach_covered (g0: heap) (rs: seq U64.t) (h: heap) (p: nat) : prop =
  exists (x: obj_addr). GMC.reachable_at_start g0 rs x /\ Seq.mem x (objects zero_addr h) /\ LL.in_extent h x p

/// The extent of a block depends only on its size.
let extent_size (h h': heap) (x: obj_addr) (p: nat)
  : Lemma (requires wosize_of_object x h' == wosize_of_object x h)
          (ensures LL.in_extent h' x p <==> LL.in_extent h x p)
  = ()

/// At the start: a word lies in an unreachable block exactly when it is a
/// word of the walk in no reachable block.
let start_words (g0: heap) (rs: seq U64.t) (gh g: heap) (sm ss: obj_addr -> prop) (p: nat)
  : Lemma (requires parts g0 rs gh g sm ss)
          (ensures unreachable_covered g0 rs p <==>
                   (U64.v zero_addr <= p /\ p < W.walk_end g0 zero_addr /\ ~(reach_covered g0 rs g0 p)))
  = let r = GMC.reachable_at_start g0 rs in
    let fwd (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr g0) /\ ~(r x) /\ LL.in_extent g0 x p)
              (ensures U64.v zero_addr <= p /\ p < W.walk_end g0 zero_addr /\ ~(reach_covered g0 rs g0 p))
      = SPC.extent_below_end g0 x p;
        let no (y: obj_addr) : Lemma (requires r y /\ Seq.mem y (objects zero_addr g0) /\ LL.in_extent g0 y p)
                                     (ensures False)
          = SPC.extents_disjoint g0 y x p
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires no)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires fwd);
    if U64.v zero_addr <= p && p < W.walk_end g0 zero_addr then begin
      let y = SPC.block_over g0 p in
      ()
    end

/// The blocks reachable at the start cover the same words at the start and
/// at the hand-over.
let reach_words (g0: heap) (rs: seq U64.t) (gh g: heap) (sm ss: obj_addr -> prop) (p: nat)
  : Lemma (requires parts g0 rs gh g sm ss)
          (ensures reach_covered g0 rs g0 p <==> reach_covered g0 rs gh p)
  = let r = GMC.reachable_at_start g0 rs in
    let one (x: obj_addr) : Lemma (requires r x) (ensures LL.in_extent gh x p <==> LL.in_extent g0 x p)
      = extent_size g0 gh x p
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)

/// At the hand-over: a word lies in a dead block or one marking handed out
/// exactly when it is a word of the walk in no reachable block.
#push-options "--z3rlimit 20"
let handover_words (g0: heap) (rs: seq U64.t) (gh g: heap) (sm ss: obj_addr -> prop) (p: nat)
  : Lemma (requires parts g0 rs gh g sm ss)
          (ensures (LL.dead_covered gh p \/ SPC.new_covered sm gh p) <==>
                   (U64.v zero_addr <= p /\ p < W.walk_end gh zero_addr /\ ~(reach_covered g0 rs gh p)))
  = let r = GMC.reachable_at_start g0 rs in
    let fwd (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr gh) /\ (~(is_black y gh) \/ sm y) /\ LL.in_extent gh y p)
              (ensures U64.v zero_addr <= p /\ p < W.walk_end gh zero_addr /\ ~(reach_covered g0 rs gh p))
      = SPC.extent_below_end gh y p;
        let no (z: obj_addr) : Lemma (requires r z /\ Seq.mem z (objects zero_addr gh) /\ LL.in_extent gh z p)
                                     (ensures False)
          = assert (z <> y);
            SPC.extents_disjoint gh z y p
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires no)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires fwd);
    if U64.v zero_addr <= p && p < W.walk_end gh zero_addr then begin
      let y = SPC.block_over gh p in
      Mark.colors_exclusive y gh
    end
#pop-options

/// What marking handed out covers the same words at the hand-over and at
/// the end: those blocks are black at the hand-over, so they survive the
/// sweep at their sizes.
let new_words (g0: heap) (rs: seq U64.t) (gh g: heap) (sm ss: obj_addr -> prop) (p: nat)
  : Lemma (requires parts g0 rs gh g sm ss)
          (ensures SPC.new_covered sm gh p <==> SPC.new_covered sm g p)
  = let one (y: obj_addr)
      : Lemma (requires sm y)
              (ensures Seq.mem y (objects zero_addr g) /\ Seq.mem y (objects zero_addr gh) /\
                       (LL.in_extent g y p <==> LL.in_extent gh y p))
      = SPC.survived_at_idle gh ss g y;
        extent_size gh g y p
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)

/// **Word by word, from the parts.**
#push-options "--z3rlimit 20"
let words (g0: heap) (rs: seq U64.t) (gh g: heap) (sm ss: obj_addr -> prop) (p: nat)
  : Lemma (requires parts g0 rs gh g sm ss)
          (ensures (unreachable_covered g0 rs p ==> SPC.free_or_new_at g (union sm ss) p) /\
                   (p < heap_size ==>
                      (unreachable_covered g0 rs p <==>
                       LL.blue_covered g p \/ SPC.new_covered (union sm ss) g p)))
  = start_words g0 rs gh g sm ss p;
    reach_words g0 rs gh g sm ss p;
    handover_words g0 rs gh g sm ss p;
    new_words g0 rs gh g sm ss p;
    SPC.covered_at_idle gh ss g;
    SPC.lossless_at_idle gh ss g;
    let un (h: heap) (a b: obj_addr -> prop)
      : Lemma (SPC.new_covered (union a b) h p <==> SPC.new_covered a h p \/ SPC.new_covered b h p)
      = ()
    in
    un g sm ss
#pop-options

/// The parts, from a run that is idle.
#push-options "--ifuel 1"
let run_words (#g0: heap) (#rs: seq U64.t) (#g: heap) (#fp: U64.t) (#since: obj_addr -> prop)
              (r: major_cycle g0 rs g fp Ph.Idle since) (p: nat)
  : Lemma (ensures (unreachable_covered g0 rs p ==> SPC.free_or_new_at g since p) /\
                   (p < heap_size ==>
                      (unreachable_covered g0 rs p <==> LL.blue_covered g p \/ SPC.new_covered since g p)))
  = match r with
    | Sweep #_ #_ #gm #fpm #sp #sm rm minor budget gh sp' _ #_ #_ #_ #ss sr _ ->
        MC.handover rm minor budget gh sp';
        SC.cycle_account sr;
        words g0 rs gh g sm ss p
#pop-options

let cycle_covered #g0 #rs #g #fp #since r =
  FStar.Classical.forall_intro (run_words r)

let cycle_lossless #g0 #rs #g #fp #since r =
  FStar.Classical.forall_intro (run_words r)
