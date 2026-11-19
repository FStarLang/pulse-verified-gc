/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Cycle - the incremental major cycle with the page allocator
/// ---------------------------------------------------------------------------
///
/// Plan §23.4.  A run of the whole incremental major cycle with the page
/// allocator: marking in slices while the program runs
/// (`GC.Spec.Pages.Cycle.Mark.pmarking`), the hand-over to the sweep when
/// nothing is grey, and the page sweep while the program runs
/// (`GC.Spec.Pages.Cycle.Sweep.psweep`), until every page is swept.  It is
/// akhil's `GC.Gen.Cycle.major_cycle` with the page state in place of the
/// free-list head.
///
/// **Its theorems are akhil's, word for word** (`GC.Gen.Cycle`), over these
/// runs: `cycle_complete`, `cycle_frees_unreachable`, `cycle_survives`,
/// `cycle_addresses_lossless`, `cycle_covered` and `cycle_lossless`, which
/// holds for every word `p < heap_size`, the heap's last word included (the
/// layout of plan §23.5 makes the walk end at `heap_size` in every page
/// state).  `cycle_account` is his with the page sweep's definition of free
/// mid-sweep (`free_sw`) in place of his cursor's.
///
/// **These runs have no minor collection.**  akhil's runs have a `Minor`
/// event in each phase (a minor collection, which promotes into the major
/// heap); the page cycle gets it with a page promotion (plan §23.6), not
/// done yet.  Until then the theorems here cover fewer runs than his: those
/// in which no minor collection happens during the major cycle.
///
/// The word-by-word proof is akhil's (`GC.Gen.Cycle.fst`: `parts`,
/// `start_words`, `reach_words`, `handover_words`, `new_words`, `words`),
/// copied, since it is private to his module.

module GC.Spec.Pages.Cycle

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Spec.Pages.Inv

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module Mark = GC.Spec.Mark
module MP = GC.Spec.MarkPhase
module S = GC.Spec.MarkPhase.Slice
module MPC = GC.Spec.MarkPhase.Completeness
module GMC = GC.Gen.MarkPhase.Completeness
module MC = GC.Gen.MarkPhase.Cycle
module GC_ = GC.Gen.Cycle
module SPC = GC.Spec.SweepPhase.Completeness
module LL = GC.Spec.FusedSweep.Lossless
module W = GC.Spec.Walk
module I = GC.Spec.AllocIface
module MS = GC.Spec.Pages.MidSweep
module SS = GC.Spec.Pages.StartSweep
module PM = GC.Spec.Pages.Cycle.Mark
module PS = GC.Spec.Pages.Cycle.Sweep

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// The run
/// ---------------------------------------------------------------------------

/// The page state a run of the sweep phase started from.
#push-options "--ifuel 1"
let rec sweep_start_st (#gh #g: heap) (#st: pstate) (#ph: I.phase) (#since: obj_addr -> prop)
                       (r: PS.psweep gh g st ph since)
  : GTot pstate (decreases r)
  = match r with
    | PS.SStart st0 _ -> st0
    | PS.SStep r1 _ _ -> sweep_start_st r1
    | PS.SAlloc r1 _ _ _ _ _ _ _ -> sweep_start_st r1
    | PS.SWrite r1 _ _ _ _ -> sweep_start_st r1
    | PS.SMinor r1 _ _ _ -> sweep_start_st r1
    | PS.SEnd r1 _ -> sweep_start_st r1
#pop-options

/// **A run of the incremental major cycle with the page allocator**, begun
/// on `g0` with the roots `rs`, to the heap `g`, page state `st` and phase
/// `ph`, with `since` the addresses its allocations handed out.
noeq type pcycle (g0: heap) (rs: seq U64.t) : heap -> pstate -> I.phase -> (obj_addr -> prop) -> Type =
  // Marking.
  | PMark :
      #g: heap -> #st: pstate -> #sp: MP.scan_pos -> #since: (obj_addr -> prop) ->
      PM.pmarking g0 rs g st sp since ->
      pcycle g0 rs g st I.Marking since
  // Marking, the mark moves that leave nothing grey, and the page sweep
  // from the heap they leave, from the page state marking left.
  | PSweep :
      #g: heap -> #st: pstate -> #sp: MP.scan_pos -> #sm: (obj_addr -> prop) ->
      PM.pmarking g0 rs g st sp sm ->
      minor: minor_state -> gh: heap -> sp': MP.scan_pos ->
      squash (PM.pmark_ok minor g st sp /\ S.mark_steps g sp gh sp' /\
              Mark.noGreyObjects gh /\ sp' == MP.scan_none) ->
      #g': heap -> #st': pstate -> #ph: I.phase -> #ss: (obj_addr -> prop) ->
      sr: PS.psweep gh g' st' ph ss ->
      squash (sweep_start_st sr == SS.start_sweep st) ->
      pcycle g0 rs g' st' ph (GC_.union sm ss)

/// The account at the run's phase: akhil's `MPC.cycle_account`, with the
/// page sweep's free mid-sweep.
#push-options "--ifuel 1"
let pcycle_account (snapshot: obj_addr -> prop) (g: heap) (st: pstate) (ph: I.phase) : prop =
  match ph with
  | I.Marking -> MPC.within_snapshot snapshot g
  | I.Sweeping -> forall (x: obj_addr). in_use (MS.free_sw st.pm) g x ==> snapshot x
  | I.Idle -> MPC.cycle_account snapshot g Ph.Idle
#pop-options

/// ---------------------------------------------------------------------------
/// What the two runs give
/// ---------------------------------------------------------------------------

/// The hand-over's facts and the sweep's account.
let handed (g0: heap) (rs: seq U64.t) (gh: heap) (sm: obj_addr -> prop) : prop =
  (forall (x: obj_addr). GMC.reachable_at_start g0 rs x ==>
     Seq.mem x (objects zero_addr g0) /\
     SPC.survived_mark gh x /\ wosize_of_object x gh == wosize_of_object x g0) /\
  (forall (x: obj_addr). SPC.survived_mark gh x ==> MC.snapshot g0 rs sm x) /\
  (forall (x: obj_addr). sm x ==> ~(GMC.reachable_at_start g0 rs x)) /\
  (forall (x: obj_addr). sm x ==> SPC.survived_mark gh x) /\
  W.walk_end g0 zero_addr == heap_size /\ W.walk_end gh zero_addr == heap_size

#push-options "--ifuel 1"
let sweep_parts (#g0: heap) (#rs: seq U64.t) (#g: heap) (#st: pstate) (#ph: I.phase)
                (#since: obj_addr -> prop) (r: pcycle g0 rs g st ph since)
  : Lemma (requires ~(I.Marking? ph))
          (ensures exists (gh: heap) (sm ss: obj_addr -> prop).
                     (forall (x: obj_addr). since x <==> sm x \/ ss x) /\
                     handed g0 rs gh sm /\ PS.psweep_inv gh ss g st ph)
  = match r with
    | PSweep #_ #_ #gm #stm #sp #sm rm minor gh sp' _ #_ #_ #_ #ss sr _ ->
        PM.phandover rm minor gh sp';
        PS.psweep_account sr;
        assert (handed g0 rs gh sm);
        FStar.Classical.exists_intro
          (fun (gh': heap) -> exists (sm' ss': obj_addr -> prop).
             (forall (x: obj_addr). since x <==> sm' x \/ ss' x) /\
             handed g0 rs gh' sm' /\ PS.psweep_inv gh' ss' g st ph) gh
#pop-options

/// ---------------------------------------------------------------------------
/// The theorems, by address
/// ---------------------------------------------------------------------------

/// **Every state of a run carries the account of the snapshot.**
#push-options "--ifuel 1 --z3rlimit 20"
let cycle_account (#g0: heap) (#rs: seq U64.t) (#g: heap) (#st: pstate) (#ph: I.phase)
                  (#since: obj_addr -> prop) (r: pcycle g0 rs g st ph since)
  : Lemma (ensures pcycle_account (MC.snapshot g0 rs since) g st ph)
  = match r with
    | PMark rm -> PM.pmark_run_account rm
    | PSweep _ _ _ _ _ _ _ ->
        sweep_parts r;
        eliminate exists (gh: heap) (sm ss: obj_addr -> prop).
          (forall (x: obj_addr). since x <==> sm x \/ ss x) /\
          handed g0 rs gh sm /\ PS.psweep_inv gh ss g st ph
        with ()
#pop-options

/// **Completeness of a run**: once it is idle again, every address outside
/// the snapshot is freed.
let cycle_complete (#g0: heap) (#rs: seq U64.t) (#g: heap) (#st: pstate) (#since: obj_addr -> prop)
                   (r: pcycle g0 rs g st I.Idle since)
  : Lemma (ensures forall (x: obj_addr). ~(MC.snapshot g0 rs since x) ==> SPC.freed g x)
  = cycle_account r;
    MPC.cycle_complete (MC.snapshot g0 rs since) g

/// The same, spelled out: an object unreachable from the roots when the
/// cycle started is freed by the end of the cycle, unless the run handed its
/// address out again.
let cycle_frees_unreachable (#g0: heap) (#rs: seq U64.t) (#g: heap) (#st: pstate) (#since: obj_addr -> prop)
                            (r: pcycle g0 rs g st I.Idle since)
  : Lemma (ensures forall (x: obj_addr).
                     ~(GMC.reachable_at_start g0 rs x) /\ ~(since x) ==> SPC.freed g x)
  = cycle_complete r

/// **What was reachable survives**: once a run is idle again, every object
/// reachable from the roots when the cycle started is a block that is not
/// free, at the size it had, and the run did not hand its address out.
let cycle_survives (#g0: heap) (#rs: seq U64.t) (#g: heap) (#st: pstate) (#since: obj_addr -> prop)
                   (r: pcycle g0 rs g st I.Idle since)
  : Lemma (ensures forall (x: obj_addr). GMC.reachable_at_start g0 rs x ==>
                     Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\
                     wosize_of_object x g == wosize_of_object x g0 /\ ~(since x))
  = sweep_parts r;
    eliminate exists (gh: heap) (sm ss: obj_addr -> prop).
      (forall (x: obj_addr). since x <==> sm x \/ ss x) /\
      handed g0 rs gh sm /\ PS.psweep_inv gh ss g st I.Idle
    with begin
      let one (x: obj_addr)
        : Lemma (requires GMC.reachable_at_start g0 rs x)
                (ensures Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\
                         wosize_of_object x g == wosize_of_object x g0 /\ ~(since x))
        = SPC.survived_at_idle gh ss g x
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires one)
    end

/// **The same, address by address**: once a run is idle again, an address
/// the run did not hand out holds a block that is not free exactly when it
/// held an object reachable from the roots when the cycle started.
let cycle_addresses_lossless (#g0: heap) (#rs: seq U64.t) (#g: heap) (#st: pstate) (#since: obj_addr -> prop)
                             (r: pcycle g0 rs g st I.Idle since)
  : Lemma (ensures forall (x: obj_addr). ~(since x) ==>
                     (GMC.reachable_at_start g0 rs x <==> ~(SPC.freed g x)))
  = cycle_complete r;
    cycle_survives r

/// ---------------------------------------------------------------------------
/// Word by word (akhil's proof, `GC.Gen.Cycle.fst`)
/// ---------------------------------------------------------------------------

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

let reach_covered (g0: heap) (rs: seq U64.t) (h: heap) (p: nat) : prop =
  exists (x: obj_addr). GMC.reachable_at_start g0 rs x /\ Seq.mem x (objects zero_addr h) /\ LL.in_extent h x p

let extent_size (h h': heap) (x: obj_addr) (p: nat)
  : Lemma (requires wosize_of_object x h' == wosize_of_object x h)
          (ensures LL.in_extent h' x p <==> LL.in_extent h x p)
  = ()

let start_words (g0: heap) (rs: seq U64.t) (gh g: heap) (sm ss: obj_addr -> prop) (p: nat)
  : Lemma (requires parts g0 rs gh g sm ss)
          (ensures GC_.unreachable_covered g0 rs p <==>
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

let reach_words (g0: heap) (rs: seq U64.t) (gh g: heap) (sm ss: obj_addr -> prop) (p: nat)
  : Lemma (requires parts g0 rs gh g sm ss)
          (ensures reach_covered g0 rs g0 p <==> reach_covered g0 rs gh p)
  = let r = GMC.reachable_at_start g0 rs in
    let one (x: obj_addr) : Lemma (requires r x) (ensures LL.in_extent gh x p <==> LL.in_extent g0 x p)
      = extent_size g0 gh x p
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)

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

#push-options "--z3rlimit 20"
let words (g0: heap) (rs: seq U64.t) (gh g: heap) (sm ss: obj_addr -> prop) (p: nat)
  : Lemma (requires parts g0 rs gh g sm ss)
          (ensures (GC_.unreachable_covered g0 rs p ==> SPC.free_or_new_at g (GC_.union sm ss) p) /\
                   (p < heap_size ==>
                      (GC_.unreachable_covered g0 rs p <==>
                       LL.blue_covered g p \/ SPC.new_covered (GC_.union sm ss) g p)))
  = start_words g0 rs gh g sm ss p;
    reach_words g0 rs gh g sm ss p;
    handover_words g0 rs gh g sm ss p;
    new_words g0 rs gh g sm ss p;
    SPC.covered_at_idle gh ss g;
    SPC.lossless_at_idle gh ss g;
    let un (h: heap) (a b: obj_addr -> prop)
      : Lemma (SPC.new_covered (GC_.union a b) h p <==> SPC.new_covered a h p \/ SPC.new_covered b h p)
      = ()
    in
    un g sm ss
#pop-options

/// The parts, from a run that is idle.
#push-options "--ifuel 1"
let run_words (#g0: heap) (#rs: seq U64.t) (#g: heap) (#st: pstate) (#since: obj_addr -> prop)
              (r: pcycle g0 rs g st I.Idle since) (p: nat)
  : Lemma (ensures (GC_.unreachable_covered g0 rs p ==> SPC.free_or_new_at g since p) /\
                   (p < heap_size ==>
                      (GC_.unreachable_covered g0 rs p <==> LL.blue_covered g p \/ SPC.new_covered since g p)))
  = match r with
    | PSweep #_ #_ #gm #stm #sp #sm rm minor gh sp' _ #_ #_ #_ #ss sr _ ->
        PM.phandover rm minor gh sp';
        PS.psweep_account sr;
        words g0 rs gh g sm ss p
#pop-options

/// **Completeness of a run, word by word**: once it is idle again, every
/// word of a block unreachable when the cycle started lies in a free block,
/// or in a block the run allocated.
let cycle_covered (#g0: heap) (#rs: seq U64.t) (#g: heap) (#st: pstate) (#since: obj_addr -> prop)
                  (r: pcycle g0 rs g st I.Idle since)
  : Lemma (ensures forall (p: nat). GC_.unreachable_covered g0 rs p ==> SPC.free_or_new_at g since p)
  = FStar.Classical.forall_intro (run_words r)

/// **The incremental cycle with the page allocator is lossless, up to what
/// it handed out**: once a run is idle again, a word of the heap -- every
/// word, the last one included -- lay in a block unreachable from the roots
/// when the cycle started exactly when it lies in a free block, or in a
/// block the run allocated.
let cycle_lossless (#g0: heap) (#rs: seq U64.t) (#g: heap) (#st: pstate) (#since: obj_addr -> prop)
                   (r: pcycle g0 rs g st I.Idle since)
  : Lemma (ensures forall (p: nat). p < heap_size ==>
                     (GC_.unreachable_covered g0 rs p <==> LL.blue_covered g p \/ SPC.new_covered since g p))
  = FStar.Classical.forall_intro (run_words r)
