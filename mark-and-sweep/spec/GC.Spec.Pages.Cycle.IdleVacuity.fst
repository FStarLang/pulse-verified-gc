/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Cycle.IdleVacuity - witnesses for plan §29: a minor
/// collection once idle, and the program's allocations with a tag
/// ---------------------------------------------------------------------------
///
/// The vacuity rule for the events plan §29 adds to the carried cycle, on
/// runs of the dark run (`Cycle.VacuityDark`) from the witness heap `W`:
///
///   * **a minor collection once the cycle is idle, that promotes**
///     (`run_idle`): root darkening, the allocation while marking and the
///     barrier write, the hand-over, the sweep's start, the step that
///     sweeps C's page, a step at every unit, the end, then a minor
///     collection of the nursery of `NurseryWitness` (one object, one root
///     at it) in `Idle`.  The collection forwards the object to a block it
///     made, white, and rewrites the root (`run_idle_promotes`); the cycle's
///     theorems hold at the end (`run_idle_theorems`).  Its allocation
///     succeeds because C's page, swept, is free or has a free slot of the
///     two-word class, and no later step changes a swept page (`room_kept`).
///   * **an allocation with a tag mid-sweep** (`run_tagged`): the dark run
///     to the step that sweeps C's page, then an allocation of one word with
///     tag 1 (`CSAllocT`), its field cleared, a step at every unit, the end.
///     The object is handed out with tag 1, white (`run_tagged_nontrivial`),
///     and the cycle's theorems hold at the end (`run_tagged_theorems`).
///   * **an allocation with a tag while marking** (`run_mark_tagged`): root
///     darkening, then an allocation of one word with tag 252, raw data
///     (`CAllocT`); the object is black, of tag 252, and the run carries the
///     `Marking` invariant and akhil's account (`run_mark_tagged_inv`).

module GC.Spec.Pages.Cycle.IdleVacuity

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv

module U64 = FStar.UInt64
module Promote = GC.Gen.Promote
module MP = GC.Spec.MarkPhase
module GMC = GC.Gen.MarkPhase.Completeness
module MStart = GC.Gen.MarkPhase.Start
module MPC = GC.Spec.MarkPhase.Completeness
module MC = GC.Gen.MarkPhase.Cycle
module SPC = GC.Spec.SweepPhase.Completeness
module LL = GC.Spec.FusedSweep.Lossless
module GC_ = GC.Gen.Cycle
module I = GC.Spec.AllocIface
module PA = GC.Spec.Pages.Allocator
module AP = GC.Spec.Pages.AllocPhase
module AT = GC.Spec.Pages.AllocTag
module ATO = GC.Spec.Pages.AllocTagOk
module SA = GC.Spec.Pages.SweepAll
module SP = GC.Spec.Pages.SweepPage
module SR = GC.Spec.Pages.SweepRun
module SS = GC.Spec.Pages.SweepStep
module RM = GC.Spec.Pages.RunMap
module MS = GC.Spec.Pages.MidSweep
module MS2 = GC.Spec.Pages.MidSweepStep
module PMP = GC.Spec.Pages.MarkPhase
module Sc = GC.Spec.Pages.Scrub
module Th = GC.Spec.Pages.Theorems
module B = GC.Spec.Pages.Blocks
module F = GC.Spec.Pages.Fill
module Header = GC.Lib.Header
module Wt = GC.Spec.Pages.Witness
module RA = GC.Spec.Pages.RoomAfter
module V = GC.Spec.Pages.Cycle.Vacuity
module D = GC.Spec.Pages.Cycle.VacuityDark
module C = GC.Spec.Pages.Cycle.Carried
module CV = GC.Spec.Pages.Cycle.CarriedVacuity
module NW = GC.Spec.Pages.NurseryWitness
module P = GC.Spec.Pages.Promote
module L = GC.Spec.Pages.Promote.Loop
module PC = GC.Spec.Pages.Promote.Collect
module PId = GC.Spec.Pages.Promote.Idle
module MV = GC.Spec.Pages.Cycle.MinorVacuity
module TF = GC.Spec.Pages.Cycle.AllocTagged
module GenInv = GC.Gen.HeapInvariant

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Room for a one-word object, kept by the sweep
/// ---------------------------------------------------------------------------

/// Page `j` is free, or a page of the two-word class with a free slot.
let room_at (pm: page_map) (j: nat{j < n_pages}) : prop =
  (entry pm j).kind == Free \/ has_free_slot pm Wt.cA j

/// **A sweep step keeps it**: such a page is swept (a free page is, by
/// `map_ok`), and a step changes no swept page's kind, mark or count of
/// free slots.
#push-options "--z3rlimit 40 --ifuel 1"
let step_room (g: heap) (st: pstate) (p: nat{p < n_pages}) (j: nat{j < n_pages})
  : Lemma (requires map_ok st.pm /\ room_at st.pm j)
          (ensures room_at (snd (SA.step g st p)).pm j)
  = let pm = st.pm in
    assert (free_ok pm j);
    assert ((entry pm j).swept);
    if (entry pm p).swept then ()
    else match (entry pm p).kind with
    | Pool c ->
        let (g', e) = SP.sweep_page g pm p in
        SS.push_entry st p e;
        let st1 = SS.push0 st p e in
        (match SS.old_tail st p e with
         | None -> ()
         | Some q -> assert (entry (SS.set_next st1.pm q (SS.page_id p)) j == (if j = q then { entry st1.pm q with next = SS.page_id p } else entry st1.pm j)))
    | LargeHead n ->
        assert (run_ok pm p);
        let fs = GC.Spec.Pages.RunList.fin g (page_base p) (page_base (p + n)) in
        let (g', pm', fp') = SR.sweep_run g pm p (GC.Spec.Pages.Cells.large_head st) in
        assert (pm' == RM.new_map pm fs p n);
        RM.new_map_ok pm fs p n
    | _ -> ()
#pop-options

/// ... and so does the rest of the sweep.
#push-options "--fuel 1 --ifuel 1"
let rec sweep_from_room (g: heap) (st: pstate) (p: nat) (j: nat{j < n_pages})
  : Lemma (requires MS.pages_ok_sw g st /\ room_at st.pm j)
          (ensures room_at (snd (SA.sweep_from g st p)).pm j)
          (decreases (if p < n_pages then n_pages - p else 0))
  = if p >= n_pages then ()
    else begin
      MS.pages_ok_sw_elim g st;
      step_room g st p j;
      MS2.step_sw g st p;
      let k = span st.pm p in
      let (g', st') = SA.step g st p in
      sweep_from_room g' st' (p + k) j
    end
#pop-options

/// Room for a one-word object: the allocator's "no room" is false.
let fit_of_room (g: heap) (st: pstate) (j: nat{j < n_pages})
  : Lemma (requires room_at st.pm j) (ensures ~(Th.no_fit g st 2))
  = RA.class2 ()

/// **The allocation of the minor collection in `Idle` succeeds** where
/// there is room.
#push-options "--z3rlimit 30"
let idle_alloc_some (g: heap) (st: pstate)
  : Lemma (requires PA.inv I.Idle g st /\ ~(Th.no_fit g st 2))
          (ensures (let (_, _, o) = AT.alloc_tag I.Idle g st 1 0UL in o =!= 0UL))
  = assert_norm (2 < pow2 54);
    PA.alloc_no_fit I.Idle g st 1;
    AT.alloc_col_tag_eq Header.White 0UL g st 1;
    assert_norm (I.new_colour I.Idle == Header.White);
    assert (PA.alloc I.Idle g st 1 == AP.alloc_col Header.White g st 1)
#pop-options

/// ---------------------------------------------------------------------------
/// A minor collection once idle
/// ---------------------------------------------------------------------------

/// The sweep after the step that swept C's page, to its end.
let gF (g: heap{V.roomy}) : GTot heap = fst (SA.sweep_from (D.g1 g) (D.s1 g) 0)
let sF (g: heap{V.roomy}) : GTot pstate = snd (SA.sweep_from (D.g1 g) (D.s1 g) 0)

/// The minor collection there.
let mi (g: heap{V.roomy}) : GTot (P.gresult pstate) = PId.icollect NW.nur (gF g) (sF g) NW.nroots
let gI (g: heap{V.roomy}) : GTot heap = (mi g).P.rmajor
let sI (g: heap{V.roomy}) : GTot pstate = (mi g).P.rst

/// The blocks it made, and every address the run hands out.
let since_mi (g: heap{V.roomy}) : obj_addr -> prop = PId.with_made SPC.nothing_new (gF g) (gI g)
let since_i (g: heap{V.roomy}) : obj_addr -> prop = GC_.union (D.since_m g) (since_mi g)

/// The sweep ends with every page swept, and C's page leaves room.
let ends (g: heap)
  : Lemma (requires V.roomy)
          (ensures MS.pages_ok_sw (gF g) (sF g) /\ PMP.all_swept (sF g) /\ room_at (sF g).pm (D.jc g))
  = D.step1 g;
    MS.pages_ok_sw_elim (D.g1 g) (D.s1 g);
    if n_pages > 0 then assert (cont_ok (D.s1 g).pm 0);
    MS2.sweep_from_sw (D.g1 g) (D.s1 g) 0;
    sweep_from_room (D.g1 g) (D.s1 g) 0 (D.jc g)

/// Its hypotheses: the nursery's shape, and its major pointers (none).
let ipre_ok (g: heap)
  : Lemma (requires V.roomy)
          (ensures GenInv.minor_heap_shape NW.nur /\ GenInv.minor_major_fields_not_free free_stw NW.nur (gF g))
  = NW.nur_shape ();
    NW.nur_fields free_stw (gF g)

/// **The run**: the dark run to the step that swept C's page, a step at
/// every unit, the end, and a minor collection once idle.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let run_idle (g: heap{V.roomy})
  : GTot (C.ccycle (D.h g) (D.rs g) (gI g) (sI g) I.Idle (since_i g)) =
  D.start_pre g;
  D.darkened_a g;
  D.gd_ok g;
  D.mal_ok g;
  D.gz_ok g;
  D.n1_storable g;
  D.write_ok g;
  D.gw_ok g;
  D.marks g;
  D.gh_no_grey g;
  ends g;
  ipre_ok g;
  let rm0 : C.cmarking (D.h g) (D.rs g) (MStart.darkened (D.h g) (D.rs g)) (D.st g) MP.scan_none SPC.nothing_new =
    C.CStart V.m0 (D.st g) () in
  let rm1 : C.cmarking (D.h g) (D.rs g) (D.gz g) (D.sb g) MP.scan_none (D.since_m g) =
    C.CAlloc rm0 V.m0 Wt.wzS (D.gb g) (D.sb g) (D.n1 g) () (D.gz g) (D.iw g) () in
  let rm2 : C.cmarking (D.h g) (D.rs g) (D.gw g) (D.sb g) MP.scan_none (D.since_m g) =
    C.CWrite rm1 V.m0 (D.oa g) (D.oa g <: hp_addr) (D.n1 g <: U64.t) () in
  let r0 : C.csweep (D.gh g) (D.gh g) (D.s0 g) I.Sweeping SPC.nothing_new = C.CSStart (D.s0 g) in
  let r1 : C.csweep (D.gh g) (D.g1 g) (D.s1 g) I.Sweeping SPC.nothing_new = C.CSStep r0 (D.jc g) in
  let r2 = CV.crest r1 0 in
  let r3 : C.csweep (D.gh g) (gF g) (sF g) I.Idle SPC.nothing_new = C.CSEnd r2 () in
  let r4 : C.csweep (D.gh g) (gI g) (sI g) I.Idle (since_mi g) = C.CSIMinor r3 NW.nur NW.nroots () in
  assert (C.cstart_st r0 == D.s0 g);
  assert (C.cstart_st r1 == C.cstart_st r0);
  assert (C.cstart_st r3 == C.cstart_st r2);
  assert (C.cstart_st r4 == C.cstart_st r3);
  C.CSweep rm2 V.m0 (D.gh g) MP.scan_none () r4 ()
#pop-options

/// The state before the collection: the `Idle` invariant, with room.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let before_idle (g: heap)
  : Lemma (requires V.roomy)
          (ensures PA.inv I.Idle (gF g) (sF g) /\ ~(Th.no_fit (gF g) (sF g) 2))
  = ends g;
    MS2.sw_end (gF g) (sF g);
    fit_of_room (gF g) (sF g) (D.jc g)
#pop-options

/// The roots forwarded: the object, to the block the allocator returned.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let roots_fwd (g: heap)
  : Lemma (requires V.roomy)
          (ensures (let a = PId.idle_tal in
                    let cs0 : P.gstate pstate = { P.major = gF g; P.st = sF g; P.fwd = Promote.empty_forwarding;
                                                 P.queue = Seq.empty } in
                    (P.forward_roots a NW.nur cs0 NW.nroots 0).P.fwd NW.nobj <> 0UL))
  = NW.nur_facts ();
    before_idle g;
    idle_alloc_some (gF g) (sF g);
    let a = PId.idle_tal in
    let cs0 : P.gstate pstate = { P.major = gF g; P.st = sF g; P.fwd = Promote.empty_forwarding;
                                 P.queue = Seq.empty } in
    assert (Seq.length NW.nroots == 1);
    assert (Seq.index NW.nroots 0 == NW.nobj);
    assert (P.forward_roots a NW.nur cs0 NW.nroots 0 ==
            P.forward_roots a NW.nur (P.forward_one a NW.nur cs0 NW.nobj) NW.nroots 1);
    assert (~(is_infix_in_minor NW.nur NW.nobj));
    assert (Promote.promoted_tag NW.nur NW.nobj == 0UL)
#pop-options

/// **The collection once idle promotes the nursery object**: it forwards
/// it to a block of the major heap that was not in use before and is after
/// -- a block the collection made, white -- and rewrites the root to it.
#push-options "--z3rlimit 40"
let run_idle_promotes (g: heap)
  : Lemma (requires V.roomy)
          (ensures (let r = mi g in
                    let v = r.P.rfwd NW.nobj in
                    v <> 0UL /\ U64.v v >= 8 /\ U64.v v < heap_size /\ U64.v v % 8 == 0 /\
                    since_mi g (v <: obj_addr) /\
                    in_use free_stw (gI g) (v <: obj_addr) /\ ~(in_use free_stw (gF g) (v <: obj_addr)) /\
                    color_of_object (v <: obj_addr) (gI g) == Header.White /\
                    Seq.index r.P.rroots 0 == v))
  = let a = PId.idle_tal in
    before_idle g;
    ipre_ok g;
    NW.nur_facts ();
    PId.idle_contract ();
    GenInv.minor_heap_shape_elim NW.nur;
    let cs0 : P.gstate pstate = { P.major = gF g; P.st = sF g; P.fwd = Promote.empty_forwarding;
                                 P.queue = Seq.empty } in
    roots_fwd g;
    let cs1 = P.forward_roots a NW.nur cs0 NW.nroots 0 in
    MV.scan_mono a NW.nur cs1 0 (Seq.length (minor_objects NW.nur)) NW.nobj;
    let cs = P.promote a NW.nur (gF g) (sF g) NW.nroots in
    assert (cs.P.fwd NW.nobj <> 0UL);
    assert (L.cpre a NW.nur (gF g) (sF g));
    PC.promoted a NW.nur (gF g) (sF g) NW.nroots;
    PC.collect_inv a NW.nur (gF g) (sF g) NW.nroots;
    assert (L.entry a NW.nur (gF g) cs.P.major cs.P.fwd NW.nobj);
    assert (L.copy_of a NW.nur (gF g) cs.P.major NW.nobj (cs.P.fwd NW.nobj));
    Promote.rewrite_roots_index NW.nroots cs.P.fwd 0;
    assert (Promote.is_minor_pointer NW.nobj);
    PId.i_facts NW.nur (gF g) (sF g) NW.nroots
#pop-options

/// **The theorems of the cycle hold at its end**: the page `Idle`
/// invariant, A and B survive, at their sizes, not handed out; the heap's
/// last word lies in a block unreachable at the start exactly when it is
/// free or new.
let run_idle_theorems (g: heap)
  : Lemma (requires V.roomy)
          (ensures PA.inv I.Idle (gI g) (sI g) /\
                   Seq.mem (D.oa g) (objects zero_addr (gI g)) /\ ~(is_blue (D.oa g) (gI g)) /\
                   Seq.mem (D.ob g) (objects zero_addr (gI g)) /\ ~(is_blue (D.ob g) (gI g)) /\
                   ~(since_i g (D.oa g)) /\ ~(since_i g (D.ob g)) /\
                   (GC_.unreachable_covered (D.h g) (D.rs g) (heap_size - 8) <==>
                    LL.blue_covered (gI g) (heap_size - 8) \/
                    SPC.new_covered (since_i g) (gI g) (heap_size - 8)))
  = D.reach_ab g;
    C.ccycle_correct (run_idle g)

/// ---------------------------------------------------------------------------
/// An allocation with a tag mid-sweep
/// ---------------------------------------------------------------------------

/// The allocation of one word with tag 1, after the step that swept C's
/// page: O, as at tag 0 (`IncrVacuity.alloc_mixed`); its field cleared.
let at1 (g: heap{V.roomy}) : GTot (heap & pstate & U64.t) = AT.alloc_tag I.Sweeping (D.g1 g) (D.s1 g) Wt.wzS 1UL
let gat (g: heap{V.roomy}) : GTot heap = let (a, _, _) = at1 g in a
let gt2 (g: heap{V.roomy}) : GTot heap = B.zeros (gat g) (U64.v (D.oo g)) Wt.wzS

/// The rest of the sweep.
let gtF (g: heap{V.roomy}) : GTot heap = fst (SA.sweep_from (gt2 g) (D.s2 g) 0)
let stF (g: heap{V.roomy}) : GTot pstate = snd (SA.sweep_from (gt2 g) (D.s2 g) 0)

/// The allocation's facts: O, white, of tag 1, at the state of tag 0; its
/// field cleared as the caller may; the mid-sweep invariant after it, and
/// every page swept at the end.
#push-options "--z3rlimit 40"
let tagged_ok (g: heap)
  : Lemma (requires V.roomy)
          (ensures at1 g == (gat g, D.s2 g, (D.oo g <: U64.t)) /\
                   Seq.mem (D.oo g) (objects zero_addr (gat g)) /\
                   U64.v (wosize_of_object (D.oo g) (gat g)) == Wt.wzS /\
                   tag_of_object (D.oo g) (gt2 g) == 1UL /\ is_white (D.oo g) (gt2 g) /\
                   AT.fields_written_away (MS.free_sw (D.s1 g).pm) (gat g) (gt2 g) (D.oo g) /\
                   MS.pages_ok_sw (gt2 g) (D.s2 g) /\
                   MS.pages_ok_sw (gtF g) (stF g) /\ PMP.all_swept (stF g))
  = GC.Spec.Pages.IncrVacuity.alloc_mixed g 1UL;
    GC.Spec.Pages.IncrVacuity.mixed_state g;
    ATO.alloc_tag_sweeping (D.g1 g) (D.s1 g) Wt.wzS 1UL;
    let x = D.oo g in
    TF.cleared_away (MS.free_sw (D.s1 g).pm) (gat g) x;
    TF.sw_tag_inv (D.g1 g) (D.s1 g) Wt.wzS 1UL (gat g) (D.s2 g) x (gt2 g);
    hd_address_spec x;
    assert (read_word (gt2 g) (hd_address x) == read_word (gat g) (hd_address x));
    tag_of_object_spec x (gat g); tag_of_object_spec x (gt2 g);
    color_of_header_eq x (gat g) (gt2 g);
    is_white_iff x (gat g); is_white_iff x (gt2 g);
    F.obj_same (gat g) (gt2 g) x x;
    MS.pages_ok_sw_elim (gt2 g) (D.s2 g);
    if n_pages > 0 then assert (cont_ok (D.s2 g).pm 0);
    MS2.sweep_from_sw (gt2 g) (D.s2 g) 0
#pop-options

/// **The run**: the dark run to the step that swept C's page, the
/// allocation with tag 1 and its cleared field, a step at every unit, the
/// end.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let run_tagged (g: heap{V.roomy})
  : GTot (C.ccycle (D.h g) (D.rs g) (gtF g) (stF g) I.Idle (D.since_d g)) =
  D.start_pre g;
  D.darkened_a g;
  D.gd_ok g;
  D.mal_ok g;
  D.gz_ok g;
  D.n1_storable g;
  D.write_ok g;
  D.gw_ok g;
  D.marks g;
  D.gh_no_grey g;
  tagged_ok g;
  let rm0 : C.cmarking (D.h g) (D.rs g) (MStart.darkened (D.h g) (D.rs g)) (D.st g) MP.scan_none SPC.nothing_new =
    C.CStart V.m0 (D.st g) () in
  let rm1 : C.cmarking (D.h g) (D.rs g) (D.gz g) (D.sb g) MP.scan_none (D.since_m g) =
    C.CAlloc rm0 V.m0 Wt.wzS (D.gb g) (D.sb g) (D.n1 g) () (D.gz g) (D.iw g) () in
  let rm2 : C.cmarking (D.h g) (D.rs g) (D.gw g) (D.sb g) MP.scan_none (D.since_m g) =
    C.CWrite rm1 V.m0 (D.oa g) (D.oa g <: hp_addr) (D.n1 g <: U64.t) () in
  let r0 : C.csweep (D.gh g) (D.gh g) (D.s0 g) I.Sweeping SPC.nothing_new = C.CSStart (D.s0 g) in
  let r1 : C.csweep (D.gh g) (D.g1 g) (D.s1 g) I.Sweeping SPC.nothing_new = C.CSStep r0 (D.jc g) in
  let r2 : C.csweep (D.gh g) (gt2 g) (D.s2 g) I.Sweeping (SPC.with_new SPC.nothing_new (D.oo g <: U64.t)) =
    C.CSAllocT r1 Wt.wzS 1UL (gat g) (D.s2 g) (D.oo g) () (gt2 g) () in
  let r3 = CV.crest r2 0 in
  let r4 : C.csweep (D.gh g) (gtF g) (stF g) I.Idle (SPC.with_new SPC.nothing_new (D.oo g <: U64.t)) =
    C.CSEnd r3 () in
  assert (C.cstart_st r0 == D.s0 g);
  assert (C.cstart_st r1 == C.cstart_st r0);
  assert (C.cstart_st r2 == C.cstart_st r1);
  assert (C.cstart_st r4 == C.cstart_st r3);
  C.CSweep rm2 V.m0 (D.gh g) MP.scan_none () r4 ()
#pop-options

/// **Not trivial**: the object handed out mid-sweep has tag 1, is white,
/// and is new.
let run_tagged_nontrivial (g: heap)
  : Lemma (requires V.roomy)
          (ensures Seq.mem (D.oo g) (objects zero_addr (gat g)) /\
                   tag_of_object (D.oo g) (gt2 g) == 1UL /\ is_white (D.oo g) (gt2 g) /\
                   D.since_d g (D.oo g))
  = tagged_ok g

/// **The theorems of the cycle hold at its end.**
let run_tagged_theorems (g: heap)
  : Lemma (requires V.roomy)
          (ensures PA.inv I.Idle (gtF g) (stF g) /\
                   Seq.mem (D.oa g) (objects zero_addr (gtF g)) /\ ~(is_blue (D.oa g) (gtF g)) /\
                   Seq.mem (D.ob g) (objects zero_addr (gtF g)) /\ ~(is_blue (D.ob g) (gtF g)) /\
                   ~(D.since_d g (D.oa g)) /\ ~(D.since_d g (D.ob g)) /\
                   (GC_.unreachable_covered (D.h g) (D.rs g) (heap_size - 8) <==>
                    LL.blue_covered (gtF g) (heap_size - 8) \/
                    SPC.new_covered (D.since_d g) (gtF g) (heap_size - 8)))
  = D.reach_ab g;
    C.ccycle_correct (run_tagged g)

/// ---------------------------------------------------------------------------
/// An allocation with a tag while marking
/// ---------------------------------------------------------------------------

/// The allocation of one word with tag 252 (raw data) right after root
/// darkening.
let mt (g: heap) : GTot (heap & pstate & U64.t) = AT.alloc_tag I.Marking (D.gd g) (D.st g) 1 252UL
let gbt (g: heap) : GTot heap = let (a, _, _) = mt g in a
let sbt (g: heap) : GTot pstate = let (_, s, _) = mt g in s
let ot (g: heap) : GTot obj_addr = Wt.as_obj (let (_, _, o) = mt g in o)

/// It succeeds, black, of tag 252, so raw data: its field may hold anything.
#push-options "--z3rlimit 40"
let mt_ok (g: heap)
  : Lemma (requires V.roomy)
          (ensures mt g == (gbt g, sbt g, (ot g <: U64.t)) /\
                   PMP.mark_inv (D.gd g) (D.st g) /\
                   Seq.mem (ot g) (objects zero_addr (gbt g)) /\
                   tag_of_object (ot g) (gbt g) == 252UL /\ is_black (ot g) (gbt g) /\
                   is_no_scan (ot g) (gbt g))
  = MV.alloc_some_mark g;
    D.gd_ok g;
    AT.alloc_col_tag_eq Header.Black 0UL (D.gd g) (D.st g) 1;
    AT.alloc_col_tag_eq Header.Black 252UL (D.gd g) (D.st g) 1;
    assert_norm (I.new_colour I.Marking == Header.Black);
    ATO.alloc_tag_marking (D.gd g) (D.st g) 1 252UL;
    is_no_scan_spec (ot g) (gbt g);
    no_scan_tag_val ()
#pop-options

/// **The run**: root darkening, then the allocation with tag 252, its
/// field left as it is.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let run_mark_tagged (g: heap{V.roomy})
  : GTot (C.ccycle (D.h g) (D.rs g) (gbt g) (sbt g) I.Marking (SPC.with_new SPC.nothing_new (ot g))) =
  D.start_pre g;
  D.darkened_a g;
  D.gd_ok g;
  mt_ok g;
  let rm0 : C.cmarking (D.h g) (D.rs g) (MStart.darkened (D.h g) (D.rs g)) (D.st g) MP.scan_none SPC.nothing_new =
    C.CStart V.m0 (D.st g) () in
  let rm0' : C.cmarking (D.h g) (D.rs g) (D.gd g) (D.st g) MP.scan_none SPC.nothing_new = rm0 in
  C.CMark (C.CAllocT rm0' V.m0 1 252UL (gbt g) (sbt g) (ot g) () (gbt g) (MC.Init_done (gbt g)) ())
#pop-options

/// **The run carries the `Marking` invariant and akhil's account**, and is
/// not trivial: the object handed out has tag 252 and is black.
let run_mark_tagged_inv (g: heap)
  : Lemma (requires V.roomy)
          (ensures PMP.mark_inv (gbt g) (sbt g) /\
                   GC.Spec.Pages.Cycle.pcycle_account
                     (MC.snapshot (D.h g) (D.rs g) (SPC.with_new SPC.nothing_new (ot g))) (gbt g) (sbt g) I.Marking /\
                   Seq.mem (ot g) (objects zero_addr (gbt g)) /\
                   tag_of_object (ot g) (gbt g) == 252UL /\ is_black (ot g) (gbt g))
  = mt_ok g;
    C.ccycle_inv (run_mark_tagged g)
