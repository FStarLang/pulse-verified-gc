/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Cycle.MinorVacuity - a carried run with a minor collection
/// that promotes
/// ---------------------------------------------------------------------------
///
/// Plan §27.6.  The vacuity rule (plan §18) for the minor events of
/// `GC.Spec.Pages.Cycle.Carried`: `run_minor g` is `run_dark`'s marking (root
/// darkening, an allocation, the barrier write that darkens B), the
/// hand-over, the sweep's start, the step that sweeps C's page, then **a
/// minor collection** of a nursery holding one object (`NurseryWitness`),
/// from one root pointing at it, then a step at every unit, and the end --
/// with only the events' own hypotheses shown.
///
/// `run_minor_promotes`: the collection forwards the nursery object to a
/// block of the major heap -- allocated by the page allocator with the
/// object's tag -- that was not in use before and is in use after, and
/// rewrites the root to it.  `run_minor_theorems` applies `ccycle_correct`.

module GC.Spec.Pages.Cycle.MinorVacuity

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
module SPC = GC.Spec.SweepPhase.Completeness
module LL = GC.Spec.FusedSweep.Lossless
module GC_ = GC.Gen.Cycle
module I = GC.Spec.AllocIface
module PA = GC.Spec.Pages.Allocator
module AP = GC.Spec.Pages.AllocPhase
module AT = GC.Spec.Pages.AllocTag
module SA = GC.Spec.Pages.SweepAll
module MS = GC.Spec.Pages.MidSweep
module MS2 = GC.Spec.Pages.MidSweepStep
module PMP = GC.Spec.Pages.MarkPhase
module Header = GC.Lib.Header
module Wt = GC.Spec.Pages.Witness
module V = GC.Spec.Pages.Cycle.Vacuity
module D = GC.Spec.Pages.Cycle.VacuityDark
module C = GC.Spec.Pages.Cycle.Carried
module CV = GC.Spec.Pages.Cycle.CarriedVacuity
module P = GC.Spec.Pages.Promote
module L = GC.Spec.Pages.Promote.Loop
module PC = GC.Spec.Pages.Promote.Collect
module PI = GC.Spec.Pages.PromoteInst
module PSw = GC.Spec.Pages.Promote.Sweep
module NW = GC.Spec.Pages.NurseryWitness
module PM = GC.Spec.Pages.Cycle.Mark
module PMk = GC.Spec.Pages.Promote.Mark
module GMM = GC.Gen.MarkPhase.Minor
module MPC = GC.Spec.MarkPhase.Completeness
module MC = GC.Gen.MarkPhase.Cycle
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module GenInv = GC.Gen.HeapInvariant

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The collection
/// ---------------------------------------------------------------------------

/// The minor collection, after the step that swept C's page.
let mc (g: heap{V.roomy}) : GTot (P.gresult pstate) = PSw.scollect NW.nur (D.g1 g) (D.s1 g) NW.nroots
let gm (g: heap{V.roomy}) : GTot heap = (mc g).P.rmajor
let sm (g: heap{V.roomy}) : GTot pstate = (mc g).P.rst

/// The rest of the sweep.
let gfm (g: heap{V.roomy}) : GTot heap = fst (SA.sweep_from (gm g) (sm g) 0)
let sfm (g: heap{V.roomy}) : GTot pstate = snd (SA.sweep_from (gm g) (sm g) 0)

/// The blocks the collection made, and every address the run hands out.
let since_mm (g: heap{V.roomy}) : obj_addr -> prop = PSw.with_made (D.s1 g).pm SPC.nothing_new (D.g1 g) (gm g)
let since_x (g: heap{V.roomy}) : obj_addr -> prop = GC_.union (D.since_m g) (since_mm g)

/// Its hypotheses: the mid-sweep invariant, the nursery's shape, and its
/// major pointers (none).
let pre_ok (g: heap)
  : Lemma (requires V.roomy)
          (ensures PSw.spre NW.nur (D.g1 g) (D.s1 g))
  = D.step1 g;
    NW.nur_shape ();
    NW.nur_fields (MS.free_sw (D.s1 g).pm) (D.g1 g)

/// The rest of the sweep ends with every page swept.
let ends (g: heap)
  : Lemma (requires V.roomy)
          (ensures MS.pages_ok_sw (gm g) (sm g) /\ MS.pages_ok_sw (gfm g) (sfm g) /\ PMP.all_swept (sfm g))
  = pre_ok g;
    PSw.s_facts NW.nur (D.g1 g) (D.s1 g) NW.nroots;
    MS.pages_ok_sw_elim (gm g) (sm g);
    if n_pages > 0 then assert (cont_ok (sm g).pm 0);
    MS2.sweep_from_sw (gm g) (sm g) 0

/// ---------------------------------------------------------------------------
/// The run
/// ---------------------------------------------------------------------------

/// **The run.**
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let run_minor (g: heap{V.roomy})
  : GTot (C.ccycle (D.h g) (D.rs g) (gfm g) (sfm g) I.Idle (since_x g)) =
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
  pre_ok g;
  ends g;
  let rm0 : C.cmarking (D.h g) (D.rs g) (MStart.darkened (D.h g) (D.rs g)) (D.st g) MP.scan_none SPC.nothing_new =
    C.CStart V.m0 (D.st g) () in
  let rm1 : C.cmarking (D.h g) (D.rs g) (D.gz g) (D.sb g) MP.scan_none (D.since_m g) =
    C.CAlloc rm0 V.m0 Wt.wzS (D.gb g) (D.sb g) (D.n1 g) () (D.gz g) (D.iw g) () in
  let rm2 : C.cmarking (D.h g) (D.rs g) (D.gw g) (D.sb g) MP.scan_none (D.since_m g) =
    C.CWrite rm1 V.m0 (D.oa g) (D.oa g <: hp_addr) (D.n1 g <: U64.t) () in
  let r0 : C.csweep (D.gh g) (D.gh g) (D.s0 g) I.Sweeping SPC.nothing_new = C.CSStart (D.s0 g) in
  let r1 : C.csweep (D.gh g) (D.g1 g) (D.s1 g) I.Sweeping SPC.nothing_new = C.CSStep r0 (D.jc g) in
  let r2 : C.csweep (D.gh g) (gm g) (sm g) I.Sweeping (since_mm g) = C.CSMinor r1 NW.nur NW.nroots () in
  let r4 = CV.crest r2 0 in
  let r5 : C.csweep (D.gh g) (gfm g) (sfm g) I.Idle (since_mm g) = C.CSEnd r4 () in
  assert (C.cstart_st r0 == D.s0 g);
  assert (C.cstart_st r1 == C.cstart_st r0);
  assert (C.cstart_st r2 == C.cstart_st r1);
  assert (C.cstart_st r5 == C.cstart_st r4);
  C.CSweep rm2 V.m0 (D.gh g) MP.scan_none () r5 ()
#pop-options

/// ---------------------------------------------------------------------------
/// It promotes
/// ---------------------------------------------------------------------------

/// The forwarding map only grows.
let normal_mono (#s: Type0) (a: P.tal s) (minor: minor_state) (cs: P.gstate s) (addr m: U64.t)
  : Lemma (requires cs.P.fwd m <> 0UL)
          (ensures (P.forward_normal a minor cs addr).P.fwd m == cs.P.fwd m)
  = ()

let one_mono (#s: Type0) (a: P.tal s) (minor: minor_state) (cs: P.gstate s) (addr m: U64.t)
  : Lemma (requires cs.P.fwd m <> 0UL)
          (ensures (P.forward_one a minor cs addr).P.fwd m == cs.P.fwd m)
  = if cs.P.fwd addr <> 0UL then ()
    else if is_infix_in_minor minor addr then
      normal_mono a minor cs (infix_parent minor addr) m
    else normal_mono a minor cs addr m

#push-options "--fuel 1 --ifuel 0"
let rec fields_mono (#s: Type0) (a: P.tal s) (minor: minor_state) (cs: P.gstate s)
                    (parent: U64.t) (idx: nat) (wz: nat) (m: U64.t)
  : Lemma (requires cs.P.fwd m <> 0UL)
          (ensures (P.forward_fields a minor cs parent idx wz).P.fwd m == cs.P.fwd m)
          (decreases (if idx >= wz then 0 else wz - idx))
  = if idx >= wz then ()
    else begin
      let fv = to_minor_offset (minor_read_field minor parent idx) in
      one_mono a minor cs fv m;
      fields_mono a minor (P.forward_one a minor cs fv) parent (idx + 1) wz m
    end

let rec scan_mono (#s: Type0) (a: P.tal s) (minor: minor_state) (cs: P.gstate s) (sc: nat) (fuel: nat) (m: U64.t)
  : Lemma (requires cs.P.fwd m <> 0UL)
          (ensures (P.scan a minor cs sc fuel).P.fwd m == cs.P.fwd m)
          (decreases fuel)
  = if fuel = 0 then ()
    else if sc >= Seq.length cs.P.queue then ()
    else begin
      let fuel' : nat = fuel - 1 in
      let obj = Seq.index cs.P.queue sc in
      let cs' = P.forward_fields a minor cs obj 0 (minor_scan_wosize minor obj) in
      fields_mono a minor cs obj 0 (minor_scan_wosize minor obj) m;
      assert (P.scan a minor cs sc fuel == P.scan a minor cs' (sc + 1) fuel');
      scan_mono a minor cs' (sc + 1) fuel' m
    end
#pop-options

/// The allocation the promotion makes succeeds: it is the sweep's
/// allocator, whose allocation of one word there succeeds (`D.alloc_ok`).
#push-options "--z3rlimit 30"
let alloc_some (g: heap)
  : Lemma (requires V.roomy)
          (ensures (let (_, _, o) = AT.alloc_tag I.Sweeping (D.g1 g) (D.s1 g) 1 0UL in o =!= 0UL))
  = D.alloc_ok g;
    AT.alloc_col_tag_eq Header.White 0UL (D.g1 g) (D.s1 g) 1;
    assert (PA.alloc I.Sweeping (D.g1 g) (D.s1 g) 1 == AP.alloc_col Header.White (D.g1 g) (D.s1 g) 1)
#pop-options

/// The roots forwarded: the object, to the block the allocator returned.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let roots_fwd (g: heap)
  : Lemma (requires V.roomy)
          (ensures (let a = PI.sw_tal (D.s1 g).pm in
                    let cs0 : P.gstate pstate = { P.major = D.g1 g; P.st = D.s1 g; P.fwd = Promote.empty_forwarding;
                                                 P.queue = Seq.empty } in
                    (P.forward_roots a NW.nur cs0 NW.nroots 0).P.fwd NW.nobj <> 0UL))
  = NW.nur_facts ();
    alloc_some g;
    let a = PI.sw_tal (D.s1 g).pm in
    let cs0 : P.gstate pstate = { P.major = D.g1 g; P.st = D.s1 g; P.fwd = Promote.empty_forwarding;
                                 P.queue = Seq.empty } in
    assert (Seq.length NW.nroots == 1);
    assert (Seq.index NW.nroots 0 == NW.nobj);
    assert (P.forward_roots a NW.nur cs0 NW.nroots 0 ==
            P.forward_roots a NW.nur (P.forward_one a NW.nur cs0 NW.nobj) NW.nroots 1);
    assert (~(is_infix_in_minor NW.nur NW.nobj));
    assert (Promote.promoted_tag NW.nur NW.nobj == 0UL)
#pop-options

/// **The collection promotes the nursery object**: it forwards it to a block
/// of the major heap that was not in use before and is after -- a block the
/// collection made -- and rewrites the root to it.
#push-options "--z3rlimit 40"
let run_minor_promotes (g: heap)
  : Lemma (requires V.roomy)
          (ensures (let r = mc g in
                    let v = r.P.rfwd NW.nobj in
                    v <> 0UL /\ U64.v v >= 8 /\ U64.v v < heap_size /\ U64.v v % 8 == 0 /\
                    since_mm g (v <: obj_addr) /\
                    in_use (MS.free_sw (D.s1 g).pm) (gm g) (v <: obj_addr) /\
                    ~(in_use (MS.free_sw (D.s1 g).pm) (D.g1 g) (v <: obj_addr)) /\
                    Seq.index r.P.rroots 0 == v))
  = let a = PI.sw_tal (D.s1 g).pm in
    pre_ok g;
    NW.nur_facts ();
    PI.sw_contract (D.s1 g).pm;
    GC.Gen.HeapInvariant.minor_heap_shape_elim NW.nur;
    let cs0 : P.gstate pstate = { P.major = D.g1 g; P.st = D.s1 g; P.fwd = Promote.empty_forwarding;
                                 P.queue = Seq.empty } in
    roots_fwd g;
    let cs1 = P.forward_roots a NW.nur cs0 NW.nroots 0 in
    scan_mono a NW.nur cs1 0 (Seq.length (minor_objects NW.nur)) NW.nobj;
    let cs = P.promote a NW.nur (D.g1 g) (D.s1 g) NW.nroots in
    assert (cs.P.fwd NW.nobj <> 0UL);
    assert (L.cpre a NW.nur (D.g1 g) (D.s1 g));
    PC.promoted a NW.nur (D.g1 g) (D.s1 g) NW.nroots;
    PC.collect_inv a NW.nur (D.g1 g) (D.s1 g) NW.nroots;
    assert (L.entry a NW.nur (D.g1 g) cs.P.major cs.P.fwd NW.nobj);
    assert (L.copy_of a NW.nur (D.g1 g) cs.P.major NW.nobj (cs.P.fwd NW.nobj));
    Promote.rewrite_roots_index NW.nroots cs.P.fwd 0;
    assert (Promote.is_minor_pointer NW.nobj)
#pop-options

/// **It is not trivial**: besides the collection that promotes, the run's
/// marking is `run_dark`'s: A and B reachable at the start, B white when
/// the barrier cut A's pointer to it and grey after.
let run_minor_nontrivial (g: heap)
  : Lemma (requires V.roomy)
          (ensures GMC.reachable_at_start (D.h g) (D.rs g) (D.oa g) /\
                   GMC.reachable_at_start (D.h g) (D.rs g) (D.ob g) /\
                   read_word (D.gz g) (D.oa g <: hp_addr) == (D.ob g <: U64.t) /\
                   is_white (D.ob g) (D.gz g) /\ is_gray (D.ob g) (D.gw g) /\
                   (let v = (mc g).P.rfwd NW.nobj in
                    v <> 0UL /\ U64.v v >= 8 /\ U64.v v < heap_size /\ U64.v v % 8 == 0 /\
                    since_mm g (v <: obj_addr)))
  = D.run_dark_nontrivial g;
    run_minor_promotes g

/// **The theorem on it**: the run ends in the page `Idle` invariant; A and
/// B survive, at their sizes, not handed out; the heap's last word lies in
/// a block unreachable at the start exactly when it is free or new.
let run_minor_theorems (g: heap)
  : Lemma (requires V.roomy)
          (ensures PA.inv I.Idle (gfm g) (sfm g) /\
                   Seq.mem (D.oa g) (objects zero_addr (gfm g)) /\ ~(is_blue (D.oa g) (gfm g)) /\
                   Seq.mem (D.ob g) (objects zero_addr (gfm g)) /\ ~(is_blue (D.ob g) (gfm g)) /\
                   ~(since_x g (D.oa g)) /\ ~(since_x g (D.ob g)) /\
                   (GC_.unreachable_covered (D.h g) (D.rs g) (heap_size - 8) <==>
                    LL.blue_covered (gfm g) (heap_size - 8) \/
                    SPC.new_covered (since_x g) (gfm g) (heap_size - 8)))
  = D.reach_ab g;
    C.ccycle_correct (run_minor g)

/// ---------------------------------------------------------------------------
/// While marking
/// ---------------------------------------------------------------------------

/// The minor collection right after root darkening.
let mcm (g: heap) : GTot (P.gresult pstate) = PMk.mcollect NW.nur (D.gd g) (D.st g) NW.nroots
let gmm (g: heap) : GTot heap = (mcm g).P.rmajor
let smm (g: heap) : GTot pstate = (mcm g).P.rst
let since_mk (g: heap) : obj_addr -> prop = GMC.with_new_blocks SPC.nothing_new (D.gd g) (gmm g)

/// The nursery holds no major pointer.
let nur_empty (w: obj_addr) : Lemma (~(GMM.nursery_refs NW.nur w))
  = let no (obj: U64.t) (j: nat)
      : Lemma (Seq.mem obj (minor_objects NW.nur) ==> minor_read_field NW.nur obj j == 0UL)
      = if Seq.mem obj (minor_objects NW.nur) then NW.nur_field obj j
    in
    FStar.Classical.forall_intro_2 no

/// Its hypotheses: the marking state, the nursery's shape, the root, the
/// root's major references (none), the nursery's major pointers (none).
#push-options "--z3rlimit 30"
let mpre_ok (g: heap)
  : Lemma (requires V.roomy)
          (ensures PM.pmark_ok NW.nur (D.gd g) (D.st g) MP.scan_none /\
                   GenInv.minor_heap_shape NW.nur /\
                   MCFH.roots_valid_for_minor_collection NW.nur (D.gd g) NW.nroots /\
                   MP.outside_refs_reached (D.gd g) MP.scan_none (GMM.root_refs (D.gd g) NW.nroots) /\
                   GenInv.minor_major_fields_not_free
                     (MPC.outside_snapshot (MC.snapshot (D.h g) (D.rs g) SPC.nothing_new)) NW.nur (D.gd g))
  = D.gd_ok g;
    D.start_pre g;
    D.darkened_a g;
    PM.start_facts V.m0 (D.h g) (D.st g) (D.rs g);
    MP.no_black_tri_color (D.gd g);
    FStar.Classical.forall_intro nur_empty;
    MP.marking_inv_start (D.gd g) (GMM.nursery_refs NW.nur);
    NW.nur_shape ();
    NW.nur_facts ();
    GenInv.minor_heap_shape_elim NW.nur;
    resolve_minor_non_infix NW.nur NW.nobj;
    NW.nroots_facts ();
    NW.nur_fields (MPC.outside_snapshot (MC.snapshot (D.h g) (D.rs g) SPC.nothing_new)) (D.gd g)
#pop-options

/// **The run, ended while marking**: root darkening, then the minor
/// collection.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let run_mark_minor (g: heap{V.roomy})
  : GTot (C.ccycle (D.h g) (D.rs g) (gmm g) (smm g) I.Marking (since_mk g)) =
  D.start_pre g;
  D.darkened_a g;
  mpre_ok g;
  let rm0 : C.cmarking (D.h g) (D.rs g) (MStart.darkened (D.h g) (D.rs g)) (D.st g) MP.scan_none SPC.nothing_new =
    C.CStart V.m0 (D.st g) () in
  let rm0' : C.cmarking (D.h g) (D.rs g) (D.gd g) (D.st g) MP.scan_none SPC.nothing_new = rm0 in
  C.CMark (C.CMinor rm0' NW.nur NW.nroots ())
#pop-options

/// The allocation the promotion makes succeeds: it is the marking
/// allocator's (`D.mal_ok`).
#push-options "--z3rlimit 30"
let alloc_some_mark (g: heap)
  : Lemma (requires V.roomy)
          (ensures (let (_, _, o) = AT.alloc_tag I.Marking (D.gd g) (D.st g) 1 0UL in o =!= 0UL))
  = D.mal_ok g;
    AT.alloc_col_tag_eq Header.Black 0UL (D.gd g) (D.st g) 1;
    assert (PA.alloc I.Marking (D.gd g) (D.st g) 1 == AP.alloc_col Header.Black (D.gd g) (D.st g) 1)
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let roots_fwd_mark (g: heap)
  : Lemma (requires V.roomy)
          (ensures (let a = PI.mark_tal in
                    let cs0 : P.gstate pstate = { P.major = D.gd g; P.st = D.st g; P.fwd = Promote.empty_forwarding;
                                                 P.queue = Seq.empty } in
                    (P.forward_roots a NW.nur cs0 NW.nroots 0).P.fwd NW.nobj <> 0UL))
  = NW.nur_facts ();
    alloc_some_mark g;
    let a = PI.mark_tal in
    let cs0 : P.gstate pstate = { P.major = D.gd g; P.st = D.st g; P.fwd = Promote.empty_forwarding;
                                 P.queue = Seq.empty } in
    assert (Seq.length NW.nroots == 1);
    assert (Seq.index NW.nroots 0 == NW.nobj);
    assert (P.forward_roots a NW.nur cs0 NW.nroots 0 ==
            P.forward_roots a NW.nur (P.forward_one a NW.nur cs0 NW.nobj) NW.nroots 1);
    assert (~(is_infix_in_minor NW.nur NW.nobj));
    assert (Promote.promoted_tag NW.nur NW.nobj == 0UL)
#pop-options

/// **It promotes**: the nursery object goes to a black block of the major
/// heap, not in use before and in use after, among the addresses the run
/// handed out; the root is rewritten to it.
#push-options "--z3rlimit 40"
let run_mark_minor_promotes (g: heap)
  : Lemma (requires V.roomy)
          (ensures (let r = mcm g in
                    let v = r.P.rfwd NW.nobj in
                    v <> 0UL /\ U64.v v >= 8 /\ U64.v v < heap_size /\ U64.v v % 8 == 0 /\
                    since_mk g (v <: obj_addr) /\ is_black (v <: obj_addr) (gmm g) /\
                    Seq.index r.P.rroots 0 == v))
  = let a = PI.mark_tal in
    mpre_ok g;
    NW.nur_facts ();
    NW.nur_fields free_stw (D.gd g);
    PI.mark_contract ();
    GenInv.minor_heap_shape_elim NW.nur;
    let cs0 : P.gstate pstate = { P.major = D.gd g; P.st = D.st g; P.fwd = Promote.empty_forwarding;
                                 P.queue = Seq.empty } in
    roots_fwd_mark g;
    let cs1 = P.forward_roots a NW.nur cs0 NW.nroots 0 in
    scan_mono a NW.nur cs1 0 (Seq.length (minor_objects NW.nur)) NW.nobj;
    let cs = P.promote a NW.nur (D.gd g) (D.st g) NW.nroots in
    assert (cs.P.fwd NW.nobj <> 0UL);
    assert (L.cpre a NW.nur (D.gd g) (D.st g));
    PC.promoted a NW.nur (D.gd g) (D.st g) NW.nroots;
    PC.collect_inv a NW.nur (D.gd g) (D.st g) NW.nroots;
    assert (L.entry a NW.nur (D.gd g) cs.P.major cs.P.fwd NW.nobj);
    assert (L.copy_of a NW.nur (D.gd g) cs.P.major NW.nobj (cs.P.fwd NW.nobj));
    let v : obj_addr = cs.P.fwd NW.nobj in
    PMk.m_new_black NW.nur (D.gd g) (D.st g) NW.nroots v;
    Promote.rewrite_roots_index NW.nroots cs.P.fwd 0;
    assert (Promote.is_minor_pointer NW.nobj)
#pop-options

/// **The theorem on it**: every state of a run is in the page invariant of
/// its phase and in akhil's account (`C.ccycle_inv`), here the page
/// `Marking` invariant after the collection.
let run_mark_minor_theorems (g: heap)
  : Lemma (requires V.roomy)
          (ensures PMP.mark_inv (gmm g) (smm g) /\
                   GC.Spec.Pages.Cycle.pcycle_account (MC.snapshot (D.h g) (D.rs g) (since_mk g)) (gmm g) (smm g) I.Marking)
  = C.ccycle_inv (run_mark_minor g)
