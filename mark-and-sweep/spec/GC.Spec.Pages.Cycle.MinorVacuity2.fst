/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Cycle.MinorVacuity2 - a minor collection that promotes an
/// object and the object it points at
/// ---------------------------------------------------------------------------
///
/// Plan §27.9.  `run_mark_minor2 g`: root darkening, then a minor
/// collection of the nursery of `NurseryWitness2` -- A, whose field points
/// at B, and B -- from one root pointing at A, as a run of the carried
/// cycle ending while marking.
///
/// `run_mark_minor2_promotes`: the collection forwards A (from the root)
/// and B (found scanning A's copy) to two different blocks, both made by
/// the collection and black; the root is rewritten to A's copy, and A's
/// copy's field is rewritten from the nursery pointer to B's copy.
///
/// B's allocation succeeds because A's left room (`GC.Spec.Pages.RoomAfter`),
/// under `two_slots`, a fact of the parameters as `roomy` is.

module GC.Spec.Pages.Cycle.MinorVacuity2

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
module Header = GC.Lib.Header
module Promote = GC.Gen.Promote
module MP = GC.Spec.MarkPhase
module GMC = GC.Gen.MarkPhase.Completeness
module GMM = GC.Gen.MarkPhase.Minor
module MStart = GC.Gen.MarkPhase.Start
module MPC = GC.Spec.MarkPhase.Completeness
module MC = GC.Gen.MarkPhase.Cycle
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module GenInv = GC.Gen.HeapInvariant
module PUpd = GC.Gen.PromoteUpdate
module SPC = GC.Spec.SweepPhase.Completeness
module I = GC.Spec.AllocIface
module PA = GC.Spec.Pages.Allocator
module AP = GC.Spec.Pages.AllocPhase
module AT = GC.Spec.Pages.AllocTag
module A = GC.Spec.Pages.Alloc
module PMP = GC.Spec.Pages.MarkPhase
module Th = GC.Spec.Pages.Theorems
module Sh = GC.Spec.Pages.Shape
module Wt = GC.Spec.Pages.Witness
module V = GC.Spec.Pages.Cycle.Vacuity
module D = GC.Spec.Pages.Cycle.VacuityDark
module PM = GC.Spec.Pages.Cycle.Mark
module C = GC.Spec.Pages.Cycle.Carried
module P = GC.Spec.Pages.Promote
module L = GC.Spec.Pages.Promote.Loop
module PC = GC.Spec.Pages.Promote.Collect
module PI = GC.Spec.Pages.PromoteInst
module PMk = GC.Spec.Pages.Promote.Mark
module N2 = GC.Spec.Pages.NurseryWitness2
module RA = GC.Spec.Pages.RoomAfter
module MV = GC.Spec.Pages.Cycle.MinorVacuity

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The collection, and the run
/// ---------------------------------------------------------------------------

let mc2 (g: heap) : GTot (P.gresult pstate) = PMk.mcollect N2.nur2 (D.gd g) (D.st g) N2.roots2
let gm2 (g: heap) : GTot heap = (mc2 g).P.rmajor
let sm2 (g: heap) : GTot pstate = (mc2 g).P.rst
let since2 (g: heap) : obj_addr -> prop = GMC.with_new_blocks SPC.nothing_new (D.gd g) (gm2 g)

/// The nursery holds no major pointer.
let nur2_empty (w: obj_addr) : Lemma (~(GMM.nursery_refs N2.nur2 w))
  = zero_addr_above_2048 ();
    let no (obj: U64.t) (j: nat)
      : Lemma (Seq.mem obj (minor_objects N2.nur2) /\ j < minor_scan_wosize N2.nur2 obj ==>
               ~(is_pointer_field (minor_read_field N2.nur2 obj j)))
      = if FStar.IndefiniteDescription.strong_excluded_middle
             (Seq.mem obj (minor_objects N2.nur2) /\ j < minor_scan_wosize N2.nur2 obj)
        then begin N2.field_val obj j; assert_norm (U64.v N2.objB == 24) end
    in
    FStar.Classical.forall_intro_2 no

/// The root is valid: A, a nursery object of one field.
#push-options "--z3rlimit 30"
let roots_ok (g: heap)
  : Lemma (MCFH.roots_valid_for_minor_collection N2.nur2 (D.gd g) N2.roots2 /\
           MP.outside_refs_reached (D.gd g) MP.scan_none (GMM.root_refs (D.gd g) N2.roots2))
  = N2.roots_facts ();
    N2.objA_known ();
    N2.mem_objects N2.objA;
    assert_norm (U64.v N2.objA == 8);
    resolve_minor_non_infix N2.nur2 N2.objA
#pop-options

/// Its hypotheses.
#push-options "--z3rlimit 30"
let mpre_ok2 (g: heap)
  : Lemma (requires V.roomy)
          (ensures PM.pmark_ok N2.nur2 (D.gd g) (D.st g) MP.scan_none /\
                   GenInv.minor_heap_shape N2.nur2 /\
                   MCFH.roots_valid_for_minor_collection N2.nur2 (D.gd g) N2.roots2 /\
                   MP.outside_refs_reached (D.gd g) MP.scan_none (GMM.root_refs (D.gd g) N2.roots2) /\
                   GenInv.minor_major_fields_not_free
                     (MPC.outside_snapshot (MC.snapshot (D.h g) (D.rs g) SPC.nothing_new)) N2.nur2 (D.gd g))
  = D.gd_ok g;
    D.start_pre g;
    D.darkened_a g;
    PM.start_facts V.m0 (D.h g) (D.st g) (D.rs g);
    MP.no_black_tri_color (D.gd g);
    FStar.Classical.forall_intro nur2_empty;
    MP.marking_inv_start (D.gd g) (GMM.nursery_refs N2.nur2);
    N2.shape ();
    roots_ok g;
    N2.no_major (MPC.outside_snapshot (MC.snapshot (D.h g) (D.rs g) SPC.nothing_new)) (D.gd g)
#pop-options

/// **The run, ended while marking**: root darkening, then the collection.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let run_mark_minor2 (g: heap{V.roomy})
  : GTot (C.ccycle (D.h g) (D.rs g) (gm2 g) (sm2 g) I.Marking (since2 g)) =
  D.start_pre g;
  D.darkened_a g;
  mpre_ok2 g;
  let rm0 : C.cmarking (D.h g) (D.rs g) (MStart.darkened (D.h g) (D.rs g)) (D.st g) MP.scan_none SPC.nothing_new =
    C.CStart V.m0 (D.st g) () in
  let rm0' : C.cmarking (D.h g) (D.rs g) (D.gd g) (D.st g) MP.scan_none SPC.nothing_new = rm0 in
  C.CMark (C.CMinor rm0' N2.nur2 N2.roots2 ())
#pop-options

/// ---------------------------------------------------------------------------
/// The two allocations succeed
/// ---------------------------------------------------------------------------

/// The marking invariant gives the lists' length.
let avail_len (g: heap) (st: pstate)
  : Lemma (requires PMP.mark_inv g st) (ensures Seq.length st.avail == n_cls)
  = eliminate exists (ys: list obj_addr). GC.Spec.Pages.ColourFacts.live_list g ys /\
                                     pages_ok (GC.Spec.Pages.Recolour.whiten g ys) st
    with GC.Spec.Pages.Step.pages_ok_elim (GC.Spec.Pages.Recolour.whiten g ys) st

/// The tagged allocator's object and state are the stage-2 allocator's.
let same_alloc (col: color) (g: heap) (st: pstate)
  : Lemma (let (_, s1, o1) = A.alloc g st 1 in
           let (_, s2, o2) = AT.alloc_col_tag col 0UL g st 1 in
           s2 == s1 /\ o2 == o1)
  = AT.alloc_col_tag_eq col 0UL g st 1

/// **The second allocation succeeds**: from any heap in the marking
/// invariant at the state the first one left.
#push-options "--z3rlimit 40"
let second_some (g: heap) (gx: heap)
  : Lemma (requires V.roomy /\ RA.two_slots /\
                    (let (_, s1, _) = AT.alloc_tag I.Marking (D.gd g) (D.st g) 1 0UL in PMP.mark_inv gx s1))
          (ensures (let (_, s1, _) = AT.alloc_tag I.Marking (D.gd g) (D.st g) 1 0UL in
                    let (_, _, o) = AT.alloc_tag I.Marking gx s1 1 0UL in o =!= 0UL))
  = D.gd_ok g;
    MV.alloc_some_mark g;
    same_alloc Header.Black (D.gd g) (D.st g);
    avail_len (D.gd g) (D.st g);
    RA.room_after (D.gd g) (D.st g) (V.jf g);
    let (_, s1, _) = AT.alloc_tag I.Marking (D.gd g) (D.st g) 1 0UL in
    RA.small2 ();
    assert (~(Th.no_fit gx s1 2));
    same_alloc Header.Black gx s1;
    AP.alloc_col_correct Header.Black gx s1 1;
    AT.alloc_col_tag_eq Header.Black 0UL gx s1 1
#pop-options

/// ---------------------------------------------------------------------------
/// The trace of the loop
/// ---------------------------------------------------------------------------

let cs0 (g: heap) : GTot (P.gstate pstate) =
  { P.major = D.gd g; P.st = D.st g; P.fwd = Promote.empty_forwarding; P.queue = Seq.empty }

/// After the root: A forwarded.
let cs1 (g: heap) : GTot (P.gstate pstate) = P.forward_one PI.mark_tal N2.nur2 (cs0 g) N2.objA

/// After scanning A's field: B forwarded.
let cs2 (g: heap) : GTot (P.gstate pstate) = P.forward_one PI.mark_tal N2.nur2 (cs1 g) N2.objB

/// The collection's context.
#push-options "--z3rlimit 30"
let ctx_ok (g: heap)
  : Lemma (requires V.roomy)
          (ensures L.cpre PI.mark_tal N2.nur2 (D.gd g) (D.st g) /\ L.ctx PI.mark_tal N2.nur2 (D.gd g) /\
                   L.linv PI.mark_tal N2.nur2 (D.gd g) (cs0 g))
  = mpre_ok2 g;
    N2.no_major free_stw (D.gd g);
    PMk.mpre_facts N2.nur2 (D.gd g) (D.st g);
    assert (L.olds PI.mark_tal (D.gd g) (D.gd g))
#pop-options

/// **A is forwarded from the root**, B not yet.
#push-options "--z3rlimit 40"
let step_a (g: heap)
  : Lemma (requires V.roomy)
          (ensures (let c1 = cs1 g in
                    let (_, s1, _) = AT.alloc_tag I.Marking (D.gd g) (D.st g) 1 0UL in
                    c1.P.fwd N2.objA <> 0UL /\ c1.P.fwd N2.objB == 0UL /\ c1.P.st == s1 /\
                    Seq.length c1.P.queue == 1 /\ Seq.index c1.P.queue 0 == N2.objA /\
                    L.linv PI.mark_tal N2.nur2 (D.gd g) c1))
  = ctx_ok g;
    MV.alloc_some_mark g;
    N2.objA_known ();
    N2.mem_objects N2.objA;
    assert_norm (U64.v N2.objA == 8 /\ U64.v N2.objB == 24);
    assert (~(is_infix_in_minor N2.nur2 N2.objA));
    assert (Promote.promoted_tag N2.nur2 N2.objA == 0UL);
    L.forward_one_keeps PI.mark_tal N2.nur2 (D.gd g) (cs0 g) N2.objA
#pop-options

/// **B is forwarded from A's field**, to another block.
#push-options "--z3rlimit 40"
let step_b (g: heap)
  : Lemma (requires V.roomy /\ RA.two_slots)
          (ensures (let c1 = cs1 g in
                    let c2 = cs2 g in
                    c2.P.fwd N2.objB <> 0UL /\ c2.P.fwd N2.objA == c1.P.fwd N2.objA /\
                    c2.P.fwd N2.objB <> c2.P.fwd N2.objA /\
                    L.linv PI.mark_tal N2.nur2 (D.gd g) c2))
  = ctx_ok g;
    step_a g;
    let c1 = cs1 g in
    second_some g c1.P.major;
    N2.objB_known ();
    N2.mem_objects N2.objB;
    assert_norm (U64.v N2.objA == 8 /\ U64.v N2.objB == 24);
    assert (~(is_infix_in_minor N2.nur2 N2.objB));
    assert (Promote.promoted_tag N2.nur2 N2.objB == 0UL);
    L.forward_one_keeps PI.mark_tal N2.nur2 (D.gd g) c1 N2.objB;
    // B's block was not in use when it was allocated; A's was
    L.promote_step PI.mark_tal N2.nur2 (D.gd g) c1.P.major c1.P.st N2.objB;
    assert (L.entry PI.mark_tal N2.nur2 (D.gd g) c1.P.major c1.P.fwd N2.objA)
#pop-options

/// **The loop is that trace**: the root forwards A; scanning A forwards B
/// through its field; nothing else changes the two entries.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let promote_trace (g: heap)
  : Lemma (requires V.roomy /\ RA.two_slots)
          (ensures (let cs = P.promote PI.mark_tal N2.nur2 (D.gd g) (D.st g) N2.roots2 in
                    cs.P.fwd N2.objA == (cs2 g).P.fwd N2.objA /\ cs.P.fwd N2.objB == (cs2 g).P.fwd N2.objB))
  = step_a g;
    step_b g;
    N2.roots_facts ();
    N2.wf_objects ();
    N2.fields ();
    N2.objA_known ();
    minor_scan_wosize_cases N2.nur2 N2.objA;
    N2.objB_offset ();
    let a = PI.mark_tal in
    assert (P.forward_roots a N2.nur2 (cs0 g) N2.roots2 0 == cs1 g);
    assert (Seq.length (minor_objects N2.nur2) == 2);
    assert (P.forward_fields a N2.nur2 (cs1 g) N2.objA 0 1 ==
            P.forward_fields a N2.nur2 (cs2 g) N2.objA 1 1);
    assert (P.scan a N2.nur2 (cs1 g) 0 2 == P.scan a N2.nur2 (cs2 g) 1 1);
    MV.scan_mono a N2.nur2 (cs2 g) 1 1 N2.objA;
    MV.scan_mono a N2.nur2 (cs2 g) 1 1 N2.objB
#pop-options

/// ---------------------------------------------------------------------------
/// What the run shows
/// ---------------------------------------------------------------------------

/// The copies, at the end of promotion.
#push-options "--z3rlimit 40"
let copies (g: heap)
  : Lemma (requires V.roomy /\ RA.two_slots)
          (ensures (let cs = P.promote PI.mark_tal N2.nur2 (D.gd g) (D.st g) N2.roots2 in
                    cs.P.fwd N2.objA <> 0UL /\ cs.P.fwd N2.objB <> 0UL /\ cs.P.fwd N2.objA <> cs.P.fwd N2.objB /\
                    L.copy_of PI.mark_tal N2.nur2 (D.gd g) cs.P.major N2.objA (cs.P.fwd N2.objA) /\
                    L.copy_of PI.mark_tal N2.nur2 (D.gd g) cs.P.major N2.objB (cs.P.fwd N2.objB) /\
                    blocks_fit cs.P.major))
  = ctx_ok g;
    step_a g;
    step_b g;
    promote_trace g;
    PC.promoted PI.mark_tal N2.nur2 (D.gd g) (D.st g) N2.roots2;
    N2.objA_known ();
    N2.objB_known ();
    let cs = P.promote PI.mark_tal N2.nur2 (D.gd g) (D.st g) N2.roots2 in
    assert (~(is_infix_in_minor N2.nur2 N2.objA));
    assert (~(is_infix_in_minor N2.nur2 N2.objB));
    assert (L.entry PI.mark_tal N2.nur2 (D.gd g) cs.P.major cs.P.fwd N2.objA);
    assert (L.entry PI.mark_tal N2.nur2 (D.gd g) cs.P.major cs.P.fwd N2.objB)
#pop-options

/// A copy of a one-field nursery object, in a clean context.
#push-options "--z3rlimit 30"
let copy_one (g0 pm: heap) (m: U64.t) (v: U64.t)
  : Lemma (requires L.copy_of PI.mark_tal N2.nur2 g0 pm m v /\ minor_wosize N2.nur2 m == 1)
          (ensures U64.v v >= 8 /\ U64.v v + 8 <= heap_size /\ U64.v v % 8 == 0 /\
                   U64.v (wosize_of_object (v <: obj_addr) pm) == 1 /\
                   in_use free_stw pm (v <: obj_addr) /\
                   tag_of_object (v <: obj_addr) pm == Promote.promoted_tag N2.nur2 m /\
                   Sh.hdr pm (U64.v v) == minor_read_field N2.nur2 m 0)
  = assert (0 < minor_wosize N2.nur2 m)
#pop-options

/// A's copy's field, rewritten by the pointer update to B's copy.
#push-options "--z3rlimit 40"
let a_field (g: heap)
  : Lemma (requires V.roomy /\ RA.two_slots)
          (ensures (let cs = P.promote PI.mark_tal N2.nur2 (D.gd g) (D.st g) N2.roots2 in
                    let vA = cs.P.fwd N2.objA in
                    U64.v vA >= 8 /\ U64.v vA + 8 <= heap_size /\ U64.v vA % 8 == 0 /\
                    read_word (gm2 g) (U64.uint_to_t (U64.v vA)) == cs.P.fwd N2.objB))
  = copies g;
    N2.fields ();
    N2.objB_offset ();
    zero_addr_above_2048 ();
    assert_norm (U64.v N2.objB == 24);
    N2.room ();
    let cs = P.promote PI.mark_tal N2.nur2 (D.gd g) (D.st g) N2.roots2 in
    let vA : obj_addr = cs.P.fwd N2.objA in
    let pm = cs.P.major in
    free_stw_ok ();
    free_def_ok_elim free_stw;
    // A's copy: scannable (tag 0), its one field the nursery pointer to B
    N2.objA_known ();
    is_no_scan_spec vA pm;
    no_scan_tag_val ();
    copy_one (D.gd g) pm N2.objA (vA <: U64.t);
    assert (U64.v vA + 0 * 8 == U64.v vA);
    assert (U64.v vA + 0 * 8 + 8 <= heap_size /\ (U64.v vA + 0 * 8) % 8 == 0);
    assert (Sh.hdr pm (U64.v vA + 0 * 8) == N2.objB);
    assert (read_word pm (U64.uint_to_t (U64.v vA + 0 * 8)) == N2.objB);
    PUpd.update_walk_field_effect pm (in_use free_stw pm) cs.P.fwd vA 0;
    assert (gm2 g == Promote.update_walk pm (in_use free_stw pm) cs.P.fwd);
    N2.minor_ptrs ();
    assert (U64.uint_to_t (U64.v vA + 0 * 8) == U64.uint_to_t (U64.v vA))
#pop-options

/// **The collection promotes A and B, and rewrites A's pointer to B**:
/// both are forwarded, to two different blocks the collection made, black;
/// the root is rewritten to A's copy, and A's copy's field from the nursery
/// pointer to B's copy.
#push-options "--z3rlimit 40"
let run_mark_minor2_promotes (g: heap)
  : Lemma (requires V.roomy /\ RA.two_slots)
          (ensures (let r = mc2 g in
                    let vA = r.P.rfwd N2.objA in
                    let vB = r.P.rfwd N2.objB in
                    U64.v vA >= 8 /\ U64.v vA < heap_size /\ U64.v vA % 8 == 0 /\
                    U64.v vB >= 8 /\ U64.v vB < heap_size /\ U64.v vB % 8 == 0 /\
                    vA <> vB /\
                    since2 g (vA <: obj_addr) /\ since2 g (vB <: obj_addr) /\
                    is_black (vA <: obj_addr) (gm2 g) /\ is_black (vB <: obj_addr) (gm2 g) /\
                    read_word (gm2 g) (vA <: hp_addr) == vB /\
                    Seq.index r.P.rroots 0 == vA))
  = ctx_ok g;
    copies g;
    a_field g;
    mpre_ok2 g;
    N2.no_major free_stw (D.gd g);
    PC.collect_inv PI.mark_tal N2.nur2 (D.gd g) (D.st g) N2.roots2;
    let cs = P.promote PI.mark_tal N2.nur2 (D.gd g) (D.st g) N2.roots2 in
    let vA : obj_addr = cs.P.fwd N2.objA in
    let vB : obj_addr = cs.P.fwd N2.objB in
    PMk.m_new_black N2.nur2 (D.gd g) (D.st g) N2.roots2 vA;
    PMk.m_new_black N2.nur2 (D.gd g) (D.st g) N2.roots2 vB;
    N2.roots_facts ();
    assert_norm (U64.v N2.objA == 8);
    N2.room ();
    Promote.rewrite_roots_index N2.roots2 cs.P.fwd 0;
    N2.minor_ptrs ()
#pop-options

/// **The theorem on it**: the page `Marking` invariant after the collection,
/// and akhil's account (`C.ccycle_inv`).
let run_mark_minor2_theorems (g: heap)
  : Lemma (requires V.roomy)
          (ensures PMP.mark_inv (gm2 g) (sm2 g) /\
                   GC.Spec.Pages.Cycle.pcycle_account (MC.snapshot (D.h g) (D.rs g) (since2 g)) (gm2 g) (sm2 g) I.Marking)
  = C.ccycle_inv (run_mark_minor2 g)
