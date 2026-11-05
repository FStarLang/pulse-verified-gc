(*
   Pulse GC (Generational) - Top-Level Entry Point Implementation

   Routes allocations by size and implements minor collection
   using Cheney-style BFS (promotes only reachable objects).
*)

module GC.Gen.Impl

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq
module ST = GC.Gen.SweptTail

open GC.Spec.Base
open GC.Spec.Phase
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Impl.MinorHeap
open GC.Gen.Impl.Promote
open GC.Gen.Impl.UpdatePtrs
open GC.Gen.ForwardingArray
open GC.Gen.RefTable
open GC.Gen.Impl.Cheney
open GC.Impl.Heap
open GC.Impl.Stack
module SpecFields = GC.Spec.Fields
module SpecObj = GC.Spec.Object
module Alloc = GC.Impl.Allocator
module Ph = GC.Spec.Phase
module AllocLemmas = GC.Spec.Allocator.Lemmas
module CheneySpec = GC.Gen.Cheney
module CheneySteps = GC.Gen.Cheney.Steps
module ML = FStar.Math.Lemmas
module MajorGC = GC.Impl
module MarkBoundedImpl = GC.Impl.MarkBounded
module MBP = GC.Impl.MarkBoundedPrecondition
module GMP = GC.Gen.MajorPrecondition
module MarkBoundedInv = GC.Spec.MarkBoundedInv
module SpecGCPost = GC.Spec.Correctness
module Mark = GC.Spec.Mark
module SweepInv = GC.Spec.SweepInv
module CheneyCorr = GC.Gen.CheneyCorrectness
module TwoPass = GC.Gen.TwoPassEquiv
module GenInv = GC.Gen.HeapInvariant
module MinorFwd = GC.Gen.MinorCollectForwarding
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module SpecHeapGraph = GC.Spec.HeapGraph
module RBridge = GC.Gen.ReachabilityBridge
module CheneyBFS = GC.Gen.CheneyBFS
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module Cheney = GC.Gen.Impl.Cheney
module SpecHeapModel = GC.Spec.HeapModel
module MRT = GC.Gen.MajorReachabilityTransfer
module GI = GC.Gen.Incremental
module MP = GC.Spec.MarkPhase
module GMM = GC.Gen.MarkPhase.Minor
module MS = GC.Gen.MarkState
module GR = Pulse.Lib.GhostReference
module MSI = GC.Gen.Impl.MarkSlice
module MSl = GC.Gen.MarkSlice
module MStart = GC.Gen.MarkPhase.Start
module Stw = GC.Spec.MarkPhase.Stw
module S = GC.Spec.MarkPhase.Slice

/// Two transports in one: `GC.Gen.MajorPrecondition` carries the pre-minor facts
/// across the minor collection to `darken_precondition`, and
/// `MarkBoundedPrecondition` carries that across root darkening to the
/// obligation `GC.Impl.collect_with_roots` actually demands.  Neither step is
/// the caller's business.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let gen_gc_major_precondition_elim minor major fp roots
  = let result = CheneySpec.cheney_collect_spec minor major fp roots in
    let st : Seq.seq obj_addr = Seq.empty in
    let cap = prepared_cap result.mc_roots in
    GMP.darken_precondition_after_minor minor major fp roots cap;
    MBP.darken_establishes_precondition result.mc_major st result.mc_roots result.mc_fp cap;
    MBP.darken_roots_match_stack result.mc_major st result.mc_roots result.mc_fp cap;
    GMP.post_minor_roots_valid_for_darkening minor major fp roots;
    (let prepared = gen_gc_prepared_state minor major fp roots in
     introduce forall (r: U64.t). Seq.mem r result.mc_roots ==>
       GC.Spec.Base.is_val_addr r /\ U64.v r >= U64.v zero_addr + U64.v mword
     with introduce _ ==> _
     with (Seq.mem_index r result.mc_roots;
           eliminate exists (i: nat{i < Seq.length result.mc_roots}).
             Seq.index result.mc_roots i == r
           with ());
     // A rewritten root is a well-formed pointer, so `resolve_field` on it is
     // `resolve_object`, and `roots_match_stack` says darkening pushed exactly
     // those resolutions.
     introduce forall (e: U64.t).
       Seq.mem e (MCFH.resolve_roots result.mc_major result.mc_roots) ==>
       GC.Spec.Base.is_val_addr e
     with introduce _ ==> _
     with (MCFH.resolve_roots_mem_inv result.mc_major result.mc_roots e;
           eliminate exists (rr: U64.t).
             Seq.mem rr result.mc_roots /\
             SpecHeapGraph.resolve_field result.mc_major rr == e
           with ());
     introduce forall (e: obj_addr).
       Seq.mem (e <: U64.t) (MCFH.resolve_roots result.mc_major result.mc_roots) ==>
       Seq.mem e (snd prepared)
     with introduce _ ==> _
     with (MCFH.resolve_roots_mem_inv result.mc_major result.mc_roots e;
           eliminate exists (rr: U64.t).
             Seq.mem rr result.mc_roots /\
             SpecHeapGraph.resolve_field result.mc_major rr == e
           with ()));
    GC.Gen.CheneyPreservation.cheney_collect_preserves_wfh_from_shape minor major fp roots;
    MBP.darken_preserves_create_graph result.mc_major st result.mc_roots result.mc_fp cap
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let gen_gc_named_root_in_stack minor major fp roots roots_out r
  = let result = CheneySpec.cheney_collect_spec minor major fp roots in
    // `r` is a root, so it is a pointer field, and resolving it is the identity.
    assert (GC.Spec.Base.is_val_addr (r <: U64.t));
    SpecHeapGraph.is_pointer_field_is_obj_addr (r <: U64.t);
    assert (SpecHeapGraph.resolve_field result.mc_major (r <: U64.t) == (r <: U64.t));
    MCFH.resolve_roots_mem result.mc_major roots_out (r <: U64.t)
#pop-options

/// The heap-shape projection is a consequence of the invariant, not an extra
/// promise: `major_heap_shape_gc_postcondition` derives "every object is white
/// or blue" from `no_black_objects` + `no_gray_objects` by colour exhaustiveness.
#push-options "--fuel 0 --ifuel 0"
let gen_gc_heap_shape_post_intro minor_data minor_bump final_major final_fp
  = GenInv.collection_heap_shape_elim
      ({ data = minor_data; bump = minor_bump } <: minor_state) final_major final_fp;
    GMP.major_heap_shape_gc_postcondition final_major final_fp
#pop-options

/// ---------------------------------------------------------------------------
/// Minor Collection — Full Implementation
/// ---------------------------------------------------------------------------

module PromoteSpec = GC.Gen.Promote
open GC.Gen.PromoteUpdate

/// Bridge lemma: fwd_bounded + represents_fwd implies valid_fwd_entries.
/// fwd_bounded gives: fwd(x) != 0 ==> >= mword /\ < heap_size /\ % mword == 0
/// represents_fwd: farr[i] == fwd(i*8)
/// valid_fwd_entries: farr[i] == 0 \/ (>= 8 /\ % 8 == 0 /\ <= heap_size)
let fwd_bounded_implies_valid_fwd_entries
  (farr: Seq.seq U64.t) (fwd: PromoteSpec.forwarding_map)
  : Lemma (requires CheneySpec.fwd_bounded fwd /\
                    represents_fwd farr fwd)
          (ensures valid_fwd_entries farr)
  = let aux (i: nat{i < fwd_array_size}) : Lemma
      (ensures (let addr = Seq.index farr i in
                addr == 0UL \/
                (U64.v addr >= 8 /\ U64.v addr % 8 == 0 /\
                 U64.v addr <= heap_size)))
    = assert (Seq.length farr == fwd_array_size);
      let addr = Seq.index farr i in
      assert (addr == fwd (U64.uint_to_t (i * 8)));
      if addr <> 0UL then begin
        assert (U64.v addr >= U64.v mword);
        assert (U64.v addr < heap_size);
        assert (U64.v addr % U64.v mword == 0)
      end
    in
    Classical.forall_intro aux

/// Derivation: fwd_above_zero_addr + fwd_bounded implies fwd_targets_stable.
/// Since targets > zero_addr >= minor_heap_size and aligned, to_minor_offset is identity
/// and is_minor_pointer is false — so the fwd_targets_stable condition holds.
let derive_fwd_targets_stable (fwd: PromoteSpec.forwarding_map)
  : Lemma (requires CheneySpec.fwd_above_zero_addr fwd /\ CheneySpec.fwd_bounded fwd)
          (ensures fwd_targets_stable fwd)
  =
  reveal_opaque (`%fwd_targets_stable) (fwd_targets_stable fwd);
  // For all x: fwd x <> 0 ==> U64.v(fwd x) > U64.v zero_addr >= minor_heap_size
  // to_minor_offset(fwd x) = fwd x (since target >= minor_heap_size, condition v < minor_heap_size fails)
  // is_minor_pointer(fwd x) = false (requires U64.v < minor_heap_size)
  // Hence ~(is_minor_pointer(...) /\ ...) trivially
  let aux (x: U64.t)
    : Lemma (requires fwd x <> 0UL)
            (ensures (let target = fwd x in
                      let target_as_minor = to_minor_offset target in
                      ~(PromoteSpec.is_minor_pointer target_as_minor /\ fwd target_as_minor <> 0UL)))
    = let target = fwd x in
      zero_addr_above_minor ();
      // From fwd_above_zero_addr: U64.v target > U64.v zero_addr >= minor_heap_size
      assert (U64.v target > U64.v zero_addr);
      assert (U64.v target >= minor_heap_size);
      // From fwd_bounded: target % 8 == 0
      assert (U64.v target % 8 == 0);
      // to_minor_offset_stable: target >= minor_heap_size /\ target % 8 == 0 ==> to_minor_offset target = target
      to_minor_offset_stable_above_minor target;
      assert (to_minor_offset target == target);
      // is_minor_pointer target requires U64.v target < minor_heap_size — contradiction
      assert (~(PromoteSpec.is_minor_pointer target))
  in
  Classical.forall_intro (Classical.move_requires aux)

module CheneyPres = GC.Gen.CheneyPreservation
module CPForwarding = GC.Gen.CheneyPreservation.Forwarding
module CPInj = GC.Gen.CheneyPreservation.Injectivity
module TPC = GC.Gen.TwoPassEquiv.Collect

#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
let minor_collect_with_isomorphism_post (ph: Ph.gc_phase)
  (minor: minor_state) (major: heap) (fp: U64.t) (free: SpecFields.free_def)
  (roots slots: Seq.seq U64.t) (n: nat) (ok: bool)
  (post_major: heap) (post_roots: Seq.seq U64.t)
  : Lemma
    (requires
      GenInv.collection_shape_with ph free minor major fp /\
      ref_table_covers_with free major slots n /\
      post_major == (CheneySpec.cheney_collect_spec_with ph free minor major fp roots).mc_major /\
      post_roots == MCFH.resolve_roots post_major
        (PromoteSpec.rewrite_roots roots
          (CheneySpec.cheney_promote ph minor major fp roots).fwd_map) /\
      MinorFwd.remembered_targets_in_roots major roots slots n /\
      MinorFwd.roots_valid_with free minor major roots /\
      (ok ==> CheneyBFS.cheney_no_oom ph minor major fp roots))
    (ensures
      (ok ==>
       MinorFwd.normal_result_reachable_subgraph_isomorphism_prop ph
         minor major fp free roots post_major post_roots /\
       MinorFwd.normal_result_non_pointer_fields_preserved_prop ph
         minor major fp free roots post_major))
  =
    if ok
    then begin
      MCFH.roots_valid_with_implies_not_free free minor major roots;
      MCFH.major_fields_covered_from_slots minor major free roots slots n;
      MinorFwd.normal_post_reachable_subgraph_isomorphism ph
        minor major fp free roots slots n;
      MinorFwd.normal_post_reachable_subgraph_isomorphism_to_result ph
        minor major fp free roots post_major post_roots;
      MinorFwd.normal_post_non_pointer_fields_preserved ph
        minor major fp free roots slots n;
      MinorFwd.normal_post_non_pointer_fields_preserved_to_result ph
        minor major fp free roots post_major
    end
#pop-options

/// ---------------------------------------------------------------------------
/// minor_collect_with: includes ref_table rewriting for full correctness
/// ---------------------------------------------------------------------------

module CE = GC.Gen.CheneyGeneric

module FA = GC.Gen.ForwardingArray
/// The spec half of the minor collection given what counts as free: the two passes over a
/// Cheney result are the collection's pointer update
/// (`TPC.two_pass_implies_collect_with`), and that collection keeps the shape
/// (`CE.cheney_collect_with_preserves_shape`).
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let minor_collect_with_spec (ph: Ph.gc_phase)
  (free: SpecFields.free_def) (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (farr slots: Seq.seq U64.t) (n: nat)
  : Lemma
    (requires
      GenInv.collection_shape_with ph free minor major fp /\
      Seq.length farr == fwd_array_size /\
      represents_fwd farr (CheneySpec.cheney_promote ph minor major fp roots).fwd_map /\
      ref_table_sound_with free major slots n /\
      ref_table_covers_with free major slots n)
    (ensures
      (let prom = CheneySpec.cheney_promote ph minor major fp roots in
       let res = CheneySpec.cheney_collect_spec_with ph free minor major fp roots in
       rewrite_slots_iter (update_promoted_iter prom.major_final farr prom.fwd_map 0)
         prom.fwd_map slots n 0 == res.mc_major /\
       GenInv.collection_shape_with ph free (minor_reset minor) res.mc_major prom.fp_final /\
       GC.Spec.SweepPhase.Intrinsic.same_heads prom.major_final res.mc_major))
  = let prom = CheneySpec.cheney_promote ph minor major fp roots in
    ST.update_heads prom.major_final free prom.fwd_map;
    GenInv.collection_shape_with_elim ph free minor major fp;
    GenInv.major_shape_with_elim ph free major fp;
    GenInv.minor_heap_shape_elim minor;
    CheneySteps.cheney_promote_fwd_above_zero_addr ph minor major fp roots;
    CheneySteps.cheney_promote_fwd_bounded ph minor major fp roots;
    derive_fwd_targets_stable prom.fwd_map;
    ref_table_sound_with_implies_valid_slot_addrs free major slots n;
    ref_table_covers_with_implies_complete free major prom.fwd_map slots n;
    CheneySteps.cheney_promote_preserves_wfh_part1 ph minor major fp roots;
    CheneySteps.cheney_promote_preserves_wfh_part4 ph minor major fp roots;
    CPForwarding.cheney_promote_fwd_valid_or_infix ph minor major fp roots;
    CPInj.cheney_promote_fwd_normal_injective ph minor major fp roots;
    TPC.two_pass_implies_collect_with ph free minor major fp roots farr slots n;
    CE.cheney_collect_with_preserves_shape ph free minor major fp roots
#pop-options

/// Compose all phases into a single verified call.  The proof is over the
/// caller's definition of free throughout: nothing here reads or assumes
/// anything of a free block.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
fn minor_collect_with (gh: gen_heap_t)
                      (roots: array U64.t) (nroots: SZ.t)
                      (fwd_arr: array U64.t)
                      (queue: larray U64.t FA.queue_size)
                      (slots: array U64.t) (nslots: SZ.t)
                      (#free: erased SpecFields.free_def)
  requires is_gen_heap gh 'd 'b 's 'fp ** gen_phase gh 's 'ph **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           pts_to slots 'sl **
           pure (SZ.v nroots == Seq.length 'rs /\
                 minor_collect_pre_with 'ph free ({ data = 'd; bump = 'b } <: minor_state) 's
                   'fp 'rs 'farr 'sl (SZ.v nslots))
  returns ok: bool
  ensures exists* d2 b2 s2 fp2 rs2 farr2 qv2.
    is_gen_heap gh d2 b2 s2 fp2 ** gen_phase gh s2 'ph **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pts_to slots 'sl **
    pure (minor_collect_post_with 'ph free ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs
            ok d2 b2 s2 fp2 rs2)
{
  unfold is_gen_heap;
  GenInv.collection_shape_with_elim 'ph free ({data = 'd; bump = 'b} <: minor_state) 's 'fp;
  GenInv.major_shape_with_elim 'ph free 's 'fp;
  GenInv.minor_heap_shape_elim ({data = 'd; bump = 'b} <: minor_state);

  // Phase 1: Cheney BFS promotion (forward roots + scan), at the collector's
  // phase: every copy is allocated with the colour the phase gives it.
  unfold gen_phase;
  let ok = cheney_promote_phase gh.minor gh.major gh.fp_ref gh.phase_ref fwd_arr queue roots nroots;
  with ms_prom ph_post. assert (Alloc.is_phase gh.phase_ref ms_prom ph_post);

  // Extract ghost state from promote phase
  with ms_post. assert (is_heap gh.major ms_post);
  with farr_post. assert (pts_to fwd_arr farr_post);
  with fp_post. assert (R.pts_to gh.fp_ref fp_post);

  // Phase 2: Update promoted objects' fields only (efficient path)
  CheneySteps.cheney_promote_fwd_bounded 'ph
    ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs;
  fwd_bounded_implies_valid_fwd_entries farr_post
    (CheneySpec.cheney_promote 'ph ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map;

  update_promoted_objects gh.major fwd_arr
    #(hide (CheneySpec.cheney_promote 'ph ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map);

  // After update: ms_updated == update_promoted_iter ms_post farr_post prom_fwd 0
  with ms_updated. assert (is_heap gh.major ms_updated);
  with farr_post2. assert (pts_to fwd_arr farr_post2);

  // Phase 2b: Rewrite ref_table slots
  ref_table_sound_with_implies_valid_slot_addrs free 's 'sl (SZ.v nslots);
  rewrite_heap_slots gh.major fwd_arr slots nslots
    #(hide (CheneySpec.cheney_promote 'ph ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map);

  // After slot rewrite: heap is the two-pass result
  with ms_final. assert (is_heap gh.major ms_final);

  // Phase 3: Rewrite roots using ghost-tracked forwarding map
  with farr_post3. assert (pts_to fwd_arr farr_post3);
  rewrite_roots_impl roots fwd_arr nroots
    #(hide (CheneySpec.cheney_promote 'ph ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map);
  with rs_out. assert (pts_to roots rs_out);

  // Phase 4: Reset minor heap
  minor_heap_reset gh.minor;

  // The two passes are the collection's update, which keeps the shape and
  // the phase.
  minor_collect_with_spec 'ph free ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs
    farr_post3 'sl (SZ.v nslots);
  // ... and is a reachable-subgraph isomorphism.
  minor_collect_with_isomorphism_post 'ph ({data = 'd; bump = 'b} <: minor_state) 's 'fp free
    'rs 'sl (SZ.v nslots) ok ms_final (MCFH.resolve_roots ms_final rs_out);

  // the phase is the same, its caches derived from the heap the pointer
  // update leaves: the update writes no header
  rewrite (Alloc.is_phase gh.phase_ref ms_prom ph_post)
       as (Alloc.is_phase gh.phase_ref ms_prom 'ph);
  phase_heads gh.phase_ref ms_final;
  fold (gen_phase gh ms_final 'ph);
  fold (is_gen_heap gh _ 0UL _ _);
  ok
}
#pop-options

/// --- The stop-the-world instance ---

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let minor_collect_idle_pre minor_st s fp rs farr sl nslots =
  GenInv.collection_heap_shape_as_free_stw minor_st s fp;
  MCFH.roots_valid_with_stw minor_st s rs
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let minor_collect_idle_post minor_st s fp rs farr sl nslots ok d2 b2 s2 fp2 rs2 =
  GenInv.collection_heap_shape_elim minor_st s fp;
  GenInv.major_heap_shape_elim s fp;
  GenInv.major_heap_shape_walk s fp;
  GenInv.minor_heap_shape_elim minor_st;
  // the collection at `free_stw` is the stop-the-world one ...
  CE.cheney_collect_spec_with_stw minor_st s fp rs;
  // ... which keeps the stop-the-world shape.
  CheneyPres.cheney_collect_preserves_collection_heap_shape minor_st s fp rs
#pop-options

/// ---------------------------------------------------------------------------
/// The minor collection
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let minor_collect_pre (minor: minor_state) (s: heap) (fp: U64.t) (ph: Ph.gc_phase)
    (rs farr sl: Seq.seq U64.t) (n: nat)
  : Lemma (requires GI.phase_shape minor s fp ph /\ minor_slots_ok ph minor s rs farr sl n)
          (ensures minor_collect_pre_with ph (GI.phase_free ph) minor s fp rs farr sl n)
  = GI.phase_shape_collection minor s fp ph
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let minor_collect_keeps_shape (minor: minor_state) (s: heap) (fp: U64.t) (ph: Ph.gc_phase)
    (rs: Seq.seq U64.t) (ok: bool)
    (d2: minor_heap) (b2: U64.t) (s2: heap) (fp2: U64.t) (rs2: Seq.seq U64.t)
  : Lemma (requires GI.phase_shape minor s fp ph /\
                    MCFH.roots_valid_for_minor_collection minor s rs /\
                    (Ph.Marking? ph ==> MP.held_reached s (GMM.roots_held s rs)) /\
                    minor_collect_post_with ph (GI.phase_free ph) minor s fp rs ok d2 b2 s2 fp2 rs2)
          (ensures GI.phase_shape ({ data = d2; bump = b2 } <: minor_state) s2 fp2 ph /\
                   (Ph.Marking? ph ==> MP.held_reached s2 (GMM.roots_held s2 rs2)))
  = match ph with
    | Ph.Idle ->
        GI.phase_free_idle ();
        CE.cheney_collect_spec_with_stw minor s fp rs;
        GI.phase_shape_idle minor s fp;
        CheneyPres.cheney_collect_preserves_collection_heap_shape minor s fp rs;
        GI.phase_shape_idle ({ data = d2; bump = b2 } <: minor_state) s2 fp2
    | Ph.Marking ->
        GI.phase_free_marking ();
        GI.minor_keeps_marking_shape minor s fp rs
    | Ph.Sweeping c ->
        GI.phase_free_sweeping c;
        GI.minor_keeps_phase_shape minor s fp c rs
#pop-options

/// ---------------------------------------------------------------------------
/// The persistent mark state across the entry points
/// ---------------------------------------------------------------------------

/// Outside marking the mark state is the empty stack with the flag down,
/// whatever the heap and the phase.
ghost
fn mark_state_off (gh: gen_heap_t) (s s': heap_state) (ph ph': Ph.gc_phase)
  requires mark_state gh s ph ** pure (~(Ph.Marking? ph) /\ ~(Ph.Marking? ph'))
  ensures mark_state gh s' ph'
{
  unfold mark_state;
  with st ov c f r. _;
  MS.mark_cache_off s s' ph ph' st ov (MSI.pos c f r);
  fold (mark_state gh s' ph')
}

/// A minor collection keeps the mark stack a cache of the grey objects:
/// while marking it keeps the grey objects (`MS.mark_cache_minor`).
let mark_cache_minor_at (minor: minor_state) (s: heap) (fp: U64.t) (ph: Ph.gc_phase)
    (rs: Seq.seq U64.t) (s2: heap) (st: Seq.seq obj_addr) (ov: bool) (p: MS.mark_pos)
  : Lemma (requires GI.phase_shape minor s fp ph /\ MS.mark_cache_ok s ph st ov p /\
                    s2 == (CheneySpec.cheney_collect_spec_with ph (GI.phase_free ph) minor s fp rs).mc_major)
          (ensures MS.mark_cache_ok s2 ph st ov p)
  = if Ph.Marking? ph then begin
      GI.phase_free_marking ();
      GI.phase_shape_collection minor s fp ph;
      MS.mark_cache_minor minor s fp rs st ov p
    end else
      MS.mark_cache_off s s2 ph ph st ov p

ghost
fn mark_state_minor (gh: gen_heap_t) (minor: minor_state) (s: heap_state) (fp: U64.t)
    (ph: Ph.gc_phase) (rs: Seq.seq U64.t) (s2: heap_state)
  requires mark_state gh s ph **
           pure (GI.phase_shape minor s fp ph /\
                 s2 == (CheneySpec.cheney_collect_spec_with ph (GI.phase_free ph) minor s fp rs).mc_major)
  ensures mark_state gh s2 ph
{
  unfold mark_state;
  with st ov c f r. _;
  mark_cache_minor_at minor s fp ph rs s2 st ov (MSI.pos c f r);
  fold (mark_state gh s2 ph)
}

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
fn minor_collect (gh: gen_heap_t)
                 (roots: array U64.t) (nroots: SZ.t)
                 (fwd_arr: array U64.t)
                 (queue: larray U64.t FA.queue_size)
                 (slots: array U64.t) (nslots: SZ.t)
  requires gc_state gh 'd 'b 's 'fp 'ph **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           pts_to slots 'sl **
           pure (SZ.v nroots == Seq.length 'rs /\
                 minor_slots_ok 'ph ({ data = 'd; bump = 'b } <: minor_state) 's
                   'rs 'farr 'sl (SZ.v nslots))
  returns ok: bool
  ensures exists* d2 b2 s2 fp2 rs2 farr2 qv2.
    gc_state gh d2 b2 s2 fp2 'ph **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pts_to slots 'sl **
    pure (minor_collect_post_with 'ph (GI.phase_free 'ph) ({ data = 'd; bump = 'b } <: minor_state)
            's 'fp 'rs ok d2 b2 s2 fp2 rs2 /\
          (Ph.Marking? 'ph ==> MP.held_reached s2 (GMM.roots_held s2 rs2)))
{
  unfold gc_state;
  minor_collect_pre ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'ph 'rs 'farr 'sl (SZ.v nslots);
  let ok = minor_collect_with gh roots nroots fwd_arr queue slots nslots
             #(hide (GI.phase_free 'ph));
  with d2 b2 s2 fp2. assert (is_gen_heap gh d2 b2 s2 fp2);
  with rs2. assert (pts_to roots rs2);
  minor_collect_keeps_shape ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'ph 'rs ok
    d2 b2 s2 fp2 rs2;
  mark_state_minor gh ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'ph 'rs s2;
  fold (gc_state gh d2 b2 s2 fp2 'ph);
  ok
}
#pop-options

/// ---------------------------------------------------------------------------
/// The major collector: starting a cycle
/// ---------------------------------------------------------------------------

module FS = GC.Spec.FusedSweep
module SPI = GC.Spec.SweepPhase.Intrinsic
module SL = GC.Spec.SweepPhase.Slice
module FSC = GC.Impl.FusedSweepCoalesce

module MarkCorr = GC.Spec.MarkBoundedCorrectness

/// The phase record at the start of the sweep.
inline_for_extraction noextract
let start_record : Alloc.phase_state =
  { Alloc.ps_kind = 1UL; Alloc.ps_cursor = zero_addr;
    Alloc.ps_swept_tail = 0UL; Alloc.ps_last_fragment = 0UL }

/// It holds the start of the sweep phase, on any heap: the cursor at the
/// first block, no cell or fragment behind it.
let start_record_rel (g: heap)
  : Lemma (Alloc.phase_rel g start_record (Ph.Sweeping zero_addr))
  = GC.Spec.Walk.reaches_refl g zero_addr;
    SPI.state_at_start g

/// The empty nursery is the one `minor_reset` gives.
let nursery_empty_reset (d: minor_heap) (b: U64.t)
  : Lemma (requires nursery_empty d b)
          (ensures minor_reset ({ data = d; bump = b } <: minor_state) ==
                   ({ data = d; bump = b } <: minor_state))
  = U64.v_inj b 0UL

/// The phase record while marking.
inline_for_extraction noextract
let marking_record : Alloc.phase_state =
  { Alloc.ps_kind = 2UL; Alloc.ps_cursor = 0UL;
    Alloc.ps_swept_tail = 0UL; Alloc.ps_last_fragment = 0UL }

/// While marking the phase record holds `Marking` whatever the heap.
ghost
fn phase_marking_any (phase: R.ref Alloc.phase_state) (g': heap)
  requires Alloc.is_phase phase 'g 'ph ** pure (Ph.Marking? 'ph)
  ensures Alloc.is_phase phase g' 'ph
{
  unfold Alloc.is_phase;
  fold (Alloc.is_phase phase g' 'ph)
}

/// What the idle state says of the heap root darkening starts from.
let start_facts (minor: minor_state) (s: heap) (fp: U64.t)
  : Lemma (requires GI.phase_shape minor s fp Ph.Idle)
          (ensures SpecFields.well_formed_heap s /\ SweepInv.no_gray_objects s /\
                   GenInv.collection_heap_shape minor s fp)
  = GI.phase_shape_idle minor s fp;
    GenInv.collection_heap_shape_elim minor s fp;
    GenInv.major_heap_shape_elim s fp

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
fn start_cycle (gh: gen_heap_t) (roots: array U64.t) (nroots: SZ.t)
  requires gc_state gh 'd 'b 's 'fp Ph.Idle **
           pts_to roots 'rs **
           pure (SZ.v nroots == Seq.length 'rs /\
                 nursery_empty 'd 'b /\
                 start_cycle_pre 's 'rs)
  ensures exists* s2.
    gc_state gh 'd 'b s2 'fp Ph.Marking **
    pts_to roots 'rs **
    pure (start_cycle_post 's 'rs s2)
{
  unfold gc_state;
  start_facts ({ data = 'd; bump = 'b } <: minor_state) 's 'fp;
  nursery_empty_reset 'd 'b;
  unfold is_gen_heap;
  unfold mark_state;
  with st ov c f r. _;
  MS.mark_cache_not_marking 's Ph.Idle st ov (MSI.pos c f r);
  stack_facts gh.mark_stack;
  Seq.lemma_empty st;
  // Root darkening onto the persistent stack, the flag raised if it ends
  // full (a root may have been dropped).
  MSl.mark_cache_start 's 'rs (stack_capacity gh.mark_stack);
  MarkBoundedImpl.darken_roots_bounded gh.major gh.mark_stack roots nroots (stack_capacity gh.mark_stack);
  with s2 st2 rs2. assert (is_heap gh.major s2 ** is_gray_stack gh.mark_stack st2 ** pts_to roots rs2);
  let full = is_full gh.mark_stack;
  R.op_Colon_Equals gh.mark_overflow full;
  R.op_Colon_Equals gh.mark_field 1UL;
  MS.mark_cache_marking s2 st2 full (MSI.pos 0UL 1UL 0UL);
  // The darkened heap is the collector's state while marking.
  MSl.darken_roots_heap 's Seq.empty Seq.empty 'rs (stack_capacity gh.mark_stack) (prepared_cap 'rs);
  MStart.mark_start_shape ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs;
  fold (mark_state gh s2 Ph.Marking);
  // Marking starts.
  unfold gen_phase;
  unfold Alloc.is_phase;
  R.op_Colon_Equals gh.phase_ref marking_record;
  fold (Alloc.is_phase gh.phase_ref s2 Ph.Marking);
  fold (gen_phase gh s2 Ph.Marking);
  fold (is_gen_heap gh 'd 'b s2 'fp);
  fold (gc_state gh 'd 'b s2 'fp Ph.Marking);
}
#pop-options

/// ---------------------------------------------------------------------------
/// The major collector: slices
/// ---------------------------------------------------------------------------

/// The phase record a slice leaves.
inline_for_extraction noextract
let slice_record (fin: bool) (c t f: U64.t) : Alloc.phase_state =
  { Alloc.ps_kind = (if fin then 0UL else 1UL);
    Alloc.ps_cursor = c; Alloc.ps_swept_tail = t; Alloc.ps_last_fragment = f }

/// The slice in the spec, from the implementation's, and the record it
/// leaves holds the phase it leaves.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let slice_result (minor: minor_state) (g: heap) (fp: U64.t) (v: Alloc.phase_state)
    (budget: U64.t) (g': heap) (c' t' f' fp': U64.t)
  : Lemma (requires v.Alloc.ps_kind = 1UL /\
                    Alloc.phase_rel g v (Alloc.phase_of v) /\
                    GI.phase_shape minor g fp (Alloc.phase_of v) /\
                    FSC.slice_matches g fp v.Alloc.ps_cursor v.Alloc.ps_swept_tail
                      v.Alloc.ps_last_fragment budget g' (c', t', f', fp'))
          (ensures (let fin = not (U64.v c' + 8 < heap_size) in
                    let v' = slice_record fin c' t' f' in
                    U64.v c' <= heap_size /\
                    (g', fp', Alloc.phase_of v') ==
                      GI.major_slice_spec g fp (Alloc.phase_of v) (U64.v budget) /\
                    GI.phase_shape minor g' fp' (Alloc.phase_of v') /\
                    Alloc.phase_rel g' v' (Alloc.phase_of v')))
  = let c = v.Alloc.ps_cursor in
    GI.phase_slice_shape minor g fp (Alloc.phase_of v) (U64.v budget);
    GI.phase_shape_sweeping minor g fp c;
    SL.sweep_slice_phase g fp c (U64.v budget);
    let (g1, fp1, st1) = SL.sweep_slice g fp (SPI.state_at g c) (U64.v budget) in
    SPI.sweep_inv_incremental_elim g1 fp1 st1.FS.cursor
#pop-options

let bounds () : Lemma (heap_size == GC.Spec.Base.heap_size /\ heap_size < pow2 57 /\
                       U64.v mword == 8 /\ pow2 57 * 2 <= pow2 64)
  = assert_norm (pow2 57 * 2 <= pow2 64)

/// What the slice needs, from the record and the sweep phase.
let slice_ready (minor: minor_state) (g: heap) (fp: U64.t) (v: Alloc.phase_state)
  : Lemma (requires v.Alloc.ps_kind = 1UL /\
                    Alloc.phase_rel g v (Alloc.phase_of v) /\
                    GI.phase_shape minor g fp (Alloc.phase_of v))
          (ensures FSC.slice_pre g fp v.Alloc.ps_cursor v.Alloc.ps_swept_tail v.Alloc.ps_last_fragment)
  = GI.phase_shape_sweeping minor g fp v.Alloc.ps_cursor

/// What the mark slice needs of the marking state.
let marking_heap_ok (minor: minor_state) (g: heap) (fp: U64.t)
  : Lemma (requires GI.phase_shape minor g fp Ph.Marking)
          (ensures MSI.heap_ok g)
  = GI.phase_shape_marking minor g fp;
    GenInv.collection_shape_with_elim Ph.Marking SpecFields.free_stw minor g fp;
    GenInv.major_shape_with_elim Ph.Marking SpecFields.free_stw g fp

/// A mark slice at `Marking`.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
fn mark_slice_at (gh: gen_heap_t) (budget: U64.t)
  requires gc_state gh 'd 'b 's 'fp Ph.Marking
  returns idle: bool
  ensures exists* s2 fp2 ph2.
    gc_state gh 'd 'b s2 fp2 ph2 **
    pure (GI.mark_slice_post 's 'fp (U64.v budget) s2 fp2 ph2 /\ idle == Ph.Idle? ph2)
{
  unfold gc_state;
  marking_heap_ok ({ data = 'd; bump = 'b } <: minor_state) 's 'fp;
  unfold is_gen_heap;
  unfold mark_state;
  with st ov c f r. _;
  MS.mark_cache_marking 's st ov (MSI.pos c f r);
  let fin = MSI.mark_slice gh.major gh.mark_stack gh.mark_overflow gh.mark_cur gh.mark_field
              gh.mark_rescan budget;
  with s2 st2 ov2 c2 f2 r2. assert (is_heap gh.major s2 ** is_gray_stack gh.mark_stack st2 **
    R.pts_to gh.mark_overflow ov2 ** R.pts_to gh.mark_cur c2 ** R.pts_to gh.mark_field f2 **
    R.pts_to gh.mark_rescan r2);
  GI.mark_steps_shape ({ data = 'd; bump = 'b } <: minor_state) 's s2 'fp;
  if fin {
    // Nothing is grey: the sweep starts.
    GI.marking_done_shape ({ data = 'd; bump = 'b } <: minor_state) s2 'fp;
    MS.mark_cache_not_marking s2 (Ph.Sweeping zero_addr) st2 ov2 (MSI.pos c2 f2 r2);
    fold (mark_state gh s2 (Ph.Sweeping zero_addr));
    unfold gen_phase;
    unfold Alloc.is_phase;
    R.op_Colon_Equals gh.phase_ref start_record;
    start_record_rel s2;
    fold (Alloc.is_phase gh.phase_ref s2 (Ph.Sweeping zero_addr));
    fold (gen_phase gh s2 (Ph.Sweeping zero_addr));
    fold (is_gen_heap gh 'd 'b s2 'fp);
    fold (gc_state gh 'd 'b s2 'fp (Ph.Sweeping zero_addr));
    false
  } else {
    MS.mark_cache_marking s2 st2 ov2 (MSI.pos c2 f2 r2);
    fold (mark_state gh s2 Ph.Marking);
    unfold gen_phase;
    phase_marking_any gh.phase_ref s2;
    fold (gen_phase gh s2 Ph.Marking);
    fold (is_gen_heap gh 'd 'b s2 'fp);
    fold (gc_state gh 'd 'b s2 'fp Ph.Marking);
    false
  }
}
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
fn major_slice (gh: gen_heap_t) (budget: U64.t)
  requires gc_state gh 'd 'b 's 'fp 'ph
  returns idle: bool
  ensures exists* s2 fp2 ph2.
    gc_state gh 'd 'b s2 fp2 ph2 **
    pure (GI.major_slice_post 's 'fp 'ph (U64.v budget) s2 fp2 ph2 /\
          idle == Ph.Idle? ph2)
{
  unfold gc_state;
  unfold is_gen_heap;
  unfold gen_phase;
  unfold Alloc.is_phase;
  let v = R.op_Bang gh.phase_ref;
  if (U64.eq v.Alloc.ps_kind 0UL) {
    // Idle: nothing to do.
    fold (Alloc.is_phase gh.phase_ref 's 'ph);
    fold (gen_phase gh 's 'ph);
    fold (is_gen_heap gh 'd 'b 's 'fp);
    fold (gc_state gh 'd 'b 's 'fp 'ph);
    true
  } else if (not (U64.eq v.Alloc.ps_kind 1UL)) {
    // Marking: a mark slice.
    fold (Alloc.is_phase gh.phase_ref 's 'ph);
    fold (gen_phase gh 's 'ph);
    fold (is_gen_heap gh 'd 'b 's 'fp);
    fold (gc_state gh 'd 'b 's 'fp 'ph);
    rewrite (gc_state gh 'd 'b 's 'fp 'ph) as (gc_state gh 'd 'b 's 'fp Ph.Marking);
    mark_slice_at gh budget
  } else {
    // Sweeping: a slice of the sweep.
    slice_ready ({ data = 'd; bump = 'b } <: minor_state) 's 'fp v;
    let fp = R.op_Bang gh.fp_ref;
    let r = FSC.sweep_slice_impl gh.major v.Alloc.ps_cursor v.Alloc.ps_swept_tail
              v.Alloc.ps_last_fragment fp budget;
    with s2. assert (is_heap gh.major s2);
    bounds ();
    match r {
      (c', t', f', fp') -> {
        slice_result ({ data = 'd; bump = 'b } <: minor_state) 's 'fp v budget s2 c' t' f' fp';
        let fin = not (U64.lt (U64.add c' mword) heap_size_u64);
        R.op_Colon_Equals gh.phase_ref (slice_record fin c' t' f');
        R.op_Colon_Equals gh.fp_ref fp';
        fold (Alloc.is_phase gh.phase_ref s2 (Alloc.phase_of (slice_record fin c' t' f')));
        fold (gen_phase gh s2 (Alloc.phase_of (slice_record fin c' t' f')));
        fold (is_gen_heap gh 'd 'b s2 fp');
        mark_state_off gh 's s2 'ph (Alloc.phase_of (slice_record fin c' t' f'));
        fold (gc_state gh 'd 'b s2 fp' (Alloc.phase_of (slice_record fin c' t' f')));
        fin
      }
    }
  }
}
#pop-options

/// A major slice keeps what the rest of the sweep leaves
/// (`SL.phase_rest`).
#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let major_slice_keeps_rest (minor: minor_state) (g: heap) (fp: U64.t) (c: U64.t)
    (budget: nat) (g': heap) (fp': U64.t) (ph': Ph.gc_phase)
  : Lemma (requires GI.phase_shape minor g fp (Ph.Sweeping c) /\
                    (g', fp', ph') == GI.major_slice_spec g fp (Ph.Sweeping c) budget)
          (ensures SL.phase_rest g' fp' ph' == SL.phase_rest g fp (Ph.Sweeping c) /\
                   (budget > GC.Spec.Base.heap_words ==> ph' == Ph.Idle))
  = GI.phase_shape_sweeping minor g fp c;
    SL.phase_rest_slice g fp (Ph.Sweeping c) budget;
    if budget > GC.Spec.Base.heap_words then
      GI.phase_slice_finishes minor g fp (Ph.Sweeping c) budget
#pop-options

/// ---------------------------------------------------------------------------
/// Full generational GC (minor collection + major collection)
/// ---------------------------------------------------------------------------

/// The unbounded budget is more words than the heap has.
let unbounded_budget () : Lemma (U64.v 0xFFFFFFFFFFFFFFFFUL > GC.Spec.Base.heap_words /\
                                 GI.unbounded (U64.v 0xFFFFFFFFFFFFFFFFUL))
  = assert_norm (pow2 57 < U64.v 0xFFFFFFFFFFFFFFFFUL);
    assert_norm (U64.v 0xFFFFFFFFFFFFFFFFUL == pow2 64 - 1)

/// Where a full collection's cycle is, from the darkened heap `g0` with the
/// root objects `droots`: marking, with the stop-the-world strengthening of
/// the marking invariant; or past marking, with what is left of the cycle
/// (`SL.phase_rest`) what the stop-the-world sweep of a marked heap of `g0`
/// leaves.
let full_rest (g0: heap) (droots: Seq.seq obj_addr) (fp0: U64.t)
    (s: heap) (fp: U64.t) (ph: Ph.gc_phase) : prop =
  (Ph.Marking? ph ==> fp == fp0 /\ Stw.marking_inv_stw g0 s droots) /\
  (~(Ph.Marking? ph) ==>
     (exists (s_mark: heap). SpecGCPost.mark_post g0 s_mark droots fp0 /\
                        SL.phase_rest s fp ph == FS.fused_sweep_coalesce s_mark fp0))

/// How far the cycle has to go: mark, then sweep.
let rank (ph: Ph.gc_phase) : nat =
  match ph with
  | Ph.Idle -> 0
  | Ph.Sweeping _ -> 1
  | Ph.Marking -> 2

/// **An unbounded slice of a full collection**: marking finishes with the
/// marked heap (`Stw.marking_inv_stw_done`), whose sweep is what is left; a
/// sweep slice finishes the sweep.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let full_slice_step (minor: minor_state) (g0: heap) (droots: Seq.seq obj_addr) (fp0: U64.t)
    (s: heap) (fp: U64.t) (ph: Ph.gc_phase) (s': heap) (fp': U64.t) (ph': Ph.gc_phase)
  : Lemma (requires GI.phase_shape minor s fp ph /\ full_rest g0 droots fp0 s fp ph /\
                    Stw.stw_start g0 droots /\ GC.Spec.FreeList.fp_in_heap fp0 g0 /\
                    ~(Ph.Idle? ph) /\
                    GI.major_slice_post s fp ph (U64.v 0xFFFFFFFFFFFFFFFFUL) s' fp' ph')
          (ensures full_rest g0 droots fp0 s' fp' ph' /\ rank ph' < rank ph)
  = unbounded_budget ();
    match ph with
    | Ph.Marking ->
        Stw.marking_inv_stw_steps g0 s s' droots;
        Stw.marking_inv_stw_done g0 s' droots fp0;
        SL.phase_rest_start s' fp0
    | Ph.Sweeping c ->
        major_slice_keeps_rest minor s fp c (U64.v 0xFFFFFFFFFFFFFFFFUL) s' fp' ph'
#pop-options

/// The start of a full collection's cycle: from the major collector's entry
/// condition at the darkened heap.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let full_start (g0: heap) (droots: Seq.seq obj_addr) (fp0: U64.t) (cap: nat)
  : Lemma (requires MajorGC.gc_precondition_with_roots g0 droots droots fp0 cap)
          (ensures Stw.stw_start g0 droots /\ GC.Spec.FreeList.fp_in_heap fp0 g0 /\
                   full_rest g0 droots fp0 g0 fp0 Ph.Marking)
  = MarkBoundedInv.bounded_mark_inv_elim_wfh g0 droots cap;
    MarkBoundedInv.bounded_mark_inv_elim_objects g0 droots cap;
    MarkBoundedInv.bounded_mark_inv_elim_density g0 droots cap;
    Stw.marking_inv_stw_start g0 droots
#pop-options


/// What the major half of a full collection leaves, from the heap the minor
/// collection left: the cycle started from it marked the darkened heap
/// (`mark_post`), and the slices until idle left what the stop-the-world
/// sweep of the marked heap leaves.  These are `MajorGC.collect`'s theorems at
/// that heap (`SpecGCPost.gc_result_fused`), chained with the minor
/// collection's isomorphism into a single isomorphism from the heap we were
/// handed to the heap we return (`MRT.end_to_end_isomorphism_intro`), so that
/// no caller has to do it.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let full_gc_major_post
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  (s_mark s_fin: heap) (fp_fin: U64.t)
  : Lemma
    (requires
      (let result = CheneySpec.cheney_collect_spec minor major fp roots in
       GenInv.collection_heap_shape minor major fp /\
       MinorFwd.roots_valid_for_minor_collection minor major roots /\
       CheneyBFS.cheney_no_oom Idle minor major fp roots /\
       MinorFwd.normal_result_reachable_subgraph_isomorphism_prop Idle
         minor major fp SpecFields.free_stw roots result.mc_major
         (MCFH.resolve_roots result.mc_major result.mc_roots) /\
       MinorFwd.normal_result_non_pointer_fields_preserved_prop Idle
         minor major fp SpecFields.free_stw roots result.mc_major /\
       SpecGCPost.mark_post (gen_gc_prepared_major minor major fp roots) s_mark
         (gen_gc_prepared_roots minor major fp roots) result.mc_fp /\
       (s_fin, fp_fin) == FS.fused_sweep_coalesce s_mark result.mc_fp))
    (ensures
      (let result = CheneySpec.cheney_collect_spec minor major fp roots in
       gen_gc_roots_post minor major fp roots result.mc_roots true /\
       gen_gc_reachable_subgraph_isomorphism_post
         minor major fp roots true s_fin result.mc_roots /\
       gen_gc_unreachable_final_blue_post minor major fp roots true s_fin))
  = let result = CheneySpec.cheney_collect_spec minor major fp roots in
    let prepared = gen_gc_prepared_state minor major fp roots in
    let prepared_major = fst prepared in
    let prepared_st = snd prepared in
    gen_gc_major_precondition_elim minor major fp roots;
    SpecGCPost.gc_result_fused prepared_major s_mark prepared_st result.mc_fp;
    SpecGCPost.gc_postcondition_elim s_fin;
    Mark.create_graph_wf_from_heap s_fin;
    assert (MRT.major_transfer_hyp prepared_major s_fin prepared_st);
    MRT.end_to_end_isomorphism_intro minor major fp roots
      result.mc_major (MCFH.resolve_roots result.mc_major result.mc_roots)
      prepared_major prepared_st s_fin
#pop-options

/// At the end, the cycle is the stop-the-world collection of a marked heap of
/// the darkened one, so `full_gc_major_post` applies.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let full_gc_end
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t) (s_fin: heap) (fp_fin: U64.t)
  : Lemma
    (requires
      (let result = CheneySpec.cheney_collect_spec minor major fp roots in
       GenInv.collection_heap_shape minor major fp /\
       MinorFwd.roots_valid_for_minor_collection minor major roots /\
       CheneyBFS.cheney_no_oom Idle minor major fp roots /\
       MinorFwd.normal_result_reachable_subgraph_isomorphism_prop Idle
         minor major fp SpecFields.free_stw roots result.mc_major
         (MCFH.resolve_roots result.mc_major result.mc_roots) /\
       MinorFwd.normal_result_non_pointer_fields_preserved_prop Idle
         minor major fp SpecFields.free_stw roots result.mc_major /\
       full_rest (gen_gc_prepared_major minor major fp roots) (gen_gc_prepared_roots minor major fp roots)
         result.mc_fp s_fin fp_fin Ph.Idle))
    (ensures
      (let result = CheneySpec.cheney_collect_spec minor major fp roots in
       gen_gc_roots_post minor major fp roots result.mc_roots true /\
       gen_gc_reachable_subgraph_isomorphism_post
         minor major fp roots true s_fin result.mc_roots /\
       gen_gc_unreachable_final_blue_post minor major fp roots true s_fin))
  = let result = CheneySpec.cheney_collect_spec minor major fp roots in
    let g0 = gen_gc_prepared_major minor major fp roots in
    let droots = gen_gc_prepared_roots minor major fp roots in
    eliminate exists (s_mark: heap). SpecGCPost.mark_post g0 s_mark droots result.mc_fp /\
                                   SL.phase_rest s_fin fp_fin Ph.Idle ==
                                     FS.fused_sweep_coalesce s_mark result.mc_fp
    with full_gc_major_post minor major fp roots s_mark s_fin fp_fin
#pop-options

/// The cycle's start, from the minor collection's result: the darkened heap
/// is `gen_gc_prepared_major`, its root objects `gen_gc_prepared_roots`.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let full_cycle_start (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
    (s_dark: heap)
  : Lemma
    (requires
      (let result = CheneySpec.cheney_collect_spec minor major fp roots in
       GenInv.collection_heap_shape minor major fp /\
       MinorFwd.roots_valid_for_minor_collection minor major roots /\
       CheneyBFS.cheney_no_oom Idle minor major fp roots /\
       start_cycle_post result.mc_major result.mc_roots s_dark))
    (ensures
      (let result = CheneySpec.cheney_collect_spec minor major fp roots in
       let g0 = gen_gc_prepared_major minor major fp roots in
       let droots = gen_gc_prepared_roots minor major fp roots in
       s_dark == g0 /\
       Stw.stw_start g0 droots /\ GC.Spec.FreeList.fp_in_heap result.mc_fp g0 /\
       full_rest g0 droots result.mc_fp s_dark result.mc_fp Ph.Marking))
  = let result = CheneySpec.cheney_collect_spec minor major fp roots in
    gen_gc_major_precondition_elim minor major fp roots;
    full_start (gen_gc_prepared_major minor major fp roots) (gen_gc_prepared_roots minor major fp roots)
      result.mc_fp (prepared_cap result.mc_roots)
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
fn full_gc (gh: gen_heap_t)
           (roots: array U64.t) (nroots: SZ.t)
           (fwd_arr: array U64.t)
           (queue: larray U64.t FA.queue_size)
           (slots: array U64.t) (nslots: SZ.t)
  requires gc_state gh 'd 'b 's 'fp Ph.Idle **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           pts_to slots 'sl **
           pure (
               SZ.v nroots == Seq.length 'rs /\
               Seq.length 'farr == fwd_array_size /\
               (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\
               ref_table_sound 's 'sl (SZ.v nslots) /\
               ref_table_covers_minor_ptrs 's 'sl (SZ.v nslots) /\
               MinorFwd.remembered_targets_in_roots 's 'rs 'sl (SZ.v nslots) /\
               MinorFwd.roots_valid_for_minor_collection
                 ({ data = 'd; bump = 'b } <: minor_state) 's 'rs)
  returns ok: bool
  ensures exists* d2 b2 s2 fp2 rs2 farr2 qv2.
    gc_state gh d2 b2 s2 fp2 Ph.Idle **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pts_to slots 'sl **
    pure (
      let minor_st : minor_state = { data = 'd; bump = 'b } in
      let minor_st_out : minor_state = { data = d2; bump = b2 } in
      (not ok ==> CheneyBFS.cheney_oom Idle minor_st 's 'fp 'rs) /\
      gen_gc_roots_post minor_st 's 'fp 'rs rs2 ok /\
      minor_st_out == minor_reset minor_st /\
      GenInv.collection_heap_shape minor_st_out s2 fp2 /\
      gen_gc_reachable_subgraph_isomorphism_post
        minor_st 's 'fp 'rs ok s2 rs2 /\
      gen_gc_unreachable_final_blue_post
        minor_st 's 'fp 'rs ok s2)
{
  unfold gc_state;
  GI.phase_shape_idle ({data = 'd; bump = 'b} <: minor_state) 's 'fp;
  // The minor collection, idle: its arguments for `free_stw`.
  minor_collect_idle_pre ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs 'farr 'sl
    (SZ.v nslots);
  GI.phase_free_idle ();
  fold (gc_state gh 'd 'b 's 'fp Ph.Idle);
  let ok = minor_collect gh roots nroots fwd_arr queue slots nslots;
  with d_mid b_mid s_mid fp_mid. assert (gc_state gh d_mid b_mid s_mid fp_mid Ph.Idle);
  with rs_mid. assert (pts_to roots rs_mid);
  minor_collect_idle_post ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs 'farr 'sl
    (SZ.v nslots) ok d_mid b_mid s_mid fp_mid rs_mid;
  PromoteSpec.rewrite_roots_length 'rs
    (CheneySpec.cheney_promote Idle ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map;
  // The major phase, but only if the minor collection succeeded.
  //
  // On the out-of-memory path some live nursery objects were never promoted, so
  // the rewritten root set still contains nursery addresses and there is nothing
  // sensible for mark-and-sweep to do with it.  `minor_collect` reports
  // that through `ok`, which also witnesses `cheney_no_oom` -- the fact the
  // major phase's entry condition is derived from.  This is why the caller
  // does not have to establish `cheney_no_oom` itself.
  if ok {
    // The rewritten roots are darkenable major objects.
    GMP.post_minor_roots_valid_for_darkening
      ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs;
    start_cycle gh roots nroots;
    with s_dark. assert (gc_state gh d_mid b_mid s_dark fp_mid Ph.Marking);
    let g0 = Ghost.hide (gen_gc_prepared_major ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs);
    let droots = Ghost.hide (gen_gc_prepared_roots ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs);
    full_cycle_start ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs s_dark;
    // Slices with an unbounded budget until idle: one marks, one sweeps.
    let mut busy = true;
    let gr = GR.alloc #nat 2;
    while (!busy)
      invariant exists* s_i fp_i ph_i vb (n: nat).
        gc_state gh d_mid b_mid s_i fp_i ph_i **
        R.pts_to busy vb ** GR.pts_to gr n **
        pure (vb == not (Ph.Idle? ph_i) /\ n == rank ph_i /\
              full_rest g0 droots fp_mid s_i fp_i ph_i)
      decreases (GR.op_Bang gr + (if !busy then 1 else 0))
    {
      with s_i fp_i ph_i. assert (gc_state gh d_mid b_mid s_i fp_i ph_i);
      unfold gc_state;
      let shape_i = Ghost.hide (GI.phase_shape ({ data = d_mid; bump = b_mid } <: minor_state)
                                  s_i fp_i ph_i);
      assert (pure (Ghost.reveal shape_i));
      fold (gc_state gh d_mid b_mid s_i fp_i ph_i);
      let idle = major_slice gh 0xFFFFFFFFFFFFFFFFUL;
      with s_j fp_j ph_j. assert (gc_state gh d_mid b_mid s_j fp_j ph_j);
      full_slice_step ({ data = d_mid; bump = b_mid } <: minor_state) g0 droots fp_mid
        s_i fp_i ph_i s_j fp_j ph_j;
      GR.op_Colon_Equals gr (rank ph_j);
      busy := not idle;
    };
    GR.free gr;
    with s_fin fp_fin ph_fin. assert (gc_state gh d_mid b_mid s_fin fp_fin ph_fin);
    rewrite (gc_state gh d_mid b_mid s_fin fp_fin ph_fin)
         as (gc_state gh d_mid b_mid s_fin fp_fin Ph.Idle);
    unfold gc_state;
    GI.phase_shape_idle ({ data = d_mid; bump = b_mid } <: minor_state) s_fin fp_fin;
    fold (gc_state gh d_mid b_mid s_fin fp_fin Ph.Idle);
    full_gc_end ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs s_fin fp_fin;
    ok
  } else {
    // Nothing ran after the minor collection, so the heap we hand back is the
    // post-minor one, and every `ok`-guarded conjunct is vacuous.
    ok
  }
}
#pop-options
