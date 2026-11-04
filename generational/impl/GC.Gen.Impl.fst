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

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Impl.MinorHeap
open GC.Gen.Impl.Promote
open GC.Gen.Impl.UpdatePtrs
open GC.Gen.RefTable
open GC.Gen.Impl.Cheney
open GC.Impl.Heap
open GC.Impl.Stack
module SpecFields = GC.Spec.Fields
module SpecObj = GC.Spec.Object
module Alloc = GC.Impl.Allocator
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
module PCS = GC.Gen.PostCollectionShape
module FreeListShape = GC.Gen.FreeListShape
module MinorFwd = GC.Gen.MinorCollectForwarding
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module SpecHeapGraph = GC.Spec.HeapGraph
module RBridge = GC.Gen.ReachabilityBridge
module CheneyBFS = GC.Gen.CheneyBFS
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module Cheney = GC.Gen.Impl.Cheney
module SpecHeapModel = GC.Spec.HeapModel
module MRT = GC.Gen.MajorReachabilityTransfer

/// Two transports in one: `GC.Gen.MajorPrecondition` carries the pre-minor facts
/// across the minor collection to `darken_precondition`, and
/// `MarkBoundedPrecondition` carries that across root darkening to the
/// obligation `GC.Impl.collect_with_roots` actually demands.  Neither step is
/// the caller's business.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let gen_gc_major_precondition_elim minor major fp roots st cap
  = let result = CheneySpec.cheney_collect_spec minor major fp roots in
    assert (Seq.equal st (Seq.empty #obj_addr));
    GMP.darken_precondition_after_minor minor major fp roots cap;
    MBP.darken_establishes_precondition result.mc_major st result.mc_roots result.mc_fp cap;
    MBP.darken_roots_match_stack result.mc_major st result.mc_roots result.mc_fp cap;
    GMP.post_minor_roots_valid_for_darkening minor major fp roots;
    (let prepared = gen_gc_prepared_state minor major fp roots st cap in
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
let gen_gc_named_root_in_stack minor major fp roots roots_out st cap r
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
/// Allocation
/// ---------------------------------------------------------------------------

/// Allocate: try minor first (if small enough), fall back to major.
#push-options "--z3rlimit 10"
fn gen_alloc (gh: gen_heap_t) (wosize: U64.t) (tag: U64.t)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pure (U64.v wosize > 0 /\ U64.v tag < 256 /\
                 SpecFields.well_formed_heap 's)
  returns obj: U64.t
  ensures exists* d2 b2 s2 fp2. is_gen_heap gh d2 b2 s2 fp2
{
  unfold is_gen_heap;
  if U64.lte wosize max_young_wosize_u64 {
    // Small object → try minor heap
    let obj = minor_alloc gh.minor wosize tag;
    if U64.eq obj 0UL {
      // Minor full — allocate directly from major
      let fp = R.op_Bang gh.fp_ref;
      let res = Alloc.allocate gh.major fp wosize tag;
      R.op_Colon_Equals gh.fp_ref (fst res);
      fold (is_gen_heap gh _ _ _ _);
      snd res
    } else {
      fold (is_gen_heap gh _ _ _ _);
      obj
    }
  } else {
    // Large object → major heap directly
    let fp = R.op_Bang gh.fp_ref;
    let res = Alloc.allocate gh.major fp wosize tag;
    R.op_Colon_Equals gh.fp_ref (fst res);
    fold (is_gen_heap gh _ _ _ _);
    snd res
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// Minor Collection — Full Implementation
/// ---------------------------------------------------------------------------

module PromoteSpec = GC.Gen.Promote
open GC.Gen.PromoteUpdate

/// Helper: extract wfh_part1 from well_formed_heap
let wfh_implies_part1 (g: heap_state)
  : Lemma (requires SpecFields.well_formed_heap g)
          (ensures SpecFields.blocks_fit g)
  = SpecFields.wf_parts ()

/// Lemma: unfold cheney_collect_spec in terms of cheney_promote
let cheney_collect_spec_unfold (minor: minor_state) (major: heap_state) (fp: U64.t) (roots: Seq.seq U64.t)
  : Lemma (let prom = CheneySpec.cheney_promote minor major fp roots in
           let res = CheneySpec.cheney_collect_spec minor major fp roots in
           res.mc_major == PromoteSpec.update_major_pointers prom.major_final prom.fwd_map /\
           res.mc_fp == prom.fp_final /\
           res.mc_roots == PromoteSpec.rewrite_roots roots prom.fwd_map)
  = ()

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
let minor_collect_full_isomorphism_post
  (minor: minor_state) (major: heap) (fp: U64.t) (free: SpecFields.free_def)
  (roots slots: Seq.seq U64.t) (n: nat) (ok: bool)
  (post_major: heap) (post_roots: Seq.seq U64.t)
  : Lemma
    (requires
      GenInv.collection_shape_with free minor major fp /\
      ref_table_covers_with free major slots n /\
      post_major == (CheneySpec.cheney_collect_spec_with free minor major fp roots).mc_major /\
      post_roots == MCFH.resolve_roots post_major
        (PromoteSpec.rewrite_roots roots
          (CheneySpec.cheney_promote minor major fp roots).fwd_map) /\
      MinorFwd.remembered_targets_in_roots major roots slots n /\
      MinorFwd.roots_valid_with free minor major roots /\
      (ok ==> CheneyBFS.cheney_no_oom minor major fp roots))
    (ensures
      (ok ==>
       MinorFwd.normal_result_reachable_subgraph_isomorphism_prop
         minor major fp free roots post_major post_roots /\
       MinorFwd.normal_result_non_pointer_fields_preserved_prop
         minor major fp free roots post_major))
  =
    if ok
    then begin
      MCFH.roots_valid_with_implies_not_free free minor major roots;
      MCFH.major_fields_covered_from_slots minor major free roots slots n;
      MinorFwd.normal_post_reachable_subgraph_isomorphism
        minor major fp free roots slots n;
      MinorFwd.normal_post_reachable_subgraph_isomorphism_to_result
        minor major fp free roots post_major post_roots;
      MinorFwd.normal_post_non_pointer_fields_preserved
        minor major fp free roots slots n;
      MinorFwd.normal_post_non_pointer_fields_preserved_to_result
        minor major fp free roots post_major
    end
#pop-options

/// ---------------------------------------------------------------------------
/// minor_collect_full: includes ref_table rewriting for full correctness
/// ---------------------------------------------------------------------------

module CE = GC.Gen.CheneyGeneric

/// The spec half of the minor collection given what counts as free: the two passes over a
/// Cheney result are the collection's pointer update
/// (`TPC.two_pass_implies_collect_with`), and that collection keeps the shape
/// (`CE.cheney_collect_with_preserves_shape`).
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let minor_collect_with_spec
  (free: SpecFields.free_def) (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (farr slots: Seq.seq U64.t) (n: nat)
  : Lemma
    (requires
      GenInv.collection_shape_with free minor major fp /\
      Seq.length farr == fwd_array_size /\
      represents_fwd farr (CheneySpec.cheney_promote minor major fp roots).fwd_map /\
      ref_table_sound_with free major slots n /\
      ref_table_covers_with free major slots n /\
      slots_pairwise_distinct slots n)
    (ensures
      (let prom = CheneySpec.cheney_promote minor major fp roots in
       let res = CheneySpec.cheney_collect_spec_with free minor major fp roots in
       rewrite_slots_iter (update_promoted_iter prom.major_final farr prom.fwd_map 0)
         prom.fwd_map slots n 0 == res.mc_major /\
       GenInv.collection_shape_with free (minor_reset minor) res.mc_major prom.fp_final))
  = let prom = CheneySpec.cheney_promote minor major fp roots in
    GenInv.collection_shape_with_elim free minor major fp;
    GenInv.major_shape_with_elim free major fp;
    GenInv.minor_heap_shape_elim minor;
    CheneySteps.cheney_promote_fwd_above_zero_addr minor major fp roots;
    CheneySteps.cheney_promote_fwd_bounded minor major fp roots;
    derive_fwd_targets_stable prom.fwd_map;
    ref_table_sound_with_implies_valid_slot_addrs free major slots n;
    ref_table_covers_with_implies_complete free major prom.fwd_map slots n;
    CheneySteps.cheney_promote_preserves_wfh_part1 minor major fp roots;
    CheneySteps.cheney_promote_preserves_wfh_part4 minor major fp roots;
    CPForwarding.cheney_promote_fwd_valid_or_infix minor major fp roots;
    CPInj.cheney_promote_fwd_normal_injective minor major fp roots;
    TPC.two_pass_implies_collect_with free minor major fp roots farr slots n;
    CE.cheney_collect_with_preserves_shape free minor major fp roots
#pop-options

/// Compose all phases into a single verified call.  The proof is over the
/// caller's definition of free throughout: nothing here reads or assumes
/// anything of a free block.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
fn minor_collect_full (gh: gen_heap_t)
                      (roots: array U64.t) (nroots: SZ.t)
                      (fwd_arr: array U64.t)
                      (queue: larray U64.t Cheney.queue_size)
                      (slots: array U64.t) (nslots: SZ.t)
                      (#free: erased SpecFields.free_def)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           pts_to slots 'sl **
           pure (SZ.v nroots == Seq.length 'rs /\
                 minor_collect_pre_with free ({ data = 'd; bump = 'b } <: minor_state) 's
                   'fp 'rs 'farr 'sl (SZ.v nslots))
  returns ok: bool
  ensures exists* d2 b2 s2 fp2 rs2 farr2 qv2.
    is_gen_heap gh d2 b2 s2 fp2 **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pts_to slots 'sl **
    pure (minor_collect_post_with free ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs
            'sl (SZ.v nslots) ok d2 b2 s2 fp2 rs2 farr2)
{
  unfold is_gen_heap;
  GenInv.collection_shape_with_elim free ({data = 'd; bump = 'b} <: minor_state) 's 'fp;
  GenInv.major_shape_with_elim free 's 'fp;
  GenInv.minor_heap_shape_elim ({data = 'd; bump = 'b} <: minor_state);

  // Phase 1: Cheney BFS promotion (forward roots + scan)
  let ok = cheney_promote_phase gh.minor gh.major gh.fp_ref fwd_arr queue roots nroots;

  // Extract ghost state from promote phase
  with ms_post. assert (is_heap gh.major ms_post);
  with farr_post. assert (pts_to fwd_arr farr_post);
  with fp_post. assert (R.pts_to gh.fp_ref fp_post);

  // Phase 2: Update promoted objects' fields only (efficient path)
  CheneySteps.cheney_promote_fwd_bounded
    ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs;
  fwd_bounded_implies_valid_fwd_entries farr_post
    (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map;

  update_promoted_objects gh.major fwd_arr
    #(hide (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map);

  // After update: ms_updated == update_promoted_iter ms_post farr_post prom_fwd 0
  with ms_updated. assert (is_heap gh.major ms_updated);
  with farr_post2. assert (pts_to fwd_arr farr_post2);

  // Phase 2b: Rewrite ref_table slots
  ref_table_sound_with_implies_valid_slot_addrs free 's 'sl (SZ.v nslots);
  rewrite_heap_slots gh.major fwd_arr slots nslots
    #(hide (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map);

  // After slot rewrite: heap is the two-pass result
  with ms_final. assert (is_heap gh.major ms_final);

  // Phase 3: Rewrite roots using ghost-tracked forwarding map
  with farr_post3. assert (pts_to fwd_arr farr_post3);
  rewrite_roots_impl roots fwd_arr nroots
    #(hide (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map);
  with rs_out. assert (pts_to roots rs_out);

  // Phase 4: Reset minor heap
  minor_heap_reset gh.minor;

  // The two passes are the collection's update, which keeps the shape.
  minor_collect_with_spec free ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs
    farr_post3 'sl (SZ.v nslots);
  // ... and is a reachable-subgraph isomorphism.
  minor_collect_full_isomorphism_post ({data = 'd; bump = 'b} <: minor_state) 's 'fp free
    'rs 'sl (SZ.v nslots) ok ms_final (MCFH.resolve_roots ms_final rs_out);

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
let minor_collect_idle_post minor_st s fp rs farr sl nslots ok d2 b2 s2 fp2 rs2 farr2 =
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
/// Full generational GC (minor collection + major collection)
/// ---------------------------------------------------------------------------

/// gen_gc composes the verified full minor collection with mark-and-sweep.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
fn gen_gc (gh: gen_heap_t)
           (roots: array U64.t) (nroots: SZ.t)
           (fwd_arr: array U64.t)
           (queue: larray U64.t Cheney.queue_size)
           (slots: array U64.t) (nslots: SZ.t)
           (st: gray_stack)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           pts_to slots 'sl **
           is_gray_stack st 'st **
             pure (
               let minor_st : minor_state = { data = 'd; bump = 'b } in
               GenInv.collection_heap_shape minor_st 's 'fp /\
               gen_gc_stack_budget 'rs 'st (stack_capacity st) /\
               SZ.v nroots == Seq.length 'rs /\
               Seq.length 'farr == fwd_array_size /\
               (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\
               ref_table_sound 's 'sl (SZ.v nslots) /\
               ref_table_covers_minor_ptrs 's 'sl (SZ.v nslots) /\
               slots_pairwise_distinct 'sl (SZ.v nslots) /\
               MinorFwd.remembered_targets_in_roots 's 'rs 'sl (SZ.v nslots) /\
               MinorFwd.roots_valid_for_minor_collection
                 ({ data = 'd; bump = 'b } <: minor_state) 's 'rs)
  returns res: (U64.t & bool)
  ensures exists* d2 b2 s2 rs2 farr2 qv2 st2.
    is_gen_heap gh d2 b2 s2 (fst res) **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pts_to slots 'sl **
    is_gray_stack st st2 **
    pure (
      let minor_st : minor_state = { data = 'd; bump = 'b } in
      let minor_st_out : minor_state = { data = d2; bump = b2 } in
      let ok = snd res in
      // Failure is reported only for a concrete out-of-memory event: an object
      // the major free list had no room for, at a point of this collection.
      (not ok ==> CheneyBFS.cheney_oom minor_st 's 'fp 'rs) /\
      gen_gc_roots_post minor_st 's 'fp 'rs rs2 ok 'st (stack_capacity st) /\
      // The nursery handed back is the zeroed one, `GC.Gen.MinorHeap.minor_reset`.
      // This is the only heap-shape fact in the postcondition that does *not*
      // follow from the invariant below; everything else about the returned
      // state, including `gen_gc_heap_shape_post`, is derived from it (see
      // `gen_gc_heap_shape_post_intro`).
      minor_st_out == minor_reset minor_st /\
      // **The collector restores its own precondition**: literally the same
      // predicate `gen_gc` demands of the state it is handed, now asserted of
      // the state it hands back.  A runtime driving an unbounded sequence of
      // collections therefore establishes the invariant once, at start-up, and
      // never again.
      //
      // The minor half is vacuous -- the nursery returned is
      // `GC.Gen.MinorHeap.minor_reset`, i.e. zeroed -- so the content of the
      // claim is `GC.Gen.HeapInvariant.major_heap_shape` of the major heap and
      // free-list head, every conjunct of it, supplied by
      // `GC.Gen.PostCollectionShape.major_gc_restores_major_heap_shape`.
      GenInv.collection_heap_shape minor_st_out s2 (fst res) /\
      gen_gc_reachable_subgraph_isomorphism_post
        minor_st 's 'fp 'rs ok s2 rs2 'st (stack_capacity st) /\
      gen_gc_unreachable_final_blue_post
        minor_st 's 'fp 'rs ok s2 'st (stack_capacity st))
{
  GenInv.collection_heap_shape_elim ({data = 'd; bump = 'b} <: minor_state) 's 'fp;
  GenInv.major_heap_shape_elim 's 'fp;
  GenInv.major_heap_shape_walk 's 'fp;
  GenInv.minor_heap_shape_elim ({data = 'd; bump = 'b} <: minor_state);

  // Phase 1: Full minor collection, including remembered-set slot rewriting,
  // on the `free_stw` definition.
  minor_collect_idle_pre ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs 'farr 'sl
    (SZ.v nslots);
  let ok = minor_collect_full gh roots nroots fwd_arr queue slots nslots
             #(hide SpecFields.free_stw);

  with d_mid b_mid ms_updated fp_mid. assert (is_gen_heap gh d_mid b_mid ms_updated fp_mid);
  with rs_mid. assert (pts_to roots rs_mid);
  with farr_mid. assert (pts_to fwd_arr farr_mid);
  with qv_mid. assert (pts_to queue qv_mid);
  assert (pts_to slots 'sl);
  minor_collect_idle_post ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs 'farr 'sl
    (SZ.v nslots) ok d_mid b_mid ms_updated fp_mid rs_mid farr_mid;

  unfold is_gen_heap;
  let fp_val = R.op_Bang gh.fp_ref;
  assert (pure (fp_val == fp_mid));

  assert (pure (ms_updated ==
    (CheneySpec.cheney_collect_spec ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).mc_major));
  assert (pure (fp_val ==
    (CheneySpec.cheney_collect_spec ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).mc_fp));
  cheney_collect_spec_unfold ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs;
  CheneyCorr.cheney_collect_preserves_objects
    ({data = 'd; bump = 'b} <: minor_state) 's 'fp SpecFields.free_stw 'rs;
  assert (pure (forall (x: obj_addr). Seq.mem x (SpecFields.objects zero_addr 's) ==>
    Seq.mem x (SpecFields.objects zero_addr ms_updated)));
  assert (pure (GenInv.collection_heap_shape
    ({ data = d_mid; bump = b_mid } <: minor_state) ms_updated fp_val));
  assert (pure (GenInv.collection_heap_shape
    ({ data = d_mid; bump = b_mid } <: minor_state) ms_updated fp_mid));
  assert (pure (rs_mid ==
    (CheneySpec.cheney_collect_spec ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).mc_roots));
  assert (pure (rs_mid ==
    PromoteSpec.rewrite_roots 'rs
      (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map));
  PromoteSpec.rewrite_roots_length 'rs
    (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map;
  assert (pure (SZ.v nroots == Seq.length rs_mid));
  assert (pure (U64.v b_mid == 0));
  // The nursery handed back by the minor collection is the zeroed one, which is
  // what makes every minor-side conjunct of `collection_heap_shape` vacuous.
  assert (pure (({ data = d_mid; bump = b_mid } <: minor_state) ==
    minor_reset ({ data = 'd; bump = 'b } <: minor_state)));
  GenInv.collection_heap_shape_elim ({ data = d_mid; bump = b_mid } <: minor_state)
    ms_updated fp_val;
  assert (pure (GenInv.major_heap_shape ms_updated fp_val));
  GenInv.major_heap_shape_elim ms_updated fp_val;
  assert (pure (SpecFields.well_formed_heap ms_updated));
  wfh_implies_part1 ms_updated;
  assert (pure (SpecFields.blocks_fit ms_updated));
  assert (pure (SpecFields.blocks_fit
    (CheneySpec.cheney_collect_spec ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).mc_major));
  // Phase 2: Major collection, but only if the minor collection succeeded.
  //
  // On the out-of-memory path some live nursery objects were never promoted, so
  // the rewritten root set still contains nursery addresses and there is nothing
  // sensible for mark-and-sweep to do with it.  `minor_collect_full` reports
  // that through `ok`, which also witnesses `cheney_no_oom` -- the fact the
  // major phase's entry condition is derived from.  This is why `gen_gc`'s
  // caller does not have to establish `cheney_no_oom` itself.
  if ok {
    MarkBoundedImpl.darken_roots_bounded gh.major st roots nroots (stack_capacity st);
    with prepared_major prepared_st roots_after. assert (
      is_heap gh.major prepared_major **
      is_gray_stack st prepared_st **
      pts_to roots roots_after);
    assert (pure (roots_after == rs_mid));
    assert (pure ((prepared_major, prepared_st) ==
      gen_gc_prepared_state
        ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs 'st (stack_capacity st)));
    gen_gc_major_precondition_elim
      ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs 'st (stack_capacity st);
    assert (pure (MajorGC.gc_precondition_with_roots
      prepared_major prepared_st prepared_st fp_val (stack_capacity st)));
    assert (pure (roots_match_stack
      (CheneySpec.cheney_collect_spec
         ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).mc_major
      rs_mid prepared_st));
    // Phase 2: Major collection (mark + sweep + coalesce)
    let final_fp = MajorGC.collect_with_roots gh.major st prepared_st fp_val;

    with s_final st_final. assert (
      is_heap gh.major s_final **
      is_gray_stack st st_final);
    assert (pure (SpecGCPost.gc_postcondition s_final));
    assert (pure (SpecGCPost.full_gc_correctness prepared_major s_final prepared_st));
    assert (pure (SpecGCPost.major_gc_live_subgraph_isomorphism
      prepared_major s_final prepared_st));
    assert (pure (SpecGCPost.major_gc_unreachable_final_blue
      prepared_major s_final prepared_st));
    assert (pure (SpecGCPost.major_gc_live_subgraph_isomorphism
      (fst (gen_gc_prepared_state
        ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs 'st (stack_capacity st)))
      s_final
      (snd (gen_gc_prepared_state
        ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs 'st (stack_capacity st)))));
    assert (pure (SpecGCPost.major_gc_unreachable_final_blue
      (fst (gen_gc_prepared_state
        ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs 'st (stack_capacity st)))
      s_final
      (snd (gen_gc_prepared_state
        ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs 'st (stack_capacity st)))));

    // Chain the two halves into a single isomorphism from the heap we were
    // handed to the heap we return, so that no caller has to do it.
    SpecGCPost.gc_postcondition_elim s_final;
    Mark.create_graph_wf_from_heap s_final;
    assert (pure (MRT.major_transfer_hyp prepared_major s_final prepared_st));
    // The reachable set is rooted at the objects the rewritten roots name, and
    // those are exactly what root darkening pushed.
    assert (pure (forall (e: U64.t).
      Seq.mem e (MCFH.resolve_roots ms_updated rs_mid) ==>
      GC.Spec.Base.is_val_addr e));
    assert (pure (forall (e: obj_addr).
      Seq.mem (e <: U64.t) (MCFH.resolve_roots ms_updated rs_mid) ==>
      Seq.mem e prepared_st));
    MRT.end_to_end_isomorphism_intro
      ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs
      ms_updated (MCFH.resolve_roots ms_updated rs_mid)
      prepared_major prepared_st s_final;

    // The collector re-establishes the generational shape invariant on the
    // heap it returns: `collect_with_roots` exposes the marked heap that
    // produced its result, and `major_gc_restores_major_heap_shape` proves all
    // conjuncts of `major_heap_shape` for `coalesce (sweep ...)`, which the
    // returned heap agrees with modulo free-block bodies.  The
    // nursery `gen_gc` hands back is `minor_reset`, which makes the minor and
    // cross-generation conjuncts vacuous.
    PCS.major_gc_restores_major_heap_shape_of_source
      prepared_major s_final prepared_st fp_val final_fp;
    GenInv.collection_heap_shape_after_minor_reset
      ({data = 'd; bump = 'b} <: minor_state) s_final final_fp;
    assert (pure (GenInv.collection_heap_shape
      ({ data = d_mid; bump = b_mid } <: minor_state) s_final final_fp));

    // Phase 6: Update free-list pointer and re-fold gen heap
    R.op_Colon_Equals gh.fp_ref final_fp;

    fold (is_gen_heap gh d_mid b_mid s_final final_fp);    (final_fp, ok)
  } else {
    // Nothing ran after the minor collection, so the heap we hand back is the
    // post-minor one.  It is already white/blue everywhere -- `major_heap_shape`
    // records both `no_black_objects` and `no_gray_objects` -- so it satisfies
    // the major-GC postcondition on its own, and every `ok`-guarded conjunct is
    // vacuous.
    GMP.major_heap_shape_gc_postcondition ms_updated fp_val;
    fold (is_gen_heap gh d_mid b_mid ms_updated fp_val);
    (fp_val, ok)
  }
}
#pop-options
