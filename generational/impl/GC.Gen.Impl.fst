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
open GC.Gen.Impl.Cheney
open GC.Impl.Heap
open GC.Impl.Stack
module SpecFields = GC.Spec.Fields
module Alloc = GC.Impl.Allocator
module AllocLemmas = GC.Spec.Allocator.Lemmas
module CheneySpec = GC.Gen.Cheney
module ML = FStar.Math.Lemmas
module MajorGC = GC.Impl
module SpecGCPost = GC.Spec.Correctness
module Mark = GC.Spec.Mark
module CheneyCorr = GC.Gen.CheneyCorrectness
module TwoPass = GC.Gen.TwoPassEquiv

/// ---------------------------------------------------------------------------
/// Allocation
/// ---------------------------------------------------------------------------

/// Allocate: try minor first (if small enough), fall back to major.
#push-options "--z3rlimit 40"
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
      let res = Alloc.allocate gh.major fp wosize;
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
    let res = Alloc.allocate gh.major fp wosize;
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

/// Helper: advancing by a multiple of 8 preserves 8-alignment
let advance_aligned (p tw: nat)
  : Lemma (requires p % 8 == 0)
          (ensures (p + tw * 8) % 8 == 0)
  = FStar.Math.Lemmas.lemma_mod_plus p tw 8

/// Helper: total_words * 8 doesn't overflow U64
/// (since total_words <= minor_heap_size < pow2 57, so tw*8 < pow2 60 < pow2 64)
let mul8_no_overflow (tw: nat)
  : Lemma (requires tw <= minor_heap_size)
          (ensures tw * 8 < pow2 64)
  = FStar.Math.Lemmas.lemma_mult_le_right 8 tw minor_heap_size;
    FStar.Math.Lemmas.lemma_mult_le_right 8 minor_heap_size (pow2 57);
    assert_norm (pow2 57 * 8 < pow2 64)

/// Helper: p + total_bytes doesn't overflow U64
/// (p <= minor_heap_size < pow2 57, total_bytes <= minor_heap_size * 8 < pow2 60)
let add_no_overflow (p tw: nat)
  : Lemma (requires p <= minor_heap_size /\ tw <= minor_heap_size)
          (ensures p + tw * 8 < pow2 64)
  = mul8_no_overflow tw;
    assert (tw * 8 < pow2 64);
    assert (p < pow2 57);
    assert_norm (pow2 57 + pow2 57 * 8 < pow2 64);
    FStar.Math.Lemmas.lemma_mult_le_right 8 tw minor_heap_size;
    assert (tw * 8 <= minor_heap_size * 8);
    FStar.Math.Lemmas.lemma_mult_le_right 8 minor_heap_size (pow2 57);
    assert (minor_heap_size * 8 <= pow2 57 * 8)

/// Phase 1: Promote all minor objects and fill forwarding array.
/// Walks minor heap linearly from 0 to bump, promoting each object.
/// Records forwarding: fwd_arr[obj/8] := new_major_addr.
#push-options "--z3rlimit 50 --fuel 4 --ifuel 1 --split_queries always"
fn promote_phase (minor: minor_heap_t) (major: heap_t) (fp_ref: R.ref U64.t)
                 (fwd_arr: array U64.t)
  requires is_minor minor 'md 'mb **
           is_heap major 'ms **
           R.pts_to fp_ref 'fp **
           pts_to fwd_arr 'farr **
           pure (SpecFields.well_formed_heap_part1 'ms /\
                 AllocLemmas.fl_valid 'ms 'fp (heap_size / U64.v mword) /\
                 AllocLemmas.fl_chain_terminates 'ms 'fp (heap_size / U64.v mword) /\
                 Seq.length 'farr == fwd_array_size /\
                 (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL))
  ensures exists* md2 mb2 ms2 fp2 farr2.
    is_minor minor md2 mb2 **
    is_heap major ms2 **
    R.pts_to fp_ref fp2 **
    pts_to fwd_arr farr2 **
    pure (md2 == 'md /\ mb2 == 'mb /\
          SpecFields.well_formed_heap_part1 ms2 /\
          AllocLemmas.fl_valid ms2 fp2 (heap_size / U64.v mword) /\
          AllocLemmas.fl_chain_terminates ms2 fp2 (heap_size / U64.v mword) /\
          Seq.length farr2 == fwd_array_size)
{
  // Read bump pointer
  unfold is_minor minor 'md 'mb;
  let bump = R.op_Bang minor.bump_ref;
  fold (is_minor minor 'md bump);
  let mut pos = 0UL;
  while (U64.lt !pos bump)
    invariant exists* md_i mb_i ms_i fp_i farr_i p_i.
      is_minor minor md_i mb_i **
      is_heap major ms_i **
      R.pts_to fp_ref fp_i **
      pts_to fwd_arr farr_i **
      R.pts_to pos p_i **
      pure (U64.v p_i <= U64.v bump /\
            U64.v p_i % 8 == 0 /\
            U64.v bump <= minor_heap_size /\
            U64.v bump % 8 == 0 /\
            md_i == 'md /\ mb_i == bump /\
            SpecFields.well_formed_heap_part1 ms_i /\
            AllocLemmas.fl_valid ms_i fp_i (heap_size / U64.v mword) /\
            AllocLemmas.fl_chain_terminates ms_i fp_i (heap_size / U64.v mword) /\
            Seq.length farr_i == Seq.length 'farr)
  {
    let p = !pos;
    if U64.gte (U64.add p 8UL) bump {
      pos := bump
    } else {
      let hdr = minor_read minor p;
      let wosize = U64.shift_right hdr 10ul;
      if U64.eq wosize 0UL {
        advance_aligned (U64.v p) 1;
        pos := U64.add p 8UL
      } else {
        let obj_addr = U64.add p 8UL;
        if U64.gte wosize minor_heap_size_u64 {
          pos := bump
        } else {
          // wosize < minor_heap_size, so (wosize+1)*8 fits in U64
          let total_words = U64.add wosize 1UL;
          mul8_no_overflow (U64.v total_words);
          let total_bytes = U64.mul total_words 8UL;
          add_no_overflow (U64.v p) (U64.v total_words);
          if U64.gt (U64.add p total_bytes) bump {
            pos := bump
          } else {
            // Establish promote_one preconditions one by one
            // obj_addr alignment: p % 8 == 0 implies (p+8) % 8 == 0
            advance_aligned (U64.v p) 1;
            // obj_addr bounds: p + total_bytes <= bump <= minor_heap_size
            // so obj_addr = p+8 < p + total_bytes <= bump <= minor_heap_size
            // and obj_addr + wosize * 8 = (p+8) + wosize*8
            //   = p + (wosize+1)*8 = p + total_bytes <= bump <= minor_heap_size
            let new_addr = promote_one minor major fp_ref obj_addr;
            with farr_pre. assert (pts_to fwd_arr farr_pre);
            let idx = SZ.uint64_to_sizet (U64.div obj_addr 8UL);
            fwd_arr.(idx) <- new_addr;
            // Prove next pos is aligned
            advance_aligned (U64.v p) (U64.v total_words);
            pos := U64.add p total_bytes
          }
        }
      }
    }
  }
}
#pop-options

/// Helper: extract wfh_part1 from well_formed_heap
let wfh_implies_part1 (g: heap_state)
  : Lemma (requires SpecFields.well_formed_heap g)
          (ensures SpecFields.well_formed_heap_part1 g)
  = reveal_opaque (`%SpecFields.well_formed_heap) SpecFields.well_formed_heap

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
    Classical.forall_intro (fun i -> aux i)

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

/// Bridge lemma: conditional two-pass ↔ full-update equivalence.
/// If the 5 preconditions of TwoPassEquiv hold, then the two-pass result
/// equals update_major_pointers (= cheney_collect_spec.mc_major).
let two_pass_implies_full_update
  (minor: minor_state) (major_pre: heap_state) (fp: U64.t) (roots: Seq.seq U64.t)
  (farr: Seq.seq U64.t) (slots: Seq.seq U64.t) (n: nat)
  : Lemma
    (requires
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       Seq.length farr == fwd_array_size /\
       valid_fwd_entries farr /\
       represents_fwd farr prom.fwd_map /\
       promoted_entries_valid_from prom.major_final farr 0 /\
       promoted_entries_disjoint prom.major_final farr /\
       SpecFields.well_formed_heap_part4 prom.major_final /\
       valid_slot_addrs slots n /\
       slots_pairwise_distinct slots n /\
       ref_table_sound major_pre slots n /\
       ref_table_complete major_pre prom.fwd_map slots n /\
       fwd_targets_stable prom.fwd_map /\
       fwd_ptrs_classified prom.major_final prom.fwd_map farr slots n /\
       SpecFields.well_formed_heap_part1 prom.major_final /\
       PromoteSpec.heap_objects_dense prom.major_final /\
       Seq.length (SpecFields.objects zero_addr prom.major_final) > 0 /\
       SpecFields.well_formed_heap major_pre /\
       AllocLemmas.fl_valid major_pre fp TwoPass.heap_fuel /\
       AllocLemmas.fl_chain_terminates major_pre fp TwoPass.heap_fuel))
    (ensures
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       rewrite_slots_iter
         (update_promoted_iter prom.major_final farr prom.fwd_map 0)
         prom.fwd_map slots n 0
       == (CheneySpec.cheney_collect_spec minor major_pre fp roots).mc_major))
  = TwoPass.promoted_plus_slots_eq_full_update minor major_pre fp roots farr slots n;
    cheney_collect_spec_unfold minor major_pre fp roots

/// Compose all phases into minor_collect using Cheney BFS.
/// Uses update_promoted_objects (efficient: only visits promoted objects).
/// The caller is responsible for updating remembered-set slots separately.
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
fn minor_collect (gh: gen_heap_t)
                 (roots: array U64.t) (nroots: SZ.t)
                 (fwd_arr: array U64.t)
                 (queue: larray U64.t Cheney.queue_size)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           pure (SpecFields.well_formed_heap 's /\
                 AllocLemmas.fl_valid 's 'fp (heap_size / U64.v mword) /\
                 AllocLemmas.fl_chain_terminates 's 'fp (heap_size / U64.v mword) /\
                 PromoteSpec.heap_objects_dense 's /\
                 PromoteSpec.chain_objects_blue 's 'fp /\
                 SZ.v nroots == Seq.length 'rs /\
                 Seq.length 'farr == fwd_array_size /\
                 (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\
                 minor_wf ({ data = 'd; bump = 'b }) /\
                  minor_guards_complete ({ data = 'd; bump = 'b }) /\
                  minor_infix_wf ({ data = 'd; bump = 'b }) /\
                 Seq.length (SpecFields.objects zero_addr 's) > 0)
  returns ok: bool
  ensures exists* d2 b2 s2 fp2 rs2 farr2 qv2.
    is_gen_heap gh d2 b2 s2 fp2 **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pure (
      let minor_st : minor_state = { data = 'd; bump = 'b } in
      let prom = CheneySpec.cheney_promote minor_st 's 'fp 'rs in
      // Post-collection heap is the result of updating only promoted objects
      s2 == update_promoted_iter prom.major_final farr2 prom.fwd_map 0 /\
      // Free pointer from promotion phase
      fp2 == prom.fp_final /\
      // Roots rewritten via forwarding map
      rs2 == PromoteSpec.rewrite_roots 'rs prom.fwd_map /\
      // Minor heap fully reset
      U64.v b2 == 0 /\
      // Forwarding array represents the spec-level forwarding map
      represents_fwd farr2 prom.fwd_map /\
      // Forwarding entries are valid (for callers that need to do additional rewrites)
      valid_fwd_entries farr2 /\
      // Structural invariants from promotion phase preserved through update
      Seq.length farr2 == fwd_array_size /\
      // Promotion preserves well_formed_heap_part1
      SpecFields.well_formed_heap_part1 prom.major_final /\
      AllocLemmas.fl_valid prom.major_final fp2 (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates prom.major_final fp2 (heap_size / U64.v mword) /\
      PromoteSpec.heap_objects_dense prom.major_final /\
      PromoteSpec.chain_objects_blue prom.major_final fp2 /\
      Seq.length (SpecFields.objects zero_addr prom.major_final) > 0)
{
  unfold is_gen_heap;

  // Phase 1: Cheney BFS promotion (forward roots + scan)
  let ok = cheney_promote_phase gh.minor gh.major gh.fp_ref fwd_arr queue roots nroots;

  // Extract ghost state from promote phase
  with ms_post. assert (is_heap gh.major ms_post);
  with farr_post. assert (pts_to fwd_arr farr_post);
  with fp_post. assert (R.pts_to gh.fp_ref fp_post);

  // Phase 2: Update promoted objects' fields only (efficient path)
  // Derive valid_fwd_entries from fwd_bounded + represents_fwd
  CheneySpec.cheney_promote_fwd_bounded
    ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs;
  fwd_bounded_implies_valid_fwd_entries farr_post
    (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map;

  update_promoted_objects gh.major fwd_arr
    #(hide (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map);

  // After update: ms_updated == update_promoted_iter ms_post farr_post prom_fwd 0
  with ms_updated. assert (is_heap gh.major ms_updated);
  assert (R.pts_to gh.fp_ref fp_post);

  // Phase 3: Rewrite roots using ghost-tracked forwarding map
  with farr_post2. assert (pts_to fwd_arr farr_post2);
  rewrite_roots_impl roots fwd_arr nroots
    #(hide (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map);

  // Phase 4: Reset minor heap
  minor_heap_reset gh.minor;

  fold (is_gen_heap gh _ 0UL _ _);
  ok
}
#pop-options

/// ---------------------------------------------------------------------------
/// minor_collect_full: includes ref_table rewriting for full correctness
/// ---------------------------------------------------------------------------

/// Compose all phases into a single verified call that achieves full
/// cheney_collect_spec correctness.  Takes a ref_table (slots array) that
/// covers all major-heap fields holding minor pointers (not belonging to
/// promoted objects — those are handled by update_promoted_objects).
#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
fn minor_collect_full (gh: gen_heap_t)
                      (roots: array U64.t) (nroots: SZ.t)
                      (fwd_arr: array U64.t)
                      (queue: larray U64.t Cheney.queue_size)
                      (slots: array U64.t) (nslots: SZ.t)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           pts_to slots 'sl **
           pure (SpecFields.well_formed_heap 's /\
                 AllocLemmas.fl_valid 's 'fp (heap_size / U64.v mword) /\
                 AllocLemmas.fl_chain_terminates 's 'fp (heap_size / U64.v mword) /\
                 PromoteSpec.heap_objects_dense 's /\
                 PromoteSpec.chain_objects_blue 's 'fp /\
                 SZ.v nroots == Seq.length 'rs /\
                 Seq.length 'farr == fwd_array_size /\
                 (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\
                 minor_wf ({ data = 'd; bump = 'b }) /\
                 minor_guards_complete ({ data = 'd; bump = 'b }) /\
                 minor_infix_wf ({ data = 'd; bump = 'b }) /\
                 Seq.length (SpecFields.objects zero_addr 's) > 0 /\
                 SZ.v nslots <= Seq.length 'sl /\
                 valid_slot_addrs 'sl (SZ.v nslots) /\
                 ref_table_sound 's 'sl (SZ.v nslots) /\
                 (let prom = CheneySpec.cheney_promote
                              ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs in
                  ref_table_complete 's prom.fwd_map 'sl (SZ.v nslots)))
  returns ok: bool
  ensures exists* d2 b2 s2 fp2 rs2 farr2 qv2.
    is_gen_heap gh d2 b2 s2 fp2 **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pts_to slots 'sl **
    pure (
      let minor_st : minor_state = { data = 'd; bump = 'b } in
      let prom = CheneySpec.cheney_promote minor_st 's 'fp 'rs in
      // Heap is the two-pass result (update promoted + rewrite slots)
      s2 == rewrite_slots_iter
              (update_promoted_iter prom.major_final farr2 prom.fwd_map 0)
              prom.fwd_map 'sl (SZ.v nslots) 0 /\
      // Free pointer from promotion phase
      fp2 == prom.fp_final /\
      // Roots rewritten via forwarding map
      rs2 == PromoteSpec.rewrite_roots 'rs prom.fwd_map /\
      // Minor heap fully reset
      U64.v b2 == 0 /\
      // Forwarding array represents the spec-level forwarding map
      represents_fwd farr2 prom.fwd_map /\
      // Forwarding entries are valid
      valid_fwd_entries farr2 /\
      Seq.length farr2 == fwd_array_size /\
      // Well-formedness preserved through promotion
      SpecFields.well_formed_heap_part1 prom.major_final /\
      // Strong correctness (conditional): under the two-pass equivalence
      // conditions, the result equals cheney_collect_spec.mc_major.
      (promoted_entries_valid_from prom.major_final farr2 0 /\
       promoted_entries_disjoint prom.major_final farr2 /\
       slots_pairwise_distinct 'sl (SZ.v nslots) /\
       fwd_ptrs_classified prom.major_final prom.fwd_map farr2 'sl (SZ.v nslots)
       ==> s2 == (CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs).mc_major))
{
  unfold is_gen_heap;

  // Phase 1: Cheney BFS promotion (forward roots + scan)
  let ok = cheney_promote_phase gh.minor gh.major gh.fp_ref fwd_arr queue roots nroots;

  // Extract ghost state from promote phase
  with ms_post. assert (is_heap gh.major ms_post);
  with farr_post. assert (pts_to fwd_arr farr_post);
  with fp_post. assert (R.pts_to gh.fp_ref fp_post);

  // Phase 2: Update promoted objects' fields only (efficient path)
  CheneySpec.cheney_promote_fwd_bounded
    ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs;
  fwd_bounded_implies_valid_fwd_entries farr_post
    (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map;

  update_promoted_objects gh.major fwd_arr
    #(hide (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map);

  // After update: ms_updated == update_promoted_iter ms_post farr_post prom_fwd 0
  with ms_updated. assert (is_heap gh.major ms_updated);
  with farr_post2. assert (pts_to fwd_arr farr_post2);

  // Phase 2b: Rewrite ref_table slots for full correctness
  rewrite_heap_slots gh.major fwd_arr slots nslots
    #(hide (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map);

  // After slot rewrite: heap is the two-pass result
  with ms_final. assert (is_heap gh.major ms_final);

  // Phase 3: Rewrite roots using ghost-tracked forwarding map
  with farr_post3. assert (pts_to fwd_arr farr_post3);
  rewrite_roots_impl roots fwd_arr nroots
    #(hide (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map);

  // Phase 4: Reset minor heap
  minor_heap_reset gh.minor;

  // Prove the conditional equivalence for the strong spec:
  // IF the 4 TwoPassEquiv conditions hold THEN s2 == cheney_collect_spec.mc_major
  // First derive fwd_targets_stable and well_formed_heap_part4 unconditionally
  CheneySpec.cheney_promote_fwd_above_zero_addr
    ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs;
  derive_fwd_targets_stable
    (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map;
  CheneySpec.cheney_promote_preserves_wfh_part4
    ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs;
  Classical.move_requires
    (two_pass_implies_full_update
       ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs farr_post3 'sl)
    (SZ.v nslots);

  fold (is_gen_heap gh _ 0UL _ _);
  ok
}
#pop-options

/// ---------------------------------------------------------------------------
/// Full generational GC (minor collection + major collection)
/// ---------------------------------------------------------------------------

/// gen_gc inlines minor collection phases directly (using update_all_objects
/// for full correctness) rather than calling minor_collect (which uses
/// update_promoted_objects for efficiency).
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
fn gen_gc (gh: gen_heap_t)
          (roots: array U64.t) (nroots: SZ.t)
          (fwd_arr: array U64.t)
          (queue: larray U64.t Cheney.queue_size)
          (st: gray_stack)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           is_gray_stack st 'st **
           pure (
             SpecFields.well_formed_heap 's /\
             AllocLemmas.fl_valid 's 'fp (heap_size / U64.v mword) /\
             AllocLemmas.fl_chain_terminates 's 'fp (heap_size / U64.v mword) /\
             PromoteSpec.heap_objects_dense 's /\
             PromoteSpec.chain_objects_blue 's 'fp /\
             SZ.v nroots == Seq.length 'rs /\
             Seq.length 'farr == fwd_array_size /\
             (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\
             minor_wf ({ data = 'd; bump = 'b }) /\
             minor_guards_complete ({ data = 'd; bump = 'b }) /\
             minor_infix_wf ({ data = 'd; bump = 'b }) /\
             Seq.length (SpecFields.objects zero_addr 's) > 0 /\
             Mark.no_black_objects 's /\
             (let res = CheneySpec.cheney_collect_spec
                          ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs in
              MajorGC.gc_precondition res.mc_major 'st res.mc_fp (stack_capacity st)))
  returns res: (U64.t & bool)
  ensures exists* d2 b2 s2 rs2 farr2 qv2 st2.
    is_gen_heap gh d2 b2 s2 (fst res) **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    is_gray_stack st st2 **
    pure (
      let minor_st : minor_state = { data = 'd; bump = 'b } in
      let result = CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs in
      let prom = CheneySpec.cheney_promote minor_st 's 'fp 'rs in
      SpecGCPost.gc_postcondition s2 /\
      SpecGCPost.full_gc_correctness result.mc_major s2 'st /\
      rs2 == result.mc_roots /\
      rs2 == PromoteSpec.rewrite_roots 'rs prom.fwd_map /\
      U64.v b2 == 0 /\
      (forall (x: obj_addr). Seq.mem x (SpecFields.objects zero_addr 's) ==>
        Seq.mem x (SpecFields.objects zero_addr result.mc_major)) /\
      SpecFields.well_formed_heap_part1 result.mc_major /\
      AllocLemmas.fl_valid result.mc_major result.mc_fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates result.mc_major result.mc_fp (heap_size / U64.v mword))
{
  unfold is_gen_heap;

  // Phase 1: Cheney BFS promotion (forward roots + scan)
  let ok = cheney_promote_phase gh.minor gh.major gh.fp_ref fwd_arr queue roots nroots;

  with ms_post. assert (is_heap gh.major ms_post);
  with farr_post. assert (pts_to fwd_arr farr_post);
  with fp_post. assert (R.pts_to gh.fp_ref fp_post);

  // Phase 2: Update ALL major-heap pointer fields (full correctness path)
  CheneySpec.update_major_pointers_preserves_fl_valid ms_post
    (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map
    fp_post;

  update_all_objects gh.major fwd_arr
    #(hide (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map);

  with ms_updated. assert (is_heap gh.major ms_updated);

  // Phase 3: Rewrite roots
  with farr_post2. assert (pts_to fwd_arr farr_post2);
  rewrite_roots_impl roots fwd_arr nroots
    #(hide (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map);

  // Phase 4: Reset minor heap
  minor_heap_reset gh.minor;

  // SPEC REFINEMENT: connect phases to cheney_collect_spec
  cheney_collect_spec_unfold ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs;
  CheneyCorr.cheney_gc_correct ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs;

  // Now: ms_updated == cheney_collect_spec(...).mc_major
  // Read post-minor free-list pointer
  let fp_val = R.op_Bang gh.fp_ref;

  // Phase 5: Major collection (mark + sweep + coalesce)
  let final_fp = MajorGC.collect gh.major st fp_val;

  with s_final st_final. assert (
    is_heap gh.major s_final **
    is_gray_stack st st_final);

  // Phase 6: Update free-list pointer and re-fold gen heap
  R.op_Colon_Equals gh.fp_ref final_fp;

  fold (is_gen_heap gh _ 0UL _ _);

  (final_fp, ok)
}
#pop-options
