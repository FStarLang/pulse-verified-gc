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
module SpecFields = GC.Spec.Fields
module Alloc = GC.Impl.Allocator
module AllocLemmas = GC.Spec.Allocator.Lemmas
module CheneySpec = GC.Gen.Cheney
module ML = FStar.Math.Lemmas

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

/// Compose all phases into minor_collect using Cheney BFS.
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
fn minor_collect (gh: gen_heap_t)
                 (roots: array U64.t) (nroots: SZ.t)
                 (fwd_arr: array U64.t)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pure (SpecFields.well_formed_heap 's /\
                 AllocLemmas.fl_valid 's 'fp (heap_size / U64.v mword) /\
                 AllocLemmas.fl_chain_terminates 's 'fp (heap_size / U64.v mword) /\
                 PromoteSpec.heap_objects_dense 's /\
                 PromoteSpec.chain_objects_blue 's 'fp /\
                 SZ.v nroots == Seq.length 'rs /\
                 Seq.length 'farr == fwd_array_size /\
                 (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL))
  ensures exists* d2 b2 s2 fp2 rs2 farr2.
    is_gen_heap gh d2 b2 s2 fp2 **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pure (
      // Spec refinement: result matches the Cheney BFS collection spec
      (let minor_st : minor_state = { data = 'd; bump = 'b } in
       let res = CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs in
       s2 == res.mc_major /\
       fp2 == res.mc_fp /\
       rs2 == res.mc_roots /\
       U64.v b2 == 0) /\
      // Structural invariants preserved
      SpecFields.well_formed_heap_part1 s2 /\
      AllocLemmas.fl_valid s2 fp2 (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates s2 fp2 (heap_size / U64.v mword))
{
  unfold is_gen_heap;

  // Phase 1: Cheney BFS promotion (forward roots + scan)
  // Postcondition: ms_post == (cheney_promote ...).major_final, etc.
  cheney_promote_phase gh.minor gh.major gh.fp_ref fwd_arr roots nroots;

  // Extract ghost state from promote phase
  with ms_post. assert (is_heap gh.major ms_post);
  with farr_post. assert (pts_to fwd_arr farr_post);
  with fp_post. assert (R.pts_to gh.fp_ref fp_post);

  // From cheney_promote_phase: represents_fwd farr_post prom.fwd_map
  // where prom = cheney_promote {data='d;bump='b} 's 'fp 'rs
  // Also: heap_objects_dense ms_post, chain_objects_blue ms_post fp_post, objects length > 0

  // Phase 2: Update major-heap pointer fields
  // Call fl_valid preservation lemma BEFORE update
  CheneySpec.update_major_pointers_preserves_fl_valid ms_post
    (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map
    fp_post;

  update_all_objects gh.major fwd_arr
    #(hide (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map);

  // After update: ms_updated == update_major_pointers ms_post prom_fwd
  with ms_updated. assert (is_heap gh.major ms_updated);
  assert (R.pts_to gh.fp_ref fp_post);

  // Phase 3: Rewrite roots using ghost-tracked forwarding map
  with farr_post2. assert (pts_to fwd_arr farr_post2);
  rewrite_roots_impl roots fwd_arr nroots
    #(hide (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map);

  // Phase 4: Reset minor heap
  minor_heap_reset gh.minor;

  // SPEC REFINEMENT: bridge from phase postconditions to cheney_collect_spec
  cheney_collect_spec_unfold ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs;
  
  // Assert each postcondition conjunct
  with rs_final. assert (pts_to roots rs_final);
  assert (pure (ms_updated == (CheneySpec.cheney_collect_spec ({data='d;bump='b} <: minor_state) 's 'fp 'rs).mc_major));
  assert (pure (fp_post == (CheneySpec.cheney_collect_spec ({data='d;bump='b} <: minor_state) 's 'fp 'rs).mc_fp));
  assert (pure (rs_final == (CheneySpec.cheney_collect_spec ({data='d;bump='b} <: minor_state) 's 'fp 'rs).mc_roots));
  assert (pure (SpecFields.well_formed_heap_part1 ms_updated));
  assert (pure (AllocLemmas.fl_valid ms_updated fp_post (heap_size / U64.v mword)));
  assert (pure (AllocLemmas.fl_chain_terminates ms_updated fp_post (heap_size / U64.v mword)));

  fold (is_gen_heap gh _ 0UL _ _)
}
#pop-options
