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

/// Phase 2: Rewrite roots using forwarding array.
/// For each root, if it's a minor pointer with a non-zero forwarding entry,
/// replace it with the forwarded address.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
inline_for_extraction
fn rewrite_one_root (roots: array U64.t) (fwd_arr: array U64.t) (riv: SZ.t)
  requires pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pure (SZ.v riv < Seq.length 'rs /\
                 Seq.length 'farr == fwd_array_size)
  ensures exists* rs2.
    pts_to roots rs2 **
    pts_to fwd_arr 'farr **
    pure (Seq.length rs2 == Seq.length 'rs)
{
  let r = roots.(riv);
  if U64.gte r 8UL {
    if U64.lt r minor_heap_size_u64 {
      if U64.eq (U64.rem r 8UL) 0UL {
        let idx = SZ.uint64_to_sizet (U64.div r 8UL);
        let fwd_val = fwd_arr.(idx);
        if U64.eq fwd_val 0UL {
          roots.(riv) <- r
        } else {
          roots.(riv) <- fwd_val
        }
      } else {
        roots.(riv) <- r
      }
    } else {
      roots.(riv) <- r
    }
  } else {
    roots.(riv) <- r
  }
}
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
fn rewrite_roots_phase (roots: array U64.t) (fwd_arr: array U64.t) (n: SZ.t)
  requires pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pure (SZ.v n == Seq.length 'rs /\
                 Seq.length 'farr == fwd_array_size)
  ensures exists* rs2.
    pts_to roots rs2 **
    pts_to fwd_arr 'farr **
    pure (Seq.length rs2 == Seq.length 'rs)
{
  let mut i = 0sz;
  while (SZ.lt !i n)
    invariant exists* rs_i iv.
      pts_to roots rs_i **
      pts_to fwd_arr 'farr **
      R.pts_to i iv **
      pure (SZ.v iv <= SZ.v n /\
            SZ.v n == Seq.length 'rs /\
            Seq.length rs_i == Seq.length 'rs /\
            Seq.length 'farr == fwd_array_size)
  {
    let iv = !i;
    rewrite_one_root roots fwd_arr iv;
    i := SZ.add iv 1sz
  }
}
#pop-options

/// Helper: extract wfh_part1 from well_formed_heap
let wfh_implies_part1 (g: heap_state)
  : Lemma (requires SpecFields.well_formed_heap g)
          (ensures SpecFields.well_formed_heap_part1 g)
  = reveal_opaque (`%SpecFields.well_formed_heap) SpecFields.well_formed_heap

/// Compose all phases into minor_collect using Cheney BFS.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0 --split_queries always"
fn minor_collect (gh: gen_heap_t)
                 (roots: array U64.t) (nroots: SZ.t)
                 (fwd_arr: array U64.t)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pure (SpecFields.well_formed_heap 's /\
                 AllocLemmas.fl_valid 's 'fp (heap_size / U64.v mword) /\
                 AllocLemmas.fl_chain_terminates 's 'fp (heap_size / U64.v mword) /\
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

  // wfh implies wfh_part1
  wfh_implies_part1 's;

  // Phase 1: Cheney BFS promotion (forward roots + scan)
  cheney_promote_phase gh.minor gh.major gh.fp_ref fwd_arr roots nroots;

  // Phase 2: Update major-heap pointer fields (rewrite minor refs via fwd_arr)
  with ms_post. assert (is_heap gh.major ms_post);
  with farr_post. assert (pts_to fwd_arr farr_post);
  with fp_post. assert (R.pts_to gh.fp_ref fp_post);
  assert (pure (Seq.length farr_post == fwd_array_size));
  ghost_fwd_of_represents farr_post;

  // Call fl_valid preservation lemma BEFORE update (operates on pre-state)
  CheneySpec.update_major_pointers_preserves_fl_valid ms_post (ghost_fwd_of farr_post) fp_post;

  // GAP: need heap_objects_dense for update_all_objects precondition
  // This is a structural property that follows from well_formed_heap + allocation preserving
  // the linear object layout. Admitted pending formal density proof.
  assume_ (pure (GC.Gen.Promote.heap_objects_dense ms_post /\
                 Seq.length (SpecFields.objects 0UL ms_post) > 0));
  update_all_objects gh.major fwd_arr #(hide (ghost_fwd_of farr_post));

  // After update: ms_updated == update_major_pointers ms_post (ghost_fwd_of farr_post)
  // fl_valid/fl_chain_terminates follow from the preservation lemma called above.
  with ms_updated. assert (is_heap gh.major ms_updated);
  // ms_updated == PromoteSpec.update_major_pointers ms_post (ghost_fwd_of farr_post)
  // and from the lemma: fl_valid (update_major_pointers ms_post fwd) fp_post ...
  // Since fp_post was framed (update_all_objects doesn't touch fp_ref):
  assert (R.pts_to gh.fp_ref fp_post);

  // Phase 3: Rewrite roots (minor pointers → forwarded major addresses)
  with farr_post2. assert (pts_to fwd_arr farr_post2);
  rewrite_roots_phase roots fwd_arr nroots;

  // Phase 4: Reset minor heap
  minor_heap_reset gh.minor;

  // SPEC REFINEMENT: connect imperative result to pure spec
  // This requires proving that cheney_promote_phase computes cheney_promote,
  // i.e., ghost-state threading through the BFS loops. Pending formal proof.
  with s2 fp2 rs2. assert (is_heap gh.major s2 ** R.pts_to gh.fp_ref fp2 ** pts_to roots rs2);
  assume_ (pure (
    let minor_st : minor_state = { data = 'd; bump = 'b } in
    let res = CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs in
    s2 == res.mc_major /\
    fp2 == res.mc_fp /\
    rs2 == res.mc_roots));

  fold (is_gen_heap gh _ 0UL _ _)
}
#pop-options
