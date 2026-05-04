(*
   Pulse GC (Generational) - Top-Level Entry Point Interface

   Provides:
   - gen_alloc: Allocate an object (routes to minor or major by size)
   - minor_collect: Promote all minor objects to major heap, rewrite pointers, reset
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
open GC.Impl.Heap
module SpecFields = GC.Spec.Fields
module AllocLemmas = GC.Spec.Allocator.Lemmas
module PromoteSpec = GC.Gen.Promote
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs

/// ---------------------------------------------------------------------------
/// Combined generational heap state
/// ---------------------------------------------------------------------------

/// The generational GC state: minor heap + major heap + free-list pointer
noeq
type gen_heap_t = {
  minor : minor_heap_t;
  major : heap_t;
  fp_ref : R.ref U64.t;    // major heap free-list head
}

/// Combined slprop for the generational heap
let is_gen_heap (gh: gen_heap_t) (d: minor_heap) (b: U64.t)
                (s: heap_state) (fp: U64.t) : slprop =
  is_minor gh.minor d b **
  is_heap gh.major s **
  R.pts_to gh.fp_ref fp

/// ---------------------------------------------------------------------------
/// Allocation
/// ---------------------------------------------------------------------------

/// Allocate an object. Small objects go to minor heap, large ones to major.
/// Returns 0UL on failure (both heaps full).
fn gen_alloc (gh: gen_heap_t) (wosize: U64.t) (tag: U64.t)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pure (U64.v wosize > 0 /\ U64.v tag < 256 /\
                 SpecFields.well_formed_heap 's)
  returns obj: U64.t
  ensures exists* d2 b2 s2 fp2. is_gen_heap gh d2 b2 s2 fp2

/// ---------------------------------------------------------------------------
/// Minor collection (full: promote + rewrite pointers + rewrite roots + reset)
/// ---------------------------------------------------------------------------

/// Trigger a minor collection:
/// 1. Promote all minor objects to major heap (filling forwarding array)
/// 2. Update major-heap pointer fields (rewrite minor refs via fwd_arr)
/// 3. Rewrite program roots (minor refs → forwarded major addresses)
/// 4. Reset the minor heap (bump = 0)
///
/// Postcondition: result matches minor_collect_all_spec
/// (promotes ALL minor objects, a sound overapproximation of live-only).
///
/// End-to-end correctness: by combining this spec-refinement postcondition with
/// the correctness theorems in GC.Gen.Correctness (gen_gc_correct, gen_gc_correct_full,
/// generational_gc_end_to_end), callers can derive:
/// - All major-heap objects survive promotion
/// - Post-collection major heap is well-formed (under minor_fields_well_formed etc.)
/// - Root rewriting is correct
/// - Minor heap is reset and ready for new allocations
/// - Composition with mark-and-sweep major GC yields full GC correctness
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
                 Seq.length 'farr == UpdatePtrs.fwd_array_size /\
                 (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL))
  ensures exists* d2 b2 s2 fp2 rs2 farr2.
    is_gen_heap gh d2 b2 s2 fp2 **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pure (
      // Spec refinement: result matches the pure specification
      (let minor_st : minor_state = { data = 'd; bump = 'b } in
       let res = PromoteSpec.minor_collect_all_spec minor_st 's 'fp 'rs in
       s2 == res.mc_major /\
       fp2 == res.mc_fp /\
       rs2 == res.mc_roots /\
       U64.v b2 == 0) /\
      // Structural invariants preserved
      SpecFields.well_formed_heap_part1 s2 /\
      AllocLemmas.fl_valid s2 fp2 (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates s2 fp2 (heap_size / U64.v mword))
