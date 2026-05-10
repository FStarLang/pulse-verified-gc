(*
   Pulse GC (Generational) - Top-Level Entry Point Interface

   Provides:
   - gen_alloc: Allocate an object (routes to minor or major by size)
   - minor_collect: Cheney-style BFS collection of minor heap
   - gen_gc: Full generational GC (minor + major collection)
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
open GC.Impl.Stack
module SpecFields = GC.Spec.Fields
module AllocLemmas = GC.Spec.Allocator.Lemmas
module CheneySpec = GC.Gen.Cheney
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module PromoteSpec = GC.Gen.Promote
module MajorGC = GC.Impl
module SpecGCPost = GC.Spec.Correctness
module Mark = GC.Spec.Mark

/// ---------------------------------------------------------------------------
/// Combined generational heap state
/// ---------------------------------------------------------------------------

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
/// Minor collection (Cheney BFS: promote reachable + update pointers + reset)
/// ---------------------------------------------------------------------------

/// Trigger a minor collection using Cheney-style BFS:
/// 1. Forward roots (promote reachable minor objects on discovery)
/// 2. BFS scan: for each promoted object, forward its children
/// 3. Update major-heap pointer fields (rewrite minor refs via fwd map)
/// 4. Rewrite program roots
/// 5. Reset minor heap (bump = 0)
///
/// Postcondition: result matches cheney_collect_spec (promotes only reachable
/// objects, not all objects — sound and precise).
///
/// Correctness properties (proven in GC.Gen.CheneyCorrectness):
/// - All pre-existing major objects survive
/// - Heap well-formedness (part 1) preserved
/// - Minor heap reset
/// - Roots rewritten via forwarding map
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
                 Seq.length 'farr == UpdatePtrs.fwd_array_size /\
                 (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\
                 minor_wf ({ data = 'd; bump = 'b }) /\
                  minor_guards_complete ({ data = 'd; bump = 'b }) /\
                 Seq.length (SpecFields.objects 0UL 's) > 0)
  ensures exists* d2 b2 s2 fp2 rs2 farr2.
    is_gen_heap gh d2 b2 s2 fp2 **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pure (
      let minor_st : minor_state = { data = 'd; bump = 'b } in
      let res = CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs in
      let prom = CheneySpec.cheney_promote minor_st 's 'fp 'rs in
      // Spec refinement: result matches the Cheney BFS collection spec
      s2 == res.mc_major /\
      fp2 == res.mc_fp /\
      rs2 == res.mc_roots /\
      U64.v b2 == 0 /\
      // Object survival: pre-existing major objects survive collection
      (forall (x: obj_addr). Seq.mem x (SpecFields.objects 0UL 's) ==>
        Seq.mem x (SpecFields.objects 0UL s2)) /\
      // Root rewriting: roots rewritten via forwarding map
      rs2 == PromoteSpec.rewrite_roots 'rs prom.fwd_map /\
      // Structural invariants preserved
      SpecFields.well_formed_heap_part1 s2 /\
      AllocLemmas.fl_valid s2 fp2 (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates s2 fp2 (heap_size / U64.v mword))

/// ---------------------------------------------------------------------------
/// Full generational GC (minor collection + major collection)
/// ---------------------------------------------------------------------------

/// Full generational GC cycle:
/// 1. Minor collection (Cheney BFS): promote reachable minor objects to major
/// 2. Major collection (mark-and-sweep): reclaim unreachable major objects
///
/// Postcondition provides:
/// - Major GC correctness (5 pillars of mark-and-sweep) on post-minor heap
/// - Minor collection properties (roots rewritten, minor heap reset)
///
/// The caller must provide gc_precondition on the post-minor heap.
/// no_black_objects on the post-minor heap is derived internally from
/// no_black_objects on the pre-minor heap via cheney_collect_no_black.
fn gen_gc (gh: gen_heap_t)
          (roots: array U64.t) (nroots: SZ.t)
          (fwd_arr: array U64.t)
          (st: gray_stack)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           is_gray_stack st 'st **
           pure (
             // --- Minor collection preconditions ---
             SpecFields.well_formed_heap 's /\
             AllocLemmas.fl_valid 's 'fp (heap_size / U64.v mword) /\
             AllocLemmas.fl_chain_terminates 's 'fp (heap_size / U64.v mword) /\
             PromoteSpec.heap_objects_dense 's /\
             PromoteSpec.chain_objects_blue 's 'fp /\
             SZ.v nroots == Seq.length 'rs /\
             Seq.length 'farr == UpdatePtrs.fwd_array_size /\
             (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\
             minor_wf ({ data = 'd; bump = 'b }) /\
             minor_guards_complete ({ data = 'd; bump = 'b }) /\
             Seq.length (SpecFields.objects 0UL 's) > 0 /\
             Mark.no_black_objects 's /\
             // --- Major GC preconditions on post-minor heap ---
             (let res = CheneySpec.cheney_collect_spec
                          ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs in
              MajorGC.gc_precondition res.mc_major 'st res.mc_fp (stack_capacity st)))
  returns final_fp: U64.t
  ensures exists* d2 b2 s2 rs2 farr2 st2.
    is_gen_heap gh d2 b2 s2 final_fp **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    is_gray_stack st st2 **
    pure (
      let minor_st : minor_state = { data = 'd; bump = 'b } in
      let res = CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs in
      let prom = CheneySpec.cheney_promote minor_st 's 'fp 'rs in
      // Major GC correctness (post-minor → post-major)
      SpecGCPost.gc_postcondition s2 /\
      SpecGCPost.full_gc_correctness res.mc_major s2 'st /\
      // Minor collection properties
      rs2 == res.mc_roots /\
      rs2 == PromoteSpec.rewrite_roots 'rs prom.fwd_map /\
      U64.v b2 == 0 /\
      // Post-minor heap properties (from minor_collect correctness)
      (forall (x: obj_addr). Seq.mem x (SpecFields.objects 0UL 's) ==>
        Seq.mem x (SpecFields.objects 0UL res.mc_major)) /\
      SpecFields.well_formed_heap_part1 res.mc_major /\
      AllocLemmas.fl_valid res.mc_major res.mc_fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates res.mc_major res.mc_fp (heap_size / U64.v mword))
