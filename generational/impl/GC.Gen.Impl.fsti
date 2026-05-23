(*
   Pulse GC (Generational) - Top-Level Entry Point Interface

   Provides:
   - gen_alloc: Allocate an object (routes to minor or major by size)
    - minor_collect_full: full Cheney minor collection with ref_table rewriting
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
module Cheney = GC.Gen.Impl.Cheney
module GenInv = GC.Gen.HeapInvariant
module MinorFwd = GC.Gen.MinorCollectForwarding

/// ---------------------------------------------------------------------------
/// Combined generational heap state
/// ---------------------------------------------------------------------------

noeq
type gen_heap_t = {
  minor : minor_heap_t;
  major : heap_t;
  fp_ref : R.ref U64.t;    // major heap free-list head
}

/// Combined slprop for the generational heap:
///   is_minor — ownership of minor heap array + bump pointer
///   is_heap  — ownership of major heap array
///   R.pts_to — ownership of the free-list head reference
let is_gen_heap (gh: gen_heap_t) (d: minor_heap) (b: U64.t)
                (s: heap_state) (fp: U64.t) : slprop =
  is_minor gh.minor d b **
  is_heap gh.major s **
  R.pts_to gh.fp_ref fp

[@@"opaque_to_smt"]
let minor_heap_no_scan_invariant (d: minor_heap) (b: U64.t) : prop =
  PromoteSpec.minor_no_scan_invariant ({ data = d; bump = b })

/// ---------------------------------------------------------------------------
/// Allocation
/// ---------------------------------------------------------------------------

/// Allocate an object. Small objects go to minor heap, large ones to major.
/// Returns 0UL on failure (both heaps full).
fn gen_alloc (gh: gen_heap_t) (wosize: U64.t) (tag: U64.t)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pure (
             // Object body size is at least 1 word (no zero-length objects)
             U64.v wosize > 0 /\
             // Tag fits in the 8-bit OCaml header field (0..255)
             U64.v tag < 256 /\
             // Major heap has valid OCaml object layout: headers have valid
             // wosize/color/tag, objects don't overlap, sizes fit within
             // heap bounds, pointer fields target valid objects, and infix
             // structure is correct
             SpecFields.well_formed_heap 's)
  returns obj: U64.t
  // Heap ownership is returned; internal state may change (bump pointer
  // advanced, or a free-list node consumed)
  ensures exists* d2 b2 s2 fp2. is_gen_heap gh d2 b2 s2 fp2

/// ---------------------------------------------------------------------------
/// Full minor collection with ref_table (full correctness)
/// ---------------------------------------------------------------------------

/// Full minor collection with a ref_table of major-heap field addresses holding
/// minor pointers. Rewrites both promoted-object fields and existing major slots,
/// proving full cheney_collect_spec correctness.
///
/// The ref_table comes from the write barrier: it records addresses of existing
/// major-heap fields that were assigned minor-heap pointers. Combined with
/// update_promoted_objects (which handles newly promoted objects), this covers
/// all minor pointers in the major heap.
///
/// The caller states this as a pre-promotion remembered-set property
/// (`ref_table_covers_minor_ptrs`); the implementation derives the
/// forwarding-map-specific `ref_table_complete` fact after computing Cheney's
/// promotion map.
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
            pure (GenInv.collection_heap_shape
                    ({ data = 'd; bump = 'b } <: minor_state) 's 'fp /\
                  SZ.v nroots == Seq.length 'rs /\
                  Seq.length 'farr == UpdatePtrs.fwd_array_size /\
                  (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\
                  UpdatePtrs.ref_table_sound 's 'sl (SZ.v nslots) /\
                  UpdatePtrs.ref_table_covers_minor_ptrs 's 'sl (SZ.v nslots) /\
                  UpdatePtrs.slots_pairwise_distinct 'sl (SZ.v nslots))
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
      s2 == UpdatePtrs.rewrite_slots_iter
              (UpdatePtrs.update_promoted_iter prom.major_final farr2 prom.fwd_map 0)
              prom.fwd_map 'sl (SZ.v nslots) 0 /\
      // Free pointer from promotion phase
      fp2 == prom.fp_final /\
      // Roots rewritten via forwarding map
      rs2 == PromoteSpec.rewrite_roots 'rs prom.fwd_map /\
      // Minor heap fully reset
      U64.v b2 == 0 /\
      // Forwarding array represents the spec-level forwarding map
      UpdatePtrs.represents_fwd farr2 prom.fwd_map /\
      // Forwarding entries are valid
      UpdatePtrs.valid_fwd_entries farr2 /\
      Seq.length farr2 == UpdatePtrs.fwd_array_size /\
      // Well-formedness preserved through promotion
      SpecFields.well_formed_heap_part1 prom.major_final /\
      // Strong correctness: the result equals cheney_collect_spec
      // (single-pass full update of all pointer fields in the major heap).
      s2 == (CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs).mc_major /\
      GenInv.collection_heap_shape ({ data = d2; bump = b2 } <: minor_state) s2 fp2 /\
      MinorFwd.minor_collect_full_forwarding_kernel
        minor_st 's 'fp 'rs 'sl (SZ.v nslots) ok s2 rs2)

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
/// - The post-minor `GenInv.full_heap_shape` used to justify the major GC call
///
/// The caller provides full heap shape plus the remembered-set table needed by
/// `minor_collect_full`. The implementation derives the post-minor major-GC
/// precondition before invoking mark-and-sweep.
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
              // Full heap shape: major layout/free-list/colors, minor layout,
              // cross-generation no-blue fields, and stack-coupled major-GC
              // preconditions.
              GenInv.full_heap_shape
                ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'st
                (stack_capacity st) /\

               // Operational array preconditions.
               SZ.v nroots == Seq.length 'rs /\
               Seq.length 'farr == UpdatePtrs.fwd_array_size /\
               (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\
               UpdatePtrs.ref_table_sound 's 'sl (SZ.v nslots) /\
               UpdatePtrs.ref_table_covers_minor_ptrs 's 'sl (SZ.v nslots) /\
               UpdatePtrs.slots_pairwise_distinct 'sl (SZ.v nslots))
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
      let result = CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs in
      let prom = CheneySpec.cheney_promote minor_st 's 'fp 'rs in

      // --- Major GC correctness (applied to the post-minor heap) ---

      // Post-GC heap is well-formed AND every object is white or blue
      // (no gray or black objects remain — marking is complete and
      // colors have been reset by sweep)
      SpecGCPost.gc_postcondition s2 /\

      // Full mark-and-sweep correctness theorem (5 pillars):
      //   1. well_formed_heap preserved through mark+sweep
      //   2. Reachability-based survival: objects reachable from roots
      //      in the post-minor heap survive sweep
      //   3. Successor preservation: surviving objects' pointer fields
      //      still point to surviving objects
      //   4. Color reset: all objects are white or blue after sweep
      //   5. Field data preservation: non-color header bits and object
      //      body data are unchanged by mark+sweep
      // Here result.mc_major is the post-minor heap (input to mark-sweep),
      // s2 is the final post-sweep heap, and 'st is the gray stack
      // contents (roots for the major GC)
      SpecGCPost.full_gc_correctness result.mc_major s2 'st /\

      // --- Minor collection properties ---

      // Roots match the Cheney spec's output
      rs2 == result.mc_roots /\

      // Roots have been pointwise rewritten through the forwarding map:
      // minor-heap pointers now point to promoted copies in major heap
      rs2 == PromoteSpec.rewrite_roots 'rs prom.fwd_map /\

      // Minor heap has been fully reset (bump = 0)
      U64.v b2 == 0 /\

      // The post-minor heap satisfies the full invariant needed for the
      // immediately following major collection.
      GenInv.full_heap_shape
        ({ data = d2; bump = b2 } <: minor_state) result.mc_major result.mc_fp
        'st (stack_capacity st) /\

      // --- Post-minor heap properties (proven by minor_collect_full) ---

      // Pre-existing major-heap objects survive minor collection
      // (promotion only adds, never removes)
      (forall (x: obj_addr). Seq.mem x (SpecFields.objects zero_addr 's) ==>
        Seq.mem x (SpecFields.objects zero_addr result.mc_major)) /\

      // Post-minor heap satisfies size-bounds invariant
      SpecFields.well_formed_heap_part1 result.mc_major)
