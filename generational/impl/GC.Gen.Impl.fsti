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
module Cheney = GC.Gen.Impl.Cheney

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
                 (queue: larray U64.t Cheney.queue_size)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           pure (
             // Major heap has valid OCaml object layout: every object's
             // header+body fits in the byte array, pointer fields target
             // valid objects, infix headers are well-formed, and no
             // spurious infix tags appear inside object bodies
             SpecFields.well_formed_heap 's /\

             // Free-list from 'fp consists of valid objects: each node is
             // a member of objects(0, major), has wosize >= 1, blue color,
             // and its first field (next pointer) links to another valid
             // node or terminates
             AllocLemmas.fl_valid 's 'fp (heap_size / U64.v mword) /\

             // Free-list traversal from 'fp terminates within
             // heap_size/mword steps (no cycles; the chain is finite)
             AllocLemmas.fl_chain_terminates 's 'fp (heap_size / U64.v mword) /\

             // Object walk is well-formed: stepping from any object's header
             // (at header + (1 + wosize) * 8 bytes) lands on another valid
             // object header. Both allocated and free-list nodes are objects,
             // so the heap is fully partitioned with no unaccounted bytes
             PromoteSpec.heap_objects_dense 's /\

             // Every allocated (non-blue) object is NOT on the free chain;
             // equivalently, the free chain only visits blue objects
             PromoteSpec.chain_objects_blue 's 'fp /\

             // nroots matches the actual root array length
             SZ.v nroots == Seq.length 'rs /\

             // Forwarding array has exactly fwd_array_size entries
             // (sized for the minor heap address range)
             Seq.length 'farr == UpdatePtrs.fwd_array_size /\

             // Forwarding array is zeroed: no stale forwarding entries
             // from a previous collection cycle
             (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\

             // Minor heap bump pointer is word-aligned, within
             // minor_heap_size, and the allocated prefix [0..bump)
             // forms a valid chain of OCaml objects
             minor_wf ({ data = 'd; bump = 'b }) /\

             // Guard completeness: any minor-heap address that passes
             // the runtime object-recognition checks (aligned, positive
             // wosize, fits before bump) is genuinely in the minor
             // object list — no false negatives when scanning
             minor_guards_complete ({ data = 'd; bump = 'b }) /\

             // Major heap contains at least one object (the initial
             // free-list sentinel; needed for free-list operations)
             Seq.length (SpecFields.objects zero_addr 's) > 0)
  ensures exists* d2 b2 s2 fp2 rs2 farr2 qv2.
    is_gen_heap gh d2 b2 s2 fp2 **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pure (
      let minor_st : minor_state = { data = 'd; bump = 'b } in
      let res = CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs in
      let prom = CheneySpec.cheney_promote minor_st 's 'fp 'rs in

      // --- Spec refinement ---
      // Post-collection major heap is exactly the Cheney BFS spec output:
      // BFS-promoted reachable minor objects, then pointer fields updated
      // to reflect forwarding
      s2 == res.mc_major /\

      // Post-collection free pointer matches spec (free-list head
      // advanced past all newly promoted objects)
      fp2 == res.mc_fp /\

      // Post-collection roots match spec output
      rs2 == res.mc_roots /\

      // Minor heap has been fully reset (bump pointer = 0, ready for
      // new allocations)
      U64.v b2 == 0 /\

      // --- Object survival ---
      // Every object that existed in the major heap before collection
      // still exists afterward; promotion only adds objects, never
      // removes existing ones
      (forall (x: obj_addr). Seq.mem x (SpecFields.objects zero_addr 's) ==>
        Seq.mem x (SpecFields.objects zero_addr s2)) /\

      // --- Root rewriting ---
      // Each root has been pointwise rewritten through the forwarding
      // map: roots pointing into the minor heap now point to the
      // promoted copy in the major heap; other roots are unchanged
      rs2 == PromoteSpec.rewrite_roots 'rs prom.fwd_map /\

      // --- Structural invariants preserved ---
      // Post-collection heap satisfies size-bounds invariant: every
      // object's header+body fits within the heap byte array
      SpecFields.well_formed_heap_part1 s2 /\

      // Post-collection free-list is valid (each node is a blue object
      // with wosize >= 1 and a valid next link)
      AllocLemmas.fl_valid s2 fp2 (heap_size / U64.v mword) /\

      // Post-collection free-list terminates (no cycles introduced
      // by promotion)
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
          (queue: larray U64.t Cheney.queue_size)
          (st: gray_stack)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           is_gray_stack st 'st **
           pure (
             // ============================
             // Minor collection preconditions
             // ============================

             // Major heap has valid OCaml object layout (see minor_collect)
             SpecFields.well_formed_heap 's /\

             // Free-list from 'fp is valid: each node is a blue object
             // with wosize >= 1 and a valid next link
             AllocLemmas.fl_valid 's 'fp (heap_size / U64.v mword) /\

             // Free-list from 'fp terminates within bounded steps
             AllocLemmas.fl_chain_terminates 's 'fp (heap_size / U64.v mword) /\

             // Object walk is well-formed: stepping header-to-header covers
             // the entire heap with no unaccounted bytes (both allocated
             // and free-list nodes are valid objects)
             PromoteSpec.heap_objects_dense 's /\

             // Free chain visits only blue objects (allocated objects
             // are not on the free list)
             PromoteSpec.chain_objects_blue 's 'fp /\

             // nroots matches root array length
             SZ.v nroots == Seq.length 'rs /\

             // Forwarding array is correctly sized for the minor
             // heap address range
             Seq.length 'farr == UpdatePtrs.fwd_array_size /\

             // Forwarding array is zeroed (clean slate for this cycle)
             (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\

             // Minor heap is well-formed: bump pointer aligned,
             // within bounds, allocated prefix is a valid object chain
             minor_wf ({ data = 'd; bump = 'b }) /\

             // Guard completeness for minor heap object recognition
             // (see minor_collect for details)
             minor_guards_complete ({ data = 'd; bump = 'b }) /\

             // Major heap has at least one object (free-list sentinel)
             Seq.length (SpecFields.objects zero_addr 's) > 0 /\

             // No major-heap object is black: the tri-color starting
             // state requires all objects to be white (allocated) or
             // blue (free) before any GC cycle begins
             Mark.no_black_objects 's /\

             // ============================
             // Major GC preconditions on the POST-minor-collection heap
             // ============================
             // These must hold on the heap state AFTER Cheney promotion,
             // since mark-and-sweep runs on that heap. The caller states
             // them in terms of cheney_collect_spec's output.
             // Includes: bounded_mark_inv (gray stack capacity sufficient),
             // fp_valid, root_props (roots are valid object addresses),
             // fp_in_heap, no_black_objects on post-minor heap,
             // no_pointer_to_blue (live objects don't point to free-list
             // nodes), no_scan_invariant (objects with tag >= 251 have
             // no pointer fields), gray/black objects are in the stack,
             // and graph well-formedness
             (let res = CheneySpec.cheney_collect_spec
                          ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs in
              MajorGC.gc_precondition res.mc_major 'st res.mc_fp (stack_capacity st)))
  returns final_fp: U64.t
  ensures exists* d2 b2 s2 rs2 farr2 qv2 st2.
    is_gen_heap gh d2 b2 s2 final_fp **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    is_gray_stack st st2 **
    pure (
      let minor_st : minor_state = { data = 'd; bump = 'b } in
      let res = CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs in
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
      // Here res.mc_major is the post-minor heap (input to mark-sweep),
      // s2 is the final post-sweep heap, and 'st is the gray stack
      // contents (roots for the major GC)
      SpecGCPost.full_gc_correctness res.mc_major s2 'st /\

      // --- Minor collection properties ---

      // Roots match the Cheney spec's output
      rs2 == res.mc_roots /\

      // Roots have been pointwise rewritten through the forwarding map:
      // minor-heap pointers now point to promoted copies in major heap
      rs2 == PromoteSpec.rewrite_roots 'rs prom.fwd_map /\

      // Minor heap has been fully reset (bump = 0)
      U64.v b2 == 0 /\

      // --- Post-minor heap properties (proven by minor_collect) ---

      // Pre-existing major-heap objects survive minor collection
      // (promotion only adds, never removes)
      (forall (x: obj_addr). Seq.mem x (SpecFields.objects zero_addr 's) ==>
        Seq.mem x (SpecFields.objects zero_addr res.mc_major)) /\

      // Post-minor heap satisfies size-bounds invariant
      SpecFields.well_formed_heap_part1 res.mc_major /\

      // Post-minor free-list is valid
      AllocLemmas.fl_valid res.mc_major res.mc_fp (heap_size / U64.v mword) /\

      // Post-minor free-list terminates
      AllocLemmas.fl_chain_terminates res.mc_major res.mc_fp (heap_size / U64.v mword))
