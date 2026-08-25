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
module MarkBoundedImpl = GC.Impl.MarkBounded
module MBP = GC.Impl.MarkBoundedPrecondition
module GMP = GC.Gen.MajorPrecondition
module MarkBoundedInv = GC.Spec.MarkBoundedInv
module SpecGCPost = GC.Spec.Correctness
module Mark = GC.Spec.Mark
module Cheney = GC.Gen.Impl.Cheney
module GenInv = GC.Gen.HeapInvariant
module MinorFwd = GC.Gen.MinorCollectForwarding
module RBridge = GC.Gen.ReachabilityBridge
module CheneyBFS = GC.Gen.CheneyBFS
module SpecHeapModel = GC.Spec.HeapModel
module MRT = GC.Gen.MajorReachabilityTransfer

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

let roots_match_stack (roots: Seq.seq U64.t) (st: Seq.seq obj_addr) : prop =
  (forall (r: U64.t). Seq.mem r roots ==> GC.Spec.Base.is_val_addr r) /\
  (forall (r: obj_addr). Seq.mem (r <: U64.t) roots ==> Seq.mem r st) /\
  (forall (r: obj_addr). Seq.mem r st ==> Seq.mem (r <: U64.t) roots)

let roots_match_stack_root_is_val_addr
  (roots: Seq.seq U64.t) (st: Seq.seq obj_addr) (r: U64.t)
  : Lemma
      (requires roots_match_stack roots st /\ Seq.mem r roots)
      (ensures is_val_addr r)
  = ()

let roots_match_stack_root_in_stack
  (roots: Seq.seq U64.t) (st: Seq.seq obj_addr) (r: obj_addr)
  : Lemma
      (requires roots_match_stack roots st /\ Seq.mem (r <: U64.t) roots)
      (ensures Seq.mem r st)
  = ()

let gen_gc_prepared_state
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  (st: Seq.seq obj_addr) (cap: nat) : GTot (heap & Seq.seq obj_addr) =
  let result = CheneySpec.cheney_collect_spec minor major fp roots in
  MarkBoundedImpl.darken_roots_bounded_spec result.mc_major st result.mc_roots cap

let gen_gc_prepared_major
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  (st: Seq.seq obj_addr) (cap: nat) : GTot heap =
  fst (gen_gc_prepared_state minor major fp roots st cap)

let gen_gc_prepared_roots
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  (st: Seq.seq obj_addr) (cap: nat) : GTot (Seq.seq obj_addr) =
  snd (gen_gc_prepared_state minor major fp roots st cap)

/// What the caller owes the collector about the gray stack it supplies.
///
/// This is the whole of it.  There is no heap in the statement: the major
/// phase's entry condition is derived internally by `GC.Gen.MajorPrecondition`
/// from `collection_heap_shape`, `roots_valid_for_minor_collection` and the
/// *runtime* success flag of the minor collection.
///
///  * `Seq.length st == 0` -- the gray stack starts empty.  It is collector
///    scratch space, not caller state, and both real clients pass an empty one.
///  * `Seq.length roots <= cap` -- darkening pushes every root, so the stack has
///    to be able to hold them.  This is the only sizing obligation.
///  * `cap > 0` rules out a zero-capacity stack.
///
/// In particular the caller does *not* have to establish `cheney_no_oom`.  An
/// earlier version did require it, which was indefensible: it is a statement
/// about the outcome of the entire Cheney BFS, no caller can discharge it, and
/// `gen_gc` reports promotion failure through its `ok` result anyway.  `gen_gc`
/// now consumes the runtime flag instead and simply skips the major phase when
/// the minor collection ran out of memory.
let gen_gc_stack_budget
  (roots: Seq.seq U64.t) (st: Seq.seq obj_addr) (cap: nat) : prop =
  Seq.length st == 0 /\
  Seq.length roots <= cap /\
  cap > 0

/// Everything the major phase needs, from pre-minor shape facts plus the
/// minor collection's own success flag.
val gen_gc_major_precondition_elim
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  (st: Seq.seq obj_addr) (cap: nat)
  : Lemma
      (requires
        GenInv.collection_heap_shape minor major fp /\
        MinorFwd.roots_valid_for_minor_collection minor major roots /\
        CheneyBFS.cheney_no_oom minor major fp roots /\
        gen_gc_stack_budget roots st cap)
      (ensures
        (let result = CheneySpec.cheney_collect_spec minor major fp roots in
         let prepared = gen_gc_prepared_state minor major fp roots st cap in
         MajorGC.gc_precondition_with_roots
           (fst prepared) (snd prepared) (snd prepared) result.mc_fp cap /\
         roots_match_stack result.mc_roots (snd prepared) /\
         SpecHeapModel.create_graph (fst prepared) ==
           SpecHeapModel.create_graph result.mc_major))

/// The roots array contains exactly the post-minor roots used by the following
/// major collection.
/// The array is rewritten by the minor collection unconditionally; the match
/// with the darkened mark stack only holds on the path where the major phase
/// actually ran.
let gen_gc_roots_post
  (minor: minor_state) (major: heap) (fp: U64.t) (roots roots_out: Seq.seq U64.t)
  (ok: bool) (st: Seq.seq obj_addr) (cap: nat) : prop =
  let result = CheneySpec.cheney_collect_spec minor major fp roots in
  roots_out == result.mc_roots /\
  (ok ==>
   roots_match_stack roots_out (gen_gc_prepared_roots minor major fp roots st cap))

/// Shape facts exposed by the abstract `gen_gc` contract: the nursery is reset,
/// the final major heap satisfies the major GC postcondition, and the post-minor
/// heap has the full shape needed by the major phase.
let gen_gc_heap_shape_post
  (minor_data: minor_heap) (minor_bump: U64.t)
  (final_major: heap) : prop =
  U64.v minor_bump == 0 /\
  SpecGCPost.gc_postcondition final_major /\
  SpecFields.blue_fields_non_infix final_major

/// **The collector restores its own precondition.**
///
/// `gen_gc` demands `GenInv.collection_heap_shape` of the heap it is handed.
/// This says it hands back a heap satisfying the same predicate, so a runtime
/// driving an unbounded sequence of collections establishes the invariant once,
/// at start-up, and never again.
///
/// The minor half is vacuous -- the nursery `gen_gc` returns is
/// `GC.Gen.MinorHeap.minor_reset`, i.e. zeroed -- so the content of the claim is
/// `GC.Gen.HeapInvariant.major_heap_shape` of the major heap and free-list head,
/// all fifteen conjuncts of it, which is what
/// `GC.Gen.PostCollectionShape.major_gc_restores_major_heap_shape` supplies.
let gen_gc_shape_restored_post
  (minor_data: minor_heap) (minor_bump: U64.t)
  (final_major: heap) (final_fp: U64.t) : prop =
  GenInv.collection_heap_shape
    ({ data = minor_data; bump = minor_bump } <: minor_state) final_major final_fp

/// Reachable subgraph correctness.
///
/// The headline conjunct is a *single* isomorphism between the reachable
/// subgraph of the heap `gen_gc` was handed and the reachable subgraph of the
/// heap it returns, with the minor collector's forwarding map as the morphism.
/// Earlier versions exposed only the two halves -- minor collection into the
/// post-minor heap, then major collection out of the post-darkening heap --
/// and left the caller to chain them.  That was not something a caller could
/// actually do: the halves are stated in different vocabularies, root darkening
/// sits between them, and transferring reachability backwards out of the final
/// heap needs the major collector's successor-preservation clause.  All of that
/// is now discharged once, inside `GC.Gen.MajorReachabilityTransfer`.
///
/// The two intermediate facts are kept because they say things the composition
/// cannot: the minor step says *where* each surviving object went, and the
/// major step says the survivors did not move again and are white.
let gen_gc_reachable_subgraph_isomorphism_post
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  (ok: bool) (final_major: heap) (roots_out: Seq.seq U64.t)
  (st: Seq.seq obj_addr) (cap: nat) : prop =
  let result = CheneySpec.cheney_collect_spec minor major fp roots in
  let prepared = gen_gc_prepared_state minor major fp roots st cap in
  (ok ==>
   MRT.end_to_end_isomorphism minor major fp roots final_major roots_out /\
   MinorFwd.normal_result_reachable_subgraph_isomorphism_prop
     minor major fp roots result.mc_major roots_out /\
   MinorFwd.normal_result_non_pointer_fields_preserved_prop
     minor major fp roots result.mc_major /\
   SpecGCPost.major_gc_live_subgraph_isomorphism
     (fst prepared) final_major (snd prepared))

/// Collection completeness: every object that remains in the final major heap
/// but is not reachable from the final roots is blue.
/// Only the sweep makes unreachable objects blue, so this is guarded on `ok`:
/// on the out-of-memory path the returned heap is the (unswept) post-minor heap.
let gen_gc_unreachable_final_blue_post
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  (ok: bool) (final_major: heap) (st: Seq.seq obj_addr) (cap: nat) : prop =
  let prepared = gen_gc_prepared_state minor major fp roots st cap in
  ok ==>
  SpecGCPost.major_gc_unreachable_final_blue (fst prepared) final_major (snd prepared)

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
///
/// The remaining reachability/validity preconditions state that `roots` is the
/// complete valid minor-collection root set for the supplied remembered table.
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
                  UpdatePtrs.slots_pairwise_distinct 'sl (SZ.v nslots) /\
                  MinorFwd.remembered_targets_in_roots 's 'rs 'sl (SZ.v nslots) /\
                  MinorFwd.roots_valid_for_minor_collection
                    ({ data = 'd; bump = 'b } <: minor_state) 's 'rs)
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
      // Minor heap fully reset: the nursery bytes are cleared as well as the
      // bump pointer, so the state handed back is literally
      // `GC.Gen.MinorHeap.minor_reset`.  That is what makes every minor-side
      // and cross-generation conjunct of `collection_heap_shape` vacuous for
      // the collector's output.
      U64.v b2 == 0 /\
      ({ data = d2; bump = b2 } <: minor_state) ==
        minor_reset ({ data = 'd; bump = 'b } <: minor_state) /\
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
      // If promotion succeeds, minor collection is a concrete reachable
      // subgraph isomorphism over the actual post-minor heap graph.
      (not ok ==> CheneyBFS.cheney_oom minor_st 's 'fp 'rs) /\
      (ok ==>
       CheneyBFS.cheney_no_oom minor_st 's 'fp 'rs /\
       MinorFwd.normal_result_reachable_subgraph_isomorphism_prop
         minor_st 's 'fp 'rs s2 rs2 /\
        MinorFwd.normal_result_non_pointer_fields_preserved_prop
         minor_st 's 'fp 'rs s2))

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
              let minor_st : minor_state = { data = 'd; bump = 'b } in
              // Shape of the heap the caller hands in.  Everything the major
              // phase needs about the *post*-minor heap is derived from this
              // internally, by `GC.Gen.MajorPrecondition`.
              GenInv.collection_heap_shape minor_st 's 'fp /\
              // `Seq.length 'st <= stack_capacity st` is not restated here: it
              // is recoverable from `is_gray_stack` via `Stack.stack_facts`.
              gen_gc_stack_budget 'rs 'st (stack_capacity st) /\

               // Operational array preconditions.
               SZ.v nroots == Seq.length 'rs /\
               Seq.length 'farr == UpdatePtrs.fwd_array_size /\
               (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\
               UpdatePtrs.ref_table_sound 's 'sl (SZ.v nslots) /\
               UpdatePtrs.ref_table_covers_minor_ptrs 's 'sl (SZ.v nslots) /\
               UpdatePtrs.slots_pairwise_distinct 'sl (SZ.v nslots) /\
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
      let result = CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs in
      let ok = snd res in
      // Failure is reported only for a concrete out-of-memory event: an object
      // the major free list had no room for, at a point of this collection.
      (not ok ==> CheneyBFS.cheney_oom minor_st 's 'fp 'rs) /\
      gen_gc_roots_post minor_st 's 'fp 'rs rs2 ok 'st (stack_capacity st) /\
      gen_gc_heap_shape_post d2 b2 s2 /\
      gen_gc_shape_restored_post d2 b2 s2 (fst res) /\
      gen_gc_reachable_subgraph_isomorphism_post
        minor_st 's 'fp 'rs ok s2 rs2 'st (stack_capacity st) /\
      gen_gc_unreachable_final_blue_post
        minor_st 's 'fp 'rs ok s2 'st (stack_capacity st))
