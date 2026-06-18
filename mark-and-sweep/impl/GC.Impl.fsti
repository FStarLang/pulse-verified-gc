(*
   Pulse GC - Top-Level Module Interface

   Exports the collect entry point combining mark, sweep, and coalesce phases.
*)

module GC.Impl

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
open GC.Impl.Stack
module U64 = FStar.UInt64
module Seq = FStar.Seq
module SpecGCPost = GC.Spec.Correctness
module SpecMark = GC.Spec.Mark
module SpecMarkInv = GC.Spec.MarkInv
module SpecMarkBoundedInv = GC.Spec.MarkBoundedInv
module SpecSweep = GC.Spec.Sweep
module SpecCoalesce = GC.Spec.Coalesce
module SpecFields = GC.Spec.Fields
module SpecObject = GC.Spec.Object
module SpecAlloc = GC.Spec.Allocator
module AllocLemmas = GC.Spec.Allocator.Lemmas
module SI = GC.Spec.SweepInv
module SpecHeapModel = GC.Spec.HeapModel
module SpecHeapGraph = GC.Spec.HeapGraph
module SpecGraph = GC.Spec.Graph

/// Initialize the heap as one large free block.
///
/// Returns the initial free-list pointer (= mword = 8).
fn init_heap (heap: heap_t)
  requires is_heap heap 's
  returns fp: U64.t
  ensures exists* s2. is_heap heap s2 **
    pure ((s2, fp) == SpecAlloc.init_heap_spec 's)

/// Allocate an object of wosize words from the dense free list.
///
/// Returns `(new_fp, obj_addr)`, with `obj_addr = 0UL` on out-of-memory.
fn allocate (heap: heap_t) (fp: U64.t) (wosize: U64.t)
  requires is_heap heap 's **
           pure (SpecFields.well_formed_heap 's)
  returns res: (U64.t & U64.t)
  ensures exists* s2. is_heap heap s2 **
    pure (let spec_res = SpecAlloc.alloc_spec 's fp (U64.v wosize) in
          s2 == spec_res.heap_out /\
          fst res == spec_res.fp_out /\
          snd res == spec_res.obj_out)

/// Allocate with the weaker allocator-specific heap precondition used during
/// promotion, where pointer closure may be temporarily violated.
fn allocate_part1 (heap: heap_t) (fp: U64.t) (wosize: U64.t)
  requires is_heap heap 's **
           pure (SpecFields.well_formed_heap_part1 's /\
                 AllocLemmas.fl_valid 's fp (heap_size / U64.v mword) /\
                 AllocLemmas.fl_chain_terminates 's fp (heap_size / U64.v mword))
  returns res: (U64.t & U64.t)
  ensures exists* s2. is_heap heap s2 **
    pure (let spec_res = SpecAlloc.alloc_spec 's fp (U64.v wosize) in
          s2 == spec_res.heap_out /\
          fst res == spec_res.fp_out /\
          snd res == spec_res.obj_out)

/// Initialize an absolute-addressed major chunk as one blue free-list block.
/// This public helper has a ghost-free C ABI and is used by the OCaml bridge for
/// the current initial dense chunk while the authoritative chunked model remains
/// internal to verification.
fn init_major_chunk_raw (heap: heap_t)
                       (base: hp_addr)
                       (fp_out: obj_addr)
                       (wz: wosize)
                       (next_fp: U64.t)
  requires is_heap heap 's **
          pure (U64.v fp_out == U64.v base + U64.v mword)
  returns new_fp: U64.t
  ensures exists* s2. is_heap heap s2 **
    pure (let hdr = GC.Impl.Object.makeHeader wz GC.Impl.Object.blue 0UL in
          s2 == GC.Spec.Heap.write_word
                 (GC.Spec.Heap.write_word 's base hdr) fp_out next_fp /\
          new_fp == fp_out)

/// Verified arithmetic for the contiguous head block required before promotion.
fn major_preflight_required_head_wosize
  (demand_words: U64.t{U64.v demand_words < pow2 64 - 1})
  requires emp
  returns needed: U64.t
  ensures emp ** pure (needed == U64.add demand_words 1UL)

/// Convert an ensured head wosize to the fresh chunk word count that creates it.
fn major_preflight_required_chunk_words
  (head_wosize: U64.t{U64.v head_wosize < pow2 64 - 1})
  requires emp
  returns words: U64.t
  ensures emp ** pure (words == U64.add head_wosize 1UL)

/// Check whether the current free-list head has the required contiguous space.
fn major_preflight_head_ready
  (head_wosize required_head_wosize: U64.t)
  requires emp
  returns ready: bool
  ensures emp ** pure (ready <==> U64.v head_wosize >= U64.v required_head_wosize)

/// Convert a chunk word count into the free-block header wosize it creates.
fn major_chunk_words_to_wosize
  (chunk_words: U64.t{U64.v chunk_words > 0 /\ U64.v chunk_words <= pow2 54})
  requires emp
  returns wz: wosize
  ensures emp ** pure (wz == U64.sub chunk_words 1UL)

/// Convert an object payload wosize to its header-inclusive word count.
fn object_words_for_wosize
  (wosize: U64.t{U64.v wosize < pow2 64 - 1})
  requires emp
  returns words: U64.t
  ensures emp ** pure (words == U64.add wosize 1UL)

/// Extract an OCaml header's wosize field.
fn major_header_wosize
  (header: U64.t)
  requires emp
  returns wz: wosize
  ensures emp ** pure (wz == getWosize header)

/// Check the concrete runtime chunk-word range needed for OCaml headers.
fn major_chunk_words_in_header_range
  (chunk_words: U64.t)
  requires emp
  returns ok: bool
  ensures emp ** pure (ok <==> (U64.v chunk_words >= 2 /\ U64.v chunk_words <= pow2 54))

/// Convert a major chunk word count to bytes after the runtime overflow check.
fn major_chunk_words_to_bytes
  (chunk_words: U64.t{U64.v chunk_words <= 2305843009213693951})
  requires emp
  returns bytes: U64.t
  ensures emp ** pure (bytes == U64.mul chunk_words mword)

/// Convert a tracked major byte count back to words.
fn major_bytes_to_words
  (bytes: U64.t)
  requires emp
  returns words: U64.t
  ensures emp ** pure (words == U64.div bytes mword)

/// Check whether a reserved arena has enough inactive bytes for an expansion.
fn major_arena_has_available_bytes
  (active_bytes reserved_bytes requested_bytes: U64.t)
  requires emp
  returns ok: bool
  ensures emp ** pure (
    ok <==> (U64.v active_bytes <= U64.v reserved_bytes /\
             U64.v requested_bytes <= U64.v reserved_bytes - U64.v active_bytes))

/// Compute the first free-list object pointer for a freshly formatted chunk.
fn major_chunk_initial_fp
  (base: U64.t{U64.v base + U64.v mword < pow2 64})
  requires emp
  returns fp: U64.t
  ensures emp ** pure (fp == U64.add base mword)

/// Select the configured expansion size unless the verified minimum is larger.
fn major_preflight_planned_chunk_words
  (configured_words required_chunk_words: U64.t)
  requires emp
  returns words: U64.t
  ensures emp ** pure (
    (U64.v configured_words >= U64.v required_chunk_words ==> words == configured_words) /\
    (U64.v configured_words < U64.v required_chunk_words ==> words == required_chunk_words))

/// Normalize a direct major-allocation request to the allocator demand wosize.
fn major_allocation_demand_wosize
  (requested_wosize: U64.t)
  requires emp
  returns wz: U64.t
  ensures emp ** pure (
    U64.v wz > 0 /\
    U64.v wz == SpecAlloc.normalized_wosize (U64.v requested_wosize))

/// Check whether two half-open runtime address ranges overlap.
fn major_ranges_overlap
  (start range_end other_start other_end: U64.t)
  requires emp
  returns overlap: bool
  ensures emp ** pure (
    overlap <==> (U64.v start < U64.v other_end /\ U64.v other_start < U64.v range_end))

/// Check whether a runtime byte address or size is word-aligned.
fn major_word_aligned
  (value: U64.t)
  requires emp
  returns aligned: bool
  ensures emp ** pure (aligned <==> (U64.v value % U64.v mword == 0))

/// Check the verified virtual major-heap end bound (`heap_size < 2^57`).
fn major_heap_end_below_verified_limit
  (heap_end: U64.t)
  requires emp
  returns ok: bool
  ensures emp ** pure (ok <==> U64.v heap_end < pow2 57)

/// Check whether adding one machine word to an address stays below `2^64`.
fn major_address_has_word_room
  (addr: U64.t)
  requires emp
  returns ok: bool
  ensures emp ** pure (ok <==> U64.v addr + U64.v mword < pow2 64)

/// Check whether a nonzero free-list pointer lies in the current major range.
fn major_free_head_in_range
  (zero: U64.t{U64.v zero + U64.v mword < pow2 64})
  (heap_end fp: U64.t)
  requires emp
  returns ok: bool
  ensures emp ** pure (
    ok <==> (U64.v fp >= U64.v zero + U64.v mword /\ U64.v fp < U64.v heap_end))

/// Compute the header address for a nonzero free-list object pointer.
fn major_free_head_header_addr
  (fp: U64.t{U64.v fp >= U64.v mword})
  requires emp
  returns header: U64.t
  ensures emp ** pure (header == U64.sub fp mword)

/// Diagnostic retry suggestion: saturating-double current words, then meet the
/// verified minimum fresh chunk size.
fn major_preflight_suggested_major_words
  (current_words required_chunk_words: U64.t)
  requires emp
  returns words: U64.t
  ensures emp ** pure (
    let half = 9223372036854775807UL in
    let max_u64 = 18446744073709551615UL in
    let doubled: U64.t =
      if U64.gt current_words half then
        max_u64
      else
        U64.mul_underspec current_words 2UL in
    (U64.v doubled >= U64.v required_chunk_words ==> words == doubled) /\
    (U64.v doubled < U64.v required_chunk_words ==> words == required_chunk_words))

/// Precondition bundle for full GC correctness (bounded mark variant).
/// The concrete gray stack may be a bounded worklist approximation of the
/// ghost root set used for correctness.
let gc_precondition_with_roots
    (s: GC.Spec.Base.heap) (st roots: Seq.seq GC.Spec.Base.obj_addr)
    (fp: U64.t) (cap: nat) : prop =
  SpecMarkBoundedInv.bounded_mark_inv s st cap /\
  SI.fp_valid fp s /\
  SpecMark.root_props s roots /\
  SpecSweep.fp_in_heap fp s /\
  SpecMark.no_black_objects s /\
  SpecMark.no_pointer_to_blue s /\
  SpecFields.no_scan_invariant s /\
  (forall (x: GC.Spec.Base.obj_addr). Seq.mem x (SpecFields.objects GC.Spec.Base.zero_addr s) /\
    (GC.Spec.Object.is_gray x s \/ GC.Spec.Object.is_black x s) ==> Seq.mem x roots) /\
  (let graph = SpecHeapModel.create_graph s in
   let roots' = SpecHeapGraph.coerce_to_vertex_list roots in
   SpecGraph.graph_wf graph /\ SpecGraph.is_vertex_set roots' /\
   SpecGraph.subset_vertices roots' graph.vertices)

let gc_precondition (s: GC.Spec.Base.heap) (st: Seq.seq GC.Spec.Base.obj_addr)
                    (fp: U64.t) (cap: nat) : prop =
  gc_precondition_with_roots s st st fp cap

/// Main garbage collection entry point with an explicit ghost root set.
fn collect_with_roots
    (heap: heap_t) (st: gray_stack)
    (roots: Ghost.erased (Seq.seq GC.Spec.Base.obj_addr)) (fp: U64.t)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (gc_precondition_with_roots 's 'st roots fp (stack_capacity st))
  returns final_fp: U64.t
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
          pure (SpecGCPost.gc_postcondition s2 /\
                SpecGCPost.full_gc_correctness 's s2 roots /\
                SpecGCPost.major_gc_live_subgraph_isomorphism 's s2 roots /\
                SpecGCPost.major_gc_unreachable_final_blue 's s2 roots)

/// Main garbage collection entry point
/// 1. Mark: bounded-stack mark with overflow handling
/// 2. Sweep: reset black objects to white, build free list
/// 3. Coalesce: merge adjacent free blocks
fn collect (heap: heap_t) (st: gray_stack) (fp: U64.t)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (gc_precondition 's 'st fp (stack_capacity st))
  returns final_fp: U64.t
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
          pure (SpecGCPost.gc_postcondition s2 /\
                SpecGCPost.full_gc_correctness 's s2 'st /\
                SpecGCPost.major_gc_live_subgraph_isomorphism 's s2 'st /\
                SpecGCPost.major_gc_unreachable_final_blue 's s2 'st)
