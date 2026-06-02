(*
   Pulse GC - Allocator Module Interface

   Public dense-heap allocation entry points plus single-chunk compatibility
   wrappers used during the chunked-major migration.  General chunked-major
   allocation/expansion helpers are intentionally implementation-private until
   mark, sweep, and the generational collector own chunked major heaps end to end.
*)

module GC.Impl.Allocator

#lang-pulse

#set-options "--split_queries always"

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
module U64 = FStar.UInt64
module MH = GC.Spec.MajorHeap
module SpecAlloc = GC.Spec.Allocator
module SpecMajorAlloc = GC.Spec.MajorAllocator
module SpecFields = GC.Spec.Fields
module AllocLemmas = GC.Spec.Allocator.Lemmas
module MajorHeap = GC.Impl.MajorHeap

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

/// Compatibility entry point for callers that already own the major heap through
/// the indexed chunk predicate, but are still in the single-chunk migration path.
fn allocate_single_indexed_major (heap: heap_t) (fp: U64.t) (wosize: U64.t)
  requires MajorHeap.inactive_prefix (MajorHeap.heap_as_major heap) 's **
           MajorHeap.is_indexed_major_heap
             (MajorHeap.heap_as_major heap)
             (MH.single_chunk_major_heap 's) **
           pure (SpecFields.well_formed_heap 's)
  returns res: (U64.t & U64.t)
  ensures exists* s2.
    MajorHeap.inactive_prefix (MajorHeap.heap_as_major heap) s2 **
    MajorHeap.is_indexed_major_heap
      (MajorHeap.heap_as_major heap)
      (MH.single_chunk_major_heap s2) **
    pure (let spec_res =
            SpecMajorAlloc.major_alloc_spec_with_fuel
              (MH.single_chunk_major_heap 's) fp (U64.v wosize)
              SpecAlloc.alloc_search_fuel in
          let dense_res = SpecAlloc.alloc_spec 's fp (U64.v wosize) in
          s2 == dense_res.heap_out /\
          fst res == dense_res.fp_out /\
          snd res == dense_res.obj_out /\
          MH.single_chunk_major_heap s2 == spec_res.major_alloc_out /\
          fst res == spec_res.major_fp_out /\
          snd res == spec_res.major_obj_out)

/// Allocate with weaker precondition: only requires well_formed_heap_part1
/// + fl_valid + fl_chain_terminates. Suitable for use during promotion where
/// full well_formed_heap (part2: pointer closure) may be temporarily violated.
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

/// Single-chunk indexed-major compatibility entry point for promotion callers
/// that only maintain the allocator-specific part of the heap invariant.
fn allocate_part1_single_indexed_major (heap: heap_t) (fp: U64.t) (wosize: U64.t)
  requires MajorHeap.inactive_prefix (MajorHeap.heap_as_major heap) 's **
           MajorHeap.is_indexed_major_heap
             (MajorHeap.heap_as_major heap)
             (MH.single_chunk_major_heap 's) **
           pure (SpecFields.well_formed_heap_part1 's /\
                 AllocLemmas.fl_valid 's fp (heap_size / U64.v mword) /\
                 AllocLemmas.fl_chain_terminates 's fp (heap_size / U64.v mword))
  returns res: (U64.t & U64.t)
  ensures exists* s2.
    MajorHeap.inactive_prefix (MajorHeap.heap_as_major heap) s2 **
    MajorHeap.is_indexed_major_heap
      (MajorHeap.heap_as_major heap)
      (MH.single_chunk_major_heap s2) **
    pure (let spec_res =
            SpecMajorAlloc.major_alloc_spec_with_fuel
              (MH.single_chunk_major_heap 's) fp (U64.v wosize)
              SpecAlloc.alloc_search_fuel in
          let dense_res = SpecAlloc.alloc_spec 's fp (U64.v wosize) in
          s2 == dense_res.heap_out /\
          fst res == dense_res.fp_out /\
          snd res == dense_res.obj_out /\
          MH.single_chunk_major_heap s2 == spec_res.major_alloc_out /\
          fst res == spec_res.major_fp_out /\
          snd res == spec_res.major_obj_out)

/// Initialize the heap as one large free block.
///
/// The entire heap becomes a single blue object with wosize = (heap_size/8) - 1.
/// Its first field is set to 0 (end of free list).
///
/// Returns the initial free-list pointer (= mword = 8).
fn init_heap (heap: heap_t)
  requires is_heap heap 's
  returns fp: U64.t
  ensures exists* s2. is_heap heap s2 **
    pure ((s2, fp) == SpecAlloc.init_heap_spec 's)
