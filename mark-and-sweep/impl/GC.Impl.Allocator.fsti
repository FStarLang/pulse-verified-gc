(*
   Pulse GC - Allocator Module Interface

   First-fit free-list allocator for the verified GC.
   Takes the heap and current free-list head, returns updated heap
   and new free-list head along with the allocated object address.
*)

module GC.Impl.Allocator

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
module U64 = FStar.UInt64
module Seq = FStar.Seq
module MH = GC.Spec.MajorHeap
module SpecAlloc = GC.Spec.Allocator
module SpecMajorAlloc = GC.Spec.MajorAllocator
module SpecFields = GC.Spec.Fields
module SpecObject = GC.Spec.Object
module SI = GC.Spec.SweepInv
module AllocLemmas = GC.Spec.Allocator.Lemmas
module MajorHeap = GC.Impl.MajorHeap

/// Allocate an object of wosize words from the free list.
///
/// Parameters:
///   heap: mutable heap array
///   fp: current free-list head (obj_addr of first free block, or 0UL)
///   wosize: number of words needed (bumped to 1 if 0)
///
/// Returns: (new_fp, obj_addr)
///   new_fp: updated free-list head
///   obj_addr: allocated object address, or 0UL if out of memory
///
/// Postcondition ties the result to the pure spec alloc_spec.
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
///
/// The implementation is identical to `allocate` — the allocator only reads
/// headers and free-list links, never inspecting object pointer fields.

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

/// Initialize an already-owned fresh chunk as one blue free-list block.
fn init_fresh_chunk_owned (heap: MajorHeap.major_heap_t)
                          (base: hp_addr) (fp_out: obj_addr)
                          (wz: wosize) (next_fp: U64.t)
                          (#fresh: Ghost.erased
                            (c:MH.heap_chunk{c.base == base /\
                                             fp_out == SpecMajorAlloc.fresh_chunk_object c /\
                                             U64.v wz == SpecMajorAlloc.fresh_chunk_wosize c}))
  requires MajorHeap.chunk_range heap (Ghost.reveal fresh)
  ensures MajorHeap.chunk_range heap
            (SpecMajorAlloc.init_fresh_chunk (Ghost.reveal fresh) next_fp).chunk_out

/// Initialize and prepend a fresh chunk, returning the new free-list head.
fn expand_major_heap_owned (heap: MajorHeap.major_heap_t)
                           (base: hp_addr) (fp_out: obj_addr)
                           (wz: wosize) (next_fp: U64.t)
                           (#mh: Ghost.erased MH.major_heap)
                           (#fresh: Ghost.erased
                             (c:MH.heap_chunk{c.base == base /\
                                              fp_out == SpecMajorAlloc.fresh_chunk_object c /\
                                              U64.v wz == SpecMajorAlloc.fresh_chunk_wosize c}))
  requires MajorHeap.chunk_range heap (Ghost.reveal fresh) **
           MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (MH.chunk_disjoint_from_all (Ghost.reveal fresh) (Ghost.reveal mh))
  returns new_fp: U64.t
  ensures MajorHeap.is_indexed_major_heap heap
            (SpecMajorAlloc.expand_major_heap
              (Ghost.reveal mh) (Ghost.reveal fresh) next_fp).major_out **
          pure (new_fp ==
            (SpecMajorAlloc.expand_major_heap
              (Ghost.reveal mh) (Ghost.reveal fresh) next_fp).fp_out)

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
