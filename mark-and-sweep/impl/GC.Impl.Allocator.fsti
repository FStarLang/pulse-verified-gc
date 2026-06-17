(*
   Pulse GC - Allocator Module Interface

   Dense-heap allocation entry points plus single-chunk compatibility wrappers
   used during the chunked-major migration.  The chunked-major allocation loop
   has a runtime-shaped verified wrapper, but extraction bundles currently keep
   this module internal so KaRaMeL does not expose ghost/dependent MajorHeap
   plumbing in the public C API.
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
module SpecHeap = GC.Spec.Heap
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

/// Initialize an absolute-addressed chunk-like range as one blue free-list
/// block.  This is a ghost-free extraction boundary helper: callers provide the
/// concrete header address and object/free-list address.
fn init_major_chunk_raw (heap: heap_t)
                       (base: hp_addr)
                       (fp_out: obj_addr)
                       (wz: wosize)
                       (next_fp: U64.t)
  requires is_heap heap 's **
          pure (U64.v fp_out == U64.v base + U64.v mword)
  returns new_fp: U64.t
  ensures exists* s2. is_heap heap s2 **
    pure (let hdr = makeHeader wz blue 0UL in
          s2 == SpecHeap.write_word (SpecHeap.write_word 's base hdr)
                 fp_out next_fp /\
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

/// Runtime-shaped chunked-major allocation over an already-active indexed major
/// heap.  The runtime argument is the public dense heap handle converted
/// internally to the chunked-major view; extraction keeps this wrapper internal
/// until the C bridge can pass a full verified chunk table without exposing
/// ghost/dependent MajorHeap plumbing.
fn allocate_major_with_fuel_runtime (heap: heap_t)
                                    (fp: U64.t)
                                    (requested_wz: wosize)
                                    (fuel: U64.t)
  requires
    MajorHeap.is_indexed_major_heap (MajorHeap.heap_as_major heap) 'mh **
    pure (U64.v requested_wz > 0 /\
          SpecMajorAlloc.major_fl_valid 'mh fp (U64.v fuel) /\
          SpecMajorAlloc.major_fl_above_zero 'mh fp (U64.v fuel) /\
          SpecMajorAlloc.major_fl_blocks_fit 'mh fp (U64.v fuel))
  returns res: (U64.t & U64.t)
  ensures
    MajorHeap.is_indexed_major_heap (MajorHeap.heap_as_major heap)
      (let r =
         SpecMajorAlloc.major_alloc_spec_with_fuel
           'mh fp (U64.v requested_wz) (U64.v fuel) in
       r.major_alloc_out) **
    pure (U64.v requested_wz > 0 /\
          SpecMajorAlloc.major_fl_valid 'mh fp (U64.v fuel) /\
          SpecMajorAlloc.major_fl_above_zero 'mh fp (U64.v fuel) /\
          SpecMajorAlloc.major_fl_blocks_fit 'mh fp (U64.v fuel) /\
          (let r =
             SpecMajorAlloc.major_alloc_spec_with_fuel
               'mh fp (U64.v requested_wz) (U64.v fuel) in
           fst res == r.major_fp_out /\
           snd res == r.major_obj_out))

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
