(*
   Pulse GC - Allocator Module Interface

   First-fit free-list allocator for the verified GC.
   Takes the heap and current free-list head, returns updated heap
   and new free-list head along with the allocated object address.
*)

module GC.Impl.Allocator

#lang-pulse

#set-options "--split_queries always"

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
module U64 = FStar.UInt64
module Seq = FStar.Seq
module MH = GC.Spec.MajorHeap
module SpecAlloc = GC.Spec.Allocator
module SpecMajorAlloc = GC.Spec.MajorAllocator
module SpecFields = GC.Spec.Fields
module SpecHeap = GC.Spec.Heap
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

/// Allocate from the current chunked-major free-list head without splitting it.
/// This is the first old-block allocation wrapper; full free-list search can
/// compose it after proving earlier blocks too small.
fn allocate_major_head_no_split (heap: MajorHeap.major_heap_t)
                                (base: hp_addr) (fp: obj_addr)
                                (block_wz requested_wz: wosize)
                                (next_fp: U64.t)
                                (#fuel: nat) (#idx: nat)
                                (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (fuel > 0 /\
                  idx < Seq.length (Ghost.reveal mh) /\
                  base == SpecHeap.hd_address fp /\
                  MH.lookup_chunk_index (Ghost.reveal mh) base == Some idx /\
                  MH.word_in_chunk (Seq.index (Ghost.reveal mh) idx) base /\
                  MH.read_word_in_major (Ghost.reveal mh) base ==
                    Some (SpecAlloc.make_header block_wz SpecAlloc.blue_bits 0UL) /\
                  MH.read_word_in_major (Ghost.reveal mh) fp == Some next_fp /\
                  U64.v fp >= U64.v zero_addr + U64.v mword /\
                  U64.v block_wz >= SpecAlloc.normalized_wosize (U64.v requested_wz) /\
                  U64.v block_wz - SpecAlloc.normalized_wosize (U64.v requested_wz) < 2)
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap
             (let r =
                SpecMajorAlloc.major_alloc_spec_with_fuel
                  (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
              r.major_alloc_out) **
           pure (let r =
                   SpecMajorAlloc.major_alloc_spec_with_fuel
                     (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
                 fst res == r.major_fp_out /\
                 snd res == r.major_obj_out)

/// Allocate from the current chunked-major free-list head by splitting it.
/// The caller supplies the split remainder header/object addresses and proves
/// they live in the same selected active chunk.
fn allocate_major_head_split (heap: MajorHeap.major_heap_t)
                             (base: hp_addr) (fp: obj_addr)
                             (block_wz requested_wz: wosize)
                             (rem_hd rem_obj: hp_addr)
                             (next_fp: U64.t)
                             (#fuel: nat) (#idx: nat)
                             (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (fuel > 0 /\
                  idx < Seq.length (Ghost.reveal mh) /\
                  base == SpecHeap.hd_address fp /\
                  MH.lookup_chunk_index (Ghost.reveal mh) base == Some idx /\
                  MH.word_in_chunk (Seq.index (Ghost.reveal mh) idx) base /\
                  MH.word_in_chunk (Seq.index (Ghost.reveal mh) idx) rem_hd /\
                  MH.word_in_chunk (Seq.index (Ghost.reveal mh) idx) rem_obj /\
                  (forall (k:nat{k < idx /\ k < Seq.length (Ghost.reveal mh)}).
                    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh) k) rem_hd)) /\
                  (forall (k:nat{k < idx /\ k < Seq.length (Ghost.reveal mh)}).
                    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh) k) rem_obj)) /\
                  MH.read_word_in_major (Ghost.reveal mh) base ==
                    Some (SpecAlloc.make_header block_wz SpecAlloc.blue_bits 0UL) /\
                  MH.read_word_in_major (Ghost.reveal mh) fp == Some next_fp /\
                  U64.v fp >= U64.v zero_addr + U64.v mword /\
                  U64.v requested_wz > 0 /\
                  U64.v block_wz >= U64.v requested_wz /\
                  U64.v block_wz - U64.v requested_wz >= 2 /\
                  U64.v base + (1 + U64.v requested_wz) * 8 < pow2 64 /\
                  U64.v rem_hd + U64.v mword < pow2 64 /\
                  U64.v rem_hd == U64.v base + (1 + U64.v requested_wz) * 8 /\
                  U64.v rem_obj == U64.v rem_hd + U64.v mword)
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap
             (let r =
                SpecMajorAlloc.major_alloc_spec_with_fuel
                  (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
              r.major_alloc_out) **
           pure (let r =
                   SpecMajorAlloc.major_alloc_spec_with_fuel
                     (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
                 fst res == r.major_fp_out /\
                 snd res == r.major_obj_out)

/// Allocate from the current chunked-major free-list head, choosing no-split
/// vs split from the existing block size and computing split addresses
/// internally.
fn allocate_major_head (heap: MajorHeap.major_heap_t)
                       (base: hp_addr) (fp: obj_addr)
                       (block_wz requested_wz: wosize)
                       (next_fp: U64.t)
                       (#fuel: nat) (#idx: nat)
                       (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (fuel > 0 /\
                  idx < Seq.length (Ghost.reveal mh) /\
                  base == SpecHeap.hd_address fp /\
                  MH.lookup_chunk_index (Ghost.reveal mh) base == Some idx /\
                  MH.word_in_chunk (Seq.index (Ghost.reveal mh) idx) base /\
                  MH.read_word_in_major (Ghost.reveal mh) base ==
                    Some (SpecAlloc.make_header block_wz SpecAlloc.blue_bits 0UL) /\
                  MH.read_word_in_major (Ghost.reveal mh) fp == Some next_fp /\
                  U64.v fp >= U64.v zero_addr + U64.v mword /\
                  U64.v requested_wz > 0 /\
                  U64.v block_wz >= U64.v requested_wz /\
                  U64.v base + (1 + U64.v block_wz) * 8 <=
                    MH.chunk_end (Seq.index (Ghost.reveal mh) idx))
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap
             (let r =
                SpecMajorAlloc.major_alloc_spec_with_fuel
                  (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
              r.major_alloc_out) **
           pure (let r =
                   SpecMajorAlloc.major_alloc_spec_with_fuel
                     (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
                 fst res == r.major_fp_out /\
                 snd res == r.major_obj_out)

/// Advance chunked-major allocation search past a too-small current free block.
/// This performs no heap mutation; it exposes the exact pure search-step
/// equality so a future loop can compose repeated advances with
/// `allocate_major_head`.
fn advance_major_search_too_small (heap: MajorHeap.major_heap_t)
                                 (head prev: U64.t)
                                 (base: hp_addr) (cur: obj_addr)
                                 (block_wz requested_wz: wosize)
                                 (next_fp: U64.t)
                                 (#fuel: (f:nat{f > 0})) (#idx: nat)
                                 (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (idx < Seq.length (Ghost.reveal mh) /\
                 base == SpecHeap.hd_address cur /\
                 MH.lookup_chunk_index (Ghost.reveal mh) base == Some idx /\
                 MH.word_in_chunk (Seq.index (Ghost.reveal mh) idx) base /\
                 MH.read_word_in_major (Ghost.reveal mh) base ==
                   Some (SpecAlloc.make_header block_wz SpecAlloc.blue_bits 0UL) /\
                 MH.read_word_in_major (Ghost.reveal mh) cur == Some next_fp /\
                 U64.v cur >= U64.v zero_addr + U64.v mword /\
                 U64.v block_wz <
                   SpecAlloc.normalized_wosize (U64.v requested_wz))
   returns next: U64.t
   ensures MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (next == next_fp /\
                 SpecMajorAlloc.major_alloc_search
                  (Ghost.reveal mh) head prev cur
                  (SpecAlloc.normalized_wosize (U64.v requested_wz)) fuel ==
                 SpecMajorAlloc.major_alloc_search
                  (Ghost.reveal mh) head cur next_fp
                  (SpecAlloc.normalized_wosize (U64.v requested_wz)) (fuel - 1))

/// Allocate a too-large/sufficient current free block reached after at least one
/// previous free-list node, in the no-split case. The previous node's link is
/// updated to the successor/remainder returned by allocation.
fn allocate_major_found_prev_no_split (heap: MajorHeap.major_heap_t)
                                     (head: U64.t) (prev: obj_addr)
                                     (base: hp_addr) (cur: obj_addr)
                                     (block_wz requested_wz: wosize)
                                     (next_fp: U64.t)
                                     (#fuel: (f:nat{f > 0}))
                                     (#cur_idx: nat) (#prev_idx: nat)
                                     (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (cur_idx < Seq.length (Ghost.reveal mh) /\
                  prev_idx < Seq.length (Ghost.reveal mh) /\
                  base == SpecHeap.hd_address cur /\
                  MH.lookup_chunk_index (Ghost.reveal mh) base == Some cur_idx /\
                  MH.word_in_chunk (Seq.index (Ghost.reveal mh) cur_idx) base /\
                  MH.word_in_chunk (Seq.index (Ghost.reveal mh) prev_idx) prev /\
                  (forall (k:nat). k < prev_idx ==>
                   ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh) k) prev)) /\
                  MH.read_word_in_major (Ghost.reveal mh) base ==
                   Some (SpecAlloc.make_header block_wz SpecAlloc.blue_bits 0UL) /\
                  MH.read_word_in_major (Ghost.reveal mh) cur == Some next_fp /\
                  U64.v prev > 0 /\
                  U64.v cur >= U64.v zero_addr + U64.v mword /\
                  U64.v block_wz >=
                   SpecAlloc.normalized_wosize (U64.v requested_wz) /\
                  U64.v block_wz -
                   SpecAlloc.normalized_wosize (U64.v requested_wz) < 2)
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap
             (let r =
                SpecMajorAlloc.major_alloc_search
                  (Ghost.reveal mh) head prev cur
                  (SpecAlloc.normalized_wosize (U64.v requested_wz)) fuel in
              r.major_alloc_out) **
           pure (let r =
                  SpecMajorAlloc.major_alloc_search
                    (Ghost.reveal mh) head prev cur
                    (SpecAlloc.normalized_wosize (U64.v requested_wz)) fuel in
                 fst res == r.major_fp_out /\
                 snd res == r.major_obj_out)

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

/// Allocate the entire freshly prepended free block.
fn allocate_fresh_expanded_exact (heap: MajorHeap.major_heap_t)
                                 (base: hp_addr) (fp_out: obj_addr)
                                 (wz: wosize) (next_fp: U64.t)
                                 (#mh: Ghost.erased MH.major_heap)
                                 (#fresh: Ghost.erased
                                   (c:MH.heap_chunk{c.base == base /\
                                                    fp_out == SpecMajorAlloc.fresh_chunk_object c /\
                                                    U64.v wz == SpecMajorAlloc.fresh_chunk_wosize c}))
  requires MajorHeap.is_indexed_major_heap heap
            (SpecMajorAlloc.expand_major_heap
              (Ghost.reveal mh) (Ghost.reveal fresh) next_fp).major_out **
           pure (U64.v base >= U64.v zero_addr)
  returns res: (U64.t & U64.t)
  ensures MajorHeap.is_indexed_major_heap heap
            (let er =
              SpecMajorAlloc.expand_major_heap
                (Ghost.reveal mh) (Ghost.reveal fresh) next_fp in
             (SpecMajorAlloc.major_alloc_spec_with_fuel
               er.major_out er.fp_out (U64.v wz) 1).major_alloc_out) **
          pure (let er =
                  SpecMajorAlloc.expand_major_heap
                    (Ghost.reveal mh) (Ghost.reveal fresh) next_fp in
                let r =
                  SpecMajorAlloc.major_alloc_spec_with_fuel
                    er.major_out er.fp_out (U64.v wz) 1 in
                fst res == r.major_fp_out /\
                snd res == r.major_obj_out)

/// Allocate the freshly prepended block without splitting it.
fn allocate_fresh_expanded_no_split (heap: MajorHeap.major_heap_t)
                                    (base: hp_addr) (fp_out: obj_addr)
                                    (fresh_wz requested_wz: wosize)
                                    (next_fp: U64.t)
                                    (#mh: Ghost.erased MH.major_heap)
                                    (#fresh_chunk: Ghost.erased
                                      (c:MH.heap_chunk{c.base == base /\
                                                       fp_out == SpecMajorAlloc.fresh_chunk_object c /\
                                                       U64.v fresh_wz == SpecMajorAlloc.fresh_chunk_wosize c}))
  requires MajorHeap.is_indexed_major_heap heap
            (SpecMajorAlloc.expand_major_heap
              (Ghost.reveal mh) (Ghost.reveal fresh_chunk) next_fp).major_out **
           pure (U64.v base >= U64.v zero_addr /\
                 U64.v requested_wz > 0 /\
                 SpecMajorAlloc.fresh_chunk_wosize (Ghost.reveal fresh_chunk) >=
                   U64.v requested_wz /\
                 SpecMajorAlloc.fresh_chunk_wosize (Ghost.reveal fresh_chunk) -
                   U64.v requested_wz < 2)
  returns res: (U64.t & U64.t)
  ensures MajorHeap.is_indexed_major_heap heap
            (let fresh_c : MH.heap_chunk = Ghost.reveal fresh_chunk in
             let er =
              SpecMajorAlloc.expand_major_heap
                (Ghost.reveal mh) fresh_c next_fp in
             (SpecMajorAlloc.major_alloc_spec_with_fuel
               er.major_out er.fp_out (U64.v requested_wz) 1).major_alloc_out) **
          pure (fst res == next_fp /\
                snd res == fp_out)

/// Split the freshly prepended free block, leaving the remainder as the new
/// free-list head.
fn allocate_fresh_expanded_split (heap: MajorHeap.major_heap_t)
                                 (base: hp_addr) (fp_out: obj_addr)
                                 (fresh_wz requested_wz: wosize)
                                 (rem_hd rem_obj: hp_addr)
                                 (next_fp: U64.t)
                                 (#mh: Ghost.erased MH.major_heap)
                                 (#fresh_chunk: Ghost.erased
                                   (c:MH.heap_chunk{c.base == base /\
                                                    fp_out == SpecMajorAlloc.fresh_chunk_object c /\
                                                    U64.v fresh_wz == SpecMajorAlloc.fresh_chunk_wosize c}))
  requires MajorHeap.is_indexed_major_heap heap
            (SpecMajorAlloc.expand_major_heap
              (Ghost.reveal mh) (Ghost.reveal fresh_chunk) next_fp).major_out **
           pure (U64.v base >= U64.v zero_addr /\
                 U64.v requested_wz > 0 /\
                 SpecMajorAlloc.fresh_chunk_wosize (Ghost.reveal fresh_chunk) -
                   U64.v requested_wz >= 2 /\
                 U64.v rem_hd == U64.v base + (1 + U64.v requested_wz) * 8 /\
                 U64.v rem_obj == U64.v rem_hd + U64.v mword)
  returns res: (U64.t & U64.t)
  ensures MajorHeap.is_indexed_major_heap heap
            (let fresh_c : MH.heap_chunk = Ghost.reveal fresh_chunk in
             let er =
              SpecMajorAlloc.expand_major_heap
                (Ghost.reveal mh) fresh_c next_fp in
             (SpecMajorAlloc.major_alloc_spec_with_fuel
               er.major_out er.fp_out (U64.v requested_wz) 1).major_alloc_out) **
          pure (fst res == rem_obj /\
                snd res == fp_out)

/// Expand with a fresh chunk and allocate from it without splitting.
fn expand_and_allocate_fresh_no_split (heap: MajorHeap.major_heap_t)
                                      (base: hp_addr) (fp_out: obj_addr)
                                      (fresh_wz requested_wz: wosize)
                                      (next_fp: U64.t)
                                      (#mh: Ghost.erased MH.major_heap)
                                      (#fresh_chunk: Ghost.erased
                                        (c:MH.heap_chunk{c.base == base /\
                                                         fp_out == SpecMajorAlloc.fresh_chunk_object c /\
                                                         U64.v fresh_wz == SpecMajorAlloc.fresh_chunk_wosize c}))
  requires MajorHeap.chunk_range heap (Ghost.reveal fresh_chunk) **
           MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (MH.chunk_disjoint_from_all (Ghost.reveal fresh_chunk) (Ghost.reveal mh) /\
                 U64.v base >= U64.v zero_addr /\
                 U64.v requested_wz > 0 /\
                 SpecMajorAlloc.fresh_chunk_wosize (Ghost.reveal fresh_chunk) >=
                   U64.v requested_wz /\
                 SpecMajorAlloc.fresh_chunk_wosize (Ghost.reveal fresh_chunk) -
                   U64.v requested_wz < 2)
  returns res: (U64.t & U64.t)
  ensures MajorHeap.is_indexed_major_heap heap
            (let er =
              SpecMajorAlloc.expand_major_heap
                (Ghost.reveal mh) (Ghost.reveal fresh_chunk) next_fp in
             (SpecMajorAlloc.major_alloc_spec_with_fuel
               er.major_out er.fp_out (U64.v requested_wz) 1).major_alloc_out) **
          pure (fst res == next_fp /\
                snd res == fp_out)

/// Expand with a fresh chunk and allocate from it by splitting the fresh block.
fn expand_and_allocate_fresh_split (heap: MajorHeap.major_heap_t)
                                  (base: hp_addr) (fp_out: obj_addr)
                                  (fresh_wz requested_wz: wosize)
                                  (rem_hd rem_obj: hp_addr)
                                  (next_fp: U64.t)
                                  (#mh: Ghost.erased MH.major_heap)
                                  (#fresh_chunk: Ghost.erased
                                    (c:MH.heap_chunk{c.base == base /\
                                                     fp_out == SpecMajorAlloc.fresh_chunk_object c /\
                                                     U64.v fresh_wz == SpecMajorAlloc.fresh_chunk_wosize c}))
  requires MajorHeap.chunk_range heap (Ghost.reveal fresh_chunk) **
           MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (MH.chunk_disjoint_from_all (Ghost.reveal fresh_chunk) (Ghost.reveal mh) /\
                 U64.v base >= U64.v zero_addr /\
                 U64.v requested_wz > 0 /\
                 SpecMajorAlloc.fresh_chunk_wosize (Ghost.reveal fresh_chunk) -
                   U64.v requested_wz >= 2 /\
                 U64.v rem_hd == U64.v base + (1 + U64.v requested_wz) * 8 /\
                 U64.v rem_obj == U64.v rem_hd + U64.v mword)
  returns res: (U64.t & U64.t)
  ensures MajorHeap.is_indexed_major_heap heap
            (let er =
              SpecMajorAlloc.expand_major_heap
                (Ghost.reveal mh) (Ghost.reveal fresh_chunk) next_fp in
             (SpecMajorAlloc.major_alloc_spec_with_fuel
               er.major_out er.fp_out (U64.v requested_wz) 1).major_alloc_out) **
          pure (fst res == rem_obj /\
                snd res == fp_out)

/// Expand with a fresh chunk and allocate from it, choosing no-split vs split
/// from the fresh block size.
fn expand_and_allocate_fresh (heap: MajorHeap.major_heap_t)
                             (base: hp_addr) (fp_out: obj_addr)
                             (fresh_wz requested_wz: wosize)
                             (next_fp: U64.t)
                             (#mh: Ghost.erased MH.major_heap)
                             (#fresh_chunk: Ghost.erased
                               (c:MH.heap_chunk{c.base == base /\
                                                fp_out == SpecMajorAlloc.fresh_chunk_object c /\
                                                U64.v fresh_wz == SpecMajorAlloc.fresh_chunk_wosize c}))
  requires MajorHeap.chunk_range heap (Ghost.reveal fresh_chunk) **
           MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (MH.chunk_disjoint_from_all (Ghost.reveal fresh_chunk) (Ghost.reveal mh) /\
                 U64.v base >= U64.v zero_addr /\
                 U64.v requested_wz > 0 /\
                 SpecMajorAlloc.fresh_chunk_wosize (Ghost.reveal fresh_chunk) >=
                   U64.v requested_wz)
  returns res: (U64.t & U64.t)
  ensures MajorHeap.is_indexed_major_heap heap
            (let fresh_c : MH.heap_chunk = Ghost.reveal fresh_chunk in
             let er =
              SpecMajorAlloc.expand_major_heap
                (Ghost.reveal mh) fresh_c next_fp in
             (SpecMajorAlloc.major_alloc_spec_with_fuel
               er.major_out er.fp_out (U64.v requested_wz) 1).major_alloc_out) **
          pure (let fresh_c : MH.heap_chunk = Ghost.reveal fresh_chunk in
                let er =
                  SpecMajorAlloc.expand_major_heap
                    (Ghost.reveal mh) fresh_c next_fp in
                let r =
                  SpecMajorAlloc.major_alloc_spec_with_fuel
                    er.major_out er.fp_out (U64.v requested_wz) 1 in
                fst res == r.major_fp_out /\
                snd res == r.major_obj_out)

/// Same as expand_and_allocate_fresh, but exposes the heap state for an
/// arbitrary positive retry fuel. Fresh-head allocation is fuel-insensitive
/// once the retry fuel is non-zero.
fn expand_and_allocate_fresh_with_fuel (heap: MajorHeap.major_heap_t)
                                       (base: hp_addr) (fp_out: obj_addr)
                                       (fresh_wz requested_wz: wosize)
                                       (next_fp: U64.t)
                                       (#fuel: nat)
                                       (#mh: Ghost.erased MH.major_heap)
                                       (#fresh_chunk: Ghost.erased
                                         (c:MH.heap_chunk{c.base == base /\
                                                          fp_out == SpecMajorAlloc.fresh_chunk_object c /\
                                                          U64.v fresh_wz == SpecMajorAlloc.fresh_chunk_wosize c}))
   requires MajorHeap.chunk_range heap (Ghost.reveal fresh_chunk) **
            MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (MH.chunk_disjoint_from_all (Ghost.reveal fresh_chunk) (Ghost.reveal mh) /\
                 U64.v base >= U64.v zero_addr /\
                 U64.v requested_wz > 0 /\
                 SpecMajorAlloc.fresh_chunk_wosize (Ghost.reveal fresh_chunk) >=
                   U64.v requested_wz)
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap
             (let fresh_c : MH.heap_chunk = Ghost.reveal fresh_chunk in
              let old_mh : MH.major_heap = Ghost.reveal mh in
              let retry_fuel : nat = fuel + 1 in
              let er =
               SpecMajorAlloc.expand_major_heap
                old_mh fresh_c next_fp in
              (SpecMajorAlloc.major_alloc_spec_with_fuel
                er.major_out er.fp_out (U64.v requested_wz)
                retry_fuel).major_alloc_out)

/// Expand with a fresh chunk after an old free-list allocation attempt
/// returned OOM, exposing the exact expand-on-OOM allocation spec.
fn expand_on_oom_with_fresh (heap: MajorHeap.major_heap_t)
                            (base: hp_addr) (fp_out: obj_addr)
                            (fresh_wz requested_wz: wosize)
                            (fp: U64.t)
                            (#fuel: nat)
                            (#mh: Ghost.erased MH.major_heap)
                            (#fresh_chunk: Ghost.erased
                              (c:MH.heap_chunk{c.base == base /\
                                               fp_out == SpecMajorAlloc.fresh_chunk_object c /\
                                               U64.v fresh_wz == SpecMajorAlloc.fresh_chunk_wosize c}))
   requires MajorHeap.chunk_range heap (Ghost.reveal fresh_chunk) **
            MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (MH.chunk_disjoint_from_all (Ghost.reveal fresh_chunk) (Ghost.reveal mh) /\
                 U64.v base >= U64.v zero_addr /\
                 U64.v requested_wz > 0 /\
                 SpecMajorAlloc.fresh_chunk_wosize (Ghost.reveal fresh_chunk) >=
                   U64.v requested_wz /\
                 (SpecMajorAlloc.major_alloc_spec_with_fuel
                   (Ghost.reveal mh) fp (U64.v requested_wz)
                   fuel).major_obj_out == 0UL)
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap
             (let old_mh : MH.major_heap = Ghost.reveal mh in
              let fresh_c : MH.heap_chunk = Ghost.reveal fresh_chunk in
              SpecMajorAlloc.major_alloc_spec_expand_on_oom
                old_mh fp (U64.v requested_wz)
                fuel fresh_c).major_alloc_out **
           pure (snd res == fp_out)

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
