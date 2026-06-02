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

/// General chunked-major first-fit allocation over the indexed active-chunk
/// ownership view.  This is the non-expanding allocation primitive; callers
/// must provide the chunked free-list validity/fit invariants and a positive
/// requested object size.
fn allocate_major_with_fuel (heap: MajorHeap.major_heap_t)
                            (fp: U64.t)
                            (requested_wz: wosize)
                            (fuel: U64.t)
                            (#mh: Ghost.erased MH.major_heap)
  requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (U64.v requested_wz > 0 /\
                 SpecMajorAlloc.major_fl_valid
                   (Ghost.reveal mh) fp (U64.v fuel) /\
                 SpecMajorAlloc.major_fl_above_zero
                   (Ghost.reveal mh) fp (U64.v fuel) /\
                 SpecMajorAlloc.major_fl_blocks_fit
                   (Ghost.reveal mh) fp (U64.v fuel))
  returns res: (U64.t & U64.t)
  ensures MajorHeap.is_indexed_major_heap heap
            (let r =
               SpecMajorAlloc.major_alloc_spec_with_fuel
                 (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel) in
             r.major_alloc_out) **
          pure (let r =
                 SpecMajorAlloc.major_alloc_spec_with_fuel
                   (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel) in
                fst res == r.major_fp_out /\
                snd res == r.major_obj_out)

/// Allocate from the current chunked-major free-list head without splitting it.
/// This is the first old-block allocation wrapper; full free-list search can
/// compose it after proving earlier blocks too small.
fn allocate_major_head_no_split (heap: MajorHeap.major_heap_t)
                                (base: hp_addr) (fp: obj_addr)
                                (hdr: U64.t) (block_wz requested_wz: wosize)
                                (next_fp: U64.t)
                                (#fuel: nat) (#idx: Ghost.erased nat)
                                (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (fuel > 0 /\
                  Ghost.reveal idx < Seq.length (Ghost.reveal mh) /\
                  base == SpecHeap.hd_address fp /\
                  MH.lookup_chunk_index (Ghost.reveal mh) base ==
                    Some (Ghost.reveal idx) /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) base /\
                  MH.read_word_in_major (Ghost.reveal mh) base == Some hdr /\
                  MH.read_word_in_major (Ghost.reveal mh) fp == Some next_fp /\
                  block_wz == SpecObject.getWosize hdr /\
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
                             (hdr: U64.t) (block_wz requested_wz: wosize)
                             (rem_hd rem_obj: hp_addr)
                             (next_fp: U64.t)
                             (#fuel: nat) (#idx: Ghost.erased nat)
                             (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (fuel > 0 /\
                  Ghost.reveal idx < Seq.length (Ghost.reveal mh) /\
                  base == SpecHeap.hd_address fp /\
                  MH.lookup_chunk_index (Ghost.reveal mh) base ==
                    Some (Ghost.reveal idx) /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) base /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) rem_hd /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) rem_obj /\
                  (forall (k:nat{k < Ghost.reveal idx /\ k < Seq.length (Ghost.reveal mh)}).
                    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh) k) rem_hd)) /\
                  (forall (k:nat{k < Ghost.reveal idx /\ k < Seq.length (Ghost.reveal mh)}).
                    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh) k) rem_obj)) /\
                  MH.read_word_in_major (Ghost.reveal mh) base == Some hdr /\
                  MH.read_word_in_major (Ghost.reveal mh) fp == Some next_fp /\
                  block_wz == SpecObject.getWosize hdr /\
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
                       (hdr: U64.t) (block_wz requested_wz: wosize)
                       (next_fp: U64.t)
                       (#fuel: nat) (#idx: Ghost.erased nat)
                       (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (fuel > 0 /\
                  Ghost.reveal idx < Seq.length (Ghost.reveal mh) /\
                  base == SpecHeap.hd_address fp /\
                  MH.lookup_chunk_index (Ghost.reveal mh) base ==
                    Some (Ghost.reveal idx) /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) base /\
                  MH.read_word_in_major (Ghost.reveal mh) base == Some hdr /\
                  MH.read_word_in_major (Ghost.reveal mh) fp == Some next_fp /\
                  block_wz == SpecObject.getWosize hdr /\
                  U64.v fp >= U64.v zero_addr + U64.v mword /\
                  U64.v requested_wz > 0 /\
                  U64.v block_wz >= U64.v requested_wz /\
                  U64.v base + (1 + U64.v block_wz) * 8 <=
                    MH.chunk_end
                      (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)))
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
                                 (hdr: U64.t) (block_wz requested_wz: wosize)
                                 (next_fp: U64.t)
                                 (#fuel: (f:nat{f > 0}))
                                 (#idx: Ghost.erased nat)
                                 (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (Ghost.reveal idx < Seq.length (Ghost.reveal mh) /\
                 base == SpecHeap.hd_address cur /\
                 MH.lookup_chunk_index (Ghost.reveal mh) base ==
                  Some (Ghost.reveal idx) /\
                 MH.word_in_chunk
                  (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) base /\
                 MH.read_word_in_major (Ghost.reveal mh) base == Some hdr /\
                 MH.read_word_in_major (Ghost.reveal mh) cur == Some next_fp /\
                 block_wz == SpecObject.getWosize hdr /\
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

/// Read the header and next-link words for a valid chunked-major free-list node.
/// Lookup indices are proof-only witnesses for the selected header/link chunks.
fn read_major_free_block (heap: MajorHeap.major_heap_t)
                         (cur: obj_addr)
                         (#fuel: (f:nat{f > 0}))
                         (#header_idx: Ghost.erased nat)
                         (#link_idx: Ghost.erased nat)
                         (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (Ghost.reveal header_idx < Seq.length (Ghost.reveal mh) /\
                  Ghost.reveal link_idx < Seq.length (Ghost.reveal mh) /\
                  MH.lookup_chunk_index
                    (Ghost.reveal mh) (SpecHeap.hd_address cur) ==
                    Some (Ghost.reveal header_idx) /\
                  MH.lookup_chunk_index (Ghost.reveal mh) cur ==
                    Some (Ghost.reveal link_idx) /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal header_idx))
                    (SpecHeap.hd_address cur) /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal link_idx)) cur /\
                  SpecMajorAlloc.major_fl_valid (Ghost.reveal mh) cur fuel)
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (let hdr = fst res in
                 let next = snd res in
                 MH.read_word_in_major (Ghost.reveal mh) (SpecHeap.hd_address cur) ==
                  Some hdr /\
                 MH.read_word_in_major (Ghost.reveal mh) cur == Some next /\
                 U64.v (SpecObject.getWosize hdr) >= 1 /\
                 next <> cur /\
                 SpecMajorAlloc.major_fl_valid (Ghost.reveal mh) next (fuel - 1))

/// Read a valid chunked-major free-list node and carry the stricter
/// `major_fl_above_zero` chain invariant to the successor.
fn read_major_free_block_above_zero (heap: MajorHeap.major_heap_t)
                                   (cur: obj_addr)
                                   (#fuel: (f:nat{f > 0}))
                                   (#header_idx: Ghost.erased nat)
                                   (#link_idx: Ghost.erased nat)
                                   (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (Ghost.reveal header_idx < Seq.length (Ghost.reveal mh) /\
                 Ghost.reveal link_idx < Seq.length (Ghost.reveal mh) /\
                 MH.lookup_chunk_index
                   (Ghost.reveal mh) (SpecHeap.hd_address cur) ==
                   Some (Ghost.reveal header_idx) /\
                 MH.lookup_chunk_index (Ghost.reveal mh) cur ==
                   Some (Ghost.reveal link_idx) /\
                 MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal header_idx))
                   (SpecHeap.hd_address cur) /\
                 MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal link_idx)) cur /\
                 U64.v cur >= U64.v zero_addr + U64.v mword /\
                 SpecMajorAlloc.major_fl_valid (Ghost.reveal mh) cur fuel /\
                 SpecMajorAlloc.major_fl_above_zero (Ghost.reveal mh) cur fuel)
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (let hdr = fst res in
                 let next = snd res in
                 MH.read_word_in_major (Ghost.reveal mh) (SpecHeap.hd_address cur) ==
                 Some hdr /\
                 MH.read_word_in_major (Ghost.reveal mh) cur == Some next /\
                 U64.v (SpecObject.getWosize hdr) >= 1 /\
                 next <> cur /\
                 SpecMajorAlloc.major_fl_valid (Ghost.reveal mh) next (fuel - 1) /\
                 SpecMajorAlloc.major_fl_above_zero
                  (Ghost.reveal mh) next (fuel - 1))

/// Allocate a too-large/sufficient current free block reached after at least one
/// previous free-list node, in the no-split case. The previous node's link is
/// updated to the successor/remainder returned by allocation.
fn allocate_major_found_prev_no_split (heap: MajorHeap.major_heap_t)
                                     (head: U64.t) (prev: obj_addr)
                                     (base: hp_addr) (cur: obj_addr)
                                     (hdr: U64.t) (block_wz requested_wz: wosize)
                                     (next_fp: U64.t)
                                     (#fuel: (f:nat{f > 0}))
                                    (#cur_idx: Ghost.erased nat)
                                    (#prev_idx: Ghost.erased nat)
                                    (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (Ghost.reveal cur_idx < Seq.length (Ghost.reveal mh) /\
                  Ghost.reveal prev_idx < Seq.length (Ghost.reveal mh) /\
                  base == SpecHeap.hd_address cur /\
                  MH.lookup_chunk_index (Ghost.reveal mh) base ==
                   Some (Ghost.reveal cur_idx) /\
                  MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_idx)) base /\
                  MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal prev_idx)) prev /\
                  (forall (k:nat). k < Ghost.reveal prev_idx ==>
                   ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh) k) prev)) /\
                  MH.read_word_in_major (Ghost.reveal mh) base == Some hdr /\
                  MH.read_word_in_major (Ghost.reveal mh) cur == Some next_fp /\
                  block_wz == SpecObject.getWosize hdr /\
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

/// Allocate a current free block reached after a previous node by splitting it.
/// The previous node is relinked to the split remainder object.
fn allocate_major_found_prev_split (heap: MajorHeap.major_heap_t)
                                   (head: U64.t) (prev: obj_addr)
                                   (base: hp_addr) (cur: obj_addr)
                                   (hdr: U64.t) (block_wz requested_wz: wosize)
                                   (rem_hd rem_obj: hp_addr)
                                   (next_fp: U64.t)
                                   (#fuel: (f:nat{f > 0}))
                                  (#cur_idx: Ghost.erased nat)
                                  (#prev_idx: Ghost.erased nat)
                                  (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (Ghost.reveal cur_idx < Seq.length (Ghost.reveal mh) /\
                  Ghost.reveal prev_idx < Seq.length (Ghost.reveal mh) /\
                  base == SpecHeap.hd_address cur /\
                  MH.lookup_chunk_index (Ghost.reveal mh) base ==
                   Some (Ghost.reveal cur_idx) /\
                  MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_idx)) base /\
                  MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_idx)) rem_hd /\
                  MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_idx)) rem_obj /\
                  (forall (k:nat{k < Ghost.reveal cur_idx /\
                                   k < Seq.length (Ghost.reveal mh)}).
                    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh) k) rem_hd)) /\
                  (forall (k:nat{k < Ghost.reveal cur_idx /\
                                   k < Seq.length (Ghost.reveal mh)}).
                    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh) k) rem_obj)) /\
                  MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal prev_idx)) prev /\
                  (forall (k:nat). k < Ghost.reveal prev_idx ==>
                    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh) k) prev)) /\
                  MH.read_word_in_major (Ghost.reveal mh) base == Some hdr /\
                  MH.read_word_in_major (Ghost.reveal mh) cur == Some next_fp /\
                  block_wz == SpecObject.getWosize hdr /\
                  U64.v prev > 0 /\
                  U64.v cur >= U64.v zero_addr + U64.v mword /\
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

/// Allocate a later free-list node, choosing no-split vs split from the block
/// size and relinking the previous free-list node appropriately.
fn allocate_major_found_prev (heap: MajorHeap.major_heap_t)
                             (head: U64.t) (prev: obj_addr)
                             (base: hp_addr) (cur: obj_addr)
                             (hdr: U64.t) (block_wz requested_wz: wosize)
                             (next_fp: U64.t)
                             (#fuel: (f:nat{f > 0}))
                             (#cur_idx: Ghost.erased nat)
                             (#prev_idx: Ghost.erased nat)
                             (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (Ghost.reveal cur_idx < Seq.length (Ghost.reveal mh) /\
                  Ghost.reveal prev_idx < Seq.length (Ghost.reveal mh) /\
                  base == SpecHeap.hd_address cur /\
                  MH.lookup_chunk_index (Ghost.reveal mh) base ==
                   Some (Ghost.reveal cur_idx) /\
                  MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_idx)) base /\
                  MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal prev_idx)) prev /\
                  (forall (k:nat). k < Ghost.reveal prev_idx ==>
                    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh) k) prev)) /\
                  MH.read_word_in_major (Ghost.reveal mh) base == Some hdr /\
                  MH.read_word_in_major (Ghost.reveal mh) cur == Some next_fp /\
                  block_wz == SpecObject.getWosize hdr /\
                  U64.v prev > 0 /\
                  U64.v cur >= U64.v zero_addr + U64.v mword /\
                  U64.v requested_wz > 0 /\
                  U64.v block_wz >= U64.v requested_wz /\
                  U64.v base + (1 + U64.v block_wz) * 8 <=
                    MH.chunk_end
                     (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_idx)))
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

/// Read the current free-list node, prove it is too small, and advance search.
/// This is the no-mutation step used before a later iteration allocates from a
/// subsequent free-list node.
fn advance_major_search_from_read (heap: MajorHeap.major_heap_t)
                                 (head prev: U64.t)
                                 (base: hp_addr) (cur: obj_addr)
                                 (requested_wz: wosize)
                                 (#fuel: (f:nat{f > 0}))
                                 (#header_idx: Ghost.erased nat)
                                 (#link_idx: Ghost.erased nat)
                                 (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (Ghost.reveal header_idx < Seq.length (Ghost.reveal mh) /\
                 Ghost.reveal link_idx < Seq.length (Ghost.reveal mh) /\
                 base == SpecHeap.hd_address cur /\
                 MH.lookup_chunk_index (Ghost.reveal mh) base ==
                  Some (Ghost.reveal header_idx) /\
                 MH.lookup_chunk_index (Ghost.reveal mh) cur ==
                  Some (Ghost.reveal link_idx) /\
                 MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal header_idx)) base /\
                 MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal link_idx)) cur /\
                 SpecMajorAlloc.major_fl_valid (Ghost.reveal mh) cur fuel /\
                 U64.v cur >= U64.v zero_addr + U64.v mword /\
                 (match MH.read_word_in_major (Ghost.reveal mh) base with
                  | Some hdr ->
                    U64.v (SpecObject.getWosize hdr) <
                      SpecAlloc.normalized_wosize (U64.v requested_wz)
                  | None -> False))
   returns next: U64.t
   ensures MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (MH.read_word_in_major (Ghost.reveal mh) cur == Some next /\
                 next <> cur /\
                 SpecMajorAlloc.major_fl_valid
                  (Ghost.reveal mh) next (fuel - 1) /\
                 SpecMajorAlloc.major_alloc_search
                  (Ghost.reveal mh) head prev cur
                  (SpecAlloc.normalized_wosize (U64.v requested_wz)) fuel ==
                 SpecMajorAlloc.major_alloc_search
                  (Ghost.reveal mh) head cur next
                  (SpecAlloc.normalized_wosize (U64.v requested_wz)) (fuel - 1))

/// Same as `advance_major_search_from_read`, additionally preserving the
/// chunked free-list above-zero invariant for the successor chain.
fn advance_major_search_from_read_above_zero (heap: MajorHeap.major_heap_t)
                                            (head prev: U64.t)
                                            (base: hp_addr) (cur: obj_addr)
                                            (requested_wz: wosize)
                                            (#fuel: (f:nat{f > 0}))
                                            (#header_idx: Ghost.erased nat)
                                            (#link_idx: Ghost.erased nat)
                                            (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (Ghost.reveal header_idx < Seq.length (Ghost.reveal mh) /\
                 Ghost.reveal link_idx < Seq.length (Ghost.reveal mh) /\
                 base == SpecHeap.hd_address cur /\
                 MH.lookup_chunk_index (Ghost.reveal mh) base ==
                  Some (Ghost.reveal header_idx) /\
                 MH.lookup_chunk_index (Ghost.reveal mh) cur ==
                  Some (Ghost.reveal link_idx) /\
                 MH.word_in_chunk
                  (Seq.index (Ghost.reveal mh) (Ghost.reveal header_idx)) base /\
                 MH.word_in_chunk
                  (Seq.index (Ghost.reveal mh) (Ghost.reveal link_idx)) cur /\
                 SpecMajorAlloc.major_fl_valid (Ghost.reveal mh) cur fuel /\
                 SpecMajorAlloc.major_fl_above_zero (Ghost.reveal mh) cur fuel /\
                 U64.v cur >= U64.v zero_addr + U64.v mword /\
                 (match MH.read_word_in_major (Ghost.reveal mh) base with
                 | Some hdr ->
                   U64.v (SpecObject.getWosize hdr) <
                     SpecAlloc.normalized_wosize (U64.v requested_wz)
                 | None -> False))
   returns next: U64.t
   ensures MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (MH.read_word_in_major (Ghost.reveal mh) cur == Some next /\
                 next <> cur /\
                 SpecMajorAlloc.major_fl_valid
                 (Ghost.reveal mh) next (fuel - 1) /\
                 SpecMajorAlloc.major_fl_above_zero
                 (Ghost.reveal mh) next (fuel - 1) /\
                 SpecMajorAlloc.major_alloc_search
                 (Ghost.reveal mh) head prev cur
                 (SpecAlloc.normalized_wosize (U64.v requested_wz)) fuel ==
                 SpecMajorAlloc.major_alloc_search
                 (Ghost.reveal mh) head cur next
                 (SpecAlloc.normalized_wosize (U64.v requested_wz)) (fuel - 1))

/// Read and allocate from the active free-list head once the header proves the
/// block is large enough.
fn allocate_major_head_from_read (heap: MajorHeap.major_heap_t)
                                (base: hp_addr) (fp: obj_addr)
                                (requested_wz: wosize)
                                (#fuel: (f:nat{f > 0}))
                                (#header_idx: Ghost.erased nat)
                                (#link_idx: Ghost.erased nat)
                                (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (Ghost.reveal header_idx < Seq.length (Ghost.reveal mh) /\
                 Ghost.reveal link_idx < Seq.length (Ghost.reveal mh) /\
                 base == SpecHeap.hd_address fp /\
                 MH.lookup_chunk_index (Ghost.reveal mh) base ==
                   Some (Ghost.reveal header_idx) /\
                 MH.lookup_chunk_index (Ghost.reveal mh) fp ==
                   Some (Ghost.reveal link_idx) /\
                 MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal header_idx)) base /\
                 MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal link_idx)) fp /\
                 SpecMajorAlloc.major_fl_valid (Ghost.reveal mh) fp fuel /\
                 U64.v fp >= U64.v zero_addr + U64.v mword /\
                 U64.v requested_wz > 0 /\
                 (match MH.read_word_in_major (Ghost.reveal mh) base with
                  | Some hdr ->
                    U64.v (SpecObject.getWosize hdr) >= U64.v requested_wz /\
                    U64.v base +
                      (1 + U64.v (SpecObject.getWosize hdr)) * 8 <=
                      MH.chunk_end
                        (Seq.index (Ghost.reveal mh) (Ghost.reveal header_idx))
                  | None -> False))
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

/// Read and allocate from the active free-list head, deriving the head lower
/// bound from `major_fl_above_zero`.
fn allocate_major_head_from_read_above_zero (heap: MajorHeap.major_heap_t)
                                           (base: hp_addr) (fp: obj_addr)
                                           (requested_wz: wosize)
                                           (#fuel: (f:nat{f > 0}))
                                           (#header_idx: Ghost.erased nat)
                                           (#link_idx: Ghost.erased nat)
                                           (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (Ghost.reveal header_idx < Seq.length (Ghost.reveal mh) /\
                 Ghost.reveal link_idx < Seq.length (Ghost.reveal mh) /\
                 base == SpecHeap.hd_address fp /\
                 MH.lookup_chunk_index (Ghost.reveal mh) base ==
                   Some (Ghost.reveal header_idx) /\
                 MH.lookup_chunk_index (Ghost.reveal mh) fp ==
                   Some (Ghost.reveal link_idx) /\
                 MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal header_idx)) base /\
                 MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal link_idx)) fp /\
                 SpecMajorAlloc.major_fl_valid (Ghost.reveal mh) fp fuel /\
                 SpecMajorAlloc.major_fl_above_zero (Ghost.reveal mh) fp fuel /\
                 U64.v requested_wz > 0 /\
                 (match MH.read_word_in_major (Ghost.reveal mh) base with
                  | Some hdr ->
                    U64.v (SpecObject.getWosize hdr) >= U64.v requested_wz /\
                    U64.v base +
                      (1 + U64.v (SpecObject.getWosize hdr)) * 8 <=
                      MH.chunk_end
                        (Seq.index (Ghost.reveal mh) (Ghost.reveal header_idx))
                  | None -> False))
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

/// Read and allocate from a later free-list node once the header proves the
/// block is large enough, relinking the already-read previous node.
fn allocate_major_found_prev_from_read (heap: MajorHeap.major_heap_t)
                                     (head: U64.t) (prev: obj_addr)
                                     (base: hp_addr) (cur: obj_addr)
                                     (requested_wz: wosize)
                                     (#fuel: (f:nat{f > 0}))
                                     (#cur_header_idx: Ghost.erased nat)
                                     (#cur_link_idx: Ghost.erased nat)
                                     (#prev_idx: Ghost.erased nat)
                                     (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (Ghost.reveal cur_header_idx < Seq.length (Ghost.reveal mh) /\
                 Ghost.reveal cur_link_idx < Seq.length (Ghost.reveal mh) /\
                 Ghost.reveal prev_idx < Seq.length (Ghost.reveal mh) /\
                 base == SpecHeap.hd_address cur /\
                 MH.lookup_chunk_index (Ghost.reveal mh) base ==
                   Some (Ghost.reveal cur_header_idx) /\
                 MH.lookup_chunk_index (Ghost.reveal mh) cur ==
                   Some (Ghost.reveal cur_link_idx) /\
                 MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_header_idx)) base /\
                 MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_link_idx)) cur /\
                 MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal prev_idx)) prev /\
                 (forall (k:nat). k < Ghost.reveal prev_idx ==>
                   ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh) k) prev)) /\
                 SpecMajorAlloc.major_fl_valid (Ghost.reveal mh) cur fuel /\
                 U64.v prev > 0 /\
                 U64.v cur >= U64.v zero_addr + U64.v mword /\
                 U64.v requested_wz > 0 /\
                 (match MH.read_word_in_major (Ghost.reveal mh) base with
                  | Some hdr ->
                    U64.v (SpecObject.getWosize hdr) >= U64.v requested_wz /\
                    U64.v base +
                      (1 + U64.v (SpecObject.getWosize hdr)) * 8 <=
                      MH.chunk_end
                       (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_header_idx))
                  | None -> False))
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

/// Read and allocate from a later free-list node, deriving current-node bounds
/// from `major_fl_above_zero` and the non-null previous-node fact from its
/// `obj_addr` type.
fn allocate_major_found_prev_from_read_above_zero
     (heap: MajorHeap.major_heap_t)
     (head: U64.t) (prev: obj_addr)
     (base: hp_addr) (cur: obj_addr)
     (requested_wz: wosize)
     (#fuel: (f:nat{f > 0}))
     (#cur_header_idx: Ghost.erased nat)
     (#cur_link_idx: Ghost.erased nat)
     (#prev_idx: Ghost.erased nat)
     (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (Ghost.reveal cur_header_idx < Seq.length (Ghost.reveal mh) /\
                 Ghost.reveal cur_link_idx < Seq.length (Ghost.reveal mh) /\
                 Ghost.reveal prev_idx < Seq.length (Ghost.reveal mh) /\
                 base == SpecHeap.hd_address cur /\
                 MH.lookup_chunk_index (Ghost.reveal mh) base ==
                   Some (Ghost.reveal cur_header_idx) /\
                 MH.lookup_chunk_index (Ghost.reveal mh) cur ==
                   Some (Ghost.reveal cur_link_idx) /\
                 MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_header_idx)) base /\
                 MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_link_idx)) cur /\
                 MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal prev_idx)) prev /\
                 (forall (k:nat). k < Ghost.reveal prev_idx ==>
                   ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh) k) prev)) /\
                 SpecMajorAlloc.major_fl_valid (Ghost.reveal mh) cur fuel /\
                 SpecMajorAlloc.major_fl_above_zero (Ghost.reveal mh) cur fuel /\
                 U64.v requested_wz > 0 /\
                 (match MH.read_word_in_major (Ghost.reveal mh) base with
                  | Some hdr ->
                    U64.v (SpecObject.getWosize hdr) >= U64.v requested_wz /\
                    U64.v base +
                      (1 + U64.v (SpecObject.getWosize hdr)) * 8 <=
                      MH.chunk_end
                       (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_header_idx))
                  | None -> False))
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

/// Advance past a too-small current node, then allocate from the next free-list
/// node. The current node's link-word index becomes the previous-node relink
/// index for the allocation from `next`.
fn allocate_major_after_advance_from_read (heap: MajorHeap.major_heap_t)
                                         (head prev: U64.t)
                                         (cur_base: hp_addr) (cur: obj_addr)
                                         (next_base: hp_addr) (next: obj_addr)
                                         (requested_wz: wosize)
                                         (#fuel: (f:nat{f > 1}))
                                         (#cur_header_idx: Ghost.erased nat)
                                         (#cur_link_idx: Ghost.erased nat)
                                         (#next_header_idx: Ghost.erased nat)
                                         (#next_link_idx: Ghost.erased nat)
                                         (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (Ghost.reveal cur_header_idx < Seq.length (Ghost.reveal mh) /\
                  Ghost.reveal cur_link_idx < Seq.length (Ghost.reveal mh) /\
                  Ghost.reveal next_header_idx < Seq.length (Ghost.reveal mh) /\
                  Ghost.reveal next_link_idx < Seq.length (Ghost.reveal mh) /\
                  cur_base == SpecHeap.hd_address cur /\
                  next_base == SpecHeap.hd_address next /\
                  MH.lookup_chunk_index (Ghost.reveal mh) cur_base ==
                    Some (Ghost.reveal cur_header_idx) /\
                  MH.lookup_chunk_index (Ghost.reveal mh) cur ==
                    Some (Ghost.reveal cur_link_idx) /\
                  MH.lookup_chunk_index (Ghost.reveal mh) next_base ==
                    Some (Ghost.reveal next_header_idx) /\
                  MH.lookup_chunk_index (Ghost.reveal mh) next ==
                    Some (Ghost.reveal next_link_idx) /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_header_idx))
                    cur_base /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_link_idx)) cur /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal next_header_idx))
                    next_base /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal next_link_idx)) next /\
                  SpecMajorAlloc.major_fl_valid (Ghost.reveal mh) cur fuel /\
                  U64.v cur >= U64.v zero_addr + U64.v mword /\
                  U64.v next >= U64.v zero_addr + U64.v mword /\
                  U64.v requested_wz > 0 /\
                  MH.read_word_in_major (Ghost.reveal mh) cur == Some next /\
                  (match MH.read_word_in_major (Ghost.reveal mh) cur_base with
                   | Some hdr ->
                     U64.v (SpecObject.getWosize hdr) <
                       SpecAlloc.normalized_wosize (U64.v requested_wz)
                   | None -> False) /\
                  (match MH.read_word_in_major (Ghost.reveal mh) next_base with
                   | Some hdr ->
                     U64.v (SpecObject.getWosize hdr) >= U64.v requested_wz /\
                     U64.v next_base +
                       (1 + U64.v (SpecObject.getWosize hdr)) * 8 <=
                       MH.chunk_end
                        (Seq.index (Ghost.reveal mh) (Ghost.reveal next_header_idx))
                   | None -> False))
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

/// Same as `allocate_major_after_advance_from_read`, deriving the current and
/// successor lower-bound facts from `major_fl_above_zero`.
fn allocate_major_after_advance_from_read_above_zero
     (heap: MajorHeap.major_heap_t)
     (head prev: U64.t)
     (cur_base: hp_addr) (cur: obj_addr)
     (next_base: hp_addr) (next: obj_addr)
     (requested_wz: wosize)
     (#fuel: (f:nat{f > 1}))
     (#cur_header_idx: Ghost.erased nat)
     (#cur_link_idx: Ghost.erased nat)
     (#next_header_idx: Ghost.erased nat)
     (#next_link_idx: Ghost.erased nat)
     (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (Ghost.reveal cur_header_idx < Seq.length (Ghost.reveal mh) /\
                 Ghost.reveal cur_link_idx < Seq.length (Ghost.reveal mh) /\
                 Ghost.reveal next_header_idx < Seq.length (Ghost.reveal mh) /\
                 Ghost.reveal next_link_idx < Seq.length (Ghost.reveal mh) /\
                 cur_base == SpecHeap.hd_address cur /\
                 next_base == SpecHeap.hd_address next /\
                 MH.lookup_chunk_index (Ghost.reveal mh) cur_base ==
                   Some (Ghost.reveal cur_header_idx) /\
                 MH.lookup_chunk_index (Ghost.reveal mh) cur ==
                   Some (Ghost.reveal cur_link_idx) /\
                 MH.lookup_chunk_index (Ghost.reveal mh) next_base ==
                   Some (Ghost.reveal next_header_idx) /\
                 MH.lookup_chunk_index (Ghost.reveal mh) next ==
                   Some (Ghost.reveal next_link_idx) /\
                 MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_header_idx))
                   cur_base /\
                 MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_link_idx)) cur /\
                 MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal next_header_idx))
                   next_base /\
                 MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal next_link_idx)) next /\
                 SpecMajorAlloc.major_fl_valid (Ghost.reveal mh) cur fuel /\
                 SpecMajorAlloc.major_fl_above_zero
                   (Ghost.reveal mh) cur fuel /\
                 U64.v requested_wz > 0 /\
                 MH.read_word_in_major (Ghost.reveal mh) cur == Some next /\
                 (match MH.read_word_in_major (Ghost.reveal mh) cur_base with
                  | Some hdr ->
                    U64.v (SpecObject.getWosize hdr) <
                      SpecAlloc.normalized_wosize (U64.v requested_wz)
                  | None -> False) /\
                 (match MH.read_word_in_major (Ghost.reveal mh) next_base with
                  | Some hdr ->
                    U64.v (SpecObject.getWosize hdr) >= U64.v requested_wz /\
                    U64.v next_base +
                      (1 + U64.v (SpecObject.getWosize hdr)) * 8 <=
                     MH.chunk_end
                       (Seq.index (Ghost.reveal mh) (Ghost.reveal next_header_idx))
                  | None -> False))
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
                                             wz == SpecMajorAlloc.fresh_chunk_wosize_u64 c}))
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
                                              wz == SpecMajorAlloc.fresh_chunk_wosize_u64 c}))
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

/// Initialize and prepend a fresh chunk, exposing that the new fresh free-list
/// head is valid and remains above `zero_addr`.
fn expand_major_heap_owned_above_zero (heap: MajorHeap.major_heap_t)
                                      (base: hp_addr) (fp_out: obj_addr)
                                      (wz: wosize) (next_fp: U64.t)
                                      (#fuel: nat)
                                      (#mh: Ghost.erased MH.major_heap)
                                      (#fresh: Ghost.erased
                                        (c:MH.heap_chunk{c.base == base /\
                                                         fp_out == SpecMajorAlloc.fresh_chunk_object c /\
                                                         wz == SpecMajorAlloc.fresh_chunk_wosize_u64 c}))
  requires MajorHeap.chunk_range heap (Ghost.reveal fresh) **
           MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (MH.chunk_disjoint_from_all (Ghost.reveal fresh) (Ghost.reveal mh) /\
                 U64.v base >= U64.v zero_addr /\
                 next_fp <> fp_out /\
                 SpecMajorAlloc.major_fl_valid (Ghost.reveal mh) next_fp fuel /\
                 SpecMajorAlloc.major_fl_above_zero (Ghost.reveal mh) next_fp fuel)
  returns new_fp: U64.t
  ensures MajorHeap.is_indexed_major_heap heap
            (SpecMajorAlloc.expand_major_heap
              (Ghost.reveal mh) (Ghost.reveal fresh) next_fp).major_out **
          pure (let er =
                  SpecMajorAlloc.expand_major_heap
                    (Ghost.reveal mh) (Ghost.reveal fresh) next_fp in
                new_fp == er.fp_out /\
                SpecMajorAlloc.major_fl_valid er.major_out new_fp (fuel + 1) /\
                SpecMajorAlloc.major_fl_above_zero er.major_out new_fp (fuel + 1))

/// Allocate the entire freshly prepended free block.
fn allocate_fresh_expanded_exact (heap: MajorHeap.major_heap_t)
                                 (base: hp_addr) (fp_out: obj_addr)
                                 (wz: wosize) (next_fp: U64.t)
                                 (#mh: Ghost.erased MH.major_heap)
                                 (#fresh: Ghost.erased
                                   (c:MH.heap_chunk{c.base == base /\
                                                    fp_out == SpecMajorAlloc.fresh_chunk_object c /\
                                                    wz == SpecMajorAlloc.fresh_chunk_wosize_u64 c}))
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
                                                       fresh_wz == SpecMajorAlloc.fresh_chunk_wosize_u64 c}))
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
                                                    fresh_wz == SpecMajorAlloc.fresh_chunk_wosize_u64 c}))
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
                                                         fresh_wz == SpecMajorAlloc.fresh_chunk_wosize_u64 c}))
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
                                                     fresh_wz == SpecMajorAlloc.fresh_chunk_wosize_u64 c}))
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
                                                fresh_wz == SpecMajorAlloc.fresh_chunk_wosize_u64 c}))
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
                                                          fresh_wz == SpecMajorAlloc.fresh_chunk_wosize_u64 c}))
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
                                               fresh_wz == SpecMajorAlloc.fresh_chunk_wosize_u64 c}))
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
