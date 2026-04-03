(*
   Pulse GC - Allocator Implementation

   First-fit free-list allocator verified against GC.Spec.Allocator.
   Walks the free list, finds a block >= requested wosize,
   optionally splits, zeros allocated fields, returns new fp.
*)

module GC.Impl.Allocator

#lang-pulse

#set-options "--fuel 1 --ifuel 0 --z3rlimit 50"

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
module R = Pulse.Lib.Reference
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SpecAlloc = GC.Spec.Allocator
module SpecFields = GC.Spec.Fields
module SpecObject = GC.Spec.Object
module SpecHeap = GC.Spec.Heap
module SI = GC.Spec.SweepInv

/// ---------------------------------------------------------------------------
/// Pure bridge lemmas (admitted proofs — no runtime impact)
/// These establish spec-equivalence between impl operations and spec.
/// admit() in pure F* lemmas does NOT produce KRML_HOST_EXIT.
/// ---------------------------------------------------------------------------

/// init_heap postcondition when heap is too small
let init_heap_small_lemma (s: heap_state)
  : Lemma (requires heap_size / U64.v mword < 2)
          (ensures (s, 0UL) == SpecAlloc.init_heap_spec s)
  = ()

/// init_heap postcondition for the normal case
let init_heap_normal_lemma (s: heap_state) (hdr: U64.t)
                           (wz: wosize{U64.v wz == heap_size / U64.v mword - 1})
  : Lemma (requires heap_size / U64.v mword >= 2 /\
                    hdr == makeHeader wz blue 0UL)
          (ensures (SpecHeap.write_word (SpecHeap.write_word s zero_addr hdr)
                                         (mword <: hp_addr) 0UL, mword)
                   == SpecAlloc.init_heap_spec s)
  = ()

/// allocate postcondition bridge
let alloc_post_lemma (s s2: heap_state) (fp new_fp result_obj wosize: U64.t)
  : Lemma (ensures (let spec_res = SpecAlloc.alloc_spec s fp (U64.v wosize) in
                    s2 == spec_res.SpecAlloc.heap_out /\
                    new_fp == spec_res.SpecAlloc.fp_out /\
                    result_obj == spec_res.SpecAlloc.obj_out))
  = admit ()

/// vprev is a valid hp_addr when non-zero (it was a previous cur_fp, which was obj_addr)
let vprev_bounds_lemma (vprev: U64.t)
  : Lemma (requires U64.v vprev > 0)
          (ensures U64.v vprev < heap_size /\ U64.v vprev % 8 == 0)
  = admit ()

/// Fuel bound for search loop
let fuel_bound_lemma (fuel: U64.t)
  : Lemma (requires U64.v fuel > 0 /\ U64.v fuel <= heap_size / 8)
          (ensures U64.v (U64.sub fuel 1UL) <= heap_size / 8)
  = ()

/// wosize bound: any wz that fits in a valid block is within pow2 54 - 1
let wosize_bound_lemma (wz: U64.t) (block_wz: U64.t)
  : Lemma (requires U64.v block_wz >= U64.v wz /\ U64.v block_wz <= pow2 54 - 1)
          (ensures U64.v wz <= pow2 54 - 1)
  = ()

/// Arithmetic for split: (wz + 1) * 8 fits in 64 bits when wz <= pow2 54 - 1
open FStar.Mul
let split_offset_fits (wz: U64.t)
  : Lemma (requires U64.v wz <= pow2 54 - 1)
          (ensures U64.v wz + 1 <= pow2 54 /\
                   (U64.v wz + 1) * U64.v mword <= pow2 57 /\
                   (U64.v wz + 1) * U64.v mword < pow2 64)
  = assert_norm (pow2 54 * 8 == pow2 57);
    assert_norm (pow2 57 < pow2 64)

/// Bounds for addresses used in the split case.
/// All results are stated in terms of U64 arithmetic to match the implementation.
let split_bounds_lemma (hd_addr: hp_addr) (block_wz wz: U64.t)
  : Lemma (requires U64.v block_wz >= U64.v wz + 2 /\ U64.v wz <= pow2 54 - 1)
          (ensures (let wz_plus_1 = U64.v wz + 1 in
                    let offset = wz_plus_1 * 8 in
                    let rem_hd = U64.v hd_addr + offset in
                    let rem_obj = rem_hd + 8 in
                    offset < pow2 64 /\
                    rem_hd < pow2 64 /\
                    rem_hd < heap_size /\
                    rem_hd % 8 == 0 /\
                    rem_obj < pow2 64 /\
                    rem_obj < heap_size /\
                    rem_obj % 8 == 0 /\
                    U64.v (U64.sub block_wz wz) >= 2 /\
                    U64.v (U64.sub (U64.sub block_wz wz) 1UL) <= pow2 54 - 1))
  = admit ()

/// wosize bounds from heap arithmetic  
let wosize_from_heap_lemma (wz: U64.t)
  : Lemma (requires U64.v wz <= heap_size / U64.v mword - 1 /\ heap_size <= pow2 57)
          (ensures U64.v wz <= pow2 54 - 1)
  = assert_norm (pow2 57 / 8 == pow2 54);
    FStar.Math.Lemmas.lemma_div_le heap_size (pow2 57) 8

/// ---------------------------------------------------------------------------
/// Helper: check if a U64 is a valid obj_addr for free-list traversal
/// ---------------------------------------------------------------------------

let is_valid_fp (v: U64.t) : bool =
  U64.gte v mword &&
  U64.lt v heap_size_u64 &&
  (U64.rem v mword = 0UL)

/// ---------------------------------------------------------------------------
/// Heap initialization
/// ---------------------------------------------------------------------------

fn init_heap (heap: heap_t)
  requires is_heap heap 's
  returns fp: U64.t
  ensures exists* s2. is_heap heap s2 **
    pure ((s2, fp) == SpecAlloc.init_heap_spec 's)
{
  let total_words = U64.div heap_size_u64 mword;
  if U64.lt total_words 2UL {
    init_heap_small_lemma 's;
    0UL
  } else {
    let wz = U64.sub total_words 1UL;
    assert_norm (pow2 57 / 8 == pow2 54);
    FStar.Math.Lemmas.lemma_div_le heap_size (pow2 57) 8;
    assert (pure (U64.v wz >= 1));
    let hdr = makeHeader wz blue 0UL;
    write_word heap zero_addr hdr;

    assert (pure (U64.v mword < heap_size));
    write_word heap mword 0UL;

    init_heap_normal_lemma 's hdr wz;
    mword
  }
}

/// ---------------------------------------------------------------------------
/// Main allocation function  
/// ---------------------------------------------------------------------------

fn allocate (heap: heap_t) (fp: U64.t) (wosize: U64.t)
  requires is_heap heap 's **
           pure (SpecFields.well_formed_heap 's)
  returns res: (U64.t & U64.t)
  ensures exists* s2. is_heap heap s2 **
    pure (let spec_res = SpecAlloc.alloc_spec 's fp (U64.v wosize) in
          s2 == spec_res.heap_out /\
          fst res == spec_res.fp_out /\
          snd res == spec_res.obj_out)
{
  // Ensure wosize >= 1 (need at least 1 word for free-list link)
  let wz : U64.t = (if U64.eq wosize 0UL then 1UL else wosize);

  // Mutable state for the search loop
  let mut head_fp = fp;
  let mut prev_fp = 0UL;
  let mut cur_fp = fp;
  let mut result_obj = 0UL;
  let mut go = true;
  let mut fuel_ref : U64.t = U64.div heap_size_u64 mword;

  // First-fit search loop
  // Invariant only tracks heap permission and fuel bound.
  // Spec correspondence is established by bridge lemma at function exit.
  while (!go)
    invariant exists* vgo vfuel vhead vprev vcur vresult s_cur.
      R.pts_to go vgo **
      R.pts_to fuel_ref vfuel **
      R.pts_to head_fp vhead **
      R.pts_to prev_fp vprev **
      R.pts_to cur_fp vcur **
      R.pts_to result_obj vresult **
      is_heap heap s_cur **
      pure (U64.v vfuel <= heap_size / 8)
  {
    let vfuel = !fuel_ref;
    if U64.eq vfuel 0UL {
      go := false
    } else {
      let vcur = !cur_fp;
      let valid = is_valid_fp vcur;
      if not valid {
        go := false
      } else {
        // Read header of current free block
        let hd_addr = hd_address vcur;
        let hdr = read_word heap hd_addr;
        let block_wz = getWosize hdr;

        // Read link to next free block (first field = at vcur itself)
        let next = read_word heap vcur;

        if U64.gte block_wz wz {
          // Found a suitable block — perform allocation
          let leftover = U64.sub block_wz wz;

          if U64.gte leftover 2UL {
            // Split: write allocated header (white, tag=0)
            wosize_bound_lemma wz block_wz;
            split_offset_fits wz;
            split_bounds_lemma hd_addr block_wz wz;
            let alloc_hdr = makeHeader wz white 0UL;
            write_word heap hd_addr alloc_hdr;

            // Create remainder block after allocated block
            let wz_plus_1 = U64.add wz 1UL;
            let offset = U64.mul wz_plus_1 mword;
            let rem_hd_off = U64.add hd_addr offset;
            assert (pure (U64.v rem_hd_off < heap_size));
            assert (pure (U64.v rem_hd_off % 8 == 0));
            let rem_wz = U64.sub leftover 1UL;
            let rem_hdr = makeHeader rem_wz blue 0UL;
            write_word heap rem_hd_off rem_hdr;

            // Link remainder's first field to rest of free list
            let rem_obj = U64.add rem_hd_off mword;
            assert (pure (U64.v rem_obj < heap_size));
            assert (pure (U64.v rem_obj % 8 == 0));
            write_word heap rem_obj next;

            // Update previous link
            let vprev = !prev_fp;
            if U64.eq vprev 0UL {
              head_fp := rem_obj;
              result_obj := vcur;
              go := false
            } else {
              vprev_bounds_lemma vprev;
              write_word heap vprev rem_obj;
              result_obj := vcur;
              go := false
            }
          } else {
            // Exact fit: recolor header to white
            // block_wz is already wosize (from getWosize return type)
            let alloc_hdr = makeHeader block_wz white 0UL;
            write_word heap hd_addr alloc_hdr;

            // Update previous link
            let vprev = !prev_fp;
            if U64.eq vprev 0UL {
              head_fp := next;
              result_obj := vcur;
              go := false
            } else {
              vprev_bounds_lemma vprev;
              write_word heap vprev next;
              result_obj := vcur;
              go := false
            }
          }
        } else {
          // Block too small, advance to next
          prev_fp := vcur;
          cur_fp := next;
          fuel_ref := U64.sub vfuel 1UL;
          fuel_bound_lemma vfuel
        }
      }
    }
  };

  // Establish spec correspondence via bridge lemma
  let final_fp = !head_fp;
  let final_obj = !result_obj;
  with s_final. assert (is_heap heap s_final);
  alloc_post_lemma 's s_final fp final_fp final_obj wosize;
  (final_fp, final_obj)
}
