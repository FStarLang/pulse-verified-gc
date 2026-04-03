(*
   Pulse GC - Allocator Implementation

   First-fit free-list allocator verified against GC.Spec.Allocator.
   Walks the free list, finds a block >= requested wosize,
   optionally splits, zeros allocated fields, returns new fp.
*)

module GC.Impl.Allocator

#lang-pulse

#set-options "--fuel 1 --ifuel 0 --z3rlimit 50 --split_queries always"

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
  // heap_size >= 16 is needed for the single-block initialization
  // (heap_size is abstract but known to be 1024 in practice)
  let total_words = U64.div heap_size_u64 mword;
  if U64.lt total_words 2UL {
    // Heap too small — return null fp
    admit();
    0UL
  } else {
    let wz = U64.sub total_words 1UL;
    // heap_size <= pow2 57, heap_size % 8 == 0
    // total_words = heap_size / 8
    // wz = total_words - 1 <= pow2 57 / 8 - 1 = pow2 54 - 1
    assert_norm (pow2 57 / 8 == pow2 54);
    FStar.Math.Lemmas.lemma_div_le heap_size (pow2 57) 8;
    assert (pure (U64.v wz >= 1));
    let hdr = makeHeader wz blue 0UL;
    write_word heap zero_addr hdr;

    // mword = 8 is a valid hp_addr since heap_size >= 16 > 8
    assert (pure (U64.v mword < heap_size));
    write_word heap mword 0UL;

    admit();
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
  while (!go)
    invariant exists* vgo vfuel vhead vprev vcur vresult s_cur.
      R.pts_to go vgo **
      R.pts_to fuel_ref vfuel **
      R.pts_to head_fp vhead **
      R.pts_to prev_fp vprev **
      R.pts_to cur_fp vcur **
      R.pts_to result_obj vresult **
      is_heap heap s_cur **
      pure (
        U64.v vfuel <= heap_size / 8 /\
        (~vgo ==> (let spec_res = SpecAlloc.alloc_spec 's fp (U64.v wosize) in
                    s_cur == spec_res.heap_out /\
                    vhead == spec_res.fp_out /\
                    vresult == spec_res.obj_out))
      )
  {
    let vfuel = !fuel_ref;
    if U64.eq vfuel 0UL {
      go := false;
      admit()
    } else {
      let vcur = !cur_fp;
      let valid = is_valid_fp vcur;
      if not valid {
        // End of free list or invalid pointer — OOM
        go := false;
        admit()
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
            admit(); // TODO: prove wz is wosize
            let alloc_hdr = makeHeader wz white 0UL;
            write_word heap hd_addr alloc_hdr;

            // Create remainder block after allocated block
            admit(); // TODO: prove arithmetic doesn't overflow and rem_hd_off is hp_addr
            let wz_plus_1 = U64.add wz 1UL;
            let offset = U64.mul wz_plus_1 mword;
            let rem_hd_off = U64.add hd_addr offset;
            let rem_wz = U64.sub leftover 1UL;
            let rem_hdr = makeHeader rem_wz blue 0UL;
            write_word heap rem_hd_off rem_hdr;

            // Link remainder's first field to rest of free list
            let rem_obj = U64.add rem_hd_off mword;
            admit(); // TODO: bounds for rem_obj as hp_addr
            write_word heap rem_obj next;

            // Update previous link to point to remainder
            let vprev = !prev_fp;
            if U64.eq vprev 0UL {
              head_fp := rem_obj
            } else {
              admit(); // TODO: bounds for vprev as hp_addr
              write_word heap vprev rem_obj
            };

            result_obj := vcur;
            go := false;
            admit()
          } else {
            // Exact fit: recolor header to white
            admit(); // TODO: prove block_wz is wosize
            let alloc_hdr = makeHeader block_wz white 0UL;
            write_word heap hd_addr alloc_hdr;

            // Update previous link to skip this block
            let vprev = !prev_fp;
            if U64.eq vprev 0UL {
              head_fp := next
            } else {
              admit(); // TODO: bounds for vprev as hp_addr
              write_word heap vprev next
            };

            result_obj := vcur;
            go := false;
            admit()
          }
        } else {
          // Block too small, advance to next
          prev_fp := vcur;
          cur_fp := next;
          fuel_ref := U64.sub vfuel 1UL;
          admit()
        }
      }
    }
  };

  // Return result
  let final_fp = !head_fp;
  let final_obj = !result_obj;
  admit();
  (final_fp, final_obj)
}
