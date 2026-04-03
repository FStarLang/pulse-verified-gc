(*
   Pulse GC - Allocator Implementation

   First-fit free-list allocator verified against GC.Spec.Allocator.
   Walks the free list, finds a block >= requested wosize,
   optionally splits, returns new fp. Fully proved — 0 admits.
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
module SA = GC.Spec.Allocator
module SF = GC.Spec.Fields
module SO = GC.Spec.Object
module SH = GC.Spec.Heap
module SI = GC.Spec.SweepInv
open FStar.Mul

/// ---------------------------------------------------------------------------
/// Pure helper lemmas (all proven — no admits)
/// ---------------------------------------------------------------------------

/// init_heap postcondition when heap is too small
let init_heap_small_lemma (s: heap_state)
  : Lemma (requires heap_size / U64.v mword < 2)
          (ensures (s, 0UL) == SA.init_heap_spec s)
  = ()

/// init_heap postcondition for the normal case
let init_heap_normal_lemma (s: heap_state) (hdr: U64.t)
                           (wz: wosize{U64.v wz == heap_size / U64.v mword - 1})
  : Lemma (requires heap_size / U64.v mword >= 2 /\
                    hdr == makeHeader wz blue 0UL)
          (ensures (SH.write_word (SH.write_word s zero_addr hdr)
                                         (mword <: hp_addr) 0UL, mword)
                   == SA.init_heap_spec s)
  = ()

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
let split_offset_fits (wz: U64.t)
  : Lemma (requires U64.v wz <= pow2 54 - 1)
          (ensures U64.v wz + 1 <= pow2 54 /\
                   (U64.v wz + 1) * U64.v mword <= pow2 57 /\
                   (U64.v wz + 1) * U64.v mword < pow2 64)
  = assert_norm (pow2 54 * 8 == pow2 57);
    assert_norm (pow2 57 < pow2 64)

/// No-overflow for split address computations
let split_no_overflow (hd: hp_addr) (wz: U64.t)
  : Lemma (requires U64.v wz <= pow2 54 - 1)
          (ensures (let offset = (U64.v wz + 1) * 8 in
                    U64.v hd + offset < pow2 64 /\
                    U64.v hd + offset + 8 < pow2 64))
  = split_offset_fits wz;
    assert_norm (pow2 57 + pow2 57 == pow2 58);
    assert_norm (pow2 58 < pow2 64)

/// wosize bounds from heap arithmetic
let wosize_from_heap_lemma (wz: U64.t)
  : Lemma (requires U64.v wz <= heap_size / U64.v mword - 1 /\ heap_size <= pow2 57)
          (ensures U64.v wz <= pow2 54 - 1)
  = assert_norm (pow2 57 / 8 == pow2 54);
    FStar.Math.Lemmas.lemma_div_le heap_size (pow2 57) 8

/// Connect impl's hd_address with spec's (both are obj - mword)
let hd_address_eq (obj: obj_addr)
  : Lemma (hd_address obj == SH.hd_address obj)
  = SH.hd_address_spec obj

/// ---------------------------------------------------------------------------
/// Helper: check if a U64 is a valid obj_addr for free-list traversal
/// ---------------------------------------------------------------------------

let is_valid_fp (v: U64.t) : bool =
  U64.gte v mword &&
  U64.lt v heap_size_u64 &&
  (U64.rem v mword = 0UL)

/// ---------------------------------------------------------------------------
/// Heap initialization (fully proved)
/// ---------------------------------------------------------------------------

fn init_heap (heap: heap_t)
  requires is_heap heap 's
  returns fp: U64.t
  ensures exists* s2. is_heap heap s2 **
    pure ((s2, fp) == SA.init_heap_spec 's)
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
/// Main allocation function (fully proved — 0 admits)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 100"
fn allocate (heap: heap_t) (fp: U64.t) (wosize: U64.t)
  requires is_heap heap 's **
           pure (SF.well_formed_heap 's)
  returns res: (U64.t & U64.t)
  ensures exists* s2. is_heap heap s2 **
    pure (let spec_res = SA.alloc_spec 's fp (U64.v wosize) in
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

  // First-fit search loop with spec-correspondence invariant.
  // When go=true: heap unchanged, tracking alloc_search correspondence.
  // When go=false: result matches alloc_spec.
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
        (if vgo then
          s_cur == 's /\
          vhead == fp /\
          vresult == 0UL /\
          (vprev == 0UL \/
           (U64.v vprev >= U64.v mword /\
            U64.v vprev < heap_size /\
            U64.v vprev % U64.v mword == 0)) /\
          SA.alloc_search 's vhead vprev vcur (U64.v wz) (U64.v vfuel) ==
            SA.alloc_spec 's fp (U64.v wosize)
        else
          (let sr = SA.alloc_spec 's fp (U64.v wosize) in
           s_cur == sr.heap_out /\
           vhead == sr.fp_out /\
           vresult == sr.obj_out))
      )
  {
    let vfuel = !fuel_ref;
    if U64.eq vfuel 0UL {
      // Fuel exhausted — OOM
      let vh = !head_fp;
      let vp = !prev_fp;
      let vc = !cur_fp;
      SA.alloc_search_fuel_0 's vh vp vc (U64.v wz);
      go := false
    } else {
      let vcur = !cur_fp;
      let valid = is_valid_fp vcur;
      if not valid {
        // Invalid cur_fp — OOM
        let vh = !head_fp;
        let vp = !prev_fp;
        SA.alloc_search_invalid 's vh vp vcur (U64.v wz) (U64.v vfuel);
        go := false
      } else {
        // vcur is a valid obj_addr — bridge impl/spec symbols
        hd_address_eq vcur;
        let hd_addr = hd_address vcur;
        let hdr = read_word heap hd_addr;
        let block_wz = getWosize hdr;
        getWosize_eq hdr;  // GC.Impl.Object.getWosize == GC.Spec.Object.getWosize

        // Read link to next free block
        let next = read_word heap vcur;
        SA.spec_next_fp_eq 's (vcur <: obj_addr);

        if U64.gte block_wz wz {
          // Found a suitable block — perform allocation
          let leftover = U64.sub block_wz wz;
          let vh = !head_fp;
          let vp = !prev_fp;

          if U64.gte leftover 2UL {
            // === SPLIT CASE ===
            wosize_bound_lemma wz block_wz;
            split_offset_fits wz;
            split_no_overflow hd_addr wz;

            // Compute remainder address
            let wz_plus_1 = U64.add wz 1UL;
            let offset = U64.mul wz_plus_1 mword;
            let rem_hd_off = U64.add hd_addr offset;

            // Runtime bounds check matching spec's alloc_from_block
            if U64.gte rem_hd_off heap_size_u64 {
              // rem_hd out of bounds — spec returns (g1, next)
              SA.alloc_from_block_split_rem_hd_oob 's (vcur <: obj_addr) (U64.v wz) next;

              // Write alloc header (white, tag=0)
              let alloc_hdr = makeHeader wz white 0UL;
              write_word heap hd_addr alloc_hdr;

              if U64.eq vp 0UL {
                SA.alloc_search_found_head 's vh vp vcur (U64.v wz) (U64.v vfuel);
                head_fp := next;
                result_obj := vcur;
                go := false
              } else {
                SA.alloc_search_found_prev 's vh vp vcur (U64.v wz) (U64.v vfuel);
                write_word heap (vp <: hp_addr) next;
                result_obj := vcur;
                go := false
              }
            } else {
              // rem_hd valid
              assert (pure (U64.v rem_hd_off < heap_size));
              assert (pure (U64.v rem_hd_off % 8 == 0));
              let rem_obj = U64.add rem_hd_off mword;

              if U64.gte rem_obj heap_size_u64 {
                // rem_obj out of bounds
                // Call spec lemma BEFORE writes
                SA.alloc_from_block_split_rem_obj_oob 's (vcur <: obj_addr) (U64.v wz) next;

                // Perform writes matching spec
                let alloc_hdr = makeHeader wz white 0UL;
                write_word heap hd_addr alloc_hdr;
                let rem_wz_u = U64.sub leftover 1UL;
                let rem_hdr = makeHeader rem_wz_u blue 0UL;
                write_word heap rem_hd_off rem_hdr;

                if U64.eq vp 0UL {
                  SA.alloc_search_found_head 's vh vp vcur (U64.v wz) (U64.v vfuel);
                  head_fp := rem_obj;
                  result_obj := vcur;
                  go := false
                } else {
                  SA.alloc_search_found_prev 's vh vp vcur (U64.v wz) (U64.v vfuel);
                  write_word heap (vp <: hp_addr) rem_obj;
                  result_obj := vcur;
                  go := false
                }
              } else {
                // Normal split
                assert (pure (U64.v rem_obj < heap_size));
                assert (pure (U64.v rem_obj % 8 == 0));

                // Call spec lemma BEFORE writes
                SA.alloc_from_block_split_normal 's (vcur <: obj_addr) (U64.v wz) next;

                // Perform writes matching spec
                let alloc_hdr = makeHeader wz white 0UL;
                write_word heap hd_addr alloc_hdr;
                let rem_wz_u = U64.sub leftover 1UL;
                let rem_hdr = makeHeader rem_wz_u blue 0UL;
                write_word heap rem_hd_off rem_hdr;
                write_word heap rem_obj next;

                if U64.eq vp 0UL {
                  SA.alloc_search_found_head 's vh vp vcur (U64.v wz) (U64.v vfuel);
                  head_fp := rem_obj;
                  result_obj := vcur;
                  go := false
                } else {
                  SA.alloc_search_found_prev 's vh vp vcur (U64.v wz) (U64.v vfuel);
                  write_word heap (vp <: hp_addr) rem_obj;
                  result_obj := vcur;
                  go := false
                }
              }
            }
          } else {
            // === EXACT FIT CASE ===
            // Call spec lemma BEFORE writes
            SA.alloc_from_block_exact 's (vcur <: obj_addr) (U64.v wz) next;

            let alloc_hdr = makeHeader block_wz white 0UL;
            write_word heap hd_addr alloc_hdr;

            if U64.eq vp 0UL {
              SA.alloc_search_found_head 's vh vp vcur (U64.v wz) (U64.v vfuel);
              head_fp := next;
              result_obj := vcur;
              go := false
            } else {
              SA.alloc_search_found_prev 's vh vp vcur (U64.v wz) (U64.v vfuel);
              write_word heap (vp <: hp_addr) next;
              result_obj := vcur;
              go := false
            }
          }
        } else {
          // Block too small — advance to next
          let vh = !head_fp;
          let vp = !prev_fp;
          hd_address_eq vcur;
          SH.hd_address_spec (vcur <: obj_addr);
          SA.alloc_search_advance 's vh vp vcur (U64.v wz) (U64.v vfuel);
          prev_fp := vcur;
          cur_fp := next;
          fuel_ref := U64.sub vfuel 1UL;
          fuel_bound_lemma vfuel
        }
      }
    }
  };

  // Post-loop: invariant with go=false gives us spec correspondence
  let final_fp = !head_fp;
  let final_obj = !result_obj;
  (final_fp, final_obj)
}
#pop-options
