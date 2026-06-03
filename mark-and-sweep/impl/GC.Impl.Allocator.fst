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
module MH = GC.Spec.MajorHeap
module SA = GC.Spec.Allocator
module SMA = GC.Spec.MajorAllocator
module SF = GC.Spec.Fields
module SO = GC.Spec.Object
module SH = GC.Spec.Heap
module SI = GC.Spec.SweepInv
module AllocLemmas = GC.Spec.Allocator.Lemmas
module MajorHeap = GC.Impl.MajorHeap
module OR = Pulse.Lib.OnRange
module T = Pulse.Lib.Trade.Util

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

let u64_positive_not_zero (x: U64.t)
  : Lemma (requires U64.v x > 0)
         (ensures x <> 0UL)
  = assert_norm (U64.v 0UL == 0)

let u64_sub_one_value (x: U64.t)
  : Lemma (requires U64.v x > 0)
          (ensures U64.v (U64.sub x 1UL) == U64.v x - 1)
  = assert_norm (U64.v 1UL == 1)

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
  U64.gte v (U64.add zero_addr mword) &&
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

/// ---------------------------------------------------------------------------
/// Single-chunk indexed-major compatibility allocation
/// ---------------------------------------------------------------------------

fn allocate_single_indexed_major (heap: heap_t) (fp: U64.t) (wosize: U64.t)
  requires MajorHeap.inactive_prefix (MajorHeap.heap_as_major heap) 's **
           MajorHeap.is_indexed_major_heap
             (MajorHeap.heap_as_major heap)
             (MH.single_chunk_major_heap 's) **
           pure (SF.well_formed_heap 's)
  returns res: (U64.t & U64.t)
  ensures exists* s2.
    MajorHeap.inactive_prefix (MajorHeap.heap_as_major heap) s2 **
    MajorHeap.is_indexed_major_heap
      (MajorHeap.heap_as_major heap)
      (MH.single_chunk_major_heap s2) **
    pure (let spec_res =
            SMA.major_alloc_spec_with_fuel
              (MH.single_chunk_major_heap 's) fp (U64.v wosize)
              SA.alloc_search_fuel in
          let dense_res = SA.alloc_spec 's fp (U64.v wosize) in
          s2 == dense_res.heap_out /\
          fst res == dense_res.fp_out /\
          snd res == dense_res.obj_out /\
          MH.single_chunk_major_heap s2 == spec_res.major_alloc_out /\
          fst res == spec_res.major_fp_out /\
          snd res == spec_res.major_obj_out)
{
  MajorHeap.single_indexed_major_to_heap_as heap 's;
  let res = allocate heap fp wosize;
  with s2. assert (
    is_heap heap s2 **
    pure (let spec_res = SA.alloc_spec 's fp (U64.v wosize) in
          s2 == spec_res.heap_out /\
          fst res == spec_res.fp_out /\
          snd res == spec_res.obj_out));
  SMA.major_alloc_spec_with_fuel_single_chunk_compat
    's fp (U64.v wosize) SA.alloc_search_fuel;
  assert (pure (SA.alloc_spec 's fp (U64.v wosize) ==
                SA.alloc_spec_with_fuel 's fp (U64.v wosize) SA.alloc_search_fuel));
  assert (pure (let dense_res = SA.alloc_spec 's fp (U64.v wosize) in
                let spec_res =
                  SMA.major_alloc_spec_with_fuel
                    (MH.single_chunk_major_heap 's) fp (U64.v wosize)
                    SA.alloc_search_fuel in
                s2 == dense_res.heap_out /\
                fst res == dense_res.fp_out /\
                snd res == dense_res.obj_out /\
                MH.single_chunk_major_heap s2 == spec_res.major_alloc_out /\
                fst res == spec_res.major_fp_out /\
                snd res == spec_res.major_obj_out));
  MajorHeap.heap_to_single_indexed_major heap;
  res
}

/// ---------------------------------------------------------------------------
/// Weak-precondition allocation (for use during promotion)
/// ---------------------------------------------------------------------------
/// Same implementation as `allocate` but only requires well_formed_heap_part1
/// + fl_valid + fl_chain_terminates. The allocator logic only reads headers
/// and free-list link pointers — it never inspects object pointer fields,
/// so well_formed_heap_part2 (pointer closure) is not needed.

#push-options "--z3rlimit 100"
fn allocate_part1 (heap: heap_t) (fp: U64.t) (wosize: U64.t)
  requires is_heap heap 's **
           pure (SF.well_formed_heap_part1 's /\
                 AllocLemmas.fl_valid 's fp (heap_size / U64.v mword) /\
                 AllocLemmas.fl_chain_terminates 's fp (heap_size / U64.v mword))
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
      let vh = !head_fp;
      let vp = !prev_fp;
      let vc = !cur_fp;
      SA.alloc_search_fuel_0 's vh vp vc (U64.v wz);
      go := false
    } else {
      let vcur = !cur_fp;
      let valid = is_valid_fp vcur;
      if not valid {
        let vh = !head_fp;
        let vp = !prev_fp;
        SA.alloc_search_invalid 's vh vp vcur (U64.v wz) (U64.v vfuel);
        go := false
      } else {
        hd_address_eq vcur;
        let hd_addr = hd_address vcur;
        let hdr = read_word heap hd_addr;
        let block_wz = getWosize hdr;
        getWosize_eq hdr;

        let next = read_word heap vcur;
        SA.spec_next_fp_eq 's (vcur <: obj_addr);

        if U64.gte block_wz wz {
          let leftover = U64.sub block_wz wz;
          let vh = !head_fp;
          let vp = !prev_fp;

          if U64.gte leftover 2UL {
            // === SPLIT CASE ===
            wosize_bound_lemma wz block_wz;
            split_offset_fits wz;
            split_no_overflow hd_addr wz;

            let wz_plus_1 = U64.add wz 1UL;
            let offset = U64.mul wz_plus_1 mword;
            let rem_hd_off = U64.add hd_addr offset;

            if U64.gte rem_hd_off heap_size_u64 {
              SA.alloc_from_block_split_rem_hd_oob 's (vcur <: obj_addr) (U64.v wz) next;

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
              assert (pure (U64.v rem_hd_off < heap_size));
              assert (pure (U64.v rem_hd_off % 8 == 0));
              let rem_obj = U64.add rem_hd_off mword;

              if U64.gte rem_obj heap_size_u64 {
                SA.alloc_from_block_split_rem_obj_oob 's (vcur <: obj_addr) (U64.v wz) next;

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
                assert (pure (U64.v rem_obj < heap_size));
                assert (pure (U64.v rem_obj % 8 == 0));

                SA.alloc_from_block_split_normal 's (vcur <: obj_addr) (U64.v wz) next;

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

  let final_fp = !head_fp;
  let final_obj = !result_obj;
  (final_fp, final_obj)
}
#pop-options

fn allocate_part1_single_indexed_major (heap: heap_t) (fp: U64.t) (wosize: U64.t)
  requires MajorHeap.inactive_prefix (MajorHeap.heap_as_major heap) 's **
           MajorHeap.is_indexed_major_heap
             (MajorHeap.heap_as_major heap)
             (MH.single_chunk_major_heap 's) **
           pure (SF.well_formed_heap_part1 's /\
                 AllocLemmas.fl_valid 's fp (heap_size / U64.v mword) /\
                 AllocLemmas.fl_chain_terminates 's fp (heap_size / U64.v mword))
  returns res: (U64.t & U64.t)
  ensures exists* s2.
    MajorHeap.inactive_prefix (MajorHeap.heap_as_major heap) s2 **
    MajorHeap.is_indexed_major_heap
      (MajorHeap.heap_as_major heap)
      (MH.single_chunk_major_heap s2) **
    pure (let spec_res =
            SMA.major_alloc_spec_with_fuel
              (MH.single_chunk_major_heap 's) fp (U64.v wosize)
              SA.alloc_search_fuel in
          let dense_res = SA.alloc_spec 's fp (U64.v wosize) in
          s2 == dense_res.heap_out /\
          fst res == dense_res.fp_out /\
          snd res == dense_res.obj_out /\
          MH.single_chunk_major_heap s2 == spec_res.major_alloc_out /\
          fst res == spec_res.major_fp_out /\
          snd res == spec_res.major_obj_out)
{
  MajorHeap.single_indexed_major_to_heap_as heap 's;
  let res = allocate_part1 heap fp wosize;
  with s2. assert (
    is_heap heap s2 **
    pure (let spec_res = SA.alloc_spec 's fp (U64.v wosize) in
          s2 == spec_res.heap_out /\
          fst res == spec_res.fp_out /\
          snd res == spec_res.obj_out));
  SMA.major_alloc_spec_with_fuel_single_chunk_compat
    's fp (U64.v wosize) SA.alloc_search_fuel;
  assert (pure (SA.alloc_spec 's fp (U64.v wosize) ==
                SA.alloc_spec_with_fuel 's fp (U64.v wosize) SA.alloc_search_fuel));
  assert (pure (let dense_res = SA.alloc_spec 's fp (U64.v wosize) in
                let spec_res =
                  SMA.major_alloc_spec_with_fuel
                    (MH.single_chunk_major_heap 's) fp (U64.v wosize)
                    SA.alloc_search_fuel in
                s2 == dense_res.heap_out /\
                fst res == dense_res.fp_out /\
                snd res == dense_res.obj_out /\
                MH.single_chunk_major_heap s2 == spec_res.major_alloc_out /\
                fst res == spec_res.major_fp_out /\
                snd res == spec_res.major_obj_out));
  MajorHeap.heap_to_single_indexed_major heap;
  res
}

fn write_word_in_indexed_major_at_erased_chunk_index
  (h: MajorHeap.major_heap_t)
  (addr: hp_addr)
  (v: U64.t)
  (#idx: Ghost.erased nat)
  (#mh: Ghost.erased (mh0:MH.major_heap{
    Ghost.reveal idx < Seq.length mh0 /\
    MH.word_in_chunk (Seq.index mh0 (Ghost.reveal idx)) addr /\
    (forall (k:nat). k < Ghost.reveal idx ==>
      ~(MH.word_in_chunk (Seq.index mh0 k) addr))}))
  requires MajorHeap.is_indexed_major_heap h (Ghost.reveal mh)
  ensures MajorHeap.is_indexed_major_heap h
            (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx)
              (MH.write_word_in_chunk
                (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) addr v)) **
          pure (MH.write_word_in_major (Ghost.reveal mh) addr v ==
            Some (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx)
              (MH.write_word_in_chunk
                (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) addr v)))
{
  unfold (MajorHeap.is_indexed_major_heap h (Ghost.reveal mh));
  assert (pure (SZ.v h.size == heap_size));
  assert (pure (MH.well_formed_major_heap (Ghost.reveal mh)));
  MH.write_word_at_index_preserves_wf
    (Ghost.reveal mh) addr v (Ghost.reveal idx);
  MH.write_word_in_major_at_index
    (Ghost.reveal mh) addr v (Ghost.reveal idx);

  assert (pure (Seq.length (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx)
    (MH.write_word_in_chunk
      (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) addr v)) ==
    Seq.length (Ghost.reveal mh)));
  unfold (MajorHeap.indexed_chunk_ranges h (Ghost.reveal mh));
  OR.on_range_get (Ghost.reveal idx)
    #(MajorHeap.chunk_range_at h (Ghost.reveal mh))
    #0
    #(Seq.length (Ghost.reveal mh));
  MajorHeap.chunk_range_at_in_bounds h (Ghost.reveal mh) (Ghost.reveal idx);
  rewrite
    (MajorHeap.chunk_range_at h (Ghost.reveal mh) (Ghost.reveal idx))
  as
    (MajorHeap.chunk_range h
      (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)));
  MajorHeap.write_word_in_chunk h addr v
    #(Ghost.hide (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)));
  MajorHeap.chunk_range_at_update_same
    h (Ghost.reveal mh) (Ghost.reveal idx)
    (MH.write_word_in_chunk
      (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) addr v);
  rewrite
    (MajorHeap.chunk_range h
      (MH.write_word_in_chunk
        (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) addr v))
  as
    (MajorHeap.chunk_range_at h
      (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx)
        (MH.write_word_in_chunk
          (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) addr v))
      (Ghost.reveal idx));
  assert (pure (forall k. 0 <= k /\ k < Ghost.reveal idx ==>
    MajorHeap.chunk_range_at h (Ghost.reveal mh) k ==
    MajorHeap.chunk_range_at h
      (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx)
        (MH.write_word_in_chunk
          (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) addr v))
      k));
  OR.on_range_frame
    (MajorHeap.chunk_range_at h (Ghost.reveal mh))
    (MajorHeap.chunk_range_at h
      (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx)
        (MH.write_word_in_chunk
          (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) addr v)))
    0
    (Ghost.reveal idx);
  rewrite
    (OR.on_range
      (MajorHeap.chunk_range_at h (Ghost.reveal mh))
      0
      (Ghost.reveal idx))
  as
    (OR.on_range
      (MajorHeap.chunk_range_at h
        (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx)
          (MH.write_word_in_chunk
            (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) addr v)))
      0
      (Ghost.reveal idx));
  assert (pure (forall k. Ghost.reveal idx + 1 <= k /\
    k < Seq.length (Ghost.reveal mh) ==>
    MajorHeap.chunk_range_at h (Ghost.reveal mh) k ==
    MajorHeap.chunk_range_at h
      (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx)
        (MH.write_word_in_chunk
          (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) addr v))
      k));
  OR.on_range_frame
    (MajorHeap.chunk_range_at h (Ghost.reveal mh))
    (MajorHeap.chunk_range_at h
      (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx)
        (MH.write_word_in_chunk
          (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) addr v)))
    (Ghost.reveal idx + 1)
    (Seq.length (Ghost.reveal mh));
  rewrite
    (OR.on_range
      (MajorHeap.chunk_range_at h (Ghost.reveal mh))
      (Ghost.reveal idx + 1)
      (Seq.length (Ghost.reveal mh)))
  as
    (OR.on_range
      (MajorHeap.chunk_range_at h
        (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx)
          (MH.write_word_in_chunk
            (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) addr v)))
      (Ghost.reveal idx + 1)
      (Seq.length (Ghost.reveal mh)));
  OR.on_range_put 0 (Ghost.reveal idx) (Seq.length (Ghost.reveal mh))
    #(MajorHeap.chunk_range_at h
      (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx)
        (MH.write_word_in_chunk
          (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) addr v)));
  rewrite each (Seq.length (Ghost.reveal mh)) as
    Seq.length (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx)
      (MH.write_word_in_chunk
        (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) addr v));
  fold (MajorHeap.indexed_chunk_ranges h
    (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx)
      (MH.write_word_in_chunk
        (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) addr v)));
  fold (MajorHeap.is_indexed_major_heap h
    (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx)
      (MH.write_word_in_chunk
        (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) addr v)))
}

fn write_word_in_indexed_major_at_erased_lookup_index
  (h: MajorHeap.major_heap_t)
  (addr: hp_addr)
  (v: U64.t)
  (#idx: Ghost.erased nat)
  (#mh: Ghost.erased (mh0:MH.major_heap{
    Ghost.reveal idx < Seq.length mh0 /\
    MH.lookup_chunk_index mh0 addr == Some (Ghost.reveal idx) /\
    MH.word_in_chunk (Seq.index mh0 (Ghost.reveal idx)) addr}))
  requires MajorHeap.is_indexed_major_heap h (Ghost.reveal mh)
  ensures MajorHeap.is_indexed_major_heap h
            (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx)
              (MH.write_word_in_chunk
                (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) addr v)) **
          pure (MH.write_word_in_major (Ghost.reveal mh) addr v ==
            Some (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx)
              (MH.write_word_in_chunk
                (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) addr v)))
{
  MH.lookup_chunk_index_some
    (Ghost.reveal mh) addr (Ghost.reveal idx);
  assert (pure (forall (k:nat). k < Ghost.reveal idx ==>
    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh) k) addr)));
  MH.write_word_in_major_at_lookup_index
    (Ghost.reveal mh) addr v (Ghost.reveal idx);
  write_word_in_indexed_major_at_erased_chunk_index h addr v
    #idx #(Ghost.hide (Ghost.reveal mh))
}

fn allocate_major_head_no_split (heap: MajorHeap.major_heap_t)
                                (base: hp_addr) (fp: obj_addr)
                                (hdr: U64.t) (block_wz requested_wz: wosize)
                                (next_fp: U64.t)
                                (#fuel: nat) (#idx: Ghost.erased nat)
                                (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (fuel > 0 /\
                  Ghost.reveal idx < Seq.length (Ghost.reveal mh) /\
                  base == SH.hd_address fp /\
                  MH.lookup_chunk_index (Ghost.reveal mh) base ==
                    Some (Ghost.reveal idx) /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) base /\
                  MH.read_word_in_major (Ghost.reveal mh) base == Some hdr /\
                  MH.read_word_in_major (Ghost.reveal mh) fp == Some next_fp /\
                  block_wz == SO.getWosize hdr /\
                  U64.v fp >= U64.v zero_addr + U64.v mword /\
                  U64.v block_wz >= SA.normalized_wosize (U64.v requested_wz) /\
                  U64.v block_wz - SA.normalized_wosize (U64.v requested_wz) < 2)
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap
             (let r =
                SMA.major_alloc_spec_with_fuel
                  (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
              r.major_alloc_out) **
           pure (let r =
                   SMA.major_alloc_spec_with_fuel
                     (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
                 fst res == r.major_fp_out /\
                 snd res == r.major_obj_out)
{
  let alloc_hdr = makeHeader block_wz white 0UL;
  assert (pure (SA.white_bits == 0UL));
  assert (pure (pack_color white == 0UL));
  assert (pure (alloc_hdr == SA.make_header block_wz SA.white_bits 0UL));
  assert (pure (alloc_hdr == SA.make_header (SO.getWosize hdr) SA.white_bits 0UL));
  assert (pure (base == SH.hd_address fp));
  SMA.major_alloc_head_no_split
    (Ghost.reveal mh) fp (U64.v requested_wz) fuel hdr next_fp;
  write_word_in_indexed_major_at_erased_lookup_index heap base alloc_hdr
    #idx #(Ghost.hide (Ghost.reveal mh));
  assert (pure (MH.write_word_in_major (Ghost.reveal mh) base alloc_hdr ==
                Some (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx)
                  (MH.write_word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal idx))
                    base alloc_hdr))));
  SMA.major_write_word_or_same_some
    (Ghost.reveal mh)
    (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx)
      (MH.write_word_in_chunk
        (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) base alloc_hdr))
    base alloc_hdr;
  assert (pure (SMA.major_write_word_or_same
                  (Ghost.reveal mh) (SH.hd_address fp) alloc_hdr ==
                Seq.upd (Ghost.reveal mh) (Ghost.reveal idx)
                  (MH.write_word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal idx))
                    base alloc_hdr)));
  assert (pure (let r =
                  SMA.major_alloc_spec_with_fuel
                    (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
                r.major_alloc_out ==
                  Seq.upd (Ghost.reveal mh) (Ghost.reveal idx)
                    (MH.write_word_in_chunk
                      (Seq.index (Ghost.reveal mh) (Ghost.reveal idx))
                      base alloc_hdr) /\
                r.major_fp_out == next_fp /\
                r.major_obj_out == fp));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx)
        (MH.write_word_in_chunk
          (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) base alloc_hdr)))
  as
    (MajorHeap.is_indexed_major_heap heap
      (let r =
         SMA.major_alloc_spec_with_fuel
           (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
       r.major_alloc_out));
  assert (pure (let r =
                  SMA.major_alloc_spec_with_fuel
                    (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
                next_fp == r.major_fp_out /\
                fp == r.major_obj_out));
  (next_fp, fp)
}

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
                  base == SH.hd_address fp /\
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
                  block_wz == SO.getWosize hdr /\
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
                SMA.major_alloc_spec_with_fuel
                  (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
              r.major_alloc_out) **
           pure (let r =
                   SMA.major_alloc_spec_with_fuel
                     (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
                 fst res == r.major_fp_out /\
                 snd res == r.major_obj_out)
{
  let alloc_hdr = makeHeader requested_wz white 0UL;
  assert (pure (SA.white_bits == 0UL));
  assert (pure (pack_color white == 0UL));
  assert (pure (U64.uint_to_t (U64.v requested_wz) == requested_wz));
  assert (pure (alloc_hdr ==
                SA.make_header (U64.uint_to_t (U64.v requested_wz))
                  SA.white_bits 0UL));

  let leftover = U64.sub block_wz requested_wz;
  let rem_wz_u = U64.sub leftover 1UL;
  assert (pure (U64.v leftover == U64.v block_wz - U64.v requested_wz));
  assert (pure (U64.v rem_wz_u == U64.v block_wz - U64.v requested_wz - 1));
  assert (pure (U64.v rem_wz_u < pow2 54));
  let rem_hdr = makeHeader rem_wz_u blue 0UL;
  assert (pure (SA.blue_bits == 2UL));
  assert (pure (pack_color blue == 2UL));
  assert (pure (U64.uint_to_t (U64.v rem_wz_u) == rem_wz_u));
  assert (pure (rem_hdr ==
                SA.make_header
                  (U64.uint_to_t (U64.v block_wz - U64.v requested_wz - 1))
                  SA.blue_bits 0UL));

  SMA.major_alloc_head_split
    (Ghost.reveal mh) fp (U64.v requested_wz) fuel hdr next_fp
    rem_hd rem_obj;

  let c0 = Ghost.hide (Seq.index (Ghost.reveal mh) (Ghost.reveal idx));
  let c1 = Ghost.hide (MH.write_word_in_chunk (Ghost.reveal c0) base alloc_hdr);
  let c2 = Ghost.hide (MH.write_word_in_chunk (Ghost.reveal c1) rem_hd rem_hdr);
  let c3 = Ghost.hide (MH.write_word_in_chunk (Ghost.reveal c2) rem_obj next_fp);

  write_word_in_indexed_major_at_erased_lookup_index heap base alloc_hdr
    #idx #(Ghost.hide (Ghost.reveal mh));
  assert (pure (Seq.index (Ghost.reveal mh) (Ghost.reveal idx) == Ghost.reveal c0));
  assert (pure (MH.write_word_in_chunk
                  (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) base alloc_hdr ==
                Ghost.reveal c1));
  assert (pure (MH.write_word_in_major (Ghost.reveal mh) base alloc_hdr ==
                Some (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx) (Ghost.reveal c1))));
  SMA.major_write_word_or_same_some
    (Ghost.reveal mh) (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx) (Ghost.reveal c1))
    base alloc_hdr;

  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx)
        (MH.write_word_in_chunk
          (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) base alloc_hdr)))
  as
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx) (Ghost.reveal c1)));

  let mh1 = Ghost.hide (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx) (Ghost.reveal c1));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx) (Ghost.reveal c1)))
  as
    (MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh1));
  assert (pure (Seq.length (Ghost.reveal mh1) == Seq.length (Ghost.reveal mh)));
  assert (pure (Ghost.reveal idx < Seq.length (Ghost.reveal mh1)));
  assert (pure (Seq.index (Ghost.reveal mh1) (Ghost.reveal idx) == Ghost.reveal c1));
  MH.write_word_in_chunk_preserves_word (Ghost.reveal c0) base alloc_hdr rem_hd;
  assert (pure (MH.word_in_chunk (Ghost.reveal c1) rem_hd));
  assert (pure (MH.word_in_chunk (Seq.index (Ghost.reveal mh1) (Ghost.reveal idx)) rem_hd));
  assert (pure (forall (k:nat). k < Ghost.reveal idx ==>
    Seq.index (Ghost.reveal mh1) k == Seq.index (Ghost.reveal mh) k));
  assert (pure (forall (k:nat). k < Ghost.reveal idx ==>
    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh1) k) rem_hd)));
  write_word_in_indexed_major_at_erased_chunk_index heap rem_hd rem_hdr
    #idx #(Ghost.hide (Ghost.reveal mh1));
  assert (pure (MH.write_word_in_major (Ghost.reveal mh1) rem_hd rem_hdr ==
                Some (Seq.upd (Ghost.reveal mh1) (Ghost.reveal idx) (Ghost.reveal c2))));
  SMA.major_write_word_or_same_some
    (Ghost.reveal mh1) (Seq.upd (Ghost.reveal mh1) (Ghost.reveal idx) (Ghost.reveal c2))
    rem_hd rem_hdr;
  SMA.seq_upd_overwrite_index (Ghost.reveal mh) (Ghost.reveal idx) (Ghost.reveal c1) (Ghost.reveal c2);
  assert (pure (Seq.upd (Ghost.reveal mh1) (Ghost.reveal idx) (Ghost.reveal c2) ==
                Seq.upd (Ghost.reveal mh) (Ghost.reveal idx) (Ghost.reveal c2)));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh1) (Ghost.reveal idx)
        (MH.write_word_in_chunk
          (Seq.index (Ghost.reveal mh1) (Ghost.reveal idx)) rem_hd rem_hdr)))
  as
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx) (Ghost.reveal c2)));

  let mh2 = Ghost.hide (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx) (Ghost.reveal c2));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx) (Ghost.reveal c2)))
  as
    (MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh2));
  assert (pure (Seq.length (Ghost.reveal mh2) == Seq.length (Ghost.reveal mh)));
  assert (pure (Ghost.reveal idx < Seq.length (Ghost.reveal mh2)));
  assert (pure (Seq.index (Ghost.reveal mh2) (Ghost.reveal idx) == Ghost.reveal c2));
  MH.write_word_in_chunk_preserves_word (Ghost.reveal c1) rem_hd rem_hdr rem_obj;
  assert (pure (MH.word_in_chunk (Ghost.reveal c2) rem_obj));
  assert (pure (MH.word_in_chunk (Seq.index (Ghost.reveal mh2) (Ghost.reveal idx)) rem_obj));
  assert (pure (forall (k:nat). k < Ghost.reveal idx ==>
    Seq.index (Ghost.reveal mh2) k == Seq.index (Ghost.reveal mh) k));
  assert (pure (forall (k:nat). k < Ghost.reveal idx ==>
    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh2) k) rem_obj)));
  write_word_in_indexed_major_at_erased_chunk_index heap rem_obj next_fp
    #idx #(Ghost.hide (Ghost.reveal mh2));
  assert (pure (MH.write_word_in_major (Ghost.reveal mh2) rem_obj next_fp ==
                Some (Seq.upd (Ghost.reveal mh2) (Ghost.reveal idx) (Ghost.reveal c3))));
  SMA.major_write_word_or_same_some
    (Ghost.reveal mh2) (Seq.upd (Ghost.reveal mh2) (Ghost.reveal idx) (Ghost.reveal c3))
    rem_obj next_fp;
  SMA.seq_upd_overwrite_index (Ghost.reveal mh) (Ghost.reveal idx) (Ghost.reveal c2) (Ghost.reveal c3);
  assert (pure (Seq.upd (Ghost.reveal mh2) (Ghost.reveal idx) (Ghost.reveal c3) ==
                Seq.upd (Ghost.reveal mh) (Ghost.reveal idx) (Ghost.reveal c3)));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh2) (Ghost.reveal idx)
        (MH.write_word_in_chunk
          (Seq.index (Ghost.reveal mh2) (Ghost.reveal idx)) rem_obj next_fp)))
  as
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx) (Ghost.reveal c3)));

  assert (pure (let r =
                  SMA.major_alloc_spec_with_fuel
                    (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
                r.major_alloc_out == Seq.upd (Ghost.reveal mh) (Ghost.reveal idx) (Ghost.reveal c3) /\
                r.major_fp_out == rem_obj /\
                r.major_obj_out == fp));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) (Ghost.reveal idx) (Ghost.reveal c3)))
  as
    (MajorHeap.is_indexed_major_heap heap
      (let r =
         SMA.major_alloc_spec_with_fuel
           (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
       r.major_alloc_out));
  assert (pure (let r =
                  SMA.major_alloc_spec_with_fuel
                    (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
                rem_obj == r.major_fp_out /\
                fp == r.major_obj_out));
  let out_fp : U64.t = rem_obj;
  let out_obj : U64.t = fp;
  (out_fp, out_obj)
}

fn allocate_major_head (heap: MajorHeap.major_heap_t)
                       (base: hp_addr) (fp: obj_addr)
                       (hdr: U64.t) (block_wz requested_wz: wosize)
                       (next_fp: U64.t)
                       (#fuel: nat) (#idx: Ghost.erased nat)
                       (#mh: Ghost.erased MH.major_heap)
    requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
             pure (fuel > 0 /\
                   Ghost.reveal idx < Seq.length (Ghost.reveal mh) /\
                   base == SH.hd_address fp /\
                   MH.lookup_chunk_index (Ghost.reveal mh) base ==
                    Some (Ghost.reveal idx) /\
                   MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) base /\
                   MH.read_word_in_major (Ghost.reveal mh) base == Some hdr /\
                   MH.read_word_in_major (Ghost.reveal mh) fp == Some next_fp /\
                   block_wz == SO.getWosize hdr /\
                   U64.v fp >= U64.v zero_addr + U64.v mword /\
                   U64.v requested_wz > 0 /\
                   U64.v block_wz >= U64.v requested_wz /\
                   U64.v base + (1 + U64.v block_wz) * 8 <=
                     MH.chunk_end
                       (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)))
    returns res: (U64.t & U64.t)
    ensures MajorHeap.is_indexed_major_heap heap
              (let r =
                 SMA.major_alloc_spec_with_fuel
                   (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
               r.major_alloc_out) **
            pure (let r =
                    SMA.major_alloc_spec_with_fuel
                      (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
                  fst res == r.major_fp_out /\
                  snd res == r.major_obj_out)
{
  let leftover = U64.sub block_wz requested_wz;
  assert (pure (U64.v leftover == U64.v block_wz - U64.v requested_wz));
  if U64.gte leftover 2UL {
    assert (pure (U64.v block_wz - U64.v requested_wz >= 2));
    wosize_bound_lemma requested_wz block_wz;
    split_offset_fits requested_wz;
    split_no_overflow base requested_wz;

    let wz_plus_1 = U64.add requested_wz 1UL;
    assert (pure (U64.v wz_plus_1 == U64.v requested_wz + 1));
    let offset = U64.mul wz_plus_1 mword;
    assert (pure (U64.v offset == (1 + U64.v requested_wz) * U64.v mword));
    assert (pure (U64.v offset == (1 + U64.v requested_wz) * 8));
    let rem_hd = U64.add base offset;
    assert (pure (U64.v rem_hd == U64.v base + (1 + U64.v requested_wz) * 8));
    assert (pure (U64.v rem_hd < heap_size));
    assert (pure (U64.v rem_hd % U64.v mword == 0));
    let rem_obj = U64.add rem_hd mword;
    assert (pure (U64.v rem_obj == U64.v rem_hd + U64.v mword));
    assert (pure (U64.v rem_obj < heap_size));
    assert (pure (U64.v rem_obj % U64.v mword == 0));

    unfold (MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh));
    assert (pure (MH.well_formed_major_heap (Ghost.reveal mh)));
    fold (MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh));

    SMA.active_head_split_remainder_words_in_chunk
      (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) base
      (U64.v block_wz) (U64.v requested_wz) rem_hd rem_obj;
    assert (pure (MH.well_formed_major_heap (Ghost.reveal mh)));
    assert (pure (Ghost.reveal idx < Seq.length (Ghost.reveal mh)));
    assert (pure (MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) rem_hd));
    assert (pure (MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) rem_obj));
    SMA.well_formed_no_prior_word_in_selected_chunk
      (Ghost.reveal mh) (Ghost.reveal idx) rem_hd;
    SMA.well_formed_no_prior_word_in_selected_chunk
      (Ghost.reveal mh) (Ghost.reveal idx) rem_obj;
    let res =
      allocate_major_head_split
        heap base fp hdr block_wz requested_wz rem_hd rem_obj next_fp
        #fuel #idx #mh;
    assert (pure (let r =
                    SMA.major_alloc_spec_with_fuel
                      (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
                  fst res == r.major_fp_out /\
                  snd res == r.major_obj_out));
    res
  } else {
    assert (pure (U64.v block_wz -
                  SA.normalized_wosize (U64.v requested_wz) < 2));
    let res =
      allocate_major_head_no_split
        heap base fp hdr block_wz requested_wz next_fp #fuel #idx #mh;
    assert (pure (let r =
                    SMA.major_alloc_spec_with_fuel
                      (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
                  fst res == r.major_fp_out /\
                  snd res == r.major_obj_out));
    res
  }
}

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
                  base == SH.hd_address cur /\
                  MH.lookup_chunk_index (Ghost.reveal mh) base ==
                   Some (Ghost.reveal idx) /\
                  MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)) base /\
                  MH.read_word_in_major (Ghost.reveal mh) base == Some hdr /\
                  MH.read_word_in_major (Ghost.reveal mh) cur == Some next_fp /\
                  block_wz == SO.getWosize hdr /\
                  U64.v cur >= U64.v zero_addr + U64.v mword /\
                  U64.v block_wz <
                    SA.normalized_wosize (U64.v requested_wz))
   returns next: U64.t
   ensures MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (next == next_fp /\
                 SMA.major_alloc_search
                   (Ghost.reveal mh) head prev cur
                   (SA.normalized_wosize (U64.v requested_wz)) fuel ==
                 SMA.major_alloc_search
                   (Ghost.reveal mh) head cur next_fp
                   (SA.normalized_wosize (U64.v requested_wz)) (fuel - 1))
{
  assert (pure (base == SH.hd_address cur));
  assert (pure (MH.read_word_in_major (Ghost.reveal mh) (SH.hd_address cur) ==
                Some hdr));
  SMA.major_spec_next_fp_some (Ghost.reveal mh) cur next_fp;
  assert (pure (SMA.major_spec_next_fp (Ghost.reveal mh) cur == next_fp));
  assert (pure (U64.v (SO.getWosize hdr) <
                SA.normalized_wosize (U64.v requested_wz)));
  SMA.major_alloc_search_advance
    (Ghost.reveal mh) head prev cur
    (SA.normalized_wosize (U64.v requested_wz)) fuel hdr;
  assert (pure (SMA.major_alloc_search
                  (Ghost.reveal mh) head prev cur
                  (SA.normalized_wosize (U64.v requested_wz)) fuel ==
                SMA.major_alloc_search
                  (Ghost.reveal mh) head cur
                  (SMA.major_spec_next_fp (Ghost.reveal mh) cur)
                  (SA.normalized_wosize (U64.v requested_wz)) (fuel - 1)));
  assert (pure (SMA.major_alloc_search
                  (Ghost.reveal mh) head cur
                  (SMA.major_spec_next_fp (Ghost.reveal mh) cur)
                  (SA.normalized_wosize (U64.v requested_wz)) (fuel - 1) ==
                SMA.major_alloc_search
                  (Ghost.reveal mh) head cur next_fp
                  (SA.normalized_wosize (U64.v requested_wz)) (fuel - 1)));
  next_fp
}

fn read_word_in_indexed_major_at_erased_lookup_index
  (h: MajorHeap.major_heap_t)
  (addr: hp_addr)
  (#idx: Ghost.erased nat)
  (#mh: Ghost.erased (mh0:MH.major_heap{
    Ghost.reveal idx < Seq.length mh0 /\
    MH.lookup_chunk_index mh0 addr == Some (Ghost.reveal idx) /\
    MH.word_in_chunk (Seq.index mh0 (Ghost.reveal idx)) addr}))
  requires MajorHeap.is_indexed_major_heap h (Ghost.reveal mh)
  returns v: U64.t
  ensures MajorHeap.is_indexed_major_heap h (Ghost.reveal mh) **
          pure (MH.read_word_in_major (Ghost.reveal mh) addr == Some v)
{
  unfold (MajorHeap.is_indexed_major_heap h (Ghost.reveal mh));
  unfold (MajorHeap.indexed_chunk_ranges h (Ghost.reveal mh));
  OR.on_range_focus (Ghost.reveal idx)
    #(MajorHeap.chunk_range_at h (Ghost.reveal mh))
    #0
    #(Seq.length (Ghost.reveal mh));
  MajorHeap.chunk_range_at_in_bounds h (Ghost.reveal mh) (Ghost.reveal idx);
  rewrite
    (MajorHeap.chunk_range_at h (Ghost.reveal mh) (Ghost.reveal idx))
  as
    (MajorHeap.chunk_range h
      (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)));
  let v =
    MajorHeap.read_word_in_chunk h addr
      #(Ghost.hide (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)));
  MajorHeap.chunk_range_at_in_bounds h (Ghost.reveal mh) (Ghost.reveal idx);
  rewrite
    (MajorHeap.chunk_range h
      (Seq.index (Ghost.reveal mh) (Ghost.reveal idx)))
  as
    (MajorHeap.chunk_range_at h (Ghost.reveal mh) (Ghost.reveal idx));
  T.elim _ _;
  fold (MajorHeap.indexed_chunk_ranges h (Ghost.reveal mh));
  MH.read_word_in_major_at_lookup_index
    (Ghost.reveal mh) addr (Ghost.reveal idx);
  fold (MajorHeap.is_indexed_major_heap h (Ghost.reveal mh));
  v
}

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
                    (Ghost.reveal mh) (SH.hd_address cur) ==
                    Some (Ghost.reveal header_idx) /\
                  MH.lookup_chunk_index (Ghost.reveal mh) cur ==
                    Some (Ghost.reveal link_idx) /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal header_idx))
                    (SH.hd_address cur) /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal link_idx)) cur /\
                  SMA.major_fl_valid (Ghost.reveal mh) cur fuel)
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (let hdr = fst res in
                 let next = snd res in
                 MH.read_word_in_major (Ghost.reveal mh) (SH.hd_address cur) ==
                   Some hdr /\
                 MH.read_word_in_major (Ghost.reveal mh) cur == Some next /\
                 U64.v (SO.getWosize hdr) >= 1 /\
                 next <> cur /\
                 SMA.major_fl_valid (Ghost.reveal mh) next (fuel - 1))
{
  assert (pure (U64.v cur >= U64.v mword));
  assert (pure (U64.v cur < heap_size));
  assert (pure (U64.v cur % U64.v mword == 0));
  SMA.major_fl_valid_gives_wosize (Ghost.reveal mh) cur fuel;
  SMA.major_fl_valid_next (Ghost.reveal mh) cur fuel;
  SMA.major_fl_valid_header_lookup_index (Ghost.reveal mh) cur fuel;
  SMA.major_fl_valid_link_lookup_index (Ghost.reveal mh) cur fuel;

  let base = SH.hd_address cur;
  assert (pure (Ghost.reveal header_idx < Seq.length (Ghost.reveal mh)));
  assert (pure (MH.word_in_chunk
                  (Seq.index (Ghost.reveal mh) (Ghost.reveal header_idx)) base));
  let hdr =
    read_word_in_indexed_major_at_erased_lookup_index
      heap base #header_idx #(Ghost.hide (Ghost.reveal mh));
  assert (pure (MH.read_word_in_major (Ghost.reveal mh) base == Some hdr));

  assert (pure (Ghost.reveal link_idx < Seq.length (Ghost.reveal mh)));
  assert (pure (MH.word_in_chunk
                  (Seq.index (Ghost.reveal mh) (Ghost.reveal link_idx)) cur));
  let next =
    read_word_in_indexed_major_at_erased_lookup_index
      heap cur #link_idx #(Ghost.hide (Ghost.reveal mh));
  assert (pure (MH.read_word_in_major (Ghost.reveal mh) cur == Some next));
  assert (pure (next <> cur));
  assert (pure (SMA.major_fl_valid (Ghost.reveal mh) next (fuel - 1)));
  (hdr, next)
}

let major_free_block_at (heap: MajorHeap.major_heap_t)
                        (cur: obj_addr)
                        (fuel: nat)
                        (mh: MH.major_heap)
                        (header_idx link_idx: nat)
  : slprop =
  MajorHeap.is_indexed_major_heap heap mh **
  pure (header_idx < Seq.length mh /\
        link_idx < Seq.length mh /\
        MH.lookup_chunk_index mh (SH.hd_address cur) == Some header_idx /\
        MH.lookup_chunk_index mh cur == Some link_idx /\
        MH.word_in_chunk
          (Seq.index mh header_idx)
          (SH.hd_address cur) /\
        MH.word_in_chunk (Seq.index mh link_idx) cur /\
        SMA.major_fl_valid mh cur fuel)

let major_free_block_witnesses (heap: MajorHeap.major_heap_t)
                               (cur: obj_addr)
                               (fuel: nat)
                               (mh: MH.major_heap)
  : slprop =
  exists* (header_idx:nat) (link_idx:nat).
    major_free_block_at heap cur fuel mh header_idx link_idx

fn read_major_free_block_exists (heap: MajorHeap.major_heap_t)
                                (cur: obj_addr)
                                (#fuel: (f:nat{f > 0}))
                                (#mh: Ghost.erased MH.major_heap)
   requires major_free_block_witnesses heap cur fuel (Ghost.reveal mh)
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (let hdr = fst res in
                 let next = snd res in
                 MH.read_word_in_major (Ghost.reveal mh) (SH.hd_address cur) ==
                   Some hdr /\
                 MH.read_word_in_major (Ghost.reveal mh) cur == Some next /\
                 U64.v (SO.getWosize hdr) >= 1 /\
                 next <> cur /\
                 SMA.major_fl_valid (Ghost.reveal mh) next (fuel - 1))
{
  unfold (major_free_block_witnesses heap cur fuel (Ghost.reveal mh));
  with header_idx link_idx. assert (
    major_free_block_at heap cur fuel (Ghost.reveal mh) header_idx link_idx
  );
  unfold (major_free_block_at heap cur fuel (Ghost.reveal mh) header_idx link_idx);
  let block =
    read_major_free_block heap cur #fuel
      #(Ghost.hide header_idx)
      #(Ghost.hide link_idx)
      #mh;
  block
}

fn read_major_free_block_by_valid (heap: MajorHeap.major_heap_t)
                                  (cur: obj_addr)
                                  (#fuel: (f:nat{f > 0}))
                                  (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (U64.v cur >= U64.v mword /\
                  U64.v cur < heap_size /\
                  U64.v cur % U64.v mword == 0 /\
                  SMA.major_fl_valid (Ghost.reveal mh) cur fuel)
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (let hdr = fst res in
                 let next = snd res in
                 MH.read_word_in_major (Ghost.reveal mh) (SH.hd_address cur) ==
                  Some hdr /\
                 MH.read_word_in_major (Ghost.reveal mh) cur == Some next /\
                 U64.v (SO.getWosize hdr) >= 1 /\
                 next <> cur /\
                 SMA.major_fl_valid (Ghost.reveal mh) next (fuel - 1))
{
  SMA.major_fl_valid_header_lookup_index (Ghost.reveal mh) cur fuel;
  SMA.major_fl_valid_link_lookup_index (Ghost.reveal mh) cur fuel;
  let header_idx =
    Ghost.hide (MH.lookup_chunk_index_value (Ghost.reveal mh) (SH.hd_address cur));
  let link_idx =
    Ghost.hide (MH.lookup_chunk_index_value (Ghost.reveal mh) cur);
  read_major_free_block heap cur #fuel #header_idx #link_idx #mh
}

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
                    (Ghost.reveal mh) (SH.hd_address cur) ==
                    Some (Ghost.reveal header_idx) /\
                  MH.lookup_chunk_index (Ghost.reveal mh) cur ==
                    Some (Ghost.reveal link_idx) /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal header_idx))
                    (SH.hd_address cur) /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal link_idx)) cur /\
                  U64.v cur >= U64.v zero_addr + U64.v mword /\
                  SMA.major_fl_valid (Ghost.reveal mh) cur fuel /\
                  SMA.major_fl_above_zero (Ghost.reveal mh) cur fuel)
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (let hdr = fst res in
                 let next = snd res in
                 MH.read_word_in_major (Ghost.reveal mh) (SH.hd_address cur) ==
                  Some hdr /\
                 MH.read_word_in_major (Ghost.reveal mh) cur == Some next /\
                 U64.v (SO.getWosize hdr) >= 1 /\
                 next <> cur /\
                 SMA.major_fl_valid (Ghost.reveal mh) next (fuel - 1) /\
                 SMA.major_fl_above_zero
                   (Ghost.reveal mh) next (fuel - 1))
{
  let block =
    read_major_free_block heap cur #fuel #header_idx #link_idx #mh;
  let next = snd block;
  SMA.major_fl_valid_above_zero_next (Ghost.reveal mh) cur fuel;
  assert (pure (SMA.major_fl_above_zero
                  (Ghost.reveal mh) next (fuel - 1)));
  block
}

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
                  base == SH.hd_address cur /\
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
                  block_wz == SO.getWosize hdr /\
                  U64.v prev > 0 /\
                  U64.v cur >= U64.v zero_addr + U64.v mword /\
                  U64.v block_wz >=
                    SA.normalized_wosize (U64.v requested_wz) /\
                  U64.v block_wz -
                    SA.normalized_wosize (U64.v requested_wz) < 2)
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap
             (let r =
                SMA.major_alloc_search
                  (Ghost.reveal mh) head prev cur
                  (SA.normalized_wosize (U64.v requested_wz)) fuel in
              r.major_alloc_out) **
           pure (let r =
                   SMA.major_alloc_search
                     (Ghost.reveal mh) head prev cur
                     (SA.normalized_wosize (U64.v requested_wz)) fuel in
                 fst res == r.major_fp_out /\
                 snd res == r.major_obj_out)
{
  let alloc_hdr = makeHeader block_wz white 0UL;
  let prev_u : U64.t = prev;
  let cur_u : U64.t = cur;
  assert (pure (SA.white_bits == 0UL));
  assert (pure (pack_color white == 0UL));
  assert (pure (alloc_hdr == SA.make_header block_wz SA.white_bits 0UL));
  assert (pure (alloc_hdr == SA.make_header (SO.getWosize hdr) SA.white_bits 0UL));
  assert (pure (base == SH.hd_address cur));

  SMA.major_spec_next_fp_some (Ghost.reveal mh) cur next_fp;
  assert (pure (SMA.major_spec_next_fp (Ghost.reveal mh) cur == next_fp));
  SMA.major_alloc_from_block_exact
    (Ghost.reveal mh) cur
    (SA.normalized_wosize (U64.v requested_wz)) next_fp hdr;
  u64_positive_not_zero prev_u;
  assert (pure (prev_u <> 0UL));
  SMA.major_alloc_search_found_prev
    (Ghost.reveal mh) head prev_u cur_u
    (SA.normalized_wosize (U64.v requested_wz)) fuel hdr;
  SMA.major_alloc_head_no_split
    (Ghost.reveal mh) cur (U64.v requested_wz) fuel hdr next_fp;

  let c0 = Ghost.hide (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_idx));
  let c1 = Ghost.hide (MH.write_word_in_chunk (Ghost.reveal c0) base alloc_hdr);
  write_word_in_indexed_major_at_erased_lookup_index heap base alloc_hdr
    #cur_idx #(Ghost.hide (Ghost.reveal mh));
  assert (pure (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_idx) == Ghost.reveal c0));
  assert (pure (MH.write_word_in_chunk
                  (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_idx)) base alloc_hdr ==
                Ghost.reveal c1));
  assert (pure (MH.write_word_in_major (Ghost.reveal mh) base alloc_hdr ==
                Some (Seq.upd (Ghost.reveal mh) (Ghost.reveal cur_idx) (Ghost.reveal c1))));
  SMA.major_write_word_or_same_some
    (Ghost.reveal mh) (Seq.upd (Ghost.reveal mh) (Ghost.reveal cur_idx) (Ghost.reveal c1))
    base alloc_hdr;
  assert (pure (SMA.major_write_word_or_same
                  (Ghost.reveal mh) (SH.hd_address cur) alloc_hdr ==
                Seq.upd (Ghost.reveal mh) (Ghost.reveal cur_idx) (Ghost.reveal c1)));
  assert (pure (let r =
                  SMA.major_alloc_spec_with_fuel
                    (Ghost.reveal mh) cur (U64.v requested_wz) fuel in
                r.major_alloc_out ==
                  Seq.upd (Ghost.reveal mh) (Ghost.reveal cur_idx) (Ghost.reveal c1) /\
                r.major_fp_out == next_fp /\
                r.major_obj_out == cur));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) (Ghost.reveal cur_idx)
        (MH.write_word_in_chunk
          (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_idx)) base alloc_hdr)))
  as
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) (Ghost.reveal cur_idx) (Ghost.reveal c1)));

  let mh1 = Ghost.hide (Seq.upd (Ghost.reveal mh) (Ghost.reveal cur_idx) (Ghost.reveal c1));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) (Ghost.reveal cur_idx) (Ghost.reveal c1)))
  as
    (MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh1));
  SMA.indexed_chunk_write_preserves_word_no_prior
    (Ghost.reveal mh) (Ghost.reveal cur_idx) (Ghost.reveal prev_idx) base prev alloc_hdr;
  assert (pure (Ghost.reveal prev_idx < Seq.length (Ghost.reveal mh1)));
  assert (pure (MH.word_in_chunk (Seq.index (Ghost.reveal mh1) (Ghost.reveal prev_idx)) prev));
  assert (pure (forall (k:nat). k < Ghost.reveal prev_idx ==>
    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh1) k) prev)));
  write_word_in_indexed_major_at_erased_chunk_index heap prev next_fp
    #prev_idx #(Ghost.hide (Ghost.reveal mh1));
  assert (pure (MH.write_word_in_major (Ghost.reveal mh1) prev next_fp ==
                Some (Seq.upd (Ghost.reveal mh1) (Ghost.reveal prev_idx)
                  (MH.write_word_in_chunk
                    (Seq.index (Ghost.reveal mh1) (Ghost.reveal prev_idx)) prev next_fp))));
  SMA.major_write_word_or_same_some
    (Ghost.reveal mh1)
    (Seq.upd (Ghost.reveal mh1) (Ghost.reveal prev_idx)
      (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh1) (Ghost.reveal prev_idx)) prev next_fp))
    prev next_fp;

  assert (pure (U64.v prev >= U64.v mword));
  assert (pure (U64.v prev > 0));
  assert (pure (prev_u <> 0UL));
  assert (pure (U64.v prev < heap_size));
  assert (pure (U64.v prev % U64.v mword == 0));
  assert (pure (let r =
                  SMA.major_alloc_search
                    (Ghost.reveal mh) head prev cur
                    (SA.normalized_wosize (U64.v requested_wz)) fuel in
                r.major_alloc_out ==
                  Seq.upd (Ghost.reveal mh1) (Ghost.reveal prev_idx)
                    (MH.write_word_in_chunk
                      (Seq.index (Ghost.reveal mh1) (Ghost.reveal prev_idx)) prev next_fp) /\
                r.major_fp_out == head /\
                r.major_obj_out == cur));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh1) (Ghost.reveal prev_idx)
        (MH.write_word_in_chunk
          (Seq.index (Ghost.reveal mh1) (Ghost.reveal prev_idx)) prev next_fp)))
  as
    (MajorHeap.is_indexed_major_heap heap
      (let r =
         SMA.major_alloc_search
           (Ghost.reveal mh) head prev cur
           (SA.normalized_wosize (U64.v requested_wz)) fuel in
       r.major_alloc_out));
  assert (pure (let r =
                  SMA.major_alloc_search
                    (Ghost.reveal mh) head prev cur
                    (SA.normalized_wosize (U64.v requested_wz)) fuel in
                head == r.major_fp_out /\
                cur == r.major_obj_out));
  (head, cur)
}

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
                  base == SH.hd_address cur /\
                  MH.lookup_chunk_index (Ghost.reveal mh) base ==
                   Some (Ghost.reveal cur_idx) /\
                  MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_idx)) base /\
                  MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_idx)) rem_hd /\
                  MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_idx)) rem_obj /\
                  (forall (k:nat{k < Ghost.reveal cur_idx /\ k < Seq.length (Ghost.reveal mh)}).
                    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh) k) rem_hd)) /\
                  (forall (k:nat{k < Ghost.reveal cur_idx /\ k < Seq.length (Ghost.reveal mh)}).
                    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh) k) rem_obj)) /\
                  MH.word_in_chunk
                   (Seq.index (Ghost.reveal mh) (Ghost.reveal prev_idx)) prev /\
                  (forall (k:nat). k < Ghost.reveal prev_idx ==>
                    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh) k) prev)) /\
                  MH.read_word_in_major (Ghost.reveal mh) base == Some hdr /\
                  MH.read_word_in_major (Ghost.reveal mh) cur == Some next_fp /\
                  block_wz == SO.getWosize hdr /\
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
                SMA.major_alloc_search
                  (Ghost.reveal mh) head prev cur
                  (SA.normalized_wosize (U64.v requested_wz)) fuel in
              r.major_alloc_out) **
           pure (let r =
                  SMA.major_alloc_search
                    (Ghost.reveal mh) head prev cur
                    (SA.normalized_wosize (U64.v requested_wz)) fuel in
                 fst res == r.major_fp_out /\
                 snd res == r.major_obj_out)
{
  let alloc_hdr = makeHeader requested_wz white 0UL;
  let prev_u : U64.t = prev;
  let cur_u : U64.t = cur;
  let rem_obj_u : U64.t = rem_obj;
  assert (pure (SA.white_bits == 0UL));
  assert (pure (pack_color white == 0UL));
  assert (pure (U64.uint_to_t (U64.v requested_wz) == requested_wz));
  assert (pure (alloc_hdr ==
                SA.make_header (U64.uint_to_t (U64.v requested_wz))
                  SA.white_bits 0UL));
  assert (pure (base == SH.hd_address cur));
  assert (pure (SA.normalized_wosize (U64.v requested_wz) ==
                U64.v requested_wz));

  let leftover = U64.sub block_wz requested_wz;
  let rem_wz_u = U64.sub leftover 1UL;
  assert (pure (U64.v leftover == U64.v block_wz - U64.v requested_wz));
  assert (pure (U64.v rem_wz_u == U64.v block_wz - U64.v requested_wz - 1));
  assert (pure (U64.v rem_wz_u < pow2 54));
  let rem_hdr = makeHeader rem_wz_u blue 0UL;
  assert (pure (SA.blue_bits == 2UL));
  assert (pure (pack_color blue == 2UL));
  assert (pure (U64.uint_to_t (U64.v rem_wz_u) == rem_wz_u));
  assert (pure (rem_hdr ==
                SA.make_header
                  (U64.uint_to_t (U64.v block_wz - U64.v requested_wz - 1))
                  SA.blue_bits 0UL));

  SMA.major_spec_next_fp_some (Ghost.reveal mh) cur next_fp;
  assert (pure (SMA.major_spec_next_fp (Ghost.reveal mh) cur == next_fp));
  assert (pure (U64.v rem_hd < heap_size));
  assert (pure (U64.v rem_hd % U64.v mword == 0));
  assert (pure (U64.v rem_obj < heap_size));
  assert (pure (U64.v rem_obj % U64.v mword == 0));
  assert (pure (U64.v base + (1 + U64.v requested_wz) * 8 < heap_size));
  assert (pure (U64.v base + (1 + U64.v requested_wz) * 8 + 8 < heap_size));
  assert (pure ((U64.v base + (1 + U64.v requested_wz) * 8) % 8 == 0));
  assert (pure ((U64.v base + (1 + U64.v requested_wz) * 8 + 8) % 8 == 0));
  SMA.major_alloc_from_block_split_normal
    (Ghost.reveal mh) cur (U64.v requested_wz) next_fp hdr;
  SMA.major_alloc_head_split
    (Ghost.reveal mh) cur (U64.v requested_wz) fuel hdr next_fp
    rem_hd rem_obj;
  u64_positive_not_zero prev_u;
  assert (pure (prev_u <> 0UL));
  SMA.major_alloc_search_found_prev
    (Ghost.reveal mh) head prev_u cur_u
    (U64.v requested_wz) fuel hdr;

  let c0 = Ghost.hide (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_idx));
  let c1 = Ghost.hide (MH.write_word_in_chunk (Ghost.reveal c0) base alloc_hdr);
  let c2 = Ghost.hide (MH.write_word_in_chunk (Ghost.reveal c1) rem_hd rem_hdr);
  let c3 = Ghost.hide (MH.write_word_in_chunk (Ghost.reveal c2) rem_obj next_fp);

  write_word_in_indexed_major_at_erased_lookup_index heap base alloc_hdr
    #cur_idx #(Ghost.hide (Ghost.reveal mh));
  assert (pure (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_idx) == Ghost.reveal c0));
  assert (pure (MH.write_word_in_chunk
                  (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_idx)) base alloc_hdr ==
                Ghost.reveal c1));
  assert (pure (MH.write_word_in_major (Ghost.reveal mh) base alloc_hdr ==
                Some (Seq.upd (Ghost.reveal mh) (Ghost.reveal cur_idx) (Ghost.reveal c1))));
  SMA.major_write_word_or_same_some
    (Ghost.reveal mh) (Seq.upd (Ghost.reveal mh) (Ghost.reveal cur_idx) (Ghost.reveal c1))
    base alloc_hdr;
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) (Ghost.reveal cur_idx)
        (MH.write_word_in_chunk
          (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_idx)) base alloc_hdr)))
  as
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) (Ghost.reveal cur_idx) (Ghost.reveal c1)));

  let mh1 = Ghost.hide (Seq.upd (Ghost.reveal mh) (Ghost.reveal cur_idx) (Ghost.reveal c1));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) (Ghost.reveal cur_idx) (Ghost.reveal c1)))
  as
    (MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh1));
  assert (pure (Seq.length (Ghost.reveal mh1) == Seq.length (Ghost.reveal mh)));
  assert (pure (Ghost.reveal cur_idx < Seq.length (Ghost.reveal mh1)));
  assert (pure (Seq.index (Ghost.reveal mh1) (Ghost.reveal cur_idx) == Ghost.reveal c1));
  MH.write_word_in_chunk_preserves_word (Ghost.reveal c0) base alloc_hdr rem_hd;
  assert (pure (MH.word_in_chunk (Seq.index (Ghost.reveal mh1) (Ghost.reveal cur_idx)) rem_hd));
  assert (pure (forall (k:nat). k < Ghost.reveal cur_idx ==>
    Seq.index (Ghost.reveal mh1) k == Seq.index (Ghost.reveal mh) k));
  assert (pure (forall (k:nat). k < Ghost.reveal cur_idx ==>
    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh1) k) rem_hd)));
  write_word_in_indexed_major_at_erased_chunk_index heap rem_hd rem_hdr
    #cur_idx #(Ghost.hide (Ghost.reveal mh1));
  assert (pure (MH.write_word_in_major (Ghost.reveal mh1) rem_hd rem_hdr ==
                Some (Seq.upd (Ghost.reveal mh1) (Ghost.reveal cur_idx) (Ghost.reveal c2))));
  SMA.major_write_word_or_same_some
    (Ghost.reveal mh1) (Seq.upd (Ghost.reveal mh1) (Ghost.reveal cur_idx) (Ghost.reveal c2))
    rem_hd rem_hdr;
  SMA.seq_upd_overwrite_index (Ghost.reveal mh) (Ghost.reveal cur_idx) (Ghost.reveal c1) (Ghost.reveal c2);
  assert (pure (Seq.upd (Ghost.reveal mh1) (Ghost.reveal cur_idx) (Ghost.reveal c2) ==
                Seq.upd (Ghost.reveal mh) (Ghost.reveal cur_idx) (Ghost.reveal c2)));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh1) (Ghost.reveal cur_idx)
        (MH.write_word_in_chunk
          (Seq.index (Ghost.reveal mh1) (Ghost.reveal cur_idx)) rem_hd rem_hdr)))
  as
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) (Ghost.reveal cur_idx) (Ghost.reveal c2)));

  let mh2 = Ghost.hide (Seq.upd (Ghost.reveal mh) (Ghost.reveal cur_idx) (Ghost.reveal c2));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) (Ghost.reveal cur_idx) (Ghost.reveal c2)))
  as
    (MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh2));
  assert (pure (Seq.length (Ghost.reveal mh2) == Seq.length (Ghost.reveal mh)));
  assert (pure (Ghost.reveal cur_idx < Seq.length (Ghost.reveal mh2)));
  assert (pure (Seq.index (Ghost.reveal mh2) (Ghost.reveal cur_idx) == Ghost.reveal c2));
  MH.write_word_in_chunk_preserves_word (Ghost.reveal c1) rem_hd rem_hdr rem_obj;
  assert (pure (MH.word_in_chunk (Seq.index (Ghost.reveal mh2) (Ghost.reveal cur_idx)) rem_obj));
  assert (pure (forall (k:nat). k < Ghost.reveal cur_idx ==>
    Seq.index (Ghost.reveal mh2) k == Seq.index (Ghost.reveal mh) k));
  assert (pure (forall (k:nat). k < Ghost.reveal cur_idx ==>
    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh2) k) rem_obj)));
  write_word_in_indexed_major_at_erased_chunk_index heap rem_obj next_fp
    #cur_idx #(Ghost.hide (Ghost.reveal mh2));
  assert (pure (MH.write_word_in_major (Ghost.reveal mh2) rem_obj next_fp ==
                Some (Seq.upd (Ghost.reveal mh2) (Ghost.reveal cur_idx) (Ghost.reveal c3))));
  SMA.major_write_word_or_same_some
    (Ghost.reveal mh2) (Seq.upd (Ghost.reveal mh2) (Ghost.reveal cur_idx) (Ghost.reveal c3))
    rem_obj next_fp;
  SMA.seq_upd_overwrite_index (Ghost.reveal mh) (Ghost.reveal cur_idx) (Ghost.reveal c2) (Ghost.reveal c3);
  assert (pure (Seq.upd (Ghost.reveal mh2) (Ghost.reveal cur_idx) (Ghost.reveal c3) ==
                Seq.upd (Ghost.reveal mh) (Ghost.reveal cur_idx) (Ghost.reveal c3)));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh2) (Ghost.reveal cur_idx)
        (MH.write_word_in_chunk
          (Seq.index (Ghost.reveal mh2) (Ghost.reveal cur_idx)) rem_obj next_fp)))
  as
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) (Ghost.reveal cur_idx) (Ghost.reveal c3)));

  let mh_cur = Ghost.hide (Seq.upd (Ghost.reveal mh) (Ghost.reveal cur_idx) (Ghost.reveal c3));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) (Ghost.reveal cur_idx) (Ghost.reveal c3)))
  as
    (MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh_cur));
  MH.write_word_in_chunk_preserves_range (Ghost.reveal c0) base alloc_hdr;
  MH.write_word_in_chunk_preserves_range (Ghost.reveal c1) rem_hd rem_hdr;
  MH.write_word_in_chunk_preserves_range (Ghost.reveal c2) rem_obj next_fp;
  assert (pure (MH.chunk_start (Ghost.reveal c3) == MH.chunk_start (Ghost.reveal c0)));
  assert (pure (MH.chunk_end (Ghost.reveal c3) == MH.chunk_end (Ghost.reveal c0)));
  SMA.indexed_chunk_replace_same_range_preserves_word_no_prior
    (Ghost.reveal mh) (Ghost.reveal cur_idx) (Ghost.reveal prev_idx)
    (Ghost.reveal c3) prev;
  assert (pure (Ghost.reveal prev_idx < Seq.length (Ghost.reveal mh_cur)));
  assert (pure (MH.word_in_chunk
    (Seq.index (Ghost.reveal mh_cur) (Ghost.reveal prev_idx)) prev));
  assert (pure (forall (k:nat). k < Ghost.reveal prev_idx ==>
    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh_cur) k) prev)));
  write_word_in_indexed_major_at_erased_chunk_index heap prev rem_obj_u
    #prev_idx #(Ghost.hide (Ghost.reveal mh_cur));
  assert (pure (MH.write_word_in_major (Ghost.reveal mh_cur) prev rem_obj_u ==
                Some (Seq.upd (Ghost.reveal mh_cur) (Ghost.reveal prev_idx)
                  (MH.write_word_in_chunk
                    (Seq.index (Ghost.reveal mh_cur) (Ghost.reveal prev_idx))
                    prev rem_obj_u))));
  SMA.major_write_word_or_same_some
    (Ghost.reveal mh_cur)
    (Seq.upd (Ghost.reveal mh_cur) (Ghost.reveal prev_idx)
      (MH.write_word_in_chunk
        (Seq.index (Ghost.reveal mh_cur) (Ghost.reveal prev_idx)) prev rem_obj_u))
    prev rem_obj_u;

  assert (pure (let r =
                  SMA.major_alloc_spec_with_fuel
                    (Ghost.reveal mh) cur (U64.v requested_wz) fuel in
                r.major_alloc_out == Ghost.reveal mh_cur /\
                r.major_fp_out == rem_obj /\
                r.major_obj_out == cur));
  assert (pure (let p = SMA.major_alloc_from_block
                            (Ghost.reveal mh) cur (U64.v requested_wz) next_fp in
                fst p == Ghost.reveal mh_cur /\
                snd p == rem_obj));
  assert (pure (let r =
                  SMA.major_alloc_search
                    (Ghost.reveal mh) head prev cur
                    (SA.normalized_wosize (U64.v requested_wz)) fuel in
                r.major_alloc_out ==
                  Seq.upd (Ghost.reveal mh_cur) (Ghost.reveal prev_idx)
                    (MH.write_word_in_chunk
                      (Seq.index (Ghost.reveal mh_cur) (Ghost.reveal prev_idx))
                      prev rem_obj_u) /\
                r.major_fp_out == head /\
                r.major_obj_out == cur));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh_cur) (Ghost.reveal prev_idx)
        (MH.write_word_in_chunk
          (Seq.index (Ghost.reveal mh_cur) (Ghost.reveal prev_idx))
          prev rem_obj_u)))
  as
    (MajorHeap.is_indexed_major_heap heap
      (let r =
         SMA.major_alloc_search
           (Ghost.reveal mh) head prev cur
           (SA.normalized_wosize (U64.v requested_wz)) fuel in
       r.major_alloc_out));
  assert (pure (let r =
                  SMA.major_alloc_search
                    (Ghost.reveal mh) head prev cur
                    (SA.normalized_wosize (U64.v requested_wz)) fuel in
                head == r.major_fp_out /\
                cur == r.major_obj_out));
  (head, cur)
}

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
                  base == SH.hd_address cur /\
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
                  block_wz == SO.getWosize hdr /\
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
                SMA.major_alloc_search
                  (Ghost.reveal mh) head prev cur
                  (SA.normalized_wosize (U64.v requested_wz)) fuel in
              r.major_alloc_out) **
           pure (let r =
                  SMA.major_alloc_search
                    (Ghost.reveal mh) head prev cur
                    (SA.normalized_wosize (U64.v requested_wz)) fuel in
                 fst res == r.major_fp_out /\
                 snd res == r.major_obj_out)
{
  let leftover = U64.sub block_wz requested_wz;
  assert (pure (U64.v leftover == U64.v block_wz - U64.v requested_wz));
  assert (pure (SA.normalized_wosize (U64.v requested_wz) ==
                U64.v requested_wz));
  if U64.gte leftover 2UL {
    assert (pure (U64.v block_wz - U64.v requested_wz >= 2));
    wosize_bound_lemma requested_wz block_wz;
    split_offset_fits requested_wz;
    split_no_overflow base requested_wz;

    let wz_plus_1 = U64.add requested_wz 1UL;
    assert (pure (U64.v wz_plus_1 == U64.v requested_wz + 1));
    let offset = U64.mul wz_plus_1 mword;
    assert (pure (U64.v offset == (1 + U64.v requested_wz) * U64.v mword));
    assert (pure (U64.v offset == (1 + U64.v requested_wz) * 8));
    let rem_hd = U64.add base offset;
    assert (pure (U64.v rem_hd == U64.v base + (1 + U64.v requested_wz) * 8));
    assert (pure (U64.v rem_hd < heap_size));
    assert (pure (U64.v rem_hd % U64.v mword == 0));
    let rem_obj = U64.add rem_hd mword;
    assert (pure (U64.v rem_obj == U64.v rem_hd + U64.v mword));
    assert (pure (U64.v rem_obj < heap_size));
    assert (pure (U64.v rem_obj % U64.v mword == 0));
    assert (pure (U64.v rem_hd + U64.v mword < pow2 64));

    unfold (MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh));
    assert (pure (MH.well_formed_major_heap (Ghost.reveal mh)));
    fold (MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh));

    SMA.active_head_split_remainder_words_in_chunk
      (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_idx)) base
      (U64.v block_wz) (U64.v requested_wz) rem_hd rem_obj;
    assert (pure (MH.word_in_chunk
      (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_idx)) rem_hd));
    assert (pure (MH.word_in_chunk
      (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_idx)) rem_obj));
    SMA.well_formed_no_prior_word_in_selected_chunk
      (Ghost.reveal mh) (Ghost.reveal cur_idx) rem_hd;
    SMA.well_formed_no_prior_word_in_selected_chunk
      (Ghost.reveal mh) (Ghost.reveal cur_idx) rem_obj;
    let res =
      allocate_major_found_prev_split
        heap head prev base cur hdr block_wz requested_wz rem_hd rem_obj next_fp
        #fuel #cur_idx #prev_idx #mh;
    assert (pure (let r =
                    SMA.major_alloc_search
                      (Ghost.reveal mh) head prev cur
                      (SA.normalized_wosize (U64.v requested_wz)) fuel in
                  fst res == r.major_fp_out /\
                  snd res == r.major_obj_out));
    res
  } else {
    assert (pure (U64.v block_wz -
                  SA.normalized_wosize (U64.v requested_wz) < 2));
    let res =
      allocate_major_found_prev_no_split
        heap head prev base cur hdr block_wz requested_wz next_fp
        #fuel #cur_idx #prev_idx #mh;
    assert (pure (let r =
                    SMA.major_alloc_search
                      (Ghost.reveal mh) head prev cur
                      (SA.normalized_wosize (U64.v requested_wz)) fuel in
                  fst res == r.major_fp_out /\
                  snd res == r.major_obj_out));
    res
  }
}

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
                  base == SH.hd_address cur /\
                  MH.lookup_chunk_index (Ghost.reveal mh) base ==
                    Some (Ghost.reveal header_idx) /\
                  MH.lookup_chunk_index (Ghost.reveal mh) cur ==
                    Some (Ghost.reveal link_idx) /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal header_idx)) base /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal link_idx)) cur /\
                  SMA.major_fl_valid (Ghost.reveal mh) cur fuel /\
                  U64.v cur >= U64.v zero_addr + U64.v mword /\
                  (match MH.read_word_in_major (Ghost.reveal mh) base with
                   | Some hdr ->
                     U64.v (SO.getWosize hdr) <
                       SA.normalized_wosize (U64.v requested_wz)
                   | None -> False))
   returns next: U64.t
   ensures MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (MH.read_word_in_major (Ghost.reveal mh) cur == Some next /\
                 next <> cur /\
                 SMA.major_fl_valid (Ghost.reveal mh) next (fuel - 1) /\
                 SMA.major_alloc_search
                   (Ghost.reveal mh) head prev cur
                   (SA.normalized_wosize (U64.v requested_wz)) fuel ==
                 SMA.major_alloc_search
                   (Ghost.reveal mh) head cur next
                   (SA.normalized_wosize (U64.v requested_wz)) (fuel - 1))
{
  let block =
    read_major_free_block heap cur #fuel #header_idx #link_idx #mh;
  let hdr = fst block;
  let next_fp = snd block;
  let block_wz = SO.getWosize hdr;
  assert (pure (MH.read_word_in_major (Ghost.reveal mh) base == Some hdr));
  assert (pure (U64.v block_wz <
                SA.normalized_wosize (U64.v requested_wz)));
  let next =
    advance_major_search_too_small
      heap head prev base cur hdr block_wz requested_wz next_fp
      #fuel #header_idx #mh;
  assert (pure (next == next_fp));
  next
}

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
                  base == SH.hd_address cur /\
                  MH.lookup_chunk_index (Ghost.reveal mh) base ==
                    Some (Ghost.reveal header_idx) /\
                  MH.lookup_chunk_index (Ghost.reveal mh) cur ==
                    Some (Ghost.reveal link_idx) /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal header_idx)) base /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal link_idx)) cur /\
                  SMA.major_fl_valid (Ghost.reveal mh) cur fuel /\
                  SMA.major_fl_above_zero (Ghost.reveal mh) cur fuel /\
                  U64.v cur >= U64.v zero_addr + U64.v mword /\
                  (match MH.read_word_in_major (Ghost.reveal mh) base with
                   | Some hdr ->
                     U64.v (SO.getWosize hdr) <
                       SA.normalized_wosize (U64.v requested_wz)
                   | None -> False))
   returns next: U64.t
   ensures MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (MH.read_word_in_major (Ghost.reveal mh) cur == Some next /\
                 next <> cur /\
                 SMA.major_fl_valid
                  (Ghost.reveal mh) next (fuel - 1) /\
                 SMA.major_fl_above_zero
                  (Ghost.reveal mh) next (fuel - 1) /\
                 SMA.major_alloc_search
                  (Ghost.reveal mh) head prev cur
                  (SA.normalized_wosize (U64.v requested_wz)) fuel ==
                 SMA.major_alloc_search
                  (Ghost.reveal mh) head cur next
                  (SA.normalized_wosize (U64.v requested_wz)) (fuel - 1))
{
  let block =
    read_major_free_block heap cur #fuel #header_idx #link_idx #mh;
  let hdr = fst block;
  let next_fp = snd block;
  let block_wz = SO.getWosize hdr;
  assert (pure (MH.read_word_in_major (Ghost.reveal mh) base == Some hdr));
  assert (pure (U64.v block_wz <
                SA.normalized_wosize (U64.v requested_wz)));
  let next =
    advance_major_search_too_small
      heap head prev base cur hdr block_wz requested_wz next_fp
      #fuel #header_idx #mh;
  SMA.major_fl_above_zero_next (Ghost.reveal mh) cur fuel next;
  assert (pure (SMA.major_fl_above_zero
                  (Ghost.reveal mh) next (fuel - 1)));
  next
}

fn advance_major_search_by_valid (heap: MajorHeap.major_heap_t)
                                  (head prev: U64.t)
                                  (cur: obj_addr)
                                  (requested_wz: wosize)
                                  (#fuel: (f:nat{f > 0}))
                                  (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (SMA.major_fl_valid (Ghost.reveal mh) cur fuel /\
                  SMA.major_fl_above_zero (Ghost.reveal mh) cur fuel /\
                  SMA.major_fl_blocks_fit (Ghost.reveal mh) cur fuel /\
                  U64.v requested_wz > 0 /\
                  (match MH.read_word_in_major (Ghost.reveal mh) (SH.hd_address cur) with
                   | Some hdr ->
                     U64.v (SO.getWosize hdr) <
                       SA.normalized_wosize (U64.v requested_wz)
                   | None -> False))
   returns next: U64.t
   ensures MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (MH.read_word_in_major (Ghost.reveal mh) cur == Some next /\
                 next <> cur /\
                 SMA.major_fl_valid (Ghost.reveal mh) next (fuel - 1) /\
                 SMA.major_fl_above_zero (Ghost.reveal mh) next (fuel - 1) /\
                 SMA.major_fl_blocks_fit (Ghost.reveal mh) next (fuel - 1) /\
                 SMA.major_alloc_search
                   (Ghost.reveal mh) head prev cur
                   (SA.normalized_wosize (U64.v requested_wz)) fuel ==
                 SMA.major_alloc_search
                   (Ghost.reveal mh) head cur next
                   (SA.normalized_wosize (U64.v requested_wz)) (fuel - 1))
{
  SMA.major_fl_above_zero_current (Ghost.reveal mh) cur fuel;
  assert (pure (U64.v cur >= U64.v zero_addr + U64.v mword));
  SMA.major_fl_valid_header_lookup_index (Ghost.reveal mh) cur fuel;
  SMA.major_fl_valid_link_lookup_index (Ghost.reveal mh) cur fuel;
  let base = SH.hd_address cur;
  let header_idx =
    Ghost.hide (MH.lookup_chunk_index_value (Ghost.reveal mh) base);
  let link_idx =
    Ghost.hide (MH.lookup_chunk_index_value (Ghost.reveal mh) cur);
  let next =
    advance_major_search_from_read_above_zero
      heap head prev base cur requested_wz #fuel #header_idx #link_idx #mh;
  SMA.major_fl_blocks_fit_next (Ghost.reveal mh) cur fuel next;
  assert (pure (SMA.major_fl_blocks_fit (Ghost.reveal mh) next (fuel - 1)));
  next
}

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
                  base == SH.hd_address fp /\
                  MH.lookup_chunk_index (Ghost.reveal mh) base ==
                    Some (Ghost.reveal header_idx) /\
                  MH.lookup_chunk_index (Ghost.reveal mh) fp ==
                    Some (Ghost.reveal link_idx) /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal header_idx)) base /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal link_idx)) fp /\
                  SMA.major_fl_valid (Ghost.reveal mh) fp fuel /\
                  U64.v fp >= U64.v zero_addr + U64.v mword /\
                  U64.v requested_wz > 0 /\
                  (match MH.read_word_in_major (Ghost.reveal mh) base with
                   | Some hdr ->
                     U64.v (SO.getWosize hdr) >= U64.v requested_wz /\
                     U64.v base + (1 + U64.v (SO.getWosize hdr)) * 8 <=
                       MH.chunk_end
                         (Seq.index (Ghost.reveal mh) (Ghost.reveal header_idx))
                   | None -> False))
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap
             (let r =
                SMA.major_alloc_spec_with_fuel
                  (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
              r.major_alloc_out) **
           pure (let r =
                   SMA.major_alloc_spec_with_fuel
                     (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
                 fst res == r.major_fp_out /\
                 snd res == r.major_obj_out)
{
  let block =
    read_major_free_block heap fp #fuel #header_idx #link_idx #mh;
  let hdr = fst block;
  let next_fp = snd block;
  let block_wz = SO.getWosize hdr;
  assert (pure (MH.read_word_in_major (Ghost.reveal mh) base == Some hdr));
  assert (pure (U64.v block_wz >= U64.v requested_wz));
  assert (pure (U64.v base + (1 + U64.v block_wz) * 8 <=
                MH.chunk_end
                  (Seq.index (Ghost.reveal mh) (Ghost.reveal header_idx))));
  let res =
    allocate_major_head
      heap base fp hdr block_wz requested_wz next_fp
      #fuel #header_idx #mh;
  assert (pure (let r =
                  SMA.major_alloc_spec_with_fuel
                    (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
                fst res == r.major_fp_out /\
                snd res == r.major_obj_out));
  res
}

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
                  base == SH.hd_address fp /\
                  MH.lookup_chunk_index (Ghost.reveal mh) base ==
                    Some (Ghost.reveal header_idx) /\
                  MH.lookup_chunk_index (Ghost.reveal mh) fp ==
                    Some (Ghost.reveal link_idx) /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal header_idx)) base /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal link_idx)) fp /\
                  SMA.major_fl_valid (Ghost.reveal mh) fp fuel /\
                  SMA.major_fl_above_zero (Ghost.reveal mh) fp fuel /\
                  U64.v requested_wz > 0 /\
                  (match MH.read_word_in_major (Ghost.reveal mh) base with
                   | Some hdr ->
                     U64.v (SO.getWosize hdr) >= U64.v requested_wz /\
                     U64.v base + (1 + U64.v (SO.getWosize hdr)) * 8 <=
                       MH.chunk_end
                         (Seq.index (Ghost.reveal mh) (Ghost.reveal header_idx))
                   | None -> False))
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap
             (let r =
                SMA.major_alloc_spec_with_fuel
                  (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
              r.major_alloc_out) **
           pure (let r =
                  SMA.major_alloc_spec_with_fuel
                    (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
                 fst res == r.major_fp_out /\
                 snd res == r.major_obj_out)
{
  SMA.major_fl_above_zero_current (Ghost.reveal mh) fp fuel;
  assert (pure (U64.v fp >= U64.v zero_addr + U64.v mword));
  allocate_major_head_from_read
    heap base fp requested_wz #fuel #header_idx #link_idx #mh
}

let major_head_alloc_at (heap: MajorHeap.major_heap_t)
                        (base: hp_addr)
                        (fp: obj_addr)
                        (requested_wz: wosize)
                        (fuel header_idx link_idx: nat)
                        (mh: MH.major_heap)
  : slprop =
  MajorHeap.is_indexed_major_heap heap mh **
  pure (fuel > 0 /\
        header_idx < Seq.length mh /\
        link_idx < Seq.length mh /\
        base == SH.hd_address fp /\
        MH.lookup_chunk_index mh base == Some header_idx /\
        MH.lookup_chunk_index mh fp == Some link_idx /\
        MH.word_in_chunk (Seq.index mh header_idx) base /\
        MH.word_in_chunk (Seq.index mh link_idx) fp /\
        SMA.major_fl_valid mh fp fuel /\
        SMA.major_fl_above_zero mh fp fuel /\
        U64.v requested_wz > 0 /\
        (match MH.read_word_in_major mh base with
         | Some hdr ->
           U64.v (SO.getWosize hdr) >= U64.v requested_wz /\
           U64.v base + (1 + U64.v (SO.getWosize hdr)) * 8 <=
             MH.chunk_end (Seq.index mh header_idx)
         | None -> False))

let major_head_alloc_witnesses (heap: MajorHeap.major_heap_t)
                               (base: hp_addr)
                               (fp: obj_addr)
                               (requested_wz: wosize)
                               (fuel: nat)
                               (mh: MH.major_heap)
  : slprop =
  exists* (header_idx:nat) (link_idx:nat).
    major_head_alloc_at heap base fp requested_wz fuel header_idx link_idx mh

fn allocate_major_head_from_read_exists (heap: MajorHeap.major_heap_t)
                                        (base: hp_addr)
                                        (fp: obj_addr)
                                        (requested_wz: wosize)
                                        (#fuel: (f:nat{f > 0}))
                                        (#mh: Ghost.erased MH.major_heap)
   requires major_head_alloc_witnesses
              heap base fp requested_wz fuel (Ghost.reveal mh)
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap
             (let r =
                SMA.major_alloc_spec_with_fuel
                  (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
              r.major_alloc_out) **
           pure (let r =
                  SMA.major_alloc_spec_with_fuel
                    (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
                 fst res == r.major_fp_out /\
                 snd res == r.major_obj_out)
{
  unfold (major_head_alloc_witnesses
            heap base fp requested_wz fuel (Ghost.reveal mh));
  with header_idx link_idx. assert (
    major_head_alloc_at
      heap base fp requested_wz fuel header_idx link_idx (Ghost.reveal mh)
  );
  unfold (major_head_alloc_at
    heap base fp requested_wz fuel header_idx link_idx (Ghost.reveal mh));
  allocate_major_head_from_read_above_zero
    heap base fp requested_wz #fuel
    #(Ghost.hide header_idx) #(Ghost.hide link_idx) #mh
}

fn allocate_major_head_by_valid (heap: MajorHeap.major_heap_t)
                                (fp: obj_addr)
                                (requested_wz: wosize)
                                (#fuel: (f:nat{f > 0}))
                                (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (SMA.major_fl_valid (Ghost.reveal mh) fp fuel /\
                  SMA.major_fl_above_zero (Ghost.reveal mh) fp fuel /\
                  SMA.major_fl_blocks_fit (Ghost.reveal mh) fp fuel /\
                  U64.v requested_wz > 0 /\
                  (match MH.read_word_in_major (Ghost.reveal mh) (SH.hd_address fp) with
                   | Some hdr ->
                     U64.v (SO.getWosize hdr) >= U64.v requested_wz
                   | None -> False))
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap
             (let r =
                SMA.major_alloc_spec_with_fuel
                  (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
              r.major_alloc_out) **
           pure (let r =
                  SMA.major_alloc_spec_with_fuel
                    (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
                 fst res == r.major_fp_out /\
                 snd res == r.major_obj_out)
{
  SMA.major_fl_above_zero_current (Ghost.reveal mh) fp fuel;
  assert (pure (U64.v fp >= U64.v zero_addr + U64.v mword));
  SMA.major_fl_valid_header_lookup_index (Ghost.reveal mh) fp fuel;
  SMA.major_fl_valid_link_lookup_index (Ghost.reveal mh) fp fuel;
  SMA.major_fl_blocks_fit_current (Ghost.reveal mh) fp fuel;
  let base = SH.hd_address fp;
  let header_idx =
    Ghost.hide (MH.lookup_chunk_index_value (Ghost.reveal mh) base);
  let link_idx =
    Ghost.hide (MH.lookup_chunk_index_value (Ghost.reveal mh) fp);
  allocate_major_head_from_read_above_zero
    heap base fp requested_wz #fuel #header_idx #link_idx #mh
}

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
                  base == SH.hd_address cur /\
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
                  SMA.major_fl_valid (Ghost.reveal mh) cur fuel /\
                  U64.v prev > 0 /\
                  U64.v cur >= U64.v zero_addr + U64.v mword /\
                  U64.v requested_wz > 0 /\
                  (match MH.read_word_in_major (Ghost.reveal mh) base with
                   | Some hdr ->
                     U64.v (SO.getWosize hdr) >= U64.v requested_wz /\
                     U64.v base + (1 + U64.v (SO.getWosize hdr)) * 8 <=
                       MH.chunk_end
                         (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_header_idx))
                   | None -> False))
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap
             (let r =
                SMA.major_alloc_search
                  (Ghost.reveal mh) head prev cur
                  (SA.normalized_wosize (U64.v requested_wz)) fuel in
              r.major_alloc_out) **
           pure (let r =
                   SMA.major_alloc_search
                     (Ghost.reveal mh) head prev cur
                     (SA.normalized_wosize (U64.v requested_wz)) fuel in
                 fst res == r.major_fp_out /\
                 snd res == r.major_obj_out)
{
  let block =
    read_major_free_block heap cur #fuel #cur_header_idx #cur_link_idx #mh;
  let hdr = fst block;
  let next_fp = snd block;
  let block_wz = SO.getWosize hdr;
  assert (pure (MH.read_word_in_major (Ghost.reveal mh) base == Some hdr));
  assert (pure (U64.v block_wz >= U64.v requested_wz));
  assert (pure (U64.v base + (1 + U64.v block_wz) * 8 <=
                MH.chunk_end
                  (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_header_idx))));
  let res =
    allocate_major_found_prev
      heap head prev base cur hdr block_wz requested_wz next_fp
      #fuel #cur_header_idx #prev_idx #mh;
  assert (pure (let r =
                  SMA.major_alloc_search
                    (Ghost.reveal mh) head prev cur
                    (SA.normalized_wosize (U64.v requested_wz)) fuel in
                fst res == r.major_fp_out /\
                snd res == r.major_obj_out));
  res
}

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
                  base == SH.hd_address cur /\
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
                  SMA.major_fl_valid (Ghost.reveal mh) cur fuel /\
                  SMA.major_fl_above_zero (Ghost.reveal mh) cur fuel /\
                  U64.v requested_wz > 0 /\
                  (match MH.read_word_in_major (Ghost.reveal mh) base with
                   | Some hdr ->
                     U64.v (SO.getWosize hdr) >= U64.v requested_wz /\
                     U64.v base + (1 + U64.v (SO.getWosize hdr)) * 8 <=
                       MH.chunk_end
                         (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_header_idx))
                   | None -> False))
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap
             (let r =
                SMA.major_alloc_search
                  (Ghost.reveal mh) head prev cur
                  (SA.normalized_wosize (U64.v requested_wz)) fuel in
              r.major_alloc_out) **
           pure (let r =
                  SMA.major_alloc_search
                    (Ghost.reveal mh) head prev cur
                    (SA.normalized_wosize (U64.v requested_wz)) fuel in
                 fst res == r.major_fp_out /\
                 snd res == r.major_obj_out)
{
  u64_positive_not_zero prev;
  SMA.major_fl_above_zero_current (Ghost.reveal mh) cur fuel;
  assert (pure (U64.v cur >= U64.v zero_addr + U64.v mword));
  allocate_major_found_prev_from_read
    heap head prev base cur requested_wz
    #fuel #cur_header_idx #cur_link_idx #prev_idx #mh
}

let major_found_prev_alloc_at (heap: MajorHeap.major_heap_t)
                              (head: U64.t)
                              (prev: obj_addr)
                              (base: hp_addr)
                              (cur: obj_addr)
                              (requested_wz: wosize)
                              (fuel cur_header_idx cur_link_idx prev_idx: nat)
                              (mh: MH.major_heap)
  : slprop =
  MajorHeap.is_indexed_major_heap heap mh **
  pure (fuel > 0 /\
        cur_header_idx < Seq.length mh /\
        cur_link_idx < Seq.length mh /\
        prev_idx < Seq.length mh /\
        base == SH.hd_address cur /\
        MH.lookup_chunk_index mh base == Some cur_header_idx /\
        MH.lookup_chunk_index mh cur == Some cur_link_idx /\
        MH.word_in_chunk (Seq.index mh cur_header_idx) base /\
        MH.word_in_chunk (Seq.index mh cur_link_idx) cur /\
        MH.word_in_chunk (Seq.index mh prev_idx) prev /\
        (forall (k:nat). k < prev_idx ==>
          ~(MH.word_in_chunk (Seq.index mh k) prev)) /\
        SMA.major_fl_valid mh cur fuel /\
        SMA.major_fl_above_zero mh cur fuel /\
        U64.v requested_wz > 0 /\
        (match MH.read_word_in_major mh base with
         | Some hdr ->
           U64.v (SO.getWosize hdr) >= U64.v requested_wz /\
           U64.v base + (1 + U64.v (SO.getWosize hdr)) * 8 <=
             MH.chunk_end (Seq.index mh cur_header_idx)
         | None -> False))

let major_found_prev_alloc_witnesses (heap: MajorHeap.major_heap_t)
                                     (head: U64.t)
                                     (prev: obj_addr)
                                     (base: hp_addr)
                                     (cur: obj_addr)
                                     (requested_wz: wosize)
                                     (fuel: nat)
                                     (mh: MH.major_heap)
  : slprop =
  exists* (cur_header_idx:nat) (cur_link_idx:nat) (prev_idx:nat).
    major_found_prev_alloc_at
      heap head prev base cur requested_wz fuel
      cur_header_idx cur_link_idx prev_idx mh

fn allocate_major_found_prev_from_read_exists (heap: MajorHeap.major_heap_t)
                                             (head: U64.t)
                                             (prev: obj_addr)
                                             (base: hp_addr)
                                             (cur: obj_addr)
                                             (requested_wz: wosize)
                                             (#fuel: (f:nat{f > 0}))
                                             (#mh: Ghost.erased MH.major_heap)
   requires major_found_prev_alloc_witnesses
              heap head prev base cur requested_wz fuel (Ghost.reveal mh)
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap
             (let r =
                SMA.major_alloc_search
                  (Ghost.reveal mh) head prev cur
                  (SA.normalized_wosize (U64.v requested_wz)) fuel in
              r.major_alloc_out) **
           pure (let r =
                  SMA.major_alloc_search
                    (Ghost.reveal mh) head prev cur
                    (SA.normalized_wosize (U64.v requested_wz)) fuel in
                 fst res == r.major_fp_out /\
                 snd res == r.major_obj_out)
{
  unfold (major_found_prev_alloc_witnesses
            heap head prev base cur requested_wz fuel (Ghost.reveal mh));
  with cur_header_idx cur_link_idx prev_idx. assert (
    major_found_prev_alloc_at
      heap head prev base cur requested_wz fuel
      cur_header_idx cur_link_idx prev_idx (Ghost.reveal mh)
  );
  unfold (major_found_prev_alloc_at
    heap head prev base cur requested_wz fuel
    cur_header_idx cur_link_idx prev_idx (Ghost.reveal mh));
  allocate_major_found_prev_from_read_above_zero
    heap head prev base cur requested_wz #fuel
    #(Ghost.hide cur_header_idx)
    #(Ghost.hide cur_link_idx)
    #(Ghost.hide prev_idx)
    #mh
}

fn allocate_major_found_prev_by_valid (heap: MajorHeap.major_heap_t)
                                      (head: U64.t)
                                      (prev: obj_addr)
                                      (cur: obj_addr)
                                      (requested_wz: wosize)
                                      (#fuel: (f:nat{f > 0}))
                                      (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (SMA.major_fl_valid (Ghost.reveal mh) cur fuel /\
                  SMA.major_fl_above_zero (Ghost.reveal mh) cur fuel /\
                  SMA.major_fl_blocks_fit (Ghost.reveal mh) cur fuel /\
                  MH.read_word_in_major (Ghost.reveal mh) prev == Some cur /\
                  U64.v requested_wz > 0 /\
                  (match MH.read_word_in_major (Ghost.reveal mh) (SH.hd_address cur) with
                   | Some hdr ->
                     U64.v (SO.getWosize hdr) >= U64.v requested_wz
                   | None -> False))
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap
             (let r =
                SMA.major_alloc_search
                  (Ghost.reveal mh) head prev cur
                  (SA.normalized_wosize (U64.v requested_wz)) fuel in
              r.major_alloc_out) **
           pure (let r =
                  SMA.major_alloc_search
                    (Ghost.reveal mh) head prev cur
                    (SA.normalized_wosize (U64.v requested_wz)) fuel in
                 fst res == r.major_fp_out /\
                 snd res == r.major_obj_out)
{
  SMA.major_fl_above_zero_current (Ghost.reveal mh) cur fuel;
  assert (pure (U64.v cur >= U64.v zero_addr + U64.v mword));
  SMA.major_fl_valid_header_lookup_index (Ghost.reveal mh) cur fuel;
  SMA.major_fl_valid_link_lookup_index (Ghost.reveal mh) cur fuel;
  SMA.major_fl_blocks_fit_current (Ghost.reveal mh) cur fuel;
  MH.read_word_in_major_lookup_index (Ghost.reveal mh) prev cur;
  let base = SH.hd_address cur;
  let cur_header_idx =
    Ghost.hide (MH.lookup_chunk_index_value (Ghost.reveal mh) base);
  let cur_link_idx =
    Ghost.hide (MH.lookup_chunk_index_value (Ghost.reveal mh) cur);
  let prev_idx =
    Ghost.hide (MH.lookup_chunk_index_value (Ghost.reveal mh) prev);
  unfold (MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh));
  assert (pure (MH.well_formed_major_heap (Ghost.reveal mh)));
  fold (MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh));
  SMA.well_formed_no_prior_word_in_selected_chunk
    (Ghost.reveal mh) (Ghost.reveal prev_idx) prev;
  assert (pure (forall (k:nat). k < Ghost.reveal prev_idx ==>
    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh) k) prev)));
  allocate_major_found_prev_from_read_above_zero
    heap head prev base cur requested_wz #fuel
    #cur_header_idx #cur_link_idx #prev_idx #mh
}

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
                  cur_base == SH.hd_address cur /\
                  next_base == SH.hd_address next /\
                  MH.lookup_chunk_index (Ghost.reveal mh) cur_base ==
                    Some (Ghost.reveal cur_header_idx) /\
                  MH.lookup_chunk_index (Ghost.reveal mh) cur ==
                    Some (Ghost.reveal cur_link_idx) /\
                  MH.lookup_chunk_index (Ghost.reveal mh) next_base ==
                    Some (Ghost.reveal next_header_idx) /\
                  MH.lookup_chunk_index (Ghost.reveal mh) next ==
                    Some (Ghost.reveal next_link_idx) /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_header_idx)) cur_base /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_link_idx)) cur /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal next_header_idx)) next_base /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal next_link_idx)) next /\
                  SMA.major_fl_valid (Ghost.reveal mh) cur fuel /\
                  U64.v cur >= U64.v zero_addr + U64.v mword /\
                  U64.v next >= U64.v zero_addr + U64.v mword /\
                  U64.v requested_wz > 0 /\
                  MH.read_word_in_major (Ghost.reveal mh) cur == Some next /\
                  (match MH.read_word_in_major (Ghost.reveal mh) cur_base with
                   | Some hdr ->
                     U64.v (SO.getWosize hdr) <
                       SA.normalized_wosize (U64.v requested_wz)
                   | None -> False) /\
                  (match MH.read_word_in_major (Ghost.reveal mh) next_base with
                   | Some hdr ->
                     U64.v (SO.getWosize hdr) >= U64.v requested_wz /\
                     U64.v next_base + (1 + U64.v (SO.getWosize hdr)) * 8 <=
                       MH.chunk_end
                         (Seq.index (Ghost.reveal mh) (Ghost.reveal next_header_idx))
                   | None -> False))
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap
             (let r =
                SMA.major_alloc_search
                  (Ghost.reveal mh) head prev cur
                  (SA.normalized_wosize (U64.v requested_wz)) fuel in
              r.major_alloc_out) **
           pure (let r =
                   SMA.major_alloc_search
                     (Ghost.reveal mh) head prev cur
                     (SA.normalized_wosize (U64.v requested_wz)) fuel in
                 fst res == r.major_fp_out /\
                 snd res == r.major_obj_out)
{
  let advanced =
    advance_major_search_from_read
      heap head prev cur_base cur requested_wz
      #fuel #cur_header_idx #cur_link_idx #mh;
  assert (pure (advanced == next));
  assert (pure (SMA.major_fl_valid (Ghost.reveal mh) next (fuel - 1)));
  MH.lookup_chunk_index_some (Ghost.reveal mh) cur (Ghost.reveal cur_link_idx);
  assert (pure (forall (k:nat). k < Ghost.reveal cur_link_idx ==>
    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh) k) cur)));
  let res =
    allocate_major_found_prev_from_read
      heap head cur next_base next requested_wz
      #(fuel - 1) #next_header_idx #next_link_idx #cur_link_idx #mh;
  assert (pure (SMA.major_alloc_search
                  (Ghost.reveal mh) head prev cur
                  (SA.normalized_wosize (U64.v requested_wz)) fuel ==
                SMA.major_alloc_search
                  (Ghost.reveal mh) head cur next
                  (SA.normalized_wosize (U64.v requested_wz)) (fuel - 1)));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (SMA.major_alloc_search
        (Ghost.reveal mh) head cur next
        (SA.normalized_wosize (U64.v requested_wz)) (fuel - 1)).major_alloc_out)
  as
    (MajorHeap.is_indexed_major_heap heap
      (SMA.major_alloc_search
        (Ghost.reveal mh) head prev cur
        (SA.normalized_wosize (U64.v requested_wz)) fuel).major_alloc_out);
  assert (pure (let r =
                  SMA.major_alloc_search
                    (Ghost.reveal mh) head prev cur
                    (SA.normalized_wosize (U64.v requested_wz)) fuel in
                fst res == r.major_fp_out /\
                snd res == r.major_obj_out));
  res
}

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
                  cur_base == SH.hd_address cur /\
                  next_base == SH.hd_address next /\
                  MH.lookup_chunk_index (Ghost.reveal mh) cur_base ==
                    Some (Ghost.reveal cur_header_idx) /\
                  MH.lookup_chunk_index (Ghost.reveal mh) cur ==
                    Some (Ghost.reveal cur_link_idx) /\
                  MH.lookup_chunk_index (Ghost.reveal mh) next_base ==
                    Some (Ghost.reveal next_header_idx) /\
                  MH.lookup_chunk_index (Ghost.reveal mh) next ==
                    Some (Ghost.reveal next_link_idx) /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_header_idx)) cur_base /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal cur_link_idx)) cur /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal next_header_idx)) next_base /\
                  MH.word_in_chunk
                    (Seq.index (Ghost.reveal mh) (Ghost.reveal next_link_idx)) next /\
                  SMA.major_fl_valid (Ghost.reveal mh) cur fuel /\
                  SMA.major_fl_above_zero (Ghost.reveal mh) cur fuel /\
                  U64.v requested_wz > 0 /\
                  MH.read_word_in_major (Ghost.reveal mh) cur == Some next /\
                  (match MH.read_word_in_major (Ghost.reveal mh) cur_base with
                   | Some hdr ->
                     U64.v (SO.getWosize hdr) <
                       SA.normalized_wosize (U64.v requested_wz)
                   | None -> False) /\
                  (match MH.read_word_in_major (Ghost.reveal mh) next_base with
                   | Some hdr ->
                     U64.v (SO.getWosize hdr) >= U64.v requested_wz /\
                     U64.v next_base + (1 + U64.v (SO.getWosize hdr)) * 8 <=
                       MH.chunk_end
                         (Seq.index (Ghost.reveal mh) (Ghost.reveal next_header_idx))
                   | None -> False))
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap
             (let r =
                SMA.major_alloc_search
                  (Ghost.reveal mh) head prev cur
                  (SA.normalized_wosize (U64.v requested_wz)) fuel in
              r.major_alloc_out) **
           pure (let r =
                  SMA.major_alloc_search
                    (Ghost.reveal mh) head prev cur
                    (SA.normalized_wosize (U64.v requested_wz)) fuel in
                 fst res == r.major_fp_out /\
                 snd res == r.major_obj_out)
{
  u64_positive_not_zero cur;
  SMA.major_fl_above_zero_current (Ghost.reveal mh) cur fuel;
  assert (pure (U64.v cur >= U64.v zero_addr + U64.v mword));
  let advanced =
    advance_major_search_from_read_above_zero
      heap head prev cur_base cur requested_wz
      #fuel #cur_header_idx #cur_link_idx #mh;
  assert (pure (advanced == next));
  assert (pure (SMA.major_fl_valid (Ghost.reveal mh) next (fuel - 1)));
  assert (pure (SMA.major_fl_above_zero (Ghost.reveal mh) next (fuel - 1)));
  u64_positive_not_zero next;
  SMA.major_fl_above_zero_current (Ghost.reveal mh) next (fuel - 1);
  assert (pure (U64.v next >= U64.v zero_addr + U64.v mword));
  MH.lookup_chunk_index_some (Ghost.reveal mh) cur (Ghost.reveal cur_link_idx);
  assert (pure (forall (k:nat). k < Ghost.reveal cur_link_idx ==>
    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh) k) cur)));
  let res =
    allocate_major_found_prev_from_read
      heap head cur next_base next requested_wz
      #(fuel - 1) #next_header_idx #next_link_idx #cur_link_idx #mh;
  assert (pure (SMA.major_alloc_search
                  (Ghost.reveal mh) head prev cur
                  (SA.normalized_wosize (U64.v requested_wz)) fuel ==
                SMA.major_alloc_search
                  (Ghost.reveal mh) head cur next
                  (SA.normalized_wosize (U64.v requested_wz)) (fuel - 1)));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (SMA.major_alloc_search
        (Ghost.reveal mh) head cur next
        (SA.normalized_wosize (U64.v requested_wz)) (fuel - 1)).major_alloc_out)
  as
    (MajorHeap.is_indexed_major_heap heap
      (SMA.major_alloc_search
        (Ghost.reveal mh) head prev cur
        (SA.normalized_wosize (U64.v requested_wz)) fuel).major_alloc_out);
  assert (pure (let r =
                  SMA.major_alloc_search
                    (Ghost.reveal mh) head prev cur
                    (SA.normalized_wosize (U64.v requested_wz)) fuel in
                fst res == r.major_fp_out /\
                snd res == r.major_obj_out));
  res
}

#push-options "--z3rlimit 120"
fn allocate_major_with_fuel_loop (heap: MajorHeap.major_heap_t)
                                (fp: U64.t)
                                (requested_wz: wosize)
                                (fuel: U64.t)
                                (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (U64.v requested_wz > 0 /\
                  SMA.major_fl_valid (Ghost.reveal mh) fp (U64.v fuel) /\
                  SMA.major_fl_above_zero (Ghost.reveal mh) fp (U64.v fuel) /\
                  SMA.major_fl_blocks_fit (Ghost.reveal mh) fp (U64.v fuel))
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap
             (let r =
                SMA.major_alloc_spec_with_fuel
                  (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel) in
              r.major_alloc_out) **
           pure (let r =
                  SMA.major_alloc_spec_with_fuel
                    (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel) in
                 fst res == r.major_fp_out /\
                 snd res == r.major_obj_out)
{
  assert (pure (SA.normalized_wosize (U64.v requested_wz) ==
               U64.v requested_wz));
  let mut head_fp = fp;
  let mut prev_fp = 0UL;
  let mut cur_fp = fp;
  let mut found = false;
  let mut go = true;
  let mut fuel_ref = fuel;

  while (!go)
   invariant exists* vgo vfuel vhead vprev vcur vfound.
     R.pts_to go vgo **
     R.pts_to fuel_ref vfuel **
     R.pts_to head_fp vhead **
     R.pts_to prev_fp vprev **
     R.pts_to cur_fp vcur **
     R.pts_to found vfound **
     MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
     pure (
       SA.normalized_wosize (U64.v requested_wz) == U64.v requested_wz /\
       U64.v vfuel <= U64.v fuel /\
       vhead == fp /\
       (if vgo then
         vfound == false /\
         SMA.major_fl_valid (Ghost.reveal mh) vcur (U64.v vfuel) /\
         SMA.major_fl_above_zero (Ghost.reveal mh) vcur (U64.v vfuel) /\
         SMA.major_fl_blocks_fit (Ghost.reveal mh) vcur (U64.v vfuel) /\
          (vprev == 0UL ==> vcur == vhead) /\
          (vprev <> 0UL ==>
            U64.v vprev >= U64.v zero_addr + U64.v mword /\
            U64.v vprev < heap_size /\
            U64.v vprev % U64.v mword == 0 /\
            MH.read_word_in_major (Ghost.reveal mh) (vprev <: obj_addr) ==
              Some vcur) /\
          SMA.major_alloc_search
            (Ghost.reveal mh) vhead vprev vcur
            (SA.normalized_wosize (U64.v requested_wz)) (U64.v vfuel) ==
          SMA.major_alloc_spec_with_fuel
            (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel)
        else
          if vfound then
            U64.v vfuel > 0 /\
            U64.v vcur >= U64.v zero_addr + U64.v mword /\
            U64.v vcur >= U64.v mword /\
            U64.v vcur < heap_size /\
            U64.v vcur % U64.v mword == 0 /\
            SMA.major_fl_valid (Ghost.reveal mh) vcur (U64.v vfuel) /\
            SMA.major_fl_above_zero (Ghost.reveal mh) vcur (U64.v vfuel) /\
            SMA.major_fl_blocks_fit (Ghost.reveal mh) vcur (U64.v vfuel) /\
            (vprev == 0UL ==> vcur == vhead) /\
            (vprev <> 0UL ==>
              U64.v vprev >= U64.v zero_addr + U64.v mword /\
              U64.v vprev < heap_size /\
              U64.v vprev % U64.v mword == 0 /\
              MH.read_word_in_major (Ghost.reveal mh) (vprev <: obj_addr) ==
                Some vcur) /\
            (match MH.read_word_in_major (Ghost.reveal mh) (SH.hd_address (vcur <: obj_addr)) with
             | Some hdr -> U64.v (SO.getWosize hdr) >= U64.v requested_wz
             | None -> False) /\
            SMA.major_alloc_search
              (Ghost.reveal mh) vhead vprev vcur
              (SA.normalized_wosize (U64.v requested_wz)) (U64.v vfuel) ==
            SMA.major_alloc_spec_with_fuel
              (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel)
          else
            (let r =
               SMA.major_alloc_spec_with_fuel
                 (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel) in
             r.major_alloc_out == Ghost.reveal mh /\
             r.major_fp_out == vhead /\
             r.major_obj_out == 0UL))
      )
  {
    let vfuel = !fuel_ref;
    if U64.eq vfuel 0UL {
      let vh = !head_fp;
      let vp = !prev_fp;
      let vc = !cur_fp;
      SMA.major_alloc_search_fuel_0
        (Ghost.reveal mh) vh vp vc
        (SA.normalized_wosize (U64.v requested_wz));
      assert (pure (let r =
                      SMA.major_alloc_spec_with_fuel
                        (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel) in
                    r.major_alloc_out == Ghost.reveal mh /\
                    r.major_fp_out == vh /\
                    r.major_obj_out == 0UL));
      go := false
    } else {
      let vcur = !cur_fp;
      let valid = is_valid_fp vcur;
      if not valid {
        let vh = !head_fp;
        let vp = !prev_fp;
        SMA.major_alloc_search_invalid
          (Ghost.reveal mh) vh vp vcur
          (SA.normalized_wosize (U64.v requested_wz)) (U64.v vfuel);
        assert (pure (let r =
                        SMA.major_alloc_spec_with_fuel
                          (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel) in
                      r.major_alloc_out == Ghost.reveal mh /\
                      r.major_fp_out == vh /\
                      r.major_obj_out == 0UL));
        go := false
      } else {
        let cur_obj : obj_addr = vcur;
        let block =
          read_major_free_block_by_valid
            heap cur_obj #(U64.v vfuel) #mh;
        let hdr = fst block;
        let block_wz = getWosize hdr;
        getWosize_eq hdr;
        assert (pure (MH.read_word_in_major
                        (Ghost.reveal mh) (SH.hd_address cur_obj) == Some hdr));
        if U64.gte block_wz requested_wz {
          assert (pure (U64.v (SO.getWosize hdr) >= U64.v requested_wz));
          let vh = !head_fp;
          let vp = !prev_fp;
          assert (pure (U64.v vfuel > 0));
          assert (pure (U64.v vcur >= U64.v zero_addr + U64.v mword));
          assert (pure (U64.v vcur >= U64.v mword));
          assert (pure (U64.v vcur < heap_size));
          assert (pure (U64.v vcur % U64.v mword == 0));
          assert (pure (SMA.major_fl_valid (Ghost.reveal mh) vcur (U64.v vfuel)));
          assert (pure (SMA.major_fl_above_zero (Ghost.reveal mh) vcur (U64.v vfuel)));
          assert (pure (SMA.major_fl_blocks_fit (Ghost.reveal mh) vcur (U64.v vfuel)));
          assert (pure (vh == fp));
          assert (pure (vp == 0UL ==> vcur == vh));
          assert (pure (vp <> 0UL ==>
            U64.v vp >= U64.v zero_addr + U64.v mword /\
            U64.v vp < heap_size /\
            U64.v vp % U64.v mword == 0 /\
            MH.read_word_in_major (Ghost.reveal mh) (vp <: obj_addr) ==
              Some vcur));
          assert (pure (
            match MH.read_word_in_major (Ghost.reveal mh) (SH.hd_address cur_obj) with
            | Some hdr' -> U64.v (SO.getWosize hdr') >= U64.v requested_wz
            | None -> False));
          assert (pure (SMA.major_alloc_search
                          (Ghost.reveal mh) vh vp vcur
                          (SA.normalized_wosize (U64.v requested_wz)) (U64.v vfuel) ==
                        SMA.major_alloc_spec_with_fuel
                          (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel)));
          found := true;
          go := false
        } else {
          assert (pure (U64.v (SO.getWosize hdr) <
                        SA.normalized_wosize (U64.v requested_wz)));
          let vh = !head_fp;
          let vp = !prev_fp;
          let next =
            advance_major_search_by_valid
              heap vh vp cur_obj requested_wz #(U64.v vfuel) #mh;
          u64_sub_one_value vfuel;
          assert (pure (U64.v (U64.sub vfuel 1UL) == U64.v vfuel - 1));
          prev_fp := vcur;
          cur_fp := next;
          fuel_ref := U64.sub vfuel 1UL
        }
      }
    }
  };

  let final_found = !found;
  let final_head = !head_fp;
  let final_prev = !prev_fp;
  let final_cur = !cur_fp;
  let final_fuel = !fuel_ref;
  if final_found {
    let cur_obj : obj_addr = final_cur;
    if U64.eq final_prev 0UL {
      let res =
        allocate_major_head_by_valid
          heap cur_obj requested_wz #(U64.v final_fuel) #mh;
      assert (pure (SMA.major_alloc_spec_with_fuel
                     (Ghost.reveal mh) cur_obj
                     (U64.v requested_wz) (U64.v final_fuel) ==
                    SMA.major_alloc_search
                     (Ghost.reveal mh) fp 0UL cur_obj
                     (SA.normalized_wosize (U64.v requested_wz))
                     (U64.v final_fuel)));
      assert (pure (let r =
                     SMA.major_alloc_spec_with_fuel
                       (Ghost.reveal mh) fp
                       (U64.v requested_wz) (U64.v fuel) in
                    (SMA.major_alloc_spec_with_fuel
                     (Ghost.reveal mh) cur_obj
                     (U64.v requested_wz)
                     (U64.v final_fuel)).major_alloc_out ==
                    r.major_alloc_out /\
                    fst res == r.major_fp_out /\
                    snd res == r.major_obj_out));
      rewrite
        (MajorHeap.is_indexed_major_heap heap
          (SMA.major_alloc_spec_with_fuel
            (Ghost.reveal mh) cur_obj
            (U64.v requested_wz)
            (U64.v final_fuel)).major_alloc_out)
      as
        (MajorHeap.is_indexed_major_heap heap
          (let r =
             SMA.major_alloc_spec_with_fuel
               (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel) in
           r.major_alloc_out));
      res
    } else {
      let prev_obj : obj_addr = final_prev;
      let res =
        allocate_major_found_prev_by_valid
          heap final_head prev_obj cur_obj requested_wz #(U64.v final_fuel) #mh;
      assert (pure (let r =
                     SMA.major_alloc_spec_with_fuel
                       (Ghost.reveal mh) fp
                       (U64.v requested_wz) (U64.v fuel) in
                    (SMA.major_alloc_search
                     (Ghost.reveal mh) final_head prev_obj cur_obj
                     (SA.normalized_wosize (U64.v requested_wz))
                     (U64.v final_fuel)).major_alloc_out ==
                    r.major_alloc_out /\
                    fst res == r.major_fp_out /\
                    snd res == r.major_obj_out));
      rewrite
        (MajorHeap.is_indexed_major_heap heap
          (SMA.major_alloc_search
            (Ghost.reveal mh) final_head prev_obj cur_obj
            (SA.normalized_wosize (U64.v requested_wz))
            (U64.v final_fuel)).major_alloc_out)
      as
        (MajorHeap.is_indexed_major_heap heap
          (let r =
             SMA.major_alloc_spec_with_fuel
               (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel) in
           r.major_alloc_out));
      res
    }
  } else {
    assert (pure (let r =
                   SMA.major_alloc_spec_with_fuel
                    (Ghost.reveal mh) fp
                    (U64.v requested_wz) (U64.v fuel) in
                  r.major_alloc_out == Ghost.reveal mh /\
                  r.major_fp_out == final_head /\
                  r.major_obj_out == 0UL));
    rewrite
      (MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh))
    as
      (MajorHeap.is_indexed_major_heap heap
        (let r =
           SMA.major_alloc_spec_with_fuel
             (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel) in
         r.major_alloc_out));
    (final_head, 0UL)
  }
}
#pop-options

fn allocate_major_with_fuel (heap: MajorHeap.major_heap_t)
                            (fp: U64.t)
                            (requested_wz: wosize)
                            (fuel: U64.t)
                            (#mh: Ghost.erased MH.major_heap)
  requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (U64.v requested_wz > 0 /\
                 SMA.major_fl_valid (Ghost.reveal mh) fp (U64.v fuel) /\
                 SMA.major_fl_above_zero (Ghost.reveal mh) fp (U64.v fuel) /\
                 SMA.major_fl_blocks_fit (Ghost.reveal mh) fp (U64.v fuel))
  returns res: (U64.t & U64.t)
  ensures MajorHeap.is_indexed_major_heap heap
            (let r =
               SMA.major_alloc_spec_with_fuel
                 (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel) in
             r.major_alloc_out) **
          pure (let r =
                 SMA.major_alloc_spec_with_fuel
                   (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel) in
                fst res == r.major_fp_out /\
                snd res == r.major_obj_out)
{
  allocate_major_with_fuel_loop heap fp requested_wz fuel #mh
}

fn allocate_major_with_fuel_preserve_oom (heap: MajorHeap.major_heap_t)
                                        (fp: U64.t)
                                        (requested_wz: wosize)
                                        (fuel: U64.t)
                                        (#mh: Ghost.erased MH.major_heap)
  requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (U64.v requested_wz > 0 /\
                 SMA.major_fl_valid (Ghost.reveal mh) fp (U64.v fuel) /\
                 SMA.major_fl_above_zero (Ghost.reveal mh) fp (U64.v fuel) /\
                 SMA.major_fl_blocks_fit (Ghost.reveal mh) fp (U64.v fuel))
  returns res: (U64.t & U64.t)
  ensures (if U64.eq (snd res) 0UL
           then MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh)
           else
             MajorHeap.is_indexed_major_heap heap
               (let r =
                  SMA.major_alloc_spec_with_fuel
                    (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel) in
                r.major_alloc_out)) **
          pure (let r =
                 SMA.major_alloc_spec_with_fuel
                   (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel) in
                fst res == r.major_fp_out /\
                snd res == r.major_obj_out /\
                (snd res == 0UL ==> r.major_alloc_out == Ghost.reveal mh))
{
  let res =
    allocate_major_with_fuel heap fp requested_wz fuel #mh;
  if U64.eq (snd res) 0UL {
    assert (pure (snd res == 0UL));
    assert (pure (U64.eq (snd res) 0UL == true));
    assert (pure ((SMA.major_alloc_spec_with_fuel
                    (Ghost.reveal mh) fp (U64.v requested_wz)
                    (U64.v fuel)).major_obj_out == 0UL));
    SMA.major_alloc_spec_with_fuel_oom_unchanged
      (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel);
    assert (pure ((SMA.major_alloc_spec_with_fuel
                    (Ghost.reveal mh) fp (U64.v requested_wz)
                    (U64.v fuel)).major_alloc_out == Ghost.reveal mh));
    rewrite
      (MajorHeap.is_indexed_major_heap heap
        (SMA.major_alloc_spec_with_fuel
          (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel)).major_alloc_out)
    as
      (MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh));
    rewrite
      (MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh))
    as
      (if U64.eq (snd res) 0UL
       then MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh)
       else
         MajorHeap.is_indexed_major_heap heap
           (let r =
              SMA.major_alloc_spec_with_fuel
                (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel) in
            r.major_alloc_out));
    res
  } else {
    assert (pure (snd res <> 0UL));
    assert (pure (U64.eq (snd res) 0UL == false));
    rewrite
      (MajorHeap.is_indexed_major_heap heap
        (let r =
           SMA.major_alloc_spec_with_fuel
             (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel) in
         r.major_alloc_out))
    as
      (if U64.eq (snd res) 0UL
       then MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh)
       else
         MajorHeap.is_indexed_major_heap heap
           (let r =
              SMA.major_alloc_spec_with_fuel
                (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel) in
            r.major_alloc_out));
    res
  }
}

fn init_fresh_chunk_owned (heap: MajorHeap.major_heap_t)
                          (base: hp_addr) (fp_out: obj_addr)
                          (wz: wosize) (next_fp: U64.t)
                          (#fresh: Ghost.erased
                            (c:MH.heap_chunk{c.base == base /\
                                             fp_out == SMA.fresh_chunk_object c /\
                                             wz == SMA.fresh_chunk_wosize_u64 c}))
  requires MajorHeap.chunk_range heap (Ghost.reveal fresh)
  ensures MajorHeap.chunk_range heap
            (SMA.init_fresh_chunk (Ghost.reveal fresh) next_fp).chunk_out
{
  let hdr = makeHeader wz blue 0UL;
  assert (pure (SA.blue_bits == 2UL));
  assert (pure (pack_color blue == 2UL));
  assert (pure (hdr == SA.make_header wz SA.blue_bits 0UL));
  assert (pure (wz == SMA.fresh_chunk_wosize_u64 (Ghost.reveal fresh)));
  assert (pure (hdr ==
                SA.make_header (SMA.fresh_chunk_wosize_u64 (Ghost.reveal fresh))
                  SA.blue_bits 0UL));
  assert (pure (MH.word_in_chunk (Ghost.reveal fresh) base));
  MajorHeap.write_word_in_chunk heap base hdr #(Ghost.hide (Ghost.reveal fresh));
  SMA.fresh_chunk_object_word (Ghost.reveal fresh);
  assert (pure (MH.word_in_chunk (Ghost.reveal fresh) fp_out));
  MH.write_word_in_chunk_preserves_word (Ghost.reveal fresh) base hdr fp_out;
  assert (pure (MH.word_in_chunk (MH.write_word_in_chunk (Ghost.reveal fresh) base hdr) fp_out));
  MajorHeap.write_word_in_chunk heap fp_out next_fp
    #(Ghost.hide (MH.write_word_in_chunk (Ghost.reveal fresh) base hdr));
  assert (pure (MH.write_word_in_chunk
                  (MH.write_word_in_chunk (Ghost.reveal fresh) base hdr)
                  fp_out next_fp ==
                (SMA.init_fresh_chunk (Ghost.reveal fresh) next_fp).chunk_out));
  rewrite
    (MajorHeap.chunk_range heap
      (MH.write_word_in_chunk
        (MH.write_word_in_chunk (Ghost.reveal fresh) base hdr)
        fp_out next_fp))
  as
    (MajorHeap.chunk_range heap
      (SMA.init_fresh_chunk (Ghost.reveal fresh) next_fp).chunk_out)
}

fn expand_major_heap_owned (heap: MajorHeap.major_heap_t)
                           (base: hp_addr) (fp_out: obj_addr)
                           (wz: wosize) (next_fp: U64.t)
                           (#mh: Ghost.erased MH.major_heap)
                           (#fresh: Ghost.erased
                             (c:MH.heap_chunk{c.base == base /\
                                              fp_out == SMA.fresh_chunk_object c /\
                                              wz == SMA.fresh_chunk_wosize_u64 c}))
  requires MajorHeap.chunk_range heap (Ghost.reveal fresh) **
           MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (MH.chunk_disjoint_from_all (Ghost.reveal fresh) (Ghost.reveal mh))
  returns new_fp: U64.t
  ensures MajorHeap.is_indexed_major_heap heap
            (SMA.expand_major_heap
              (Ghost.reveal mh) (Ghost.reveal fresh) next_fp).major_out **
          pure (new_fp ==
            (SMA.expand_major_heap
              (Ghost.reveal mh) (Ghost.reveal fresh) next_fp).fp_out)
{
  init_fresh_chunk_owned heap base fp_out wz next_fp #fresh;
  SMA.init_fresh_chunk_disjoint_from_all (Ghost.reveal mh) (Ghost.reveal fresh) next_fp;
  MajorHeap.prepend_chunk_to_indexed_major heap
    #mh
    #(Ghost.hide (SMA.init_fresh_chunk (Ghost.reveal fresh) next_fp).chunk_out);
  assert (pure ((SMA.expand_major_heap (Ghost.reveal mh) (Ghost.reveal fresh) next_fp).fp_out ==
                fp_out));
  fp_out
}

fn expand_major_heap_owned_above_zero (heap: MajorHeap.major_heap_t)
                                      (base: hp_addr) (fp_out: obj_addr)
                                      (wz: wosize) (next_fp: U64.t)
                                      (#fuel: nat)
                                      (#mh: Ghost.erased MH.major_heap)
                                      (#fresh: Ghost.erased
                                        (c:MH.heap_chunk{c.base == base /\
                                                         fp_out == SMA.fresh_chunk_object c /\
                                                         wz == SMA.fresh_chunk_wosize_u64 c}))
  requires MajorHeap.chunk_range heap (Ghost.reveal fresh) **
           MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (MH.chunk_disjoint_from_all (Ghost.reveal fresh) (Ghost.reveal mh) /\
                 U64.v base >= U64.v zero_addr /\
                 next_fp <> fp_out /\
                 SMA.major_fl_valid (Ghost.reveal mh) next_fp fuel /\
                 SMA.major_fl_above_zero (Ghost.reveal mh) next_fp fuel)
  returns new_fp: U64.t
  ensures MajorHeap.is_indexed_major_heap heap
            (SMA.expand_major_heap
              (Ghost.reveal mh) (Ghost.reveal fresh) next_fp).major_out **
          pure (let er =
                  SMA.expand_major_heap
                    (Ghost.reveal mh) (Ghost.reveal fresh) next_fp in
                new_fp == er.fp_out /\
                SMA.major_fl_valid er.major_out new_fp (fuel + 1) /\
                SMA.major_fl_above_zero er.major_out new_fp (fuel + 1))
{
  let new_fp =
    expand_major_heap_owned heap base fp_out wz next_fp #mh #fresh;
  assert (pure (new_fp == fp_out));
  assert (pure (fp_out == SMA.fresh_chunk_object (Ghost.reveal fresh)));
  assert (pure (next_fp <> SMA.fresh_chunk_object (Ghost.reveal fresh)));
  SMA.expand_major_heap_links_fl_valid
    (Ghost.reveal mh) (Ghost.reveal fresh) next_fp fuel;
  SMA.expand_major_heap_links_fl_above_zero
    (Ghost.reveal mh) (Ghost.reveal fresh) next_fp fuel;
  assert (pure (let er =
                  SMA.expand_major_heap
                    (Ghost.reveal mh) (Ghost.reveal fresh) next_fp in
                new_fp == er.fp_out /\
                SMA.major_fl_valid er.major_out new_fp (fuel + 1) /\
                SMA.major_fl_above_zero er.major_out new_fp (fuel + 1)));
  new_fp
}

fn allocate_fresh_expanded_exact (heap: MajorHeap.major_heap_t)
                                 (base: hp_addr) (fp_out: obj_addr)
                                 (wz: wosize) (next_fp: U64.t)
                                 (#mh: Ghost.erased MH.major_heap)
                                 (#fresh: Ghost.erased
                                   (c:MH.heap_chunk{c.base == base /\
                                                    fp_out == SMA.fresh_chunk_object c /\
                                                    wz == SMA.fresh_chunk_wosize_u64 c}))
  requires MajorHeap.is_indexed_major_heap heap
            (SMA.expand_major_heap
              (Ghost.reveal mh) (Ghost.reveal fresh) next_fp).major_out **
           pure (U64.v base >= U64.v zero_addr)
  returns res: (U64.t & U64.t)
  ensures MajorHeap.is_indexed_major_heap heap
            (let er =
              SMA.expand_major_heap
                (Ghost.reveal mh) (Ghost.reveal fresh) next_fp in
             (SMA.major_alloc_spec_with_fuel
               er.major_out er.fp_out (U64.v wz) 1).major_alloc_out) **
          pure (let er =
                  SMA.expand_major_heap
                    (Ghost.reveal mh) (Ghost.reveal fresh) next_fp in
                let r =
                  SMA.major_alloc_spec_with_fuel
                    er.major_out er.fp_out (U64.v wz) 1 in
                fst res == r.major_fp_out /\
                snd res == r.major_obj_out)
{
  let er = Ghost.hide (SMA.expand_major_heap (Ghost.reveal mh) (Ghost.reveal fresh) next_fp);
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (SMA.expand_major_heap (Ghost.reveal mh) (Ghost.reveal fresh) next_fp).major_out)
  as
    (MajorHeap.is_indexed_major_heap heap (Ghost.reveal er).major_out);
  let init = Ghost.hide (SMA.init_fresh_chunk (Ghost.reveal fresh) next_fp).chunk_out;
  let hdr = makeHeader wz white 0UL;
  assert (pure (SA.white_bits == 0UL));
  assert (pure (pack_color white == 0UL));
  assert (pure (hdr == SA.make_header wz SA.white_bits 0UL));
  assert (pure (wz == SMA.fresh_chunk_wosize_u64 (Ghost.reveal fresh)));
  assert (pure (hdr ==
                SA.make_header (SMA.fresh_chunk_wosize_u64 (Ghost.reveal fresh))
                  SA.white_bits 0UL));
  SMA.major_alloc_after_expand_exact (Ghost.reveal mh) (Ghost.reveal fresh) next_fp 0;
  assert (pure ((Ghost.reveal er).fp_out == fp_out));
  assert (pure (Seq.length (Ghost.reveal er).major_out > 0));
  assert (pure (Seq.index (Ghost.reveal er).major_out 0 == Ghost.reveal init));
  assert (pure (MH.word_in_chunk (Ghost.reveal init) base));
  assert (pure (MH.lookup_chunk_index (Ghost.reveal er).major_out base == Some 0));
  MajorHeap.write_word_in_indexed_major_at_lookup_index heap base hdr 0
    #(Ghost.hide (Ghost.reveal er).major_out);
  assert (pure (Seq.upd (Ghost.reveal er).major_out 0
                  (MH.write_word_in_chunk (Seq.index (Ghost.reveal er).major_out 0) base hdr) ==
                Seq.upd (Ghost.reveal er).major_out 0
                  (MH.write_word_in_chunk (Ghost.reveal init) base
                    (SA.make_header (SMA.fresh_chunk_wosize_u64 (Ghost.reveal fresh))
                      SA.white_bits 0UL))));
  assert (pure (let r = SMA.major_alloc_spec_with_fuel (Ghost.reveal er).major_out (Ghost.reveal er).fp_out (U64.v wz) 1 in
                Seq.upd (Ghost.reveal er).major_out 0
                  (MH.write_word_in_chunk (Seq.index (Ghost.reveal er).major_out 0) base hdr) ==
                r.major_alloc_out /\
                next_fp == r.major_fp_out /\
                fp_out == r.major_obj_out));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal er).major_out 0
        (MH.write_word_in_chunk (Seq.index (Ghost.reveal er).major_out 0) base hdr)))
  as
    (MajorHeap.is_indexed_major_heap heap
      (SMA.major_alloc_spec_with_fuel (Ghost.reveal er).major_out (Ghost.reveal er).fp_out (U64.v wz) 1).major_alloc_out);
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (SMA.major_alloc_spec_with_fuel (Ghost.reveal er).major_out (Ghost.reveal er).fp_out (U64.v wz) 1).major_alloc_out)
  as
    (MajorHeap.is_indexed_major_heap heap
      (let er' = SMA.expand_major_heap (Ghost.reveal mh) (Ghost.reveal fresh) next_fp in
       (SMA.major_alloc_spec_with_fuel er'.major_out er'.fp_out (U64.v wz) 1).major_alloc_out));
  (next_fp, fp_out)
}

fn allocate_fresh_expanded_no_split (heap: MajorHeap.major_heap_t)
                                    (base: hp_addr) (fp_out: obj_addr)
                                    (fresh_wz requested_wz: wosize)
                                    (next_fp: U64.t)
                                    (#mh: Ghost.erased MH.major_heap)
                                    (#fresh_chunk: Ghost.erased
                                      (c:MH.heap_chunk{c.base == base /\
                                                       fp_out == SMA.fresh_chunk_object c /\
                                                       fresh_wz == SMA.fresh_chunk_wosize_u64 c}))
  requires MajorHeap.is_indexed_major_heap heap
            (SMA.expand_major_heap
              (Ghost.reveal mh) (Ghost.reveal fresh_chunk) next_fp).major_out **
           pure (U64.v base >= U64.v zero_addr /\
                 U64.v requested_wz > 0 /\
                 SMA.fresh_chunk_wosize (Ghost.reveal fresh_chunk) >=
                   U64.v requested_wz /\
                 SMA.fresh_chunk_wosize (Ghost.reveal fresh_chunk) -
                   U64.v requested_wz < 2)
  returns res: (U64.t & U64.t)
  ensures MajorHeap.is_indexed_major_heap heap
            (let er =
              SMA.expand_major_heap
                (Ghost.reveal mh) (Ghost.reveal fresh_chunk) next_fp in
             (SMA.major_alloc_spec_with_fuel
               er.major_out er.fp_out (U64.v requested_wz) 1).major_alloc_out) **
          pure (fst res == next_fp /\
                snd res == fp_out)
{
  let er = Ghost.hide (SMA.expand_major_heap (Ghost.reveal mh) (Ghost.reveal fresh_chunk) next_fp);
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (SMA.expand_major_heap (Ghost.reveal mh) (Ghost.reveal fresh_chunk) next_fp).major_out)
  as
    (MajorHeap.is_indexed_major_heap heap (Ghost.reveal er).major_out);
  let init = Ghost.hide (SMA.init_fresh_chunk (Ghost.reveal fresh_chunk) next_fp).chunk_out;
  let hdr = makeHeader fresh_wz white 0UL;
  assert (pure (SA.white_bits == 0UL));
  assert (pure (pack_color white == 0UL));
  assert (pure (fresh_wz == SMA.fresh_chunk_wosize_u64 (Ghost.reveal fresh_chunk)));
  assert (pure (hdr ==
                SA.make_header (SMA.fresh_chunk_wosize_u64 (Ghost.reveal fresh_chunk))
                  SA.white_bits 0UL));
  SMA.major_alloc_after_expand_no_split
    (Ghost.reveal mh) (Ghost.reveal fresh_chunk) next_fp (U64.v requested_wz) 0;
  assert (pure ((Ghost.reveal er).fp_out == fp_out));
  assert (pure (Seq.length (Ghost.reveal er).major_out > 0));
  assert (pure (Seq.index (Ghost.reveal er).major_out 0 == Ghost.reveal init));
  assert (pure (MH.word_in_chunk (Ghost.reveal init) base));
  assert (pure (MH.lookup_chunk_index (Ghost.reveal er).major_out base == Some 0));
  MajorHeap.write_word_in_indexed_major_at_lookup_index heap base hdr 0
    #(Ghost.hide (Ghost.reveal er).major_out);
  assert (pure (Seq.upd (Ghost.reveal er).major_out 0
                  (MH.write_word_in_chunk (Seq.index (Ghost.reveal er).major_out 0) base hdr) ==
                Seq.upd (Ghost.reveal er).major_out 0
                  (MH.write_word_in_chunk (Ghost.reveal init) base
                    (SA.make_header (SMA.fresh_chunk_wosize_u64 (Ghost.reveal fresh_chunk))
                      SA.white_bits 0UL))));
  assert (pure (let r = SMA.major_alloc_spec_with_fuel
                           (Ghost.reveal er).major_out (Ghost.reveal er).fp_out
                           (U64.v requested_wz) 1 in
                Seq.upd (Ghost.reveal er).major_out 0
                  (MH.write_word_in_chunk (Seq.index (Ghost.reveal er).major_out 0) base hdr) ==
                r.major_alloc_out /\
                next_fp == r.major_fp_out /\
                fp_out == r.major_obj_out));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal er).major_out 0
        (MH.write_word_in_chunk (Seq.index (Ghost.reveal er).major_out 0) base hdr)))
  as
    (MajorHeap.is_indexed_major_heap heap
      (SMA.major_alloc_spec_with_fuel
        (Ghost.reveal er).major_out (Ghost.reveal er).fp_out (U64.v requested_wz) 1).major_alloc_out);
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (SMA.major_alloc_spec_with_fuel
        (Ghost.reveal er).major_out (Ghost.reveal er).fp_out (U64.v requested_wz) 1).major_alloc_out)
  as
    (MajorHeap.is_indexed_major_heap heap
      (let er' = SMA.expand_major_heap (Ghost.reveal mh) (Ghost.reveal fresh_chunk) next_fp in
       (SMA.major_alloc_spec_with_fuel er'.major_out er'.fp_out (U64.v requested_wz) 1).major_alloc_out));
  assert (pure (let er' = SMA.expand_major_heap (Ghost.reveal mh) (Ghost.reveal fresh_chunk) next_fp in
                let r = SMA.major_alloc_spec_with_fuel er'.major_out er'.fp_out
                  (U64.v requested_wz) 1 in
                next_fp == r.major_fp_out /\
                fp_out == r.major_obj_out));
  let out_fp : U64.t = next_fp;
  let out_obj : U64.t = fp_out;
  (out_fp, out_obj)
}

fn allocate_fresh_expanded_split (heap: MajorHeap.major_heap_t)
                                 (base: hp_addr) (fp_out: obj_addr)
                                 (fresh_wz requested_wz: wosize)
                                 (rem_hd rem_obj: hp_addr)
                                 (next_fp: U64.t)
                                 (#mh: Ghost.erased MH.major_heap)
                                 (#fresh_chunk: Ghost.erased
                                   (c:MH.heap_chunk{c.base == base /\
                                                    fp_out == SMA.fresh_chunk_object c /\
                                                    fresh_wz == SMA.fresh_chunk_wosize_u64 c}))
  requires MajorHeap.is_indexed_major_heap heap
            (SMA.expand_major_heap
              (Ghost.reveal mh) (Ghost.reveal fresh_chunk) next_fp).major_out **
           pure (U64.v base >= U64.v zero_addr /\
                 U64.v requested_wz > 0 /\
                 SMA.fresh_chunk_wosize (Ghost.reveal fresh_chunk) -
                   U64.v requested_wz >= 2 /\
                 U64.v rem_hd == U64.v base + (1 + U64.v requested_wz) * 8 /\
                 U64.v rem_obj == U64.v rem_hd + U64.v mword)
  returns res: (U64.t & U64.t)
  ensures MajorHeap.is_indexed_major_heap heap
            (let er =
              SMA.expand_major_heap
                (Ghost.reveal mh) (Ghost.reveal fresh_chunk) next_fp in
             (SMA.major_alloc_spec_with_fuel
               er.major_out er.fp_out (U64.v requested_wz) 1).major_alloc_out) **
          pure (fst res == rem_obj /\
                snd res == fp_out)
{
  let er = Ghost.hide (SMA.expand_major_heap (Ghost.reveal mh) (Ghost.reveal fresh_chunk) next_fp);
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (SMA.expand_major_heap (Ghost.reveal mh) (Ghost.reveal fresh_chunk) next_fp).major_out)
  as
    (MajorHeap.is_indexed_major_heap heap (Ghost.reveal er).major_out);
  let init = Ghost.hide (SMA.init_fresh_chunk (Ghost.reveal fresh_chunk) next_fp).chunk_out;

  let alloc_hdr = makeHeader requested_wz white 0UL;
  assert (pure (SA.white_bits == 0UL));
  assert (pure (pack_color white == 0UL));
  assert (pure (U64.uint_to_t (U64.v requested_wz) == requested_wz));
  assert (pure (alloc_hdr ==
                SA.make_header (U64.uint_to_t (U64.v requested_wz))
                  SA.white_bits 0UL));

  let leftover = U64.sub fresh_wz requested_wz;
  let rem_wz_u = U64.sub leftover 1UL;
  assert (pure (U64.v fresh_wz == SMA.fresh_chunk_wosize (Ghost.reveal fresh_chunk)));
  assert (pure (U64.v leftover ==
                SMA.fresh_chunk_wosize (Ghost.reveal fresh_chunk) - U64.v requested_wz));
  assert (pure (U64.v rem_wz_u ==
                SMA.fresh_chunk_wosize (Ghost.reveal fresh_chunk) - U64.v requested_wz - 1));
  assert (pure (U64.v rem_wz_u < pow2 54));
  let rem_hdr = makeHeader rem_wz_u blue 0UL;
  assert (pure (SA.blue_bits == 2UL));
  assert (pure (pack_color blue == 2UL));
  assert (pure (U64.uint_to_t (U64.v rem_wz_u) == rem_wz_u));
  assert (pure (rem_hdr ==
                SA.make_header
                  (U64.uint_to_t
                    (SMA.fresh_chunk_wosize (Ghost.reveal fresh_chunk) -
                     U64.v requested_wz - 1))
                  SA.blue_bits 0UL));

  let c1 = Ghost.hide (MH.write_word_in_chunk (Ghost.reveal init) base alloc_hdr);
  let c2 = Ghost.hide (MH.write_word_in_chunk (Ghost.reveal c1) rem_hd rem_hdr);
  let c3 = Ghost.hide (MH.write_word_in_chunk (Ghost.reveal c2) rem_obj next_fp);

  SMA.major_alloc_after_expand_split
    (Ghost.reveal mh) (Ghost.reveal fresh_chunk) next_fp (U64.v requested_wz) 0
    rem_hd rem_obj;
  SMA.fresh_chunk_split_remainder_fits
    (Ghost.reveal fresh_chunk) next_fp (U64.v requested_wz) rem_hd rem_obj;

  assert (pure ((Ghost.reveal er).fp_out == fp_out));
  assert (pure (Seq.length (Ghost.reveal er).major_out > 0));
  assert (pure (Seq.index (Ghost.reveal er).major_out 0 == Ghost.reveal init));
  assert (pure (MH.word_in_chunk (Ghost.reveal init) base));
  assert (pure (MH.lookup_chunk_index (Ghost.reveal er).major_out base == Some 0));
  MajorHeap.write_word_in_indexed_major_at_lookup_index heap base alloc_hdr 0
    #(Ghost.hide (Ghost.reveal er).major_out);

  assert (pure (Seq.upd (Ghost.reveal er).major_out 0
                  (MH.write_word_in_chunk (Seq.index (Ghost.reveal er).major_out 0) base alloc_hdr) ==
                Seq.upd (Ghost.reveal er).major_out 0 (Ghost.reveal c1)));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal er).major_out 0
        (MH.write_word_in_chunk (Seq.index (Ghost.reveal er).major_out 0) base alloc_hdr)))
  as
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal er).major_out 0 (Ghost.reveal c1)));

  let mh1 = Ghost.hide (Seq.upd (Ghost.reveal er).major_out 0 (Ghost.reveal c1));
  assert (pure (Ghost.reveal mh1 == Seq.upd (Ghost.reveal er).major_out 0 (Ghost.reveal c1)));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal er).major_out 0 (Ghost.reveal c1)))
  as
    (MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh1));
  assert (pure (Seq.length (Ghost.reveal mh1) == Seq.length (Ghost.reveal er).major_out));
  assert (pure (0 < Seq.length (Ghost.reveal mh1)));
  assert (pure (Seq.index (Ghost.reveal mh1) 0 == Ghost.reveal c1));
  assert (pure (MH.word_in_chunk (Ghost.reveal c1) rem_hd));
  assert (pure (MH.word_in_chunk (Seq.index (Ghost.reveal mh1) 0) rem_hd));
  assert (pure (MH.lookup_chunk_index (Ghost.reveal mh1) rem_hd == Some 0));
  MajorHeap.write_word_in_indexed_major_at_lookup_index heap rem_hd rem_hdr 0
    #(Ghost.hide (Ghost.reveal mh1));

  assert (pure (Seq.index (Ghost.reveal mh1) 0 == Ghost.reveal c1));
  assert (pure (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh1) 0) rem_hd rem_hdr ==
                Ghost.reveal c2));
  SMA.seq_upd_overwrite_head (Ghost.reveal er).major_out (Ghost.reveal c1) (Ghost.reveal c2);
  assert (pure (Seq.upd (Ghost.reveal mh1) 0 (Ghost.reveal c2) ==
                Seq.upd (Ghost.reveal er).major_out 0 (Ghost.reveal c2)));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh1) 0
        (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh1) 0) rem_hd rem_hdr)))
  as
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal er).major_out 0 (Ghost.reveal c2)));

  let mh2 = Ghost.hide (Seq.upd (Ghost.reveal er).major_out 0 (Ghost.reveal c2));
  assert (pure (Ghost.reveal mh2 == Seq.upd (Ghost.reveal er).major_out 0 (Ghost.reveal c2)));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal er).major_out 0 (Ghost.reveal c2)))
  as
    (MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh2));
  assert (pure (Seq.length (Ghost.reveal mh2) == Seq.length (Ghost.reveal er).major_out));
  assert (pure (0 < Seq.length (Ghost.reveal mh2)));
  assert (pure (Seq.index (Ghost.reveal mh2) 0 == Ghost.reveal c2));
  assert (pure (MH.word_in_chunk (Ghost.reveal c2) rem_obj));
  assert (pure (MH.word_in_chunk (Seq.index (Ghost.reveal mh2) 0) rem_obj));
  assert (pure (MH.lookup_chunk_index (Ghost.reveal mh2) rem_obj == Some 0));
  MajorHeap.write_word_in_indexed_major_at_lookup_index heap rem_obj next_fp 0
    #(Ghost.hide (Ghost.reveal mh2));

  assert (pure (Seq.index (Ghost.reveal mh2) 0 == Ghost.reveal c2));
  assert (pure (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh2) 0) rem_obj next_fp ==
                Ghost.reveal c3));
  SMA.seq_upd_overwrite_head (Ghost.reveal er).major_out (Ghost.reveal c2) (Ghost.reveal c3);
  assert (pure (Seq.upd (Ghost.reveal mh2) 0 (Ghost.reveal c3) ==
                Seq.upd (Ghost.reveal er).major_out 0 (Ghost.reveal c3)));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh2) 0
        (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh2) 0) rem_obj next_fp)))
  as
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal er).major_out 0 (Ghost.reveal c3)));

  assert (pure (let r = SMA.major_alloc_spec_with_fuel
                           (Ghost.reveal er).major_out (Ghost.reveal er).fp_out
                           (U64.v requested_wz) 1 in
                Seq.upd (Ghost.reveal er).major_out 0 (Ghost.reveal c3) ==
                  r.major_alloc_out /\
                rem_obj == r.major_fp_out /\
                fp_out == r.major_obj_out));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal er).major_out 0 (Ghost.reveal c3)))
  as
    (MajorHeap.is_indexed_major_heap heap
      (SMA.major_alloc_spec_with_fuel
        (Ghost.reveal er).major_out (Ghost.reveal er).fp_out (U64.v requested_wz) 1).major_alloc_out);
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (SMA.major_alloc_spec_with_fuel
        (Ghost.reveal er).major_out (Ghost.reveal er).fp_out (U64.v requested_wz) 1).major_alloc_out)
  as
    (MajorHeap.is_indexed_major_heap heap
      (let er' = SMA.expand_major_heap (Ghost.reveal mh) (Ghost.reveal fresh_chunk) next_fp in
       (SMA.major_alloc_spec_with_fuel er'.major_out er'.fp_out (U64.v requested_wz) 1).major_alloc_out));
  assert (pure (let er' = SMA.expand_major_heap (Ghost.reveal mh) (Ghost.reveal fresh_chunk) next_fp in
                let r = SMA.major_alloc_spec_with_fuel er'.major_out er'.fp_out
                  (U64.v requested_wz) 1 in
                rem_obj == r.major_fp_out /\
                fp_out == r.major_obj_out));
  let out_fp : U64.t = rem_obj;
  let out_obj : U64.t = fp_out;
  (out_fp, out_obj)
}

fn expand_and_allocate_fresh_no_split (heap: MajorHeap.major_heap_t)
                                      (base: hp_addr) (fp_out: obj_addr)
                                      (fresh_wz requested_wz: wosize)
                                      (next_fp: U64.t)
                                      (#mh: Ghost.erased MH.major_heap)
                                      (#fresh_chunk: Ghost.erased
                                        (c:MH.heap_chunk{c.base == base /\
                                                         fp_out == SMA.fresh_chunk_object c /\
                                                         fresh_wz == SMA.fresh_chunk_wosize_u64 c}))
  requires MajorHeap.chunk_range heap (Ghost.reveal fresh_chunk) **
           MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (MH.chunk_disjoint_from_all (Ghost.reveal fresh_chunk) (Ghost.reveal mh) /\
                 U64.v base >= U64.v zero_addr /\
                 U64.v requested_wz > 0 /\
                 SMA.fresh_chunk_wosize (Ghost.reveal fresh_chunk) >=
                   U64.v requested_wz /\
                 SMA.fresh_chunk_wosize (Ghost.reveal fresh_chunk) -
                   U64.v requested_wz < 2)
  returns res: (U64.t & U64.t)
  ensures MajorHeap.is_indexed_major_heap heap
            (let er =
              SMA.expand_major_heap
                (Ghost.reveal mh) (Ghost.reveal fresh_chunk) next_fp in
             (SMA.major_alloc_spec_with_fuel
               er.major_out er.fp_out (U64.v requested_wz) 1).major_alloc_out) **
          pure (fst res == next_fp /\
                snd res == fp_out)
{
  let new_fp =
    expand_major_heap_owned heap base fp_out fresh_wz next_fp #mh #fresh_chunk;
  assert (pure (new_fp == fp_out));
  let res =
    allocate_fresh_expanded_no_split
      heap base fp_out fresh_wz requested_wz next_fp #mh #fresh_chunk;
  res
}

fn expand_and_allocate_fresh_split (heap: MajorHeap.major_heap_t)
                                  (base: hp_addr) (fp_out: obj_addr)
                                  (fresh_wz requested_wz: wosize)
                                  (rem_hd rem_obj: hp_addr)
                                  (next_fp: U64.t)
                                  (#mh: Ghost.erased MH.major_heap)
                                  (#fresh_chunk: Ghost.erased
                                    (c:MH.heap_chunk{c.base == base /\
                                                     fp_out == SMA.fresh_chunk_object c /\
                                                     fresh_wz == SMA.fresh_chunk_wosize_u64 c}))
  requires MajorHeap.chunk_range heap (Ghost.reveal fresh_chunk) **
           MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (MH.chunk_disjoint_from_all (Ghost.reveal fresh_chunk) (Ghost.reveal mh) /\
                 U64.v base >= U64.v zero_addr /\
                 U64.v requested_wz > 0 /\
                 SMA.fresh_chunk_wosize (Ghost.reveal fresh_chunk) -
                   U64.v requested_wz >= 2 /\
                 U64.v rem_hd == U64.v base + (1 + U64.v requested_wz) * 8 /\
                 U64.v rem_obj == U64.v rem_hd + U64.v mword)
  returns res: (U64.t & U64.t)
  ensures MajorHeap.is_indexed_major_heap heap
            (let er =
              SMA.expand_major_heap
                (Ghost.reveal mh) (Ghost.reveal fresh_chunk) next_fp in
             (SMA.major_alloc_spec_with_fuel
               er.major_out er.fp_out (U64.v requested_wz) 1).major_alloc_out) **
          pure (fst res == rem_obj /\
                snd res == fp_out)
{
  let new_fp =
    expand_major_heap_owned heap base fp_out fresh_wz next_fp #mh #fresh_chunk;
  assert (pure (new_fp == fp_out));
  let res =
    allocate_fresh_expanded_split
      heap base fp_out fresh_wz requested_wz rem_hd rem_obj next_fp #mh #fresh_chunk;
  res
}

fn expand_and_allocate_fresh (heap: MajorHeap.major_heap_t)
                             (base: hp_addr) (fp_out: obj_addr)
                             (fresh_wz requested_wz: wosize)
                             (next_fp: U64.t)
                             (#mh: Ghost.erased MH.major_heap)
                             (#fresh_chunk: Ghost.erased
                               (c:MH.heap_chunk{c.base == base /\
                                                fp_out == SMA.fresh_chunk_object c /\
                                                fresh_wz == SMA.fresh_chunk_wosize_u64 c}))
  requires MajorHeap.chunk_range heap (Ghost.reveal fresh_chunk) **
           MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
           pure (MH.chunk_disjoint_from_all (Ghost.reveal fresh_chunk) (Ghost.reveal mh) /\
                 U64.v base >= U64.v zero_addr /\
                 U64.v requested_wz > 0 /\
                 SMA.fresh_chunk_wosize (Ghost.reveal fresh_chunk) >=
                   U64.v requested_wz)
  returns res: (U64.t & U64.t)
  ensures MajorHeap.is_indexed_major_heap heap
            (let fresh_c : MH.heap_chunk = Ghost.reveal fresh_chunk in
             let er =
              SMA.expand_major_heap
                (Ghost.reveal mh) fresh_c next_fp in
             (SMA.major_alloc_spec_with_fuel
               er.major_out er.fp_out (U64.v requested_wz) 1).major_alloc_out) **
          pure (let fresh_c : MH.heap_chunk = Ghost.reveal fresh_chunk in
                let er =
                  SMA.expand_major_heap
                    (Ghost.reveal mh) fresh_c next_fp in
                let r =
                  SMA.major_alloc_spec_with_fuel
                    er.major_out er.fp_out (U64.v requested_wz) 1 in
                fst res == r.major_fp_out /\
                snd res == r.major_obj_out)
{
  let leftover = U64.sub fresh_wz requested_wz;
  assert (pure (U64.v fresh_wz == SMA.fresh_chunk_wosize (Ghost.reveal fresh_chunk)));
  assert (pure (U64.v leftover ==
                SMA.fresh_chunk_wosize (Ghost.reveal fresh_chunk) - U64.v requested_wz));
  if U64.gte leftover 2UL {
    assert (pure (SMA.fresh_chunk_wosize (Ghost.reveal fresh_chunk) -
                  U64.v requested_wz >= 2));
    wosize_bound_lemma requested_wz fresh_wz;
    split_offset_fits requested_wz;
    split_no_overflow base requested_wz;
    SMA.fresh_chunk_split_remainder_addr_bounds
      (Ghost.reveal fresh_chunk) (U64.v requested_wz);

    let wz_plus_1 = U64.add requested_wz 1UL;
    assert (pure (U64.v wz_plus_1 == U64.v requested_wz + 1));
    let offset = U64.mul wz_plus_1 mword;
    assert (pure (U64.v offset == (1 + U64.v requested_wz) * U64.v mword));
    assert (pure (U64.v offset == (1 + U64.v requested_wz) * 8));
    let rem_hd = U64.add base offset;
    assert (pure (U64.v rem_hd == U64.v base + (1 + U64.v requested_wz) * 8));
    assert (pure (U64.v rem_hd < heap_size));
    assert (pure (U64.v rem_hd % U64.v mword == 0));
    let rem_obj = U64.add rem_hd mword;
    assert (pure (U64.v rem_obj == U64.v rem_hd + U64.v mword));
    assert (pure (U64.v rem_obj < heap_size));
    assert (pure (U64.v rem_obj % U64.v mword == 0));

    let res =
      expand_and_allocate_fresh_split
        heap base fp_out fresh_wz requested_wz rem_hd rem_obj next_fp
        #mh #fresh_chunk;
    SMA.major_alloc_after_expand_split
      (Ghost.reveal mh) (Ghost.reveal fresh_chunk) next_fp (U64.v requested_wz) 0
      rem_hd rem_obj;
    assert (pure (let fresh_c : MH.heap_chunk = Ghost.reveal fresh_chunk in
                  let er = SMA.expand_major_heap (Ghost.reveal mh) fresh_c next_fp in
                  let r = SMA.major_alloc_spec_with_fuel
                    er.major_out er.fp_out (U64.v requested_wz) 1 in
                  rem_obj == r.major_fp_out /\
                  fp_out == r.major_obj_out));
    assert (pure (let fresh_c : MH.heap_chunk = Ghost.reveal fresh_chunk in
                  let er = SMA.expand_major_heap (Ghost.reveal mh) fresh_c next_fp in
                  let r = SMA.major_alloc_spec_with_fuel
                    er.major_out er.fp_out (U64.v requested_wz) 1 in
                  fst res == r.major_fp_out /\
                  snd res == r.major_obj_out));
    res
  } else {
    assert (pure (SMA.fresh_chunk_wosize (Ghost.reveal fresh_chunk) -
                  U64.v requested_wz < 2));
    let res =
      expand_and_allocate_fresh_no_split
        heap base fp_out fresh_wz requested_wz next_fp #mh #fresh_chunk;
    SMA.major_alloc_after_expand_no_split
      (Ghost.reveal mh) (Ghost.reveal fresh_chunk) next_fp (U64.v requested_wz) 0;
    assert (pure (let fresh_c : MH.heap_chunk = Ghost.reveal fresh_chunk in
                  let er = SMA.expand_major_heap (Ghost.reveal mh) fresh_c next_fp in
                  let r = SMA.major_alloc_spec_with_fuel
                    er.major_out er.fp_out (U64.v requested_wz) 1 in
                  next_fp == r.major_fp_out /\
                  fp_out == r.major_obj_out));
    assert (pure (let fresh_c : MH.heap_chunk = Ghost.reveal fresh_chunk in
                  let er = SMA.expand_major_heap (Ghost.reveal mh) fresh_c next_fp in
                  let r = SMA.major_alloc_spec_with_fuel
                    er.major_out er.fp_out (U64.v requested_wz) 1 in
                  fst res == r.major_fp_out /\
                  snd res == r.major_obj_out));
    res
  }
}

fn expand_and_allocate_fresh_with_fuel (heap: MajorHeap.major_heap_t)
                                       (base: hp_addr) (fp_out: obj_addr)
                                       (fresh_wz requested_wz: wosize)
                                       (next_fp: U64.t)
                                       (#fuel: nat)
                                       (#mh: Ghost.erased MH.major_heap)
                                       (#fresh_chunk: Ghost.erased
                                         (c:MH.heap_chunk{c.base == base /\
                                                          fp_out == SMA.fresh_chunk_object c /\
                                                          fresh_wz == SMA.fresh_chunk_wosize_u64 c}))
   requires MajorHeap.chunk_range heap (Ghost.reveal fresh_chunk) **
            MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (MH.chunk_disjoint_from_all (Ghost.reveal fresh_chunk) (Ghost.reveal mh) /\
                  U64.v base >= U64.v zero_addr /\
                  U64.v requested_wz > 0 /\
                  SMA.fresh_chunk_wosize (Ghost.reveal fresh_chunk) >=
                    U64.v requested_wz)
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap
             (let fresh_c : MH.heap_chunk = Ghost.reveal fresh_chunk in
              let old_mh : MH.major_heap = Ghost.reveal mh in
              let retry_fuel : nat = fuel + 1 in
              let er =
               SMA.expand_major_heap
                 old_mh fresh_c next_fp in
              (SMA.major_alloc_spec_with_fuel
                er.major_out er.fp_out (U64.v requested_wz)
                retry_fuel).major_alloc_out)
{
  let res =
    expand_and_allocate_fresh
      heap base fp_out fresh_wz requested_wz next_fp #mh #fresh_chunk;
  SMA.major_alloc_after_expand_fuel_irrelevant
    (Ghost.reveal mh) (Ghost.reveal fresh_chunk) next_fp
    (U64.v requested_wz) fuel;
  assert (pure (let fresh_c : MH.heap_chunk = Ghost.reveal fresh_chunk in
                let old_mh : MH.major_heap = Ghost.reveal mh in
                let retry_fuel : nat = fuel + 1 in
                let er = SMA.expand_major_heap old_mh fresh_c next_fp in
                SMA.major_alloc_spec_with_fuel
                  er.major_out er.fp_out (U64.v requested_wz) 1 ==
                SMA.major_alloc_spec_with_fuel
                  er.major_out er.fp_out (U64.v requested_wz)
                  retry_fuel));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (let fresh_c : MH.heap_chunk = Ghost.reveal fresh_chunk in
       let old_mh : MH.major_heap = Ghost.reveal mh in
       let er = SMA.expand_major_heap old_mh fresh_c next_fp in
       (SMA.major_alloc_spec_with_fuel
         er.major_out er.fp_out (U64.v requested_wz) 1).major_alloc_out))
  as
    (MajorHeap.is_indexed_major_heap heap
      (let fresh_c : MH.heap_chunk = Ghost.reveal fresh_chunk in
       let old_mh : MH.major_heap = Ghost.reveal mh in
       let retry_fuel : nat = fuel + 1 in
       let er = SMA.expand_major_heap old_mh fresh_c next_fp in
       (SMA.major_alloc_spec_with_fuel
         er.major_out er.fp_out (U64.v requested_wz) retry_fuel).major_alloc_out));
  res
}

fn expand_on_oom_with_fresh (heap: MajorHeap.major_heap_t)
                            (base: hp_addr) (fp_out: obj_addr)
                            (fresh_wz requested_wz: wosize)
                            (fp: U64.t)
                            (#fuel: nat)
                            (#mh: Ghost.erased MH.major_heap)
                            (#fresh_chunk: Ghost.erased
                              (c:MH.heap_chunk{c.base == base /\
                                               fp_out == SMA.fresh_chunk_object c /\
                                               fresh_wz == SMA.fresh_chunk_wosize_u64 c}))
   requires MajorHeap.chunk_range heap (Ghost.reveal fresh_chunk) **
            MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (MH.chunk_disjoint_from_all (Ghost.reveal fresh_chunk) (Ghost.reveal mh) /\
                  U64.v base >= U64.v zero_addr /\
                  U64.v requested_wz > 0 /\
                  SMA.fresh_chunk_wosize (Ghost.reveal fresh_chunk) >=
                    U64.v requested_wz /\
                  (SMA.major_alloc_spec_with_fuel
                    (Ghost.reveal mh) fp (U64.v requested_wz)
                    fuel).major_obj_out == 0UL)
   returns res: (U64.t & U64.t)
   ensures MajorHeap.is_indexed_major_heap heap
             (let old_mh : MH.major_heap = Ghost.reveal mh in
              let fresh_c : MH.heap_chunk = Ghost.reveal fresh_chunk in
              SMA.major_alloc_spec_expand_on_oom
                old_mh fp (U64.v requested_wz)
                fuel fresh_c).major_alloc_out **
           pure (let old_mh : MH.major_heap = Ghost.reveal mh in
                 let fresh_c : MH.heap_chunk = Ghost.reveal fresh_chunk in
                 let r =
                   SMA.major_alloc_spec_expand_on_oom
                     old_mh fp (U64.v requested_wz)
                     fuel fresh_c in
                 fst res == r.major_fp_out /\
                 snd res == r.major_obj_out)
{
  let res =
    expand_and_allocate_fresh
      heap base fp_out fresh_wz requested_wz fp #mh #fresh_chunk;
  SMA.major_alloc_after_expand_fuel_irrelevant
    (Ghost.reveal mh) (Ghost.reveal fresh_chunk) fp
    (U64.v requested_wz) fuel;
  assert (pure ((SMA.major_alloc_spec_with_fuel
                  (Ghost.reveal mh) fp (U64.v requested_wz)
                  fuel).major_obj_out == 0UL));
  assert (pure (SMA.major_alloc_spec_expand_on_oom
                  (Ghost.reveal mh) fp (U64.v requested_wz)
                  fuel (Ghost.reveal fresh_chunk) ==
                (let fresh_c : MH.heap_chunk = Ghost.reveal fresh_chunk in
                 let er = SMA.expand_major_heap (Ghost.reveal mh) fresh_c fp in
                 SMA.major_alloc_spec_with_fuel
                   er.major_out er.fp_out (U64.v requested_wz)
                   (fuel + 1))));
  assert (pure (let fresh_c : MH.heap_chunk = Ghost.reveal fresh_chunk in
                let er = SMA.expand_major_heap (Ghost.reveal mh) fresh_c fp in
                SMA.major_alloc_spec_with_fuel
                  er.major_out er.fp_out (U64.v requested_wz) 1 ==
                SMA.major_alloc_spec_with_fuel
                  er.major_out er.fp_out (U64.v requested_wz)
                  (fuel + 1)));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (let fresh_c : MH.heap_chunk = Ghost.reveal fresh_chunk in
       let er = SMA.expand_major_heap (Ghost.reveal mh) fresh_c fp in
       (SMA.major_alloc_spec_with_fuel
         er.major_out er.fp_out (U64.v requested_wz) 1).major_alloc_out))
  as
    (MajorHeap.is_indexed_major_heap heap
      (SMA.major_alloc_spec_expand_on_oom
        (Ghost.reveal mh) fp (U64.v requested_wz)
        fuel (Ghost.reveal fresh_chunk)).major_alloc_out);
  SMA.major_alloc_after_expand_returns_fresh
    (Ghost.reveal mh) (Ghost.reveal fresh_chunk) fp
    (U64.v requested_wz) 0;
  assert (pure (let old_mh : MH.major_heap = Ghost.reveal mh in
                let fresh_c : MH.heap_chunk = Ghost.reveal fresh_chunk in
                let r =
                  SMA.major_alloc_spec_expand_on_oom
                    old_mh fp (U64.v requested_wz)
                    fuel fresh_c in
                fst res == r.major_fp_out /\
                snd res == r.major_obj_out));
  assert (pure (snd res == fp_out));
  res
}

fn allocate_major_expand_on_oom_with_fresh (heap: MajorHeap.major_heap_t)
                                           (base: hp_addr) (fp_out: obj_addr)
                                           (fresh_wz requested_wz: wosize)
                                           (fp: U64.t) (fuel: U64.t)
                                           (#mh: Ghost.erased MH.major_heap)
                                           (#fresh_chunk: Ghost.erased
                                             (c:MH.heap_chunk{c.base == base /\
                                                              fp_out == SMA.fresh_chunk_object c /\
                                                              fresh_wz == SMA.fresh_chunk_wosize_u64 c}))
    requires MajorHeap.chunk_range heap (Ghost.reveal fresh_chunk) **
             MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
             pure (MH.chunk_disjoint_from_all (Ghost.reveal fresh_chunk) (Ghost.reveal mh) /\
                   U64.v base >= U64.v zero_addr /\
                   U64.v requested_wz > 0 /\
                   SMA.fresh_chunk_wosize (Ghost.reveal fresh_chunk) >=
                     U64.v requested_wz /\
                   SMA.major_fl_valid (Ghost.reveal mh) fp (U64.v fuel) /\
                   SMA.major_fl_above_zero (Ghost.reveal mh) fp (U64.v fuel) /\
                   SMA.major_fl_blocks_fit (Ghost.reveal mh) fp (U64.v fuel))
    returns res: (U64.t & U64.t)
    ensures (let old_r =
               SMA.major_alloc_spec_with_fuel
                 (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel) in
             let final_r =
               SMA.major_alloc_spec_expand_on_oom
                 (Ghost.reveal mh) fp (U64.v requested_wz)
                 (U64.v fuel) (Ghost.reveal fresh_chunk) in
             if U64.eq old_r.major_obj_out 0UL then
               MajorHeap.is_indexed_major_heap heap final_r.major_alloc_out
             else
               (MajorHeap.chunk_range heap (Ghost.reveal fresh_chunk) **
                MajorHeap.is_indexed_major_heap heap final_r.major_alloc_out)) **
            pure (let old_r =
                    SMA.major_alloc_spec_with_fuel
                      (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel) in
                  let final_r =
                    SMA.major_alloc_spec_expand_on_oom
                      (Ghost.reveal mh) fp (U64.v requested_wz)
                      (U64.v fuel) (Ghost.reveal fresh_chunk) in
                  fst res == final_r.major_fp_out /\
                  snd res == final_r.major_obj_out /\
                  MH.chunk_disjoint_from_all
                    (Ghost.reveal fresh_chunk) old_r.major_alloc_out)
{
  let old_res =
    allocate_major_with_fuel_preserve_oom
      heap fp requested_wz fuel #mh;
  SMA.major_alloc_spec_with_fuel_preserves_chunk_disjoint
    (Ghost.reveal fresh_chunk) (Ghost.reveal mh) fp
    (U64.v requested_wz) (U64.v fuel);
  if U64.eq (snd old_res) 0UL {
    assert (pure (snd old_res == 0UL));
    assert (pure ((SMA.major_alloc_spec_with_fuel
                    (Ghost.reveal mh) fp (U64.v requested_wz)
                    (U64.v fuel)).major_obj_out == 0UL));
    assert (pure (U64.eq
                    ((SMA.major_alloc_spec_with_fuel
                       (Ghost.reveal mh) fp (U64.v requested_wz)
                       (U64.v fuel)).major_obj_out)
                    0UL == true));
    let res =
      expand_on_oom_with_fresh
        heap base fp_out fresh_wz requested_wz fp #(U64.v fuel)
        #mh #fresh_chunk;
    assert (pure (let old_r =
                    SMA.major_alloc_spec_with_fuel
                      (Ghost.reveal mh) fp (U64.v requested_wz)
                      (U64.v fuel) in
                  U64.eq old_r.major_obj_out 0UL == true));
    rewrite
      (MajorHeap.is_indexed_major_heap heap
        (let old_mh : MH.major_heap = Ghost.reveal mh in
         let fresh_c : MH.heap_chunk = Ghost.reveal fresh_chunk in
         SMA.major_alloc_spec_expand_on_oom
           old_mh fp (U64.v requested_wz)
           (U64.v fuel) fresh_c).major_alloc_out)
    as
      (let old_r =
         SMA.major_alloc_spec_with_fuel
           (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel) in
       let final_r =
         SMA.major_alloc_spec_expand_on_oom
           (Ghost.reveal mh) fp (U64.v requested_wz)
           (U64.v fuel) (Ghost.reveal fresh_chunk) in
       if U64.eq old_r.major_obj_out 0UL then
         MajorHeap.is_indexed_major_heap heap final_r.major_alloc_out
       else
         (MajorHeap.chunk_range heap (Ghost.reveal fresh_chunk) **
          MajorHeap.is_indexed_major_heap heap final_r.major_alloc_out));
    assert (pure (let old_r =
                    SMA.major_alloc_spec_with_fuel
                      (Ghost.reveal mh) fp (U64.v requested_wz)
                      (U64.v fuel) in
                  let final_r =
                    SMA.major_alloc_spec_expand_on_oom
                      (Ghost.reveal mh) fp (U64.v requested_wz)
                      (U64.v fuel) (Ghost.reveal fresh_chunk) in
                  fst res == final_r.major_fp_out /\
                  snd res == final_r.major_obj_out /\
                  MH.chunk_disjoint_from_all
                    (Ghost.reveal fresh_chunk) old_r.major_alloc_out));
    res
  } else {
    assert (pure (snd old_res <> 0UL));
    assert (pure (U64.eq (snd old_res) 0UL == false));
    assert (pure ((SMA.major_alloc_spec_with_fuel
                    (Ghost.reveal mh) fp (U64.v requested_wz)
                    (U64.v fuel)).major_obj_out <> 0UL));
    assert (pure (U64.eq
                    ((SMA.major_alloc_spec_with_fuel
                       (Ghost.reveal mh) fp (U64.v requested_wz)
                       (U64.v fuel)).major_obj_out)
                    0UL == false));
    assert (pure (SMA.major_alloc_spec_expand_on_oom
                    (Ghost.reveal mh) fp (U64.v requested_wz)
                    (U64.v fuel) (Ghost.reveal fresh_chunk) ==
                  SMA.major_alloc_spec_with_fuel
                    (Ghost.reveal mh) fp (U64.v requested_wz)
                    (U64.v fuel)));
    rewrite
      (MajorHeap.is_indexed_major_heap heap
        (let r =
           SMA.major_alloc_spec_with_fuel
             (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel) in
         r.major_alloc_out))
    as
      (MajorHeap.is_indexed_major_heap heap
        (let final_r =
           SMA.major_alloc_spec_expand_on_oom
             (Ghost.reveal mh) fp (U64.v requested_wz)
             (U64.v fuel) (Ghost.reveal fresh_chunk) in
         final_r.major_alloc_out));
    rewrite
      (MajorHeap.chunk_range heap (Ghost.reveal fresh_chunk) **
       MajorHeap.is_indexed_major_heap heap
        (let final_r =
           SMA.major_alloc_spec_expand_on_oom
             (Ghost.reveal mh) fp (U64.v requested_wz)
             (U64.v fuel) (Ghost.reveal fresh_chunk) in
         final_r.major_alloc_out))
    as
      (let old_r =
         SMA.major_alloc_spec_with_fuel
           (Ghost.reveal mh) fp (U64.v requested_wz) (U64.v fuel) in
       let final_r =
         SMA.major_alloc_spec_expand_on_oom
           (Ghost.reveal mh) fp (U64.v requested_wz)
           (U64.v fuel) (Ghost.reveal fresh_chunk) in
       if U64.eq old_r.major_obj_out 0UL then
         MajorHeap.is_indexed_major_heap heap final_r.major_alloc_out
       else
         (MajorHeap.chunk_range heap (Ghost.reveal fresh_chunk) **
          MajorHeap.is_indexed_major_heap heap final_r.major_alloc_out));
    assert (pure (let old_r =
                    SMA.major_alloc_spec_with_fuel
                      (Ghost.reveal mh) fp (U64.v requested_wz)
                      (U64.v fuel) in
                  let final_r =
                    SMA.major_alloc_spec_expand_on_oom
                      (Ghost.reveal mh) fp (U64.v requested_wz)
                      (U64.v fuel) (Ghost.reveal fresh_chunk) in
                  fst old_res == final_r.major_fp_out /\
                  snd old_res == final_r.major_obj_out /\
                  MH.chunk_disjoint_from_all
                    (Ghost.reveal fresh_chunk) old_r.major_alloc_out));
    old_res
  }
}
