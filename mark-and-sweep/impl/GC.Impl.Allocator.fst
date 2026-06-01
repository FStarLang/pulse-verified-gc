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

fn allocate_major_head_no_split (heap: MajorHeap.major_heap_t)
                                (base: hp_addr) (fp: obj_addr)
                                (block_wz requested_wz: wosize)
                                (next_fp: U64.t)
                                (#fuel: nat) (#idx: nat)
                                (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (fuel > 0 /\
                  idx < Seq.length (Ghost.reveal mh) /\
                  base == SH.hd_address fp /\
                  MH.lookup_chunk_index (Ghost.reveal mh) base == Some idx /\
                  MH.word_in_chunk (Seq.index (Ghost.reveal mh) idx) base /\
                  MH.read_word_in_major (Ghost.reveal mh) base ==
                    Some (SA.make_header block_wz SA.blue_bits 0UL) /\
                  MH.read_word_in_major (Ghost.reveal mh) fp == Some next_fp /\
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
  let block_hdr = SA.make_header block_wz SA.blue_bits 0UL;
  let alloc_hdr = makeHeader block_wz white 0UL;
  assert (pure (SA.white_bits == 0UL));
  assert (pure (pack_color white == 0UL));
  assert (pure (alloc_hdr == SA.make_header block_wz SA.white_bits 0UL));
  AllocLemmas.make_header_getWosize block_wz SA.blue_bits 0UL;
  assert (pure (SO.getWosize block_hdr == block_wz));
  assert (pure (base == SH.hd_address fp));
  SMA.major_alloc_head_no_split
    (Ghost.reveal mh) fp (U64.v requested_wz) fuel block_hdr next_fp;
  MajorHeap.write_word_in_indexed_major_at_lookup_index heap base alloc_hdr idx
    #(Ghost.hide (Ghost.reveal mh));
  assert (pure (MH.write_word_in_major (Ghost.reveal mh) base alloc_hdr ==
                Some (Seq.upd (Ghost.reveal mh) idx
                  (MH.write_word_in_chunk
                    (Seq.index (Ghost.reveal mh) idx) base alloc_hdr))));
  SMA.major_write_word_or_same_some
    (Ghost.reveal mh)
    (Seq.upd (Ghost.reveal mh) idx
      (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh) idx) base alloc_hdr))
    base alloc_hdr;
  assert (pure (SMA.major_write_word_or_same
                  (Ghost.reveal mh) (SH.hd_address fp) alloc_hdr ==
                Seq.upd (Ghost.reveal mh) idx
                  (MH.write_word_in_chunk
                    (Seq.index (Ghost.reveal mh) idx) base alloc_hdr)));
  assert (pure (let r =
                  SMA.major_alloc_spec_with_fuel
                    (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
                r.major_alloc_out ==
                  Seq.upd (Ghost.reveal mh) idx
                    (MH.write_word_in_chunk
                      (Seq.index (Ghost.reveal mh) idx) base alloc_hdr) /\
                r.major_fp_out == next_fp /\
                r.major_obj_out == fp));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) idx
        (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh) idx) base alloc_hdr)))
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
                             (block_wz requested_wz: wosize)
                             (rem_hd rem_obj: hp_addr)
                             (next_fp: U64.t)
                             (#fuel: nat) (#idx: nat)
                             (#mh: Ghost.erased MH.major_heap)
   requires MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh) **
            pure (fuel > 0 /\
                  idx < Seq.length (Ghost.reveal mh) /\
                  base == SH.hd_address fp /\
                  MH.lookup_chunk_index (Ghost.reveal mh) base == Some idx /\
                  MH.word_in_chunk (Seq.index (Ghost.reveal mh) idx) base /\
                  MH.word_in_chunk (Seq.index (Ghost.reveal mh) idx) rem_hd /\
                  MH.word_in_chunk (Seq.index (Ghost.reveal mh) idx) rem_obj /\
                  (forall (k:nat{k < idx /\ k < Seq.length (Ghost.reveal mh)}).
                    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh) k) rem_hd)) /\
                  (forall (k:nat{k < idx /\ k < Seq.length (Ghost.reveal mh)}).
                    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh) k) rem_obj)) /\
                  MH.read_word_in_major (Ghost.reveal mh) base ==
                    Some (SA.make_header block_wz SA.blue_bits 0UL) /\
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
                SMA.major_alloc_spec_with_fuel
                  (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
              r.major_alloc_out) **
           pure (let r =
                   SMA.major_alloc_spec_with_fuel
                     (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
                 fst res == r.major_fp_out /\
                 snd res == r.major_obj_out)
{
  let block_hdr = SA.make_header block_wz SA.blue_bits 0UL;
  let alloc_hdr = makeHeader requested_wz white 0UL;
  assert (pure (SA.white_bits == 0UL));
  assert (pure (pack_color white == 0UL));
  assert (pure (U64.uint_to_t (U64.v requested_wz) == requested_wz));
  assert (pure (alloc_hdr ==
                SA.make_header (U64.uint_to_t (U64.v requested_wz))
                  SA.white_bits 0UL));
  AllocLemmas.make_header_getWosize block_wz SA.blue_bits 0UL;
  assert (pure (SO.getWosize block_hdr == block_wz));

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
    (Ghost.reveal mh) fp (U64.v requested_wz) fuel block_hdr next_fp
    rem_hd rem_obj;

  let c0 = Ghost.hide (Seq.index (Ghost.reveal mh) idx);
  let c1 = Ghost.hide (MH.write_word_in_chunk (Ghost.reveal c0) base alloc_hdr);
  let c2 = Ghost.hide (MH.write_word_in_chunk (Ghost.reveal c1) rem_hd rem_hdr);
  let c3 = Ghost.hide (MH.write_word_in_chunk (Ghost.reveal c2) rem_obj next_fp);

  MajorHeap.write_word_in_indexed_major_at_lookup_index heap base alloc_hdr idx
    #(Ghost.hide (Ghost.reveal mh));
  assert (pure (Seq.index (Ghost.reveal mh) idx == Ghost.reveal c0));
  assert (pure (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh) idx) base alloc_hdr ==
                Ghost.reveal c1));
  assert (pure (MH.write_word_in_major (Ghost.reveal mh) base alloc_hdr ==
                Some (Seq.upd (Ghost.reveal mh) idx (Ghost.reveal c1))));
  SMA.major_write_word_or_same_some
    (Ghost.reveal mh) (Seq.upd (Ghost.reveal mh) idx (Ghost.reveal c1))
    base alloc_hdr;

  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) idx
        (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh) idx) base alloc_hdr)))
  as
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) idx (Ghost.reveal c1)));

  let mh1 = Ghost.hide (Seq.upd (Ghost.reveal mh) idx (Ghost.reveal c1));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) idx (Ghost.reveal c1)))
  as
    (MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh1));
  assert (pure (Seq.length (Ghost.reveal mh1) == Seq.length (Ghost.reveal mh)));
  assert (pure (idx < Seq.length (Ghost.reveal mh1)));
  assert (pure (Seq.index (Ghost.reveal mh1) idx == Ghost.reveal c1));
  MH.write_word_in_chunk_preserves_word (Ghost.reveal c0) base alloc_hdr rem_hd;
  assert (pure (MH.word_in_chunk (Ghost.reveal c1) rem_hd));
  assert (pure (MH.word_in_chunk (Seq.index (Ghost.reveal mh1) idx) rem_hd));
  assert (pure (forall (k:nat). k < idx ==>
    Seq.index (Ghost.reveal mh1) k == Seq.index (Ghost.reveal mh) k));
  assert (pure (forall (k:nat). k < idx ==>
    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh1) k) rem_hd)));
  MajorHeap.write_word_in_indexed_major_at_chunk_index heap rem_hd rem_hdr idx
    #(Ghost.hide (Ghost.reveal mh1));
  assert (pure (MH.write_word_in_major (Ghost.reveal mh1) rem_hd rem_hdr ==
                Some (Seq.upd (Ghost.reveal mh1) idx (Ghost.reveal c2))));
  SMA.major_write_word_or_same_some
    (Ghost.reveal mh1) (Seq.upd (Ghost.reveal mh1) idx (Ghost.reveal c2))
    rem_hd rem_hdr;
  SMA.seq_upd_overwrite_index (Ghost.reveal mh) idx (Ghost.reveal c1) (Ghost.reveal c2);
  assert (pure (Seq.upd (Ghost.reveal mh1) idx (Ghost.reveal c2) ==
                Seq.upd (Ghost.reveal mh) idx (Ghost.reveal c2)));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh1) idx
        (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh1) idx) rem_hd rem_hdr)))
  as
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) idx (Ghost.reveal c2)));

  let mh2 = Ghost.hide (Seq.upd (Ghost.reveal mh) idx (Ghost.reveal c2));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) idx (Ghost.reveal c2)))
  as
    (MajorHeap.is_indexed_major_heap heap (Ghost.reveal mh2));
  assert (pure (Seq.length (Ghost.reveal mh2) == Seq.length (Ghost.reveal mh)));
  assert (pure (idx < Seq.length (Ghost.reveal mh2)));
  assert (pure (Seq.index (Ghost.reveal mh2) idx == Ghost.reveal c2));
  MH.write_word_in_chunk_preserves_word (Ghost.reveal c1) rem_hd rem_hdr rem_obj;
  assert (pure (MH.word_in_chunk (Ghost.reveal c2) rem_obj));
  assert (pure (MH.word_in_chunk (Seq.index (Ghost.reveal mh2) idx) rem_obj));
  assert (pure (forall (k:nat). k < idx ==>
    Seq.index (Ghost.reveal mh2) k == Seq.index (Ghost.reveal mh) k));
  assert (pure (forall (k:nat). k < idx ==>
    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh2) k) rem_obj)));
  MajorHeap.write_word_in_indexed_major_at_chunk_index heap rem_obj next_fp idx
    #(Ghost.hide (Ghost.reveal mh2));
  assert (pure (MH.write_word_in_major (Ghost.reveal mh2) rem_obj next_fp ==
                Some (Seq.upd (Ghost.reveal mh2) idx (Ghost.reveal c3))));
  SMA.major_write_word_or_same_some
    (Ghost.reveal mh2) (Seq.upd (Ghost.reveal mh2) idx (Ghost.reveal c3))
    rem_obj next_fp;
  SMA.seq_upd_overwrite_index (Ghost.reveal mh) idx (Ghost.reveal c2) (Ghost.reveal c3);
  assert (pure (Seq.upd (Ghost.reveal mh2) idx (Ghost.reveal c3) ==
                Seq.upd (Ghost.reveal mh) idx (Ghost.reveal c3)));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh2) idx
        (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh2) idx) rem_obj next_fp)))
  as
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) idx (Ghost.reveal c3)));

  assert (pure (let r =
                  SMA.major_alloc_spec_with_fuel
                    (Ghost.reveal mh) fp (U64.v requested_wz) fuel in
                r.major_alloc_out == Seq.upd (Ghost.reveal mh) idx (Ghost.reveal c3) /\
                r.major_fp_out == rem_obj /\
                r.major_obj_out == fp));
  rewrite
    (MajorHeap.is_indexed_major_heap heap
      (Seq.upd (Ghost.reveal mh) idx (Ghost.reveal c3)))
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

fn init_fresh_chunk_owned (heap: MajorHeap.major_heap_t)
                          (base: hp_addr) (fp_out: obj_addr)
                          (wz: wosize) (next_fp: U64.t)
                          (#fresh: Ghost.erased
                            (c:MH.heap_chunk{c.base == base /\
                                             fp_out == SMA.fresh_chunk_object c /\
                                             U64.v wz == SMA.fresh_chunk_wosize c}))
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
                                              U64.v wz == SMA.fresh_chunk_wosize c}))
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

fn allocate_fresh_expanded_exact (heap: MajorHeap.major_heap_t)
                                 (base: hp_addr) (fp_out: obj_addr)
                                 (wz: wosize) (next_fp: U64.t)
                                 (#mh: Ghost.erased MH.major_heap)
                                 (#fresh: Ghost.erased
                                   (c:MH.heap_chunk{c.base == base /\
                                                    fp_out == SMA.fresh_chunk_object c /\
                                                    U64.v wz == SMA.fresh_chunk_wosize c}))
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
                                                       U64.v fresh_wz == SMA.fresh_chunk_wosize c}))
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
                                                    U64.v fresh_wz == SMA.fresh_chunk_wosize c}))
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
                                                         U64.v fresh_wz == SMA.fresh_chunk_wosize c}))
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
                                                     U64.v fresh_wz == SMA.fresh_chunk_wosize c}))
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
                                                U64.v fresh_wz == SMA.fresh_chunk_wosize c}))
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
                                                          U64.v fresh_wz == SMA.fresh_chunk_wosize c}))
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
                                               U64.v fresh_wz == SMA.fresh_chunk_wosize c}))
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
           pure (snd res == fp_out)
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
  assert (pure (snd res == fp_out));
  res
}
