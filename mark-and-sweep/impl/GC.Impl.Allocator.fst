(*
   Pulse GC - Allocator Implementation

   First-fit free-list allocator verified against GC.Spec.Allocator.
   Walks the free list, finds a block >= requested wosize,
   optionally splits, returns new fp. Fully proved — 0 admits.
*)

module GC.Impl.Allocator

#lang-pulse

#set-options "--fuel 1 --ifuel 0 --z3rlimit 12"

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
module R = Pulse.Lib.Reference
module SpecBase = GC.Spec.Base
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SA = GC.Spec.Allocator
module SF = GC.Spec.Fields
module SO = GC.Spec.Object
module SH = GC.Spec.Heap
module SI = GC.Spec.SweepInv
module AllocLemmas = GC.Spec.Allocator.Lemmas
module SpecAlloc = GC.Spec.Allocator
module SpecFields = GC.Spec.Fields
module SpecObject = GC.Spec.Object

/// ---------------------------------------------------------------------------
/// Pure helper lemmas (all proven — no admits)
/// ---------------------------------------------------------------------------

/// init_heap postcondition when heap is too small
let init_heap_small_lemma (s: heap_state)
  : Lemma (requires SpecBase.heap_words < 2)
          (ensures (s, 0UL) == SA.init_heap_spec s)
  = ()

/// init_heap postcondition for the normal case
let init_heap_normal_lemma (s: heap_state) (hdr: U64.t)
                           (wz: wosize{U64.v wz == SpecBase.heap_words - 1})
  : Lemma (requires SpecBase.heap_words >= 2 /\
                    hdr == makeHeader wz blue 0UL)
          (ensures ((SH.write_word (SH.write_word s zero_addr hdr)
                                          (mword <: hp_addr) 0UL, mword)
                    <: SpecBase.heap & U64.t)
                   == SA.init_heap_spec s)
  = ()

/// Fuel bound for search loop
let fuel_bound_lemma (fuel: U64.t)
  : Lemma (requires U64.v fuel > 0 /\ U64.v fuel <= heap_size / 8)
          (ensures U64.v (U64.sub fuel 1UL) <= heap_size / 8)
  = ()

/// `fuel <> 0UL ==> U64.v fuel > 0`.
///
/// Trivial, but every proof obligation is now discharged as its own SMT query
/// carrying the enclosing Pulse loop's full context, in which even this times
/// out.  Proving it here, where the context is empty, removes the SMT call at
/// the use site.
let fuel_nonzero_lemma (fuel: U64.t)
  : Lemma (requires fuel <> 0UL) (ensures U64.v fuel > 0)
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

/// Arithmetic for right-justified allocation: the object header sits at
/// `hd + leftover * 8`.  Establishes that it is word-aligned and that neither
/// it nor the object address one word above it overflows 64 bits.
let rightjust_no_overflow (hd: hp_addr) (leftover: U64.t)
  : Lemma (requires U64.v leftover <= pow2 54 - 1)
          (ensures (let off = U64.v leftover * U64.v mword in
                    off <= pow2 57 /\
                    off < pow2 64 /\
                    U64.v hd + off < pow2 64 /\
                    U64.v hd + off + U64.v mword < pow2 64 /\
                    (U64.v hd + off) % U64.v mword == 0))
  = assert_norm (pow2 54 * 8 == pow2 57);
    assert_norm (pow2 57 + pow2 57 == pow2 58);
    assert_norm (pow2 58 + pow2 58 == pow2 59);
    assert_norm (pow2 59 < pow2 64);
    FStar.Math.Lemmas.multiple_modulo_lemma (U64.v leftover) 8;
    FStar.Math.Lemmas.lemma_mod_add_distr (U64.v hd) (U64.v leftover * 8) 8

/// wosize bounds from heap arithmetic
let wosize_from_heap_lemma (wz: U64.t)
  : Lemma (requires U64.v wz <= SpecBase.heap_words - 1 /\ heap_size <= pow2 57)
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

/// Two distinct word-aligned addresses are a full word apart, so writing at
/// one leaves the other's word intact.  Used to show that repairing the
/// predecessor's link does not disturb the block header the allocation then
/// reads back.
let prev_write_keeps_header (g: SpecBase.heap) (p: SpecBase.hp_addr)
                            (hd: SpecBase.hp_addr) (v: U64.t)
  : Lemma (requires U64.v p <> U64.v hd)
          (ensures SH.read_word (SH.write_word g p v) hd == SH.read_word g hd)
  = SH.read_write_different g p hd v

/// ---------------------------------------------------------------------------
/// Main allocation function (fully proved — 0 admits)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 60"
fn allocate (heap: heap_t) (fp: U64.t) (wosize: U64.t) (tag: U64.t{U64.v tag < 256})
  requires is_heap heap 's **
           pure (SF.well_formed_heap 's /\
                 U64.v wosize >= 1)
  returns res: (U64.t & U64.t)
  ensures exists* s2. is_heap heap s2 **
    pure (let spec_res = SA.alloc_spec 's fp (U64.v wosize) tag in
          s2 == spec_res.heap_out /\
          fst res == spec_res.fp_out /\
          snd res == spec_res.obj_out)
{
  // Ensure wosize >= 1 (need at least 1 word for free-list link)
  // wosize >= 1 by precondition; `alloc_spec`'s 0 -> 1 bump is the identity.
  let wz : U64.t = wosize;

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
          SA.alloc_search 's vhead vprev vcur (U64.v wz) tag (U64.v vfuel) ==
            SA.alloc_spec 's fp (U64.v wosize) tag
        else
          (let sr = SA.alloc_spec 's fp (U64.v wosize) tag in
           s_cur == sr.heap_out /\
           vhead == sr.fp_out /\
           vresult == sr.obj_out))
      )
    decreases (U64.v !fuel_ref + (if !go then 1 else 0))
  {
    let vfuel = !fuel_ref;
    if U64.eq vfuel 0UL {
      // Fuel exhausted — OOM
      let vh = !head_fp;
      let vp = !prev_fp;
      let vc = !cur_fp;
      SA.alloc_search_fuel_0 's vh vp vc (U64.v wz) tag;
      go := false
    } else {
      fuel_nonzero_lemma vfuel;
      let vcur = !cur_fp;
      let valid = is_valid_fp vcur;
      if not valid {
        // Invalid cur_fp — OOM
        let vh = !head_fp;
        let vp = !prev_fp;
        SA.alloc_search_invalid 's vh vp vcur (U64.v wz) (U64.v vfuel) tag;
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
          // Found a suitable block.  The object is RIGHT-JUSTIFIED inside it,
          // as stock OCaml's nf_allocate_block does: its header sits
          // `leftover` words above `hd`, so the remainder keeps `hd`, keeps
          // its address, and keeps the link word already stored at hd + 8.
          // The allocated header therefore declares EXACTLY `wz`.
          let leftover = U64.sub block_wz wz;
          let vh = !head_fp;
          let vp = !prev_fp;
          wosize_bound_lemma wz block_wz;
          rightjust_no_overflow hd_addr leftover;

          let alloc_hd_off = U64.add hd_addr (U64.mul leftover mword);
          let alloc_obj = U64.add alloc_hd_off mword;

          if U64.gte alloc_obj heap_size_u64 {
            // The right-justified object would leave the heap.  Unreachable
            // for a well-formed block once wz >= 1, but the spec guards it.
            SA.alloc_search_found_oob 's vh vp vcur (U64.v wz) (U64.v vfuel) tag;
            go := false
          } else {
            assert (pure (U64.v alloc_hd_off < heap_size));
            assert (pure (U64.v alloc_hd_off % 8 == 0));

            if U64.gte leftover 1UL {
              // Split, or a one-word leftover: both write the same two words,
              // the remainder header at hd (wosize leftover - 1, which at
              // leftover = 1 is the empty block, header only) and the object
              // header right-justified above it.  They differ only in what
              // replaces `obj` in the free list.
              SA.alloc_from_block_split_normal 's (vcur <: obj_addr) (U64.v wz) next tag;
              let new_fp = (if U64.gte leftover 2UL then vcur else next);

              // `vp = hd_addr` means the predecessor has wosize 0, which a
              // free list never contains; `alloc_search` treats it exactly
              // like an absent or invalid predecessor, so the two cases share
              // this branch.  The header writes are duplicated into each side
              // rather than hoisted -- Pulse cannot frame a `let` across the
              // `if` here -- and on the predecessor side they come SECOND,
              // matching the order `alloc_search` fixes.
              let vp_unusable = (if U64.eq vp 0UL then true else U64.eq vp hd_addr);
              if vp_unusable {
                SA.alloc_search_found_head 's vh vp vcur (U64.v wz) (U64.v vfuel) tag;
                SA.alloc_from_block_split_normal 's (vcur <: obj_addr) (U64.v wz) next tag;
                let rem_hdr = makeHeader (U64.sub leftover 1UL) blue 0UL;
                write_word heap hd_addr rem_hdr;
                let alloc_hdr = makeHeader wz white tag;
                write_word heap alloc_hd_off alloc_hdr;
                head_fp := new_fp;
                result_obj := alloc_obj;
                go := false
              } else {
                // re-state what `is_valid_fp` established; the branch above
                // pushed it far enough back that the coercion below stalls
                assert (pure (U64.v vcur >= U64.v mword));
                assert (pure (U64.v vcur < heap_size));
                assert (pure (U64.v vcur % U64.v mword == 0));
                SA.alloc_search_found_prev 's vh vp vcur (U64.v wz) (U64.v vfuel) tag;
                write_word heap (vp <: hp_addr) new_fp;
                prev_write_keeps_header 's (vp <: hp_addr) hd_addr new_fp;
                SA.alloc_from_block_split_normal
                  (SH.write_word 's (vp <: hp_addr) new_fp) (vcur <: obj_addr) (U64.v wz) next tag;
                let rem_hdr = makeHeader (U64.sub leftover 1UL) blue 0UL;
                write_word heap hd_addr rem_hdr;
                let alloc_hdr = makeHeader wz white tag;
                write_word heap alloc_hd_off alloc_hdr;
                result_obj := alloc_obj;
                go := false
              }
            } else {
              // === EXACT FIT === leftover = 0, so alloc_hd_off = hd_addr and
              // alloc_obj = vcur; the block is detached from the free list.
              SA.alloc_from_block_exact 's (vcur <: obj_addr) (U64.v wz) next tag;
              // Same split of cases, and the same ordering, as above.
              let vp_unusable = (if U64.eq vp 0UL then true else U64.eq vp hd_addr);
              if vp_unusable {
                SA.alloc_search_found_head 's vh vp vcur (U64.v wz) (U64.v vfuel) tag;
                SA.alloc_from_block_exact 's (vcur <: obj_addr) (U64.v wz) next tag;
                let alloc_hdr = makeHeader wz white tag;
                write_word heap hd_addr alloc_hdr;
                head_fp := next;
                result_obj := alloc_obj;
                go := false
              } else {
                // re-state what `is_valid_fp` established; the branch above
                // pushed it far enough back that the coercion below stalls
                assert (pure (U64.v vcur >= U64.v mword));
                assert (pure (U64.v vcur < heap_size));
                assert (pure (U64.v vcur % U64.v mword == 0));
                SA.alloc_search_found_prev 's vh vp vcur (U64.v wz) (U64.v vfuel) tag;
                write_word heap (vp <: hp_addr) next;
                prev_write_keeps_header 's (vp <: hp_addr) hd_addr next;
                // the link write left the block header where it was, so the
                // exact-fit unfolding applies to the relinked heap too
                assert (pure (SH.read_word (SH.write_word 's (vp <: hp_addr) next)
                                           (SH.hd_address (vcur <: obj_addr))
                              == SH.read_word 's (SH.hd_address (vcur <: obj_addr))));
                hd_address_eq vcur;
                getWosize_eq hdr;
                assert (pure (SH.hd_address (vcur <: obj_addr) == hd_addr));
                assert (pure (SH.read_word 's hd_addr == hdr));
                assert (pure (U64.v leftover == 0));
                assert (pure (U64.v block_wz == U64.v wz));
                assert (pure (U64.v (SO.getWosize hdr) == U64.v wz));
                SA.alloc_from_block_exact
                  (SH.write_word 's (vp <: hp_addr) next) (vcur <: obj_addr) (U64.v wz) next tag;
                let alloc_hdr = makeHeader wz white tag;
                write_word heap hd_addr alloc_hdr;
                result_obj := alloc_obj;
                go := false
              }
            }
          }
        } else {
          // Block too small — advance to next
          let vh = !head_fp;
          let vp = !prev_fp;
          hd_address_eq vcur;
          SH.hd_address_spec (vcur <: obj_addr);
          SA.alloc_search_advance 's vh vp vcur (U64.v wz) (U64.v vfuel) tag;
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
/// Weak-precondition allocation (for use during promotion)
/// ---------------------------------------------------------------------------
/// Same implementation as `allocate` but only requires well_formed_heap_part1
/// + fl_valid + fl_chain_terminates. The allocator logic only reads headers
/// and free-list link pointers — it never inspects object pointer fields,
/// so well_formed_heap_part2 (pointer closure) is not needed.

#push-options "--z3rlimit 60"
fn allocate_part1 (heap: heap_t) (fp: U64.t) (wosize: U64.t) (tag: U64.t{U64.v tag < 256})
  requires is_heap heap 's **
           pure (SF.well_formed_heap_part1 's /\
                 AllocLemmas.fl_valid 's fp SpecBase.heap_words /\
                 AllocLemmas.fl_chain_terminates 's fp SpecBase.heap_words /\
                 U64.v wosize >= 1)
  returns res: (U64.t & U64.t)
  ensures exists* s2. is_heap heap s2 **
    pure (let spec_res = SA.alloc_spec 's fp (U64.v wosize) tag in
          s2 == spec_res.heap_out /\
          fst res == spec_res.fp_out /\
          snd res == spec_res.obj_out)
{
  // Ensure wosize >= 1 (need at least 1 word for free-list link)
  // wosize >= 1 by precondition; `alloc_spec`'s 0 -> 1 bump is the identity.
  let wz : U64.t = wosize;

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
          SA.alloc_search 's vhead vprev vcur (U64.v wz) tag (U64.v vfuel) ==
            SA.alloc_spec 's fp (U64.v wosize) tag
        else
          (let sr = SA.alloc_spec 's fp (U64.v wosize) tag in
           s_cur == sr.heap_out /\
           vhead == sr.fp_out /\
           vresult == sr.obj_out))
      )
    decreases (U64.v !fuel_ref + (if !go then 1 else 0))
  {
    let vfuel = !fuel_ref;
    if U64.eq vfuel 0UL {
      let vh = !head_fp;
      let vp = !prev_fp;
      let vc = !cur_fp;
      SA.alloc_search_fuel_0 's vh vp vc (U64.v wz) tag;
      go := false
    } else {
      fuel_nonzero_lemma vfuel;
      let vcur = !cur_fp;
      let valid = is_valid_fp vcur;
      if not valid {
        let vh = !head_fp;
        let vp = !prev_fp;
        SA.alloc_search_invalid 's vh vp vcur (U64.v wz) (U64.v vfuel) tag;
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
          // Found a suitable block.  The object is RIGHT-JUSTIFIED inside it,
          // as stock OCaml's nf_allocate_block does: its header sits
          // `leftover` words above `hd`, so the remainder keeps `hd`, keeps
          // its address, and keeps the link word already stored at hd + 8.
          // The allocated header therefore declares EXACTLY `wz`.
          let leftover = U64.sub block_wz wz;
          let vh = !head_fp;
          let vp = !prev_fp;
          wosize_bound_lemma wz block_wz;
          rightjust_no_overflow hd_addr leftover;

          let alloc_hd_off = U64.add hd_addr (U64.mul leftover mword);
          let alloc_obj = U64.add alloc_hd_off mword;

          if U64.gte alloc_obj heap_size_u64 {
            // The right-justified object would leave the heap.  Unreachable
            // for a well-formed block once wz >= 1, but the spec guards it.
            SA.alloc_search_found_oob 's vh vp vcur (U64.v wz) (U64.v vfuel) tag;
            go := false
          } else {
            assert (pure (U64.v alloc_hd_off < heap_size));
            assert (pure (U64.v alloc_hd_off % 8 == 0));

            if U64.gte leftover 1UL {
              // Split, or a one-word leftover: both write the same two words,
              // the remainder header at hd (wosize leftover - 1, which at
              // leftover = 1 is the empty block, header only) and the object
              // header right-justified above it.  They differ only in what
              // replaces `obj` in the free list.
              SA.alloc_from_block_split_normal 's (vcur <: obj_addr) (U64.v wz) next tag;
              let new_fp = (if U64.gte leftover 2UL then vcur else next);

              // `vp = hd_addr` means the predecessor has wosize 0, which a
              // free list never contains; `alloc_search` treats it exactly
              // like an absent or invalid predecessor, so the two cases share
              // this branch.  The header writes are duplicated into each side
              // rather than hoisted -- Pulse cannot frame a `let` across the
              // `if` here -- and on the predecessor side they come SECOND,
              // matching the order `alloc_search` fixes.
              let vp_unusable = (if U64.eq vp 0UL then true else U64.eq vp hd_addr);
              if vp_unusable {
                SA.alloc_search_found_head 's vh vp vcur (U64.v wz) (U64.v vfuel) tag;
                SA.alloc_from_block_split_normal 's (vcur <: obj_addr) (U64.v wz) next tag;
                let rem_hdr = makeHeader (U64.sub leftover 1UL) blue 0UL;
                write_word heap hd_addr rem_hdr;
                let alloc_hdr = makeHeader wz white tag;
                write_word heap alloc_hd_off alloc_hdr;
                head_fp := new_fp;
                result_obj := alloc_obj;
                go := false
              } else {
                // re-state what `is_valid_fp` established; the branch above
                // pushed it far enough back that the coercion below stalls
                assert (pure (U64.v vcur >= U64.v mword));
                assert (pure (U64.v vcur < heap_size));
                assert (pure (U64.v vcur % U64.v mword == 0));
                SA.alloc_search_found_prev 's vh vp vcur (U64.v wz) (U64.v vfuel) tag;
                write_word heap (vp <: hp_addr) new_fp;
                prev_write_keeps_header 's (vp <: hp_addr) hd_addr new_fp;
                SA.alloc_from_block_split_normal
                  (SH.write_word 's (vp <: hp_addr) new_fp) (vcur <: obj_addr) (U64.v wz) next tag;
                let rem_hdr = makeHeader (U64.sub leftover 1UL) blue 0UL;
                write_word heap hd_addr rem_hdr;
                let alloc_hdr = makeHeader wz white tag;
                write_word heap alloc_hd_off alloc_hdr;
                result_obj := alloc_obj;
                go := false
              }
            } else {
              // === EXACT FIT === leftover = 0, so alloc_hd_off = hd_addr and
              // alloc_obj = vcur; the block is detached from the free list.
              SA.alloc_from_block_exact 's (vcur <: obj_addr) (U64.v wz) next tag;
              // Same split of cases, and the same ordering, as above.
              let vp_unusable = (if U64.eq vp 0UL then true else U64.eq vp hd_addr);
              if vp_unusable {
                SA.alloc_search_found_head 's vh vp vcur (U64.v wz) (U64.v vfuel) tag;
                SA.alloc_from_block_exact 's (vcur <: obj_addr) (U64.v wz) next tag;
                let alloc_hdr = makeHeader wz white tag;
                write_word heap hd_addr alloc_hdr;
                head_fp := next;
                result_obj := alloc_obj;
                go := false
              } else {
                // re-state what `is_valid_fp` established; the branch above
                // pushed it far enough back that the coercion below stalls
                assert (pure (U64.v vcur >= U64.v mword));
                assert (pure (U64.v vcur < heap_size));
                assert (pure (U64.v vcur % U64.v mword == 0));
                SA.alloc_search_found_prev 's vh vp vcur (U64.v wz) (U64.v vfuel) tag;
                write_word heap (vp <: hp_addr) next;
                prev_write_keeps_header 's (vp <: hp_addr) hd_addr next;
                // the link write left the block header where it was, so the
                // exact-fit unfolding applies to the relinked heap too
                assert (pure (SH.read_word (SH.write_word 's (vp <: hp_addr) next)
                                           (SH.hd_address (vcur <: obj_addr))
                              == SH.read_word 's (SH.hd_address (vcur <: obj_addr))));
                hd_address_eq vcur;
                getWosize_eq hdr;
                assert (pure (SH.hd_address (vcur <: obj_addr) == hd_addr));
                assert (pure (SH.read_word 's hd_addr == hdr));
                assert (pure (U64.v leftover == 0));
                assert (pure (U64.v block_wz == U64.v wz));
                assert (pure (U64.v (SO.getWosize hdr) == U64.v wz));
                SA.alloc_from_block_exact
                  (SH.write_word 's (vp <: hp_addr) next) (vcur <: obj_addr) (U64.v wz) next tag;
                let alloc_hdr = makeHeader wz white tag;
                write_word heap hd_addr alloc_hdr;
                result_obj := alloc_obj;
                go := false
              }
            }
          }
        } else {
          let vh = !head_fp;
          let vp = !prev_fp;
          hd_address_eq vcur;
          SH.hd_address_spec (vcur <: obj_addr);
          SA.alloc_search_advance 's vh vp vcur (U64.v wz) (U64.v vfuel) tag;
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
