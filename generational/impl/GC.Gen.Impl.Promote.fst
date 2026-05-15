(*
   Pulse GC (Generational) - Minor→Major Promotion Implementation

   Copies objects from the minor bump-pointer heap to the major free-list heap.
*)

module GC.Gen.Impl.Promote

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Impl.MinorHeap
open GC.Impl.Heap
module Alloc = GC.Impl.Allocator
module AllocLemmas = GC.Spec.Allocator.Lemmas
module AllocProps = GC.Gen.AllocProps
module SF = GC.Spec.Fields
module Obj = GC.Impl.Object
module SpecObj = GC.Spec.Object
module Header = GC.Lib.Header
module SpecHeap = GC.Spec.Heap

/// Read the wosize from a minor object's header (header is at obj - 8)
inline_for_extraction
fn read_minor_wosize (minor: minor_heap_t) (obj: U64.t)
  requires is_minor minor 'md 'mb **
           pure (U64.v obj >= 8 /\ U64.v obj < minor_heap_size /\ U64.v obj % 8 == 0)
  returns wosize: U64.t
  ensures is_minor minor 'md 'mb **
          pure (U64.v wosize == minor_wosize {data='md; bump='mb} obj)
{
  let hdr_addr = U64.sub obj 8UL;
  let hdr = minor_read minor hdr_addr;
  // wosize is bits 10-63 of header
  U64.shift_right hdr 10ul
}

/// Copy wosize fields from minor[src_obj + 0..] to major[dst_obj + 0..]
/// Copies fields at indices 0..(wosize-1), matching spec copy_fields.
///
/// Postcondition: the output heap equals the spec's copy_fields result.
/// This spec refinement enables callers to apply spec-level preservation lemmas.
module PromoteSpec = GC.Gen.Promote
module WBL = GC.Gen.WriteBodyLemmas

private let u64_gt_as_nat_gt (x: U64.t) (y: U64.t)
  : Lemma (requires U64.gt x y == true)
          (ensures U64.v x > U64.v y)
  = ()

private let u64_not_gt_as_nat_le (x: U64.t) (y: U64.t)
  : Lemma (requires U64.gt x y == false)
          (ensures U64.v x <= U64.v y)
  = ()

inline_for_extraction
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"
fn copy_fields_loop (minor: minor_heap_t) (major: heap_t)
                    (src_obj: U64.t) (dst_obj: U64.t)
                    (wosize: U64.t)
  requires is_minor minor 'md 'mb **
           is_heap major 'ms **
           pure (U64.v src_obj >= 8 /\ U64.v src_obj % 8 == 0 /\
                 U64.v src_obj + U64.v wosize * 8 <= minor_heap_size /\
                 U64.v dst_obj >= 8 /\ U64.v dst_obj % 8 == 0 /\
                 U64.v dst_obj + U64.v wosize * 8 <= heap_size /\
                 U64.v wosize > 0)
  ensures exists* md2 mb2 ms2.
    is_minor minor md2 mb2 **
    is_heap major ms2 **
    pure (md2 == 'md /\ mb2 == 'mb /\
          ms2 == WBL.copy_fields {data='md; bump='mb} 'ms src_obj dst_obj 0 (U64.v wosize))
{
  let mut i = 0UL;
  while (U64.lt !i wosize)
    invariant exists* md_i mb_i ms_i iv.
      is_minor minor md_i mb_i **
      is_heap major ms_i **
      R.pts_to i iv **
      pure (U64.v iv >= 0 /\ U64.v iv <= U64.v wosize /\
            U64.v src_obj >= 8 /\ U64.v src_obj % 8 == 0 /\
            U64.v src_obj + U64.v wosize * 8 <= minor_heap_size /\
            U64.v dst_obj >= 8 /\ U64.v dst_obj % 8 == 0 /\
            U64.v dst_obj + U64.v wosize * 8 <= heap_size /\
            U64.v wosize > 0 /\
            md_i == 'md /\ mb_i == 'mb /\
            // Spec refinement: remaining copy_fields from current state
            // equals full copy_fields from initial state
            WBL.copy_fields {data='md; bump='mb} ms_i src_obj dst_obj (U64.v iv) (U64.v wosize) ==
            WBL.copy_fields {data='md; bump='mb} 'ms src_obj dst_obj 0 (U64.v wosize))
  {
    let iv = !i;
    // Source: minor_obj + iv * 8
    let src_off = U64.mul iv 8UL;
    let src_addr = U64.add src_obj src_off;
    // NL arithmetic: iv < wosize ==> src_obj + iv*8 + 8 <= minor_heap_size
    assert (pure (U64.v iv < U64.v wosize /\
                  U64.v src_addr == U64.v src_obj + U64.v iv * 8 /\
                  U64.v src_obj + (U64.v iv + 1) * 8 <= U64.v src_obj + U64.v wosize * 8 /\
                  U64.v src_addr + 8 <= minor_heap_size /\
                  U64.v src_addr % 8 == 0));
    let field_val = minor_read minor src_addr;
    // Dest: major_obj + iv * 8
    let dst_off = U64.mul iv 8UL;
    let dst_addr = U64.add dst_obj dst_off;
    // SMT hints: bounds and alignment needed for copy_fields_step to fire
    assert (pure (U64.v iv < U64.v wosize /\
                  U64.v dst_obj + U64.v iv * 8 + 8 <= heap_size /\
                  (U64.v dst_obj + U64.v iv * 8) % 8 == 0 /\
                  U64.v dst_addr == U64.v dst_obj + U64.v iv * 8 /\
                  U64.v src_addr == U64.v src_obj + U64.v iv * 8));
    write_word major dst_addr field_val;
    i := U64.add iv 1UL
  }
}
#pop-options

private let promote_leftover_addr_valid
  (obj: obj_addr) (wosize: U64.t) (wz_read: U64.t) (g: heap)
  : Lemma (requires
             U64.v (SpecObj.wosize_of_object obj g) == U64.v wz_read /\
             U64.v obj + U64.v (SpecObj.wosize_of_object obj g) * 8 <= heap_size /\
             U64.v wz_read > U64.v wosize)
          (ensures
             U64.v (U64.add obj (U64.mul wosize 8UL)) == U64.v obj + U64.v wosize * 8 /\
             U64.v (U64.add obj (U64.mul wosize 8UL)) + 8 <= heap_size /\
             U64.v (U64.add obj (U64.mul wosize 8UL)) % 8 == 0)
  = let extra_addr = U64.add obj (U64.mul wosize 8UL) in
    assert (U64.v extra_addr == U64.v obj + U64.v wosize * 8);
    FStar.Math.Lemmas.lemma_mult_le_right 8 (U64.v wosize + 1) (U64.v wz_read);
    FStar.Math.Lemmas.distributivity_add_left (U64.v wosize) 1 8;
    assert (U64.v extra_addr + 8 == U64.v obj + (U64.v wosize + 1) * 8);
    assert (U64.v extra_addr + 8 <= U64.v obj + U64.v wz_read * 8);
    assert (U64.v extra_addr + 8 <= heap_size);
    FStar.Math.Lemmas.lemma_mod_plus (U64.v obj) (U64.v wosize) 8;
    assert (U64.v extra_addr % 8 == 0)

inline_for_extraction
fn clean_promote_leftover_write_impl
  (major: heap_t) (obj: obj_addr) (wosize: U64.t) (wz_read: U64.t)
  requires is_heap major 'ms **
           pure (wz_read == SpecObj.getWosize (SpecHeap.read_word 'ms (SpecHeap.hd_address obj)) /\
                 U64.v obj + U64.v (SpecObj.wosize_of_object obj 'ms) * 8 <= heap_size /\
                 U64.gt wz_read wosize == true /\
                 U64.v wosize > 0)
  ensures is_heap major (PromoteSpec.clean_promote_leftover 'ms (obj <: U64.t) (U64.v wosize))
{
  u64_gt_as_nat_gt wz_read wosize;
  assert (pure (U64.v wz_read > U64.v wosize));
  SpecObj.wosize_of_object_spec obj 'ms;
  assert (pure (U64.v (SpecObj.wosize_of_object obj 'ms) == U64.v wz_read));
  promote_leftover_addr_valid obj wosize wz_read 'ms;
  let extra_addr = U64.add obj (U64.mul wosize 8UL);
  assert (pure (U64.v extra_addr + 8 <= heap_size));
  write_word major (extra_addr <: hp_addr) 0UL;
  PromoteSpec.clean_promote_leftover_is_write 'ms obj (U64.v wosize);
  rewrite (is_heap major (SpecHeap.write_word 'ms (extra_addr <: hp_addr) 0UL))
       as (is_heap major (PromoteSpec.clean_promote_leftover 'ms (obj <: U64.t) (U64.v wosize)))
}

inline_for_extraction
fn clean_promote_leftover_noop_impl
  (major: heap_t) (obj: obj_addr) (wosize: U64.t) (wz_read: U64.t)
  requires is_heap major 'ms **
           pure (wz_read == SpecObj.getWosize (SpecHeap.read_word 'ms (SpecHeap.hd_address obj)) /\
                 U64.gt wz_read wosize == false /\
                 U64.v wosize > 0)
  ensures is_heap major (PromoteSpec.clean_promote_leftover 'ms (obj <: U64.t) (U64.v wosize))
{
  u64_not_gt_as_nat_le wz_read wosize;
  assert (pure (U64.v wz_read <= U64.v wosize));
  SpecObj.wosize_of_object_spec obj 'ms;
  PromoteSpec.clean_promote_leftover_noop 'ms obj (U64.v wosize);
  rewrite (is_heap major 'ms)
       as (is_heap major (PromoteSpec.clean_promote_leftover 'ms (obj <: U64.t) (U64.v wosize)))
}

/// Promote one minor-heap object to the major heap.
/// Returns the new address in major heap (0UL on OOM).
///
/// Preconditions only require well_formed_heap_part1 (not full wfh) because
/// during a promotion loop, pointer closure (part2) is temporarily violated
/// (minor pointers are written into the major heap body). The allocator only
/// needs part1 + fl_valid + fl_chain_terminates to function correctly.
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0 --split_queries always"
inline_for_extraction
fn promote_one (minor: minor_heap_t) (major: heap_t) (fp_ref: R.ref U64.t)
               (obj: U64.t)
  requires is_minor minor 'md 'mb **
           is_heap major 'ms **
           R.pts_to fp_ref 'fp **
           pure (U64.v obj >= 8 /\ U64.v obj < minor_heap_size /\
                 U64.v obj % 8 == 0 /\
                 // Minor object body within bounds (from minor_objects_wosize_bound)
                 U64.v obj + minor_wosize {data='md; bump='mb} obj * 8 <= minor_heap_size /\
                 // Major heap structural well-formedness (weaker than full wfh)
                 SF.well_formed_heap_part1 'ms /\
                 AllocLemmas.fl_valid 'ms 'fp (heap_size / U64.v mword) /\
                 AllocLemmas.fl_chain_terminates 'ms 'fp (heap_size / U64.v mword))
  returns new_addr: U64.t
  ensures exists* md2 mb2 ms2 fp2.
    is_minor minor md2 mb2 **
    is_heap major ms2 **
    R.pts_to fp_ref fp2 **
    pure (let minor_st = {data='md; bump='mb} in
          let wz = minor_wosize minor_st obj in
          md2 == 'md /\ mb2 == 'mb /\
          SF.well_formed_heap_part1 ms2 /\
          AllocLemmas.fl_valid ms2 fp2 (heap_size / U64.v mword) /\
          AllocLemmas.fl_chain_terminates ms2 fp2 (heap_size / U64.v mword) /\
          (wz > 0 ==>
            (let spec_res = PromoteSpec.promote_object minor_st 'ms obj 'fp wz in
             ms2 == spec_res.major_out /\
             fp2 == spec_res.fp_out /\
             new_addr == spec_res.new_addr)) /\
          (wz == 0 ==> ms2 == 'ms /\ fp2 == 'fp /\ new_addr == 0UL))
{
  // Read the wosize from the minor object header
  let wosize = read_minor_wosize minor obj;
  if U64.eq wosize 0UL {
    // Zero-sized object, nothing to copy
    0UL
  } else {
    // Allocate space in major heap (using weak precondition variant)
    let fp = R.op_Bang fp_ref;
    let res = Alloc.allocate_part1 major fp wosize;
    let new_fp = fst res;
    let new_obj = snd res;
    R.op_Colon_Equals fp_ref new_fp;
    if U64.eq new_obj 0UL {
      // OOM — alloc_spec with obj_out=0 returns heap unchanged
      AllocLemmas.alloc_spec_preserves_wfh_part1 'ms fp (U64.v wosize);
      AllocLemmas.alloc_spec_preserves_fl_valid_part1 'ms fp (U64.v wosize);
      AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 'ms fp (U64.v wosize);
      // Spec refinement for OOM: promote_object returns {major_out='ms; fp_out='fp; new_addr=0UL}
      AllocProps.alloc_spec_oom_unchanged 'ms fp (U64.v wosize);
      PromoteSpec.promote_object_oom {data='md; bump='mb} 'ms obj 'fp (U64.v wosize);
      0UL
    } else {
      // Derive bounds from allocator postconditions:
      AllocProps.alloc_spec_obj_in_objects_part1 'ms fp (U64.v wosize);
      assert (pure (U64.v new_obj >= U64.v mword /\
                    U64.v new_obj < heap_size /\
                    U64.v new_obj % U64.v mword == 0));
      AllocLemmas.alloc_spec_preserves_wfh_part1 'ms fp (U64.v wosize);
      AllocLemmas.alloc_spec_preserves_fl_valid_part1 'ms fp (U64.v wosize);
      AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 'ms fp (U64.v wosize);
      AllocProps.alloc_spec_obj_wosize_part1 'ms fp (U64.v wosize);
      SF.wfh_part1_obj_bound
        (GC.Spec.Allocator.alloc_spec 'ms fp (U64.v wosize)).heap_out
        (new_obj <: obj_addr);
      assert (pure (U64.v new_obj + U64.v wosize * 8 <= heap_size));
      AllocLemmas.alloc_spec_obj_not_in_chain_part1 'ms fp (U64.v wosize);
      // Copy all fields (0..wosize-1) from minor to major
      copy_fields_loop minor major obj new_obj wosize;
      // Bind the existential witnesses from copy_fields_loop
      with md_c mb_c ms_c. _;
      // copy_fields preserves object membership and header bounds for the promoted block
      WBL.copy_fields_preserves_objects_aux
        {data='md; bump='mb}
        (GC.Spec.Allocator.alloc_spec 'ms 'fp (U64.v wosize)).heap_out
        obj (new_obj <: obj_addr) 0 (U64.v wosize);
      WBL.copy_fields_preserves_wfh_part1
        {data='md; bump='mb}
        (GC.Spec.Allocator.alloc_spec 'ms 'fp (U64.v wosize)).heap_out
        obj (new_obj <: obj_addr) (U64.v wosize);
      // Read promoted major header to inspect the allocated block size
      let major_hdr_addr = U64.sub new_obj 8UL;
      SpecHeap.hd_address_spec (new_obj <: obj_addr);
      assert (pure (U64.v major_hdr_addr == U64.v (SpecHeap.hd_address (new_obj <: obj_addr))));
      assert (pure (major_hdr_addr == SpecHeap.hd_address (new_obj <: obj_addr)));
      let major_hdr = read_word major major_hdr_addr;
      let wz_read = SpecObj.getWosize major_hdr;
      assert (pure (major_hdr == SpecHeap.read_word ms_c major_hdr_addr));
      assert (pure (wz_read == SpecObj.getWosize (SpecHeap.read_word ms_c (SpecHeap.hd_address (new_obj <: obj_addr)))));
      SF.wfh_part1_obj_bound ms_c (new_obj <: obj_addr);
      // Zero the allocator leftover field when the allocated block is larger than requested
      if U64.gt wz_read wosize {
        clean_promote_leftover_write_impl major (new_obj <: obj_addr) wosize wz_read
      } else {
        clean_promote_leftover_noop_impl major (new_obj <: obj_addr) wosize wz_read
      };
      // --- Retag: copy the tag from minor header to the promoted major header ---
      let minor_hdr = minor_read minor (U64.sub obj 8UL);
      let tag = Obj.getTag minor_hdr;
      minor_tag_bound {data='md; bump='mb} obj;
      assert (pure (U64.v tag == minor_tag {data='md; bump='mb} obj));
      assert (pure (minor_tag {data='md; bump='mb} obj < 256));
      let major_hdr_cleaned = read_word major major_hdr_addr;
      let wz_cleaned = SpecObj.getWosize major_hdr_cleaned;
      let new_hdr = Obj.makeHeader wz_cleaned Header.White tag;
      Obj.makeHeader_eq_pack_header wz_cleaned Header.White tag;
      SpecObj.makeHeader_is_pack_header64 wz_cleaned Header.White tag;
      assert (pure (new_hdr == SpecObj.makeHeader wz_cleaned Header.White tag));
      PromoteSpec.set_promoted_tag_unfold
        (PromoteSpec.clean_promote_leftover ms_c (new_obj <: U64.t) (U64.v wosize))
        (new_obj <: obj_addr)
        (minor_tag {data='md; bump='mb} obj);
      assert (pure (
        SpecHeap.write_word
          (PromoteSpec.clean_promote_leftover ms_c (new_obj <: U64.t) (U64.v wosize))
          major_hdr_addr
          new_hdr ==
        PromoteSpec.set_promoted_tag
          (PromoteSpec.clean_promote_leftover ms_c (new_obj <: U64.t) (U64.v wosize))
          (new_obj <: U64.t)
          (minor_tag {data='md; bump='mb} obj)));
      write_word major major_hdr_addr new_hdr;
      // Ghost: prove spec refinement + allocator invariant preservation
      PromoteSpec.promote_object_success {data='md; bump='mb} 'ms obj 'fp (U64.v wosize);
      PromoteSpec.promote_object_preserves_alloc_invariants
        {data='md; bump='mb} 'ms obj 'fp (U64.v wosize);
      new_obj
    }
  }
}
#pop-options
