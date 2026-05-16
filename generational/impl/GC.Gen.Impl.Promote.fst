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

inline_for_extraction
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
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
    // NL arithmetic for minor_read precondition (Z3 4.13.3 needs help)
    FStar.Math.Lemmas.lemma_mult_le_right 8 (U64.v iv) (U64.v wosize - 1);
    FStar.Math.Lemmas.lemma_mod_plus (U64.v src_obj) (U64.v iv) 8;
    assert (pure (U64.v src_addr + 8 <= minor_heap_size /\
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

/// Zero the padding field if the allocator gave extra space (leftover=1 case).
/// After this, the ghost state matches zero_promote_padding.
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0 --split_queries always"
inline_for_extraction
fn zero_padding_step (major: heap_t) (dst_obj: U64.t) (wosize: U64.t)
  requires is_heap major 'ms **
           pure (U64.v dst_obj >= U64.v mword /\
                 U64.v dst_obj < heap_size /\
                 U64.v dst_obj % U64.v mword == 0 /\
                 U64.v wosize > 0 /\
                 SF.well_formed_heap_part1 'ms /\
                 Seq.mem ((dst_obj <: obj_addr)) (SF.objects zero_addr 'ms) /\
                 U64.v dst_obj + U64.v wosize * 8 <= heap_size)
  ensures exists* ms'. is_heap major ms' **
    pure (ms' == PromoteSpec.zero_promote_padding 'ms (dst_obj <: U64.t) (U64.v wosize))
{
  let hdr_addr = U64.sub dst_obj 8UL;
  SpecHeap.hd_address_spec (dst_obj <: obj_addr);
  let hdr = read_word major hdr_addr;
  let actual_wz = SpecObj.getWosize hdr;
  SpecObj.wosize_of_object_spec (dst_obj <: obj_addr) 'ms;
  if U64.gt actual_wz wosize {
    // actual_wz > wosize means pad_addr + 8 <= heap_size by wfh_part1 bounds
    SF.wfh_part1_obj_bound 'ms (dst_obj <: obj_addr);
    assert (pure (U64.v actual_wz > U64.v wosize));
    assert (pure (U64.v dst_obj + U64.v actual_wz * 8 <= heap_size));
    assert (pure (U64.v dst_obj + U64.v wosize * 8 + 8 <= heap_size));
    let pad_addr = U64.add dst_obj (U64.mul wosize 8UL);
    write_word major pad_addr 0UL;
    PromoteSpec.zero_promote_padding_write 'ms (dst_obj <: obj_addr) (U64.v wosize)
  } else {
    PromoteSpec.zero_promote_padding_noop 'ms (dst_obj <: obj_addr) (U64.v wosize)
  }
}
#pop-options

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
      // Establish wfh_part1 and membership in copied heap for zero_padding_step
      AllocLemmas.alloc_spec_preserves_wfh_part1 'ms fp (U64.v wosize);
      WBL.copy_fields_preserves_wfh_part1 {data='md; bump='mb}
        (GC.Spec.Allocator.alloc_spec 'ms fp (U64.v wosize)).heap_out
        obj (new_obj <: obj_addr) (U64.v wosize);
      WBL.copy_fields_preserves_objects_aux {data='md; bump='mb}
        (GC.Spec.Allocator.alloc_spec 'ms fp (U64.v wosize)).heap_out
        obj (new_obj <: obj_addr) 0 (U64.v wosize);
      // --- Zero padding field if allocator gave extra space (leftover=1 case) ---
      zero_padding_step major new_obj wosize;
      with ms_p. _;
      // --- Retag: copy the tag from minor header to the promoted major header ---
      // Read minor header to extract the original tag
      let minor_hdr = minor_read minor (U64.sub obj 8UL);
      let tag = Obj.getTag minor_hdr;
      // Connect impl tag to spec minor_tag and establish bound
      minor_tag_bound {data='md; bump='mb} obj;
      assert (pure (U64.v tag == minor_tag {data='md; bump='mb} obj));
      assert (pure (minor_tag {data='md; bump='mb} obj < 256));
      // Read promoted major header (from padded state) and rebuild with correct tag
      let major_hdr_addr = U64.sub new_obj 8UL;
      SpecHeap.hd_address_spec (new_obj <: obj_addr);
      assert (pure (major_hdr_addr == SpecHeap.hd_address (new_obj <: obj_addr)));
      let major_hdr = read_word major major_hdr_addr;
      let wz_read = SpecObj.getWosize major_hdr;
      let new_hdr = Obj.makeHeader wz_read Header.White tag;
      // Bridge: Obj.makeHeader == SpecObj.makeHeader (both compute pack_header)
      Obj.makeHeader_eq_pack_header wz_read Header.White tag;
      SpecObj.makeHeader_is_pack_header64 wz_read Header.White tag;
      assert (pure (new_hdr == SpecObj.makeHeader wz_read Header.White tag));
      // Unfold set_promoted_tag so SMT sees it equals our write_word on padded state
      PromoteSpec.set_promoted_tag_unfold ms_p (new_obj <: obj_addr) (minor_tag {data='md; bump='mb} obj);
      // Assert the key equality: our write matches set_promoted_tag
      assert (pure (
        SpecHeap.write_word ms_p major_hdr_addr new_hdr ==
        PromoteSpec.set_promoted_tag ms_p (new_obj <: U64.t) (minor_tag {data='md; bump='mb} obj)));
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
