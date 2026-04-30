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
          ms2 == PromoteSpec.copy_fields {data='md; bump='mb} 'ms src_obj dst_obj 0 (U64.v wosize))
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
            PromoteSpec.copy_fields {data='md; bump='mb} ms_i src_obj dst_obj (U64.v iv) (U64.v wosize) ==
            PromoteSpec.copy_fields {data='md; bump='mb} 'ms src_obj dst_obj 0 (U64.v wosize))
  {
    let iv = !i;
    // Source: minor_obj + iv * 8
    let src_off = U64.mul iv 8UL;
    let src_addr = U64.add src_obj src_off;
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

/// Promote one minor-heap object to the major heap.
/// Returns the new address in major heap (0UL on OOM).
///
/// Preconditions only require well_formed_heap_part1 (not full wfh) because
/// during a promotion loop, pointer closure (part2) is temporarily violated
/// (minor pointers are written into the major heap body). The allocator only
/// needs part1 + fl_valid + fl_chain_terminates to function correctly.
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
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
    pure (SF.well_formed_heap_part1 ms2 /\
          AllocLemmas.fl_valid ms2 fp2 (heap_size / U64.v mword) /\
          AllocLemmas.fl_chain_terminates ms2 fp2 (heap_size / U64.v mword))
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
      // So wfh_part1, fl_valid, fl_chain_terminates are preserved trivially
      AllocLemmas.alloc_spec_preserves_wfh_part1 'ms fp (U64.v wosize);
      AllocLemmas.alloc_spec_preserves_fl_valid_part1 'ms fp (U64.v wosize);
      AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 'ms fp (U64.v wosize);
      0UL
    } else {
      // Derive bounds from allocator postconditions:
      // 1. wfh_part1 is already our precondition (no need to reveal_opaque)
      // 2. new_obj is a valid obj_addr in the output heap
      AllocProps.alloc_spec_obj_in_objects_part1 'ms fp (U64.v wosize);
      assert (pure (U64.v new_obj >= U64.v mword /\
                    U64.v new_obj < heap_size /\
                    U64.v new_obj % U64.v mword == 0));
      // 3. The output heap preserves wfh_part1
      AllocLemmas.alloc_spec_preserves_wfh_part1 'ms fp (U64.v wosize);
      // 4. Preserve fl_valid and fl_chain_terminates
      AllocLemmas.alloc_spec_preserves_fl_valid_part1 'ms fp (U64.v wosize);
      AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 'ms fp (U64.v wosize);
      // 5. The output object has wosize >= requested
      AllocProps.alloc_spec_obj_wosize_part1 'ms fp (U64.v wosize);
      // 6. From wfh_part1 + mem: obj + wosize_of_object * 8 <= heap_size
      SF.wfh_part1_obj_bound
        (GC.Spec.Allocator.alloc_spec 'ms fp (U64.v wosize)).heap_out
        (new_obj <: obj_addr);
      // 7. Since wosize_of_object >= requested_wz and obj + wz_actual*8 <= heap_size:
      assert (pure (U64.v new_obj + U64.v wosize * 8 <= heap_size));
      // 8. chain_avoids: new_obj is not in the free-list chain of the output
      AllocLemmas.alloc_spec_obj_not_in_chain_part1 'ms fp (U64.v wosize);
      // 9. Invoke composite lemma: copy_fields preserves all allocator invariants.
      //    This is a pure lemma — we call it BEFORE copy_fields_loop so its conclusion
      //    (about copy_fields applied to the alloc result) is in the pure context.
      PromoteSpec.copy_fields_preserves_alloc_invariants
        {data='md; bump='mb}
        (GC.Spec.Allocator.alloc_spec 'ms fp (U64.v wosize)).heap_out
        obj (new_obj <: obj_addr) (U64.v wosize) new_fp;
      // Copy all fields (0..wosize-1) from minor to major
      copy_fields_loop minor major obj new_obj wosize;
      // After copy_fields_loop: ms2 == copy_fields ... (alloc_spec ...).heap_out ...
      // Combined with the lemma ensures, we get wfh_part1/fl_valid/fl_chain_terminates ms2
      new_obj
    }
  }
}
#pop-options
