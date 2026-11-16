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
module AllocProps = GC.Spec.Allocator.Props
module AP = GC.Spec.Allocator.Phase
module ST = GC.Gen.SweptTail
module FLA = GC.Spec.FreeList.Ascending
module FLAsc = GC.Gen.FreeListAscending
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

/// Read the tag from a minor object's header (low 8 bits)
inline_for_extraction
fn read_minor_tag (minor: minor_heap_t) (obj: U64.t)
  requires is_minor minor 'md 'mb **
           pure (U64.v obj >= 8 /\ U64.v obj < minor_heap_size /\ U64.v obj % 8 == 0)
  returns tag: U64.t
  ensures is_minor minor 'md 'mb **
          pure (U64.v tag == minor_tag {data='md; bump='mb} obj)
{
  let hdr_addr = U64.sub obj 8UL;
  let hdr = minor_read minor hdr_addr;
  // tag is bits 0-7 of header
  U64.logand hdr 0xFFUL
}

/// Read the number of fields the collector may scan in a minor object.
///
/// An object whose tag is at least `no_scan_tag` (251) holds raw bytes rather
/// than fields, so its contents must never be interpreted as pointers; for
/// scanning purposes it has no fields at all.  This is the runtime counterpart
/// of `GC.Gen.MinorHeap.minor_scan_wosize`, and mirrors the two guards the
/// major heap already carries (`update_all_objects`, `mark_and_push`).
///
/// Note this is *not* the size used to promote the object: promotion copies the
/// whole body verbatim, no-scan or not, and so keeps using `read_minor_wosize`.
inline_for_extraction
fn read_minor_scan_wosize (minor: minor_heap_t) (obj: U64.t)
  requires is_minor minor 'md 'mb **
           pure (U64.v obj >= 8 /\ U64.v obj < minor_heap_size /\ U64.v obj % 8 == 0)
  returns wosize: U64.t
  ensures is_minor minor 'md 'mb **
          pure (U64.v wosize == minor_scan_wosize {data='md; bump='mb} obj)
{
  let tag = read_minor_tag minor obj;
  if (U64.gte tag 251UL) {
    0UL
  } else {
    read_minor_wosize minor obj
  }
}

/// Copy wosize fields from minor[src_obj + 0..] to major[dst_obj + 0..]
/// Copies fields at indices 0..(wosize-1), matching spec copy_fields.
///
/// Postcondition: the output heap equals the spec's copy_fields result.
/// This spec refinement enables callers to apply spec-level preservation lemmas.
module PromoteSpec = GC.Gen.Promote
module Ph = GC.Spec.Phase
module WBL = GC.Gen.WriteBodyLemmas

let field_in_bounds (limit obj_addr wosize jv: nat)
  : Lemma (requires limit < pow2 57 /\
                    obj_addr + wosize * 8 <= limit /\
                    obj_addr % 8 == 0 /\
                    jv < wosize)
          (ensures jv * 8 < pow2 64 /\
                   obj_addr + jv * 8 < pow2 64 /\
                   obj_addr + jv * 8 + 8 <= limit /\
                   (obj_addr + jv * 8) % 8 == 0 /\
                   jv + 1 < pow2 64)
  =
  FStar.Math.Lemmas.lemma_mult_le_right 8 (jv + 1) wosize;
  assert ((jv + 1) * 8 <= wosize * 8);
  assert (jv * 8 + 8 <= wosize * 8);
  assert (obj_addr + jv * 8 + 8 <= obj_addr + wosize * 8);
  assert_norm (pow2 57 < pow2 64);
  FStar.Math.Lemmas.cancel_mul_mod jv 8;
  FStar.Math.Lemmas.modulo_addition_lemma obj_addr 8 jv

inline_for_extraction
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
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
    decreases (U64.v wosize - U64.v !i)
  {
    let iv = !i;
    assert (pure (U64.v iv < U64.v wosize));
    field_in_bounds minor_heap_size (U64.v src_obj) (U64.v wosize) (U64.v iv);
    field_in_bounds heap_size (U64.v dst_obj) (U64.v wosize) (U64.v iv);
    // Source: minor_obj + iv * 8
    let src_off = U64.mul iv 8UL;
    assert (pure (U64.v src_off == U64.v iv * 8));
    let src_addr = U64.add src_obj src_off;
    // Prove minor_read precondition
    assert (pure (U64.v src_addr == U64.v src_obj + U64.v iv * 8));
    assert (pure (U64.v src_addr + 8 <= U64.v src_obj + U64.v wosize * 8));
    assert (pure (U64.v src_addr + 8 <= minor_heap_size /\ U64.v src_addr % 8 == 0));
    let field_val = minor_read minor src_addr;
    // Dest: major_obj + iv * 8
    let dst_off = U64.mul iv 8UL;
    assert (pure (U64.v dst_off == U64.v iv * 8));
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

/// ---------------------------------------------------------------------------
/// The phase record across a promotion
/// ---------------------------------------------------------------------------

/// The caches across a change that keeps the walk and every header.
let phase_rel_heads (g g': heap) (v: Alloc.phase_state) (ph: Ph.gc_phase)
  : Lemma (requires Alloc.phase_rel g v ph /\ GC.Spec.SweepPhase.Intrinsic.same_heads g g')
          (ensures Alloc.phase_rel g' v ph)
  = GC.Spec.SweepPhase.Intrinsic.state_at_heads g g' v.Alloc.ps_cursor

ghost
fn phase_heads (phase: R.ref Alloc.phase_state) (g': heap)
  requires Alloc.is_phase phase 'g 'ph ** pure (GC.Spec.SweepPhase.Intrinsic.same_heads 'g g')
  ensures Alloc.is_phase phase g' 'ph
{
  unfold (Alloc.is_phase phase 'g 'ph);
  with v. assert (R.pts_to phase v);
  phase_rel_heads 'g g' v 'ph;
  fold (Alloc.is_phase phase g' 'ph)
}

ghost
fn phase_idle (phase: R.ref Alloc.phase_state) (g': heap)
  requires Alloc.is_phase phase 'g Ph.Idle
  ensures Alloc.is_phase phase g' Ph.Idle
{
  unfold (Alloc.is_phase phase 'g Ph.Idle);
  fold (Alloc.is_phase phase g' Ph.Idle)
}

/// A nursery object's size is far below a header's limit.
let wz_small (obj wz: nat)
  : Lemma (requires obj + wz * 8 <= minor_heap_size) (ensures wz < pow2 54)
  = FStar.Math.Lemmas.pow2_plus 54 3;
    assert_norm (pow2 3 == 8)

/// Promote one minor-heap object to the major heap, at the collector's phase.
/// Returns the new address in major heap (0UL on OOM).
///
/// The promotion runs at the phase the record holds, which it keeps derived
/// from the heap: the allocation does (`Alloc.allocate`), and the copy of
/// the fields writes no header (`GC.Gen.SweptTail.promote_heads`).  Nothing
/// of pointer closure is needed: during a promotion loop it is temporarily
/// violated (minor pointers are written into the major heap body).
#push-options "--z3rlimit 25 --fuel 0 --ifuel 0"
inline_for_extraction
fn promote_one (minor: minor_heap_t) (major: heap_t) (fp_ref: R.ref U64.t)
               (phase: R.ref Alloc.phase_state) (obj: U64.t)
  requires is_minor minor 'md 'mb **
           is_heap major 'ms **
           R.pts_to fp_ref 'fp **
           Alloc.is_phase phase 'ms 'ph **
           pure (U64.v obj >= 8 /\ U64.v obj < minor_heap_size /\
                 U64.v obj % 8 == 0 /\
                 U64.v obj + minor_wosize {data='md; bump='mb} obj * 8 <= minor_heap_size /\
                 FLA.fl_ascending 'ms 'fp)
  returns new_addr: U64.t
  ensures exists* md2 mb2 ms2 fp2.
    is_minor minor md2 mb2 **
    is_heap major ms2 **
    R.pts_to fp_ref fp2 **
    Alloc.is_phase phase ms2 'ph **
    pure (let minor_st = {data='md; bump='mb} in
          let wz = minor_wosize minor_st obj in
          md2 == 'md /\ mb2 == 'mb /\
          GC.Spec.Fields.blocks_fit ms2 /\
          GC.Spec.Allocator.Lemmas.fl_valid ms2 fp2 heap_words /\
          GC.Spec.Allocator.Lemmas.fl_chain_terminates ms2 fp2 heap_words /\
          FLA.fl_ascending ms2 fp2 /\
          (wz > 0 ==>
            (let spec_res = PromoteSpec.promote_object minor_st 'ms obj 'fp wz 'ph in
             ms2 == spec_res.major_out /\
             fp2 == spec_res.fp_out /\
             new_addr == spec_res.new_addr)) /\
          (wz == 0 ==> ms2 == 'ms /\ fp2 == 'fp /\ new_addr == 0UL))
{
  GC.Spec.SweepPhase.Util.part1_holds 'ms;
  FLA.fl_ascending_valid 'ms 'fp;
  // Read the wosize from the minor object header
  let wosize = read_minor_wosize minor obj;
  if U64.eq wosize 0UL {
    // Zero-sized object, nothing to copy
    0UL
  } else {
    // The copy is allocated with the minor object's tag, as
    // `caml_alloc_shr (wosize, tag)` does, so its header is written once.
    let minor_hdr = minor_read minor (U64.sub obj 8UL);
    let tag = Obj.getTag minor_hdr;
    // Connect impl tag to spec minor_tag and establish bound
    minor_tag_bound {data='md; bump='mb} obj;
    assert (pure (U64.v tag == minor_tag {data='md; bump='mb} obj));
    assert (pure (tag == PromoteSpec.promoted_tag {data='md; bump='mb} obj));
    // The allocation is at the phase the record holds, and keeps its caches
    // derived; the copy below writes no header.
    wz_small (U64.v obj) (U64.v wosize);
    ST.promote_heads 'ph 'ms 'fp {data='md; bump='mb} obj (U64.v wosize);
    FLAsc.promote_object_preserves_fl_ascending {data='md; bump='mb} 'ms obj 'fp (U64.v wosize) 'ph;
    PromoteSpec.promote_object_preserves_alloc_invariants {data='md; bump='mb} 'ms obj 'fp (U64.v wosize) 'ph;
    let new_obj = Alloc.allocate major fp_ref phase wosize tag;
    AP.alloc_at_fields 'ph 'ms 'fp (U64.v wosize) tag;
    if U64.eq new_obj 0UL {
      // OOM: nothing changes
      PromoteSpec.promote_object_oom {data='md; bump='mb} 'ms obj 'fp (U64.v wosize) 'ph;
      0UL
    } else {
      // Derive bounds from allocator postconditions:
      AP.alloc_at_obj_body_within_heap 'ph 'ms 'fp (U64.v wosize) tag;
      AP.alloc_at_obj_wosize 'ph 'ms 'fp (U64.v wosize) tag;
      assert (pure (U64.v new_obj >= U64.v mword /\
                    U64.v new_obj < heap_size /\
                    U64.v new_obj % U64.v mword == 0));
      assert (pure (U64.v new_obj + U64.v wosize * 8 <= heap_size));
      PromoteSpec.promote_object_success {data='md; bump='mb} 'ms obj 'fp (U64.v wosize) 'ph;
      // Copy all fields (0..wosize-1) from minor to major
      copy_fields_loop minor major obj new_obj wosize;
      with ms2. assert (is_heap major ms2);
      phase_heads phase ms2;
      new_obj
    }
  }
}
#pop-options
