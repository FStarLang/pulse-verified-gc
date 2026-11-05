/// ---------------------------------------------------------------------------
/// GC.Gen.Impl.Promote — Pulse implementation of minor→major promotion
/// ---------------------------------------------------------------------------
///
/// Copies live minor objects to the major heap during minor collection.

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
module PromoteSpec = GC.Gen.Promote
module Alloc = GC.Impl.Allocator
module Ph = GC.Spec.Phase
module FLA = GC.Spec.FreeList.Ascending

/// ---------------------------------------------------------------------------
/// Read wosize from a minor heap object header
/// ---------------------------------------------------------------------------

inline_for_extraction
fn read_minor_wosize (minor: minor_heap_t) (obj: U64.t)
  requires is_minor minor 'md 'mb **
           pure (U64.v obj >= 8 /\ U64.v obj < minor_heap_size /\ U64.v obj % 8 == 0)
  returns wosize: U64.t
  ensures is_minor minor 'md 'mb **
          pure (U64.v wosize == minor_wosize {data='md; bump='mb} obj)

inline_for_extraction
fn read_minor_tag (minor: minor_heap_t) (obj: U64.t)
  requires is_minor minor 'md 'mb **
           pure (U64.v obj >= 8 /\ U64.v obj < minor_heap_size /\ U64.v obj % 8 == 0)
  returns tag: U64.t
  ensures is_minor minor 'md 'mb **
          pure (U64.v tag == minor_tag {data='md; bump='mb} obj)

/// Read the number of fields the collector may scan in a minor object: 0 for a
/// no-scan object (tag >= 251), whose body is raw data, and the full wosize
/// otherwise.  See `GC.Gen.MinorHeap.minor_scan_wosize`.
inline_for_extraction
fn read_minor_scan_wosize (minor: minor_heap_t) (obj: U64.t)
  requires is_minor minor 'md 'mb **
           pure (U64.v obj >= 8 /\ U64.v obj < minor_heap_size /\ U64.v obj % 8 == 0)
  returns wosize: U64.t
  ensures is_minor minor 'md 'mb **
          pure (U64.v wosize == minor_scan_wosize {data='md; bump='mb} obj)

/// ---------------------------------------------------------------------------
/// The allocator at the collector's phase
/// ---------------------------------------------------------------------------

/// **Allocate at the phase the record holds**, keeping its caches the ones
/// derived from the heap (`Alloc.is_phase`): `Alloc.allocate`, whose in-place
/// update of `swept_tail` (`Alloc.record_after_alloc`) is the derived one
/// after the allocation (`GC.Gen.SweptTail.alloc_caches`) -- which needs the
/// free list exact and ascending while sweeping.  The phase stays as it is.
inline_for_extraction
fn allocate_at_phase (heap: heap_t) (fp: U64.t) (phase: R.ref Alloc.phase_state)
                     (wosize: U64.t) (tag: U64.t{U64.v tag < 256})
  requires is_heap heap 's ** Alloc.is_phase phase 's 'ph **
           pure (U64.v wosize >= 1 /\ (Ph.Sweeping? 'ph ==> FLA.fl_ascending 's fp))
  returns res: (U64.t & U64.t)
  ensures exists* s2. is_heap heap s2 ** Alloc.is_phase phase s2 'ph **
    pure (let spec_res = GC.Spec.Allocator.Cursor.alloc_phase 's fp 'ph (U64.v wosize) tag in
          s2 == spec_res.GC.Spec.Allocator.heap_out /\
          fst res == spec_res.GC.Spec.Allocator.fp_out /\
          snd res == spec_res.GC.Spec.Allocator.obj_out)

/// A change that keeps the walk and every header keeps the phase record's
/// caches derived.
ghost
fn phase_heads (phase: R.ref Alloc.phase_state) (g': heap)
  requires Alloc.is_phase phase 'g 'ph ** pure (GC.Spec.SweepPhase.Intrinsic.same_heads 'g g')
  ensures Alloc.is_phase phase g' 'ph

/// Idle, the record holds the phase whatever the heap.
ghost
fn phase_idle (phase: R.ref Alloc.phase_state) (g': heap)
  requires Alloc.is_phase phase 'g Ph.Idle
  ensures Alloc.is_phase phase g' Ph.Idle

/// ---------------------------------------------------------------------------
/// Promote a single object from minor heap to major heap.
///
/// 1. Read wosize from minor object header
/// 2. Allocate in major heap
/// 3. Copy fields from minor to major
///
/// Returns the new major-heap address (0 if OOM).
/// ---------------------------------------------------------------------------

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
