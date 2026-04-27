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
               (obj: U64.t)
  requires is_minor minor 'md 'mb **
           is_heap major 'ms **
           R.pts_to fp_ref 'fp **
           pure (U64.v obj >= 8 /\ U64.v obj < minor_heap_size /\
                 U64.v obj % 8 == 0)
  returns new_addr: U64.t
  ensures exists* md2 mb2 ms2 fp2.
    is_minor minor md2 mb2 **
    is_heap major ms2 **
    R.pts_to fp_ref fp2
