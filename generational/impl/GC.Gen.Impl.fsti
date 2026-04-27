(*
   Pulse GC (Generational) - Top-Level Entry Point Interface

   Provides:
   - gen_alloc: Allocate an object (routes to minor or major by size)
   - minor_collect: Promote live minor objects to major heap
   - major_collect: Full mark-sweep-coalesce on major heap
*)

module GC.Gen.Impl

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
module SpecFields = GC.Spec.Fields

/// ---------------------------------------------------------------------------
/// Combined generational heap state
/// ---------------------------------------------------------------------------

/// The generational GC state: minor heap + major heap + free-list pointer
noeq
type gen_heap_t = {
  minor : minor_heap_t;
  major : heap_t;
  fp_ref : R.ref U64.t;    // major heap free-list head
}

/// Combined slprop for the generational heap
let is_gen_heap (gh: gen_heap_t) (d: minor_heap) (b: U64.t)
                (s: heap_state) (fp: U64.t) : slprop =
  is_minor gh.minor d b **
  is_heap gh.major s **
  R.pts_to gh.fp_ref fp

/// ---------------------------------------------------------------------------
/// Allocation
/// ---------------------------------------------------------------------------

/// Allocate an object. Small objects go to minor heap, large ones to major.
/// Returns 0UL on failure (both heaps full).
fn gen_alloc (gh: gen_heap_t) (wosize: U64.t) (tag: U64.t)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pure (U64.v wosize > 0 /\ U64.v tag < 256 /\
                 SpecFields.well_formed_heap 's)
  returns obj: U64.t
  ensures exists* d2 b2 s2 fp2. is_gen_heap gh d2 b2 s2 fp2

/// ---------------------------------------------------------------------------
/// Minor collection
/// ---------------------------------------------------------------------------

/// Trigger a minor collection: promote all minor objects to major heap,
/// then reset the minor heap.
fn minor_collect (gh: gen_heap_t)
  requires is_gen_heap gh 'd 'b 's 'fp
  ensures exists* d2 b2 s2 fp2. is_gen_heap gh d2 b2 s2 fp2 **
          pure (U64.v b2 == 0)  // minor heap reset after collection
