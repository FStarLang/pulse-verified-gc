(*
   Pulse GC (Generational) - Minor Heap Implementation Interface

   Bump-pointer allocator for the minor (young) generation.
   Objects are allocated sequentially; the entire heap is reset after
   a minor collection (no per-object deallocation).
*)

module GC.Gen.Impl.MinorHeap

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

/// ---------------------------------------------------------------------------
/// Types
/// ---------------------------------------------------------------------------

/// Minor heap is a byte array + mutable bump pointer
noeq
type minor_heap_t = {
  data : array U8.t;
  size : (n:SZ.t{SZ.v n == minor_heap_size});
  bump_ref : R.ref U64.t;
}

/// The heap predicate: indexes by the byte array content and bump offset.
/// Mirrors the pattern of GC.Impl.Heap.is_heap which indexes by heap_state.
let is_minor (mh: minor_heap_t) (d: minor_heap) (b: U64.t) : slprop =
  pts_to mh.data d **
  R.pts_to mh.bump_ref b **
  pure (U64.v b % 8 == 0 /\ U64.v b <= minor_heap_size)

/// ---------------------------------------------------------------------------
/// Allocation
/// ---------------------------------------------------------------------------

/// Bump-allocate an object in the minor heap.
/// Returns 0UL on OOM, or the object address (bump + 8) on success.
fn minor_alloc (mh: minor_heap_t) (wosize: U64.t) (tag: U64.t)
  requires is_minor mh 'd 'b **
           pure (U64.v wosize > 0 /\ U64.v wosize <= max_young_wosize /\
                 U64.v tag < 256)
  returns obj: U64.t
  ensures exists* d2 b2. is_minor mh d2 b2 **
    pure (
      (obj == 0UL ==> d2 == 'd /\ b2 == 'b) /\
      (obj <> 0UL ==> U64.v b2 % 8 == 0 /\ U64.v b2 <= minor_heap_size))

/// ---------------------------------------------------------------------------
/// Read / Write
/// ---------------------------------------------------------------------------

/// Read a 64-bit word from the minor heap at a word-aligned offset
fn minor_read (mh: minor_heap_t) (addr: U64.t)
  requires is_minor mh 'd 'b **
           pure (U64.v addr + 8 <= minor_heap_size /\ U64.v addr % 8 == 0)
  returns v: U64.t
  ensures is_minor mh 'd 'b **
          pure (v == minor_read_word_t 'd addr)

/// Write a 64-bit word to the minor heap at a word-aligned offset
fn minor_write (mh: minor_heap_t) (addr: U64.t) (v: U64.t)
  requires is_minor mh 'd 'b **
           pure (U64.v addr + 8 <= minor_heap_size /\ U64.v addr % 8 == 0)
  ensures is_minor mh (minor_write_word_t 'd addr v) 'b

/// ---------------------------------------------------------------------------
/// Reset (after minor collection)
/// ---------------------------------------------------------------------------

/// Reset the bump pointer to 0
fn minor_heap_reset (mh: minor_heap_t)
  requires is_minor mh 'd 'b
  ensures is_minor mh 'd 0UL

/// ---------------------------------------------------------------------------
/// Initialization
/// ---------------------------------------------------------------------------

/// Allocate a fresh minor heap (all zeros, bump = 0)
fn alloc_minor_heap (_: unit)
  requires emp
  returns mh: minor_heap_t
  ensures is_minor mh (Seq.create minor_heap_size 0uy) 0UL
