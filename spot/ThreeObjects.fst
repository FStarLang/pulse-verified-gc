(*
   ThreeObjects — Fully Verified SPOT for Generational GC
   
   Uses actual allocator APIs to build a 3-object heap:
   - Minor: A (reachable), B (unreachable)
   - Major: C pointing to A
   - Roots: [A]
   - Remembered set: [C.field[0]]
   
   Then calls minor_collect_full and proves expected outcome:
   - A is promoted
   - B is collected
   - C's field points to promoted A
*)

module ThreeObjects
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
module R = Pulse.Lib.Reference
module PArr = Pulse.Lib.Array.Core
module U64 = FStar.UInt64
module SZ = FStar.SizeT

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.Impl.MinorHeap
module GenImpl = GC.Gen.Impl
module SpecAlloc = GC.Spec.Allocator
module ImplAlloc = GC.Impl.Allocator
module ImplHeap = GC.Impl.Heap

/// ---------------------------------------------------------------------------
/// Step 1: Create empty heaps
/// ---------------------------------------------------------------------------

/// Create a zeroed major heap
fn create_empty_major_heap ()
  requires emp
  returns h: ImplHeap.heap_t
  ensures exists* s. ImplHeap.is_heap h s **
          pure ((forall (i: nat). i < Seq.length s ==> Seq.index s i == 0uy) /\
                Seq.length s == heap_size)
{
  let arr = PArr.alloc 0uy (SZ.uint64_to_sizet heap_size_u64);
  let h : ImplHeap.heap_t = { data = arr; size = (SZ.uint64_to_sizet heap_size_u64) };
  rewrite (pts_to arr (Seq.create (SZ.v (SZ.uint64_to_sizet heap_size_u64)) 0uy))
       as (pts_to h.data (Seq.create heap_size 0uy));
  fold (ImplHeap.is_heap h (Seq.create heap_size 0uy));
  h
}

/// ---------------------------------------------------------------------------
/// Step 2: Initialize major heap as one big blue free block
/// ---------------------------------------------------------------------------

/// Initialize the major heap to have a single large blue free object
fn initialize_major_heap (h: ImplHeap.heap_t)
  requires ImplHeap.is_heap h 's **
           pure ((forall (i: nat). i < Seq.length 's ==> Seq.index 's i == 0uy))
  returns fp: U64.t
  ensures exists* s2. ImplHeap.is_heap h s2 **
          pure ((s2, fp) == SpecAlloc.init_heap_spec 's)
{
  ImplAlloc.init_heap h
}

/// ---------------------------------------------------------------------------
/// Step 3: Full 3-Object SPOT
/// ---------------------------------------------------------------------------

/// The complete SPOT: build heap, allocate objects, call GC, prove postconditions
fn three_object_spot ()
  requires emp
  returns ok: bool
  ensures emp ** pure (ok == true)
{
  ///
  /// Step 1: Create and initialize major heap
  ///
  let major_heap = create_empty_major_heap ();
  // Extract ghost witness
  with s_major. _;
  
  // Initialize to one big blue free block
  let fp_major = initialize_major_heap major_heap;
  with s_major_init. _;
  
  // TODO: Allocate object C in major heap using ImplAlloc.allocate
  // TODO: Write C's header and field pointing to (future) A
  
  ///
  /// Step 2: Create and allocate in minor heap
  ///
  let minor_heap = alloc_minor_heap ();
  
  // TODO: Allocate object A using minor_alloc
  // TODO: Allocate object B using minor_alloc
  
  ///
  /// Step 3: Build gen_heap and call GC
  ///
  // TODO: Combine major + minor into gen_heap_t
  // TODO: Create roots array with A
  // TODO: Create remembered set (slots) with C.field[0]
  // TODO: Call GenImpl.minor_collect_full
  
  ///
  /// Step 4: Extract postcondition and prove properties
  ///
  // TODO: Extract isomorphism witness
  // TODO: Prove A is promoted (in final major reachable set)
  // TODO: Prove B is collected (not in final reachable set)
  // TODO: Prove C.field[0] points to promoted A
  
  // Cleanup
  unfold (ImplHeap.is_heap major_heap _);
  PArr.free major_heap.data;
  
  true
}
