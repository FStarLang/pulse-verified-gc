module GC.SPOT.ThreeObjects.Clean

/// Clean 3-object SPOT using allocator-based construction
///
/// Heap structure:
/// - Major: Object C (wosize=1) pointing to minor object A
/// - Minor: Object A (wosize=1), Object B (wosize=1)
/// - Roots: [A]
/// - Remembered set: [&C.field0]
///
/// Expected result:
/// - A promoted to major heap
/// - B collected
/// - C.field0 updated to point to promoted A

#lang-pulse

open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Allocator
module SpecAlloc = GC.Spec.Allocator
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Impl.MinorHeap
open GC.Gen.Impl
open GC.Impl.Heap
open GC.Impl.Allocator

module EmptyLemmas = GC.SPOT.EmptyHeapLemmas
module GenInv = GC.Gen.HeapInvariant
module Cheney = GC.Gen.Impl.Cheney  
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module MinorFwd = GC.Gen.MinorCollectForwarding
module RBridge = GC.Gen.ReachabilityBridge

/// Platform assumption
assume val platform_fits_u64 : squash SZ.fits_u64

let sz (n: nat{n < pow2 64}) : (s:SZ.t{SZ.v s == n}) =
  assert (SZ.fits_u64);
  SZ.uint64_to_sizet (U64.uint_to_t n)

let heap_size_fits () : Lemma (heap_size < pow2 64) =
  FStar.Math.Lemmas.pow2_lt_compat 64 57

let fwd_array_size_fits () : Lemma (UpdatePtrs.fwd_array_size < pow2 64) =
  FStar.Math.Lemmas.pow2_lt_compat 64 57

```pulse
fn three_object_spot ()
  requires emp
  returns _:unit
  ensures emp
{
  /// Phase 1: Create major heap with init_heap
  heap_size_fits ();
  let heap_sz = sz heap_size;
  let heap_bytes = A.alloc 0uy heap_sz;
  let major_heap : heap_t = { data = heap_bytes; size = heap_sz };
  
  rewrite (A.pts_to heap_bytes (Seq.create (SZ.v heap_sz) 0uy))
       as (A.pts_to major_heap.data (Seq.create heap_size 0uy));
  fold (is_heap major_heap (Seq.create heap_size 0uy));
  
  // Initialize to single blue block
  let fp_init = init_heap major_heap;
  
  /// Phase 2: Allocate object C in major heap
  // TODO: Use allocator to allocate C
  // For now, we'll work with the init_heap state
  
  /// Phase 3: Create minor heap and allocate A, B
  let minor = alloc_minor_heap ();
  
  // TODO: Use minor allocator to allocate A and B
  
  /// Phase 4: Set up pointers
  // C.field0 := A
  // A.field0 := some_value
  // B.field0 := some_value
  
  /// Phase 5: Create GC parameter arrays
  fwd_array_size_fits ();
  let fwd_arr = A.alloc 0UL (sz UpdatePtrs.fwd_array_size);
  let queue = A.alloc 0UL (sz Cheney.queue_size);
  
  // 1 root (A)
  let roots = A.alloc 0UL (sz 1);
  
  // 1 slot (C.field0 address)
  let slots = A.alloc 0UL (sz 1);
  
  /// Phase 6: Prove preconditions
  // TODO: Systematic precondition proofs
  admit();
  
  /// Phase 7: Call GC
  unfold (is_heap major_heap);
  with major_data. assert (A.pts_to major_heap.data major_data);
  unfold (is_minor minor);
  with minor_data minor_bump. assert (A.pts_to minor.data minor_data);
  
  fold (is_heap major_heap major_data);
  fold (is_minor minor minor_data minor_bump);
  
  let fp_ref = R.alloc fp_init;
  let gh : gen_heap_t = { minor = minor; major = major_heap; fp_ref = fp_ref };
  
  rewrite each (is_heap major_heap major_data) as (is_heap gh.major major_data);
  rewrite each (is_minor minor minor_data minor_bump) as (is_minor gh.minor minor_data minor_bump);
  rewrite each (R.pts_to fp_ref fp_init) as (R.pts_to gh.fp_ref fp_init);
  fold (is_gen_heap gh minor_data minor_bump major_data fp_init);
  
  let nroots = sz 1;
  let nslots = sz 1;
  
  with roots_seq fwd_seq slots_seq. assert (
    A.pts_to roots roots_seq **
    A.pts_to fwd_arr fwd_seq **
    A.pts_to slots slots_seq
  );
  
  // Preconditions (currently admitted)
  admit();
  
  let ok = minor_collect_full gh roots nroots fwd_arr queue slots nslots;
  
  /// Phase 8: Prove postconditions
  // TODO: Prove isomorphism properties
  admit();
  
  // Cleanup
  unfold (is_gen_heap gh);
  unfold (is_heap gh.major);
  with major_final. assert (A.pts_to gh.major.data major_final);
  A.free gh.major.data;
  
  unfold (is_minor gh.minor);
  with minor_final minor_bump_final. assert (A.pts_to gh.minor.data minor_final);
  A.free gh.minor.data;
  R.free gh.minor.bump_ref;
  
  with fp_final. assert (R.pts_to gh.fp_ref fp_final);
  R.free gh.fp_ref;
  
  A.free roots;
  A.free fwd_arr;
  A.free queue;
  A.free slots;
  
  ()
}
```
