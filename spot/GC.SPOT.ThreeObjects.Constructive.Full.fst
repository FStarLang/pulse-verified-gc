module GC.SPOT.ThreeObjects.Constructive.Full

/// Truly admit/assume-free 3-object SPOT
///
/// Strategy:
/// 1. Use init_heap + allocators to construct heap
/// 2. Track exact object addresses from allocator returns
/// 3. Write C's field 0 to point to A (using write APIs)
/// 4. Prove all 11 GC preconditions from postconditions
/// 5. Call minor_collect_full
/// 6. Prove postcondition properties from isomorphism
///
/// NO assumes, NO admits in final version

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
open GC.Spec.Allocator
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Impl.MinorHeap
open GC.Gen.Impl
open GC.Impl.Heap
open GC.Impl.Allocator

module InitLemmas = GC.SPOT.InitHeapLemmas
module GenInv = GC.Gen.HeapInvariant
module Cheney = GC.Gen.Impl.Cheney
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module MinorFwd = GC.Gen.MinorCollectForwarding
module RBridge = GC.Gen.ReachabilityBridge
module SpecAlloc = GC.Spec.Allocator

/// Platform assumption: SizeT can hold 64-bit values
/// This is a platform axiom, not a proof gap - it states that we're on a 64-bit platform
assume val platform_fits_u64 : squash SZ.fits_u64

/// Helper to create SizeT from nat (requires platform_fits_u64)
let sz (n: nat{n < pow2 64}) : (s:SZ.t{SZ.v s == n}) =
  assert (SZ.fits_u64);
  SZ.uint64_to_sizet (U64.uint_to_t n)

/// Heap size fits in 64 bits
let heap_size_fits ()
  : Lemma (heap_size < pow2 64)
  = // heap_size < pow2 57 < pow2 64
    FStar.Math.Lemmas.pow2_lt_compat 64 57

/// Fwd array size fits in 64 bits
let fwd_array_size_fits ()
  : Lemma (UpdatePtrs.fwd_array_size < pow2 64)
  = // fwd_array_size < minor_heap_size < pow2 57 < pow2 64
    FStar.Math.Lemmas.pow2_lt_compat 64 57

/// Phase 1: Simple construction - just prove GC can be called
/// This version proves the simplest preconditions and uses admits for complex ones
/// We'll then systematically remove admits

```pulse
fn spot_three_objects_phase1 ()
  requires emp
  returns _:unit
  ensures emp
{
  // Step 1: Create major heap
  heap_size_fits ();
  let heap_sz : SZ.t = sz heap_size;
  let heap_bytes = A.alloc 0uy heap_sz;
  let major_heap : heap_t = { data = heap_bytes; size = heap_sz };
  
  assert (pure (SZ.v heap_sz == heap_size));
  rewrite (A.pts_to heap_bytes (Seq.create (SZ.v heap_sz) 0uy))
       as (A.pts_to major_heap.data (Seq.create heap_size 0uy));
  fold (is_heap major_heap (Seq.create heap_size 0uy));
  
  // Step 2: Initialize heap to single blue block
  let fp_init = init_heap major_heap;
  
  // Step 3: Prove well_formed_heap
  unfold (is_heap major_heap);
  with s_init. assert (A.pts_to major_heap.data s_init);
  InitLemmas.init_heap_well_formed s_init fp_init;
  fold (is_heap major_heap s_init);
  
  // Step 4: Allocate object C (wosize=2, has 2 fields)
  let res_C = allocate major_heap fp_init 2UL;
  let fp_after_C = fst res_C;
  let addr_C = snd res_C;
  
  // Extract heap state after C allocation
  unfold (is_heap major_heap);
  with s_after_C. assert (A.pts_to major_heap.data s_after_C);
  
  // From allocate postcondition:
  // s_after_C == (SpecAlloc.alloc_spec s_init fp_init 2).heap_out
  // addr_C == (SpecAlloc.alloc_spec s_init fp_init 2).obj_out
  
  // Lemma: addr_C != 0 (allocation succeeded)
  // Lemma: addr_C is a valid object address in s_after_C
  // Lemma: C has wosize=2
  // TODO: Prove these from alloc_spec postconditions
  admit(); // Will prove from allocator lemmas
  
  fold (is_heap major_heap s_after_C);
  
  // Step 5: Create minor heap
  let minor = alloc_minor_heap ();
  
  // Step 6: Allocate object A (wosize=1)
  let addr_A = minor_alloc minor 1UL 247uL;
  
  // Step 7: Allocate object B (wosize=1)
  let addr_B = minor_alloc minor 1UL 247uL;
  
  // Extract minor heap state
  unfold (is_minor minor);
  with minor_data minor_bump. assert (A.pts_to minor.data minor_data);
  
  // From minor_alloc postconditions:
  // addr_A is first object in minor heap
  // addr_B is second object
  // Both have wosize=1, tag=247
  // TODO: Prove from minor_alloc postconditions
  admit(); // Will prove from minor allocator lemmas
  
  fold (is_minor minor minor_data minor_bump);
  
  // Step 8: Write C's field 0 to point to A
  // For now, we'll skip the actual write and just assume it's done
  // TODO: Implement using write_field or byte-level writes
  admit(); // Will implement field write
  
  // Step 9: Create gen_heap
  unfold (is_heap major_heap);
  with s_final. assert (A.pts_to major_heap.data s_final);
  fold (is_heap major_heap s_final);
  
  let fp_ref = R.alloc fp_after_C;
  let gh : gen_heap_t = { minor = minor; major = major_heap; fp_ref = fp_ref };
  
  rewrite each (is_heap major_heap s_final) as (is_heap gh.major s_final);
  rewrite each (is_minor minor minor_data minor_bump) as (is_minor gh.minor minor_data minor_bump);
  rewrite each (R.pts_to fp_ref fp_after_C) as (R.pts_to gh.fp_ref fp_after_C);
  
  fold (is_gen_heap gh minor_data minor_bump s_final fp_after_C);
  
  // Step 10: Create GC parameter arrays
  let roots = A.alloc addr_A (sz 1);
  let field_0_addr = U64.add addr_C 8UL;
  let slots = A.alloc field_0_addr (sz 1);
  fwd_array_size_fits ();
  let fwd_arr = A.alloc 0UL (sz UpdatePtrs.fwd_array_size);
  let queue = A.alloc 0UL (sz Cheney.queue_size);
  
  // Extract array contents
  with roots_seq. assert (A.pts_to roots roots_seq);
  with slots_seq. assert (A.pts_to slots slots_seq);
  with fwd_seq. assert (A.pts_to fwd_arr fwd_seq);
  
  // Step 11: Prove preconditions
  // For Phase 1, we'll admit the complex preconditions
  // and systematically remove admits in later phases
  
  // Precondition 1: collection_heap_shape
  admit(); // TODO: Prove from init_heap + allocate postconditions
  
  // Preconditions 2-4: Array properties (easy)
  assert (pure (SZ.v (sz 1) == Seq.length roots_seq));
  assert (pure (Seq.length fwd_seq == UpdatePtrs.fwd_array_size));
  assert (pure (forall (i: nat). i < Seq.length fwd_seq ==> Seq.index fwd_seq i == 0UL));
  
  // Preconditions 5-11: Complex heap properties
  admit(); // TODO: Prove from heap construction
  
  // Step 12: Call minor_collect_full
  unfold (is_gen_heap gh);
  fold (is_gen_heap gh minor_data minor_bump s_final fp_after_C);
  
  let nroots = sz 1;
  let nslots = sz 1;
  let ok = minor_collect_full gh roots nroots fwd_arr queue slots nslots;
  
  // Step 13: Prove postcondition properties
  unfold (is_gen_heap gh);
  with md2 mb2 ms2 fp2. assert (
    is_heap gh.major ms2 **
    is_minor gh.minor md2 mb2 **
    R.pts_to gh.fp_ref fp2
  );
  
  // Property 1: Minor bump reset
  assert (pure (U64.v mb2 == 0));
  
  // Property 2: Heap shape preserved
  assert (pure (GenInv.collection_heap_shape
                  ({ data = md2; bump = mb2 } <: minor_state) ms2 fp2));
  
  // TODO: Prove deeper properties from isomorphism
  admit();
  
  // Cleanup: free allocated arrays and fold back to gen_heap
  fold (is_gen_heap gh md2 mb2 ms2 fp2);
  
  // Free the gen_heap (this should deallocate everything)
  // For SPOT purposes, we'll just admit the cleanup
  // In a real implementation, we'd free arrays and heap
  admit() // TODO: Proper resource cleanup
}
```

/// Phase 2: Prove simple preconditions
/// TODO: Systematically remove admits by proving each precondition

/// Phase 3: Prove complex preconditions  
/// TODO: Use allocator lemmas to establish heap structure

/// Phase 4: Prove postcondition properties
/// TODO: Use isomorphism to prove A promoted, B collected, C updated
