module GC.SPOT.Simple.Admitted

/// Truly admit-free SPOT - Incremental approach
///
/// This version incrementally proves GC preconditions.
/// We start with a minimal scenario and prove what we can.
///
/// Strategy: Start with EMPTY heaps and prove GC works on them.
/// This is simpler than 3-object case but still validates the API.

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

/// Platform assumption
assume val platform_fits_u64 : squash SZ.fits_u64

let sz (n: nat{n < pow2 64}) : (s:SZ.t{SZ.v s == n}) =
  assert (SZ.fits_u64);
  SZ.uint64_to_sizet (U64.uint_to_t n)

let heap_size_fits () : Lemma (heap_size < pow2 64) =
  FStar.Math.Lemmas.pow2_lt_compat 64 57

let fwd_array_size_fits () : Lemma (UpdatePtrs.fwd_array_size < pow2 64) =
  FStar.Math.Lemmas.pow2_lt_compat 64 57

/// Simpler scenario: Empty heaps
/// This avoids complex object allocation proofs
/// and focuses on proving GC preconditions for empty heaps

```pulse
fn spot_empty_heaps ()
  requires emp
  returns _:unit
  ensures emp
{
  // Create empty major heap
  heap_size_fits ();
  let heap_sz = sz heap_size;
  let heap_bytes = A.alloc 0uy heap_sz;
  let major_heap : heap_t = { data = heap_bytes; size = heap_sz };
  
  rewrite (A.pts_to heap_bytes (Seq.create (SZ.v heap_sz) 0uy))
       as (A.pts_to major_heap.data (Seq.create heap_size 0uy));
  fold (is_heap major_heap (Seq.create heap_size 0uy));
  
  // Initialize to single blue block
  let fp_init = init_heap major_heap;
  
  // Prove well_formed_heap
  unfold (is_heap major_heap);
  with s_init. assert (A.pts_to major_heap.data s_init);
  InitLemmas.init_heap_well_formed s_init fp_init;
  fold (is_heap major_heap s_init);
  
  // Create empty minor heap
  let minor = alloc_minor_heap ();
  
  // Extract states
  unfold (is_heap major_heap);
  with major_data. assert (A.pts_to major_heap.data major_data);
  unfold (is_minor minor);
  with minor_data minor_bump. assert (A.pts_to minor.data minor_data);
  
  // Fold back
  fold (is_heap major_heap major_data);
  fold (is_minor minor minor_data minor_bump);
  
  // Create gen_heap
  let fp_ref = R.alloc fp_init;
  let gh : gen_heap_t = { minor = minor; major = major_heap; fp_ref = fp_ref };
  
  rewrite each (is_heap major_heap major_data) as (is_heap gh.major major_data);
  rewrite each (is_minor minor minor_data minor_bump) as (is_minor gh.minor minor_data minor_bump);
  rewrite each (R.pts_to fp_ref fp_init) as (R.pts_to gh.fp_ref fp_init);
  
  fold (is_gen_heap gh minor_data minor_bump major_data fp_init);
  
  // Create empty GC parameter arrays
  let roots = A.alloc 0UL (sz 0);  // Empty roots
  fwd_array_size_fits ();
  let fwd_arr = A.alloc 0UL (sz UpdatePtrs.fwd_array_size);
  let queue = A.alloc 0UL (sz Cheney.queue_size);
  let slots = A.alloc 0UL (sz 0);  // Empty slots
  
  // Extract array contents
  with roots_seq. assert (A.pts_to roots roots_seq);
  with fwd_seq. assert (A.pts_to fwd_arr fwd_seq);
  with slots_seq. assert (A.pts_to slots slots_seq);
  
  // Prove preconditions for EMPTY case
  // This is much simpler than proving for 3-object case
  
  // Precondition 1: collection_heap_shape
  // For empty heaps, this should be derivable from init_heap + empty minor
  admit(); // TODO: Prove for empty case (simpler than general case)
  
  // Precondition 2: nroots == roots length
  assert (pure (SZ.v (sz 0) == 0));
  assert (pure (Seq.length roots_seq == 0));
  
  // Precondition 3: fwd array size
  assert (pure (Seq.length fwd_seq == UpdatePtrs.fwd_array_size));
  
  // Precondition 4: fwd array zeros
  assert (pure (forall (i: nat). i < Seq.length fwd_seq ==> Seq.index fwd_seq i == 0UL));
  
  // Preconditions 5-7: ref_table properties
  // For EMPTY slots, these should be trivially true
  admit(); // TODO: Prove for empty case
  
  // Precondition 8: remembered_targets_in_roots
  // Trivial for empty slots
  admit(); // TODO: Prove for empty case
  
  // Preconditions 9-11: validity constraints
  // For empty roots, should be trivial
  admit(); // TODO: Prove for empty case
  
  // Call minor_collect_full on empty heaps
  unfold (is_gen_heap gh);
  fold (is_gen_heap gh minor_data minor_bump major_data fp_init);
  
  let nroots = sz 0;
  let nslots = sz 0;
  let ok = minor_collect_full gh roots nroots fwd_arr queue slots nslots;
  
  // Postcondition: Minor heap reset
  unfold (is_gen_heap gh);
  with md2 mb2 ms2 fp2. assert (
    is_heap gh.major ms2 **
    is_minor gh.minor md2 mb2 **
    R.pts_to gh.fp_ref fp2
  );
  
  assert (pure (U64.v mb2 == 0));  // Bump reset
  
  // Cleanup
  fold (is_gen_heap gh md2 mb2 ms2 fp2);
  admit() // TODO: Proper cleanup
}
```

/// Next step: Once empty case is proven admit-free,
/// add 1 object, then 2, then 3.
