module GC.SPOT.SimpleAllocator

/// Simpler SPOT: Just demonstrate that we can use init_heap + init_heap_well_formed
/// to call the allocate function. This is the KEY blocker we've resolved.

#lang-pulse
open Pulse.Lib.Pervasives
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Allocator
open GC.Spec.Fields
open GC.Impl.Heap
open GC.Impl.Allocator
open GC.SPOT.InitHeapLemmas

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"

/// Demonstrate: init_heap + lemma enables allocate
fn simple_allocator_spot ()
  ensures emp ** pure (true)
{
  // Step 1: Create zeroed heap bytes
  let heap_sz = SZ.uint64_to_sizet (U64.uint_to_t heap_size);
  let heap_bytes = A.alloc 0uy heap_sz;
  
  // Step 2: Create heap_t
  let h : heap_t = { data = heap_bytes; size = heap_sz };
  
  // Step 3: Rewrite sequence to match expected type
  assert (pure (SZ.v heap_sz == heap_size));
  rewrite (A.pts_to heap_bytes (Seq.create (SZ.v heap_sz) 0uy))
       as (A.pts_to h.data (Seq.create heap_size 0uy));
  
  // Step 4: Fold is_heap predicate
  fold (is_heap h (Seq.create heap_size 0uy));
  
  // Step 4: Initialize heap
  let fp = init_heap h;
  
  // At this point:
  // - We have is_heap h s for some s
  // - (s, fp) == init_heap_spec (Seq.create heap_size 0uy)
  // - But we need well_formed_heap s to call allocate
  
  // Step 5: Extract ghost state and call lemma
  unfold (is_heap h);
  with s. assert (A.pts_to h.data s);
  
  // Call our infrastructure lemma!
  init_heap_well_formed s fp;
  
  // Now we have: well_formed_heap s
  // This unlocks the allocate function!
  
  // Step 6: Fold is_heap back
  fold (is_heap h s);
  
  // Step 7: Allocate an object
  let res = allocate h fp 2UL;  // wosize=2
  let new_fp = fst res;
  let obj_addr = snd res;
  
  // Success! We've proven the blocker is resolved.
  // obj_addr is either 0 (OOM) or a valid allocated object
  
  // Cleanup
  unfold (is_heap h);
  drop_ (A.pts_to h.data _);
  ()
}

#pop-options
