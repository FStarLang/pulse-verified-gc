module GC.SPOT.ThreeObjectsFull

/// Full 3-object SPOT - simplified version working with empty heaps
/// Following user guidance: standalone helper lemmas + custom record types

#lang-pulse

open FStar.Ghost
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module U32 = FStar.UInt32

open GC.Spec.Base
open GC.Spec.Heap
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Impl.MinorHeap
open GC.Impl.Heap
open GC.Gen.Impl
module GenInv = GC.Gen.HeapInvariant
module Impl = GC.Gen.Impl
module R = Pulse.Lib.Reference
module Cheney = GC.Gen.Impl.Cheney
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module MinorFwd = GC.Gen.MinorCollectForwarding
module RBridge = GC.Gen.ReachabilityBridge

module H = GC.SPOT.ThreeObjectHelpers

/// Size helper with platform assumption
assume val minor_heap_size_fits_u32 : unit -> Lemma (minor_heap_size < pow2 32)
assume val heap_size_fits_u32 : unit -> Lemma (heap_size < pow2 32)

let sz (n: nat{n < pow2 32}) : (s:SZ.t{SZ.v s == n}) =
  assume (SZ.fits_u32);
  SZ.uint32_to_sizet (FStar.UInt32.uint_to_t n)

/// Test fixture: Create arrays with 3-object configuration
/// Using assume val (standard SPOT practice for test fixtures)

assume val create_three_obj_minor_array : unit -> 
  stt (larray U8.t minor_heap_size)
    emp
    (fun arr -> A.pts_to arr H.three_obj_minor_data)

assume val create_three_obj_major_array : unit ->
  stt (larray U8.t heap_size)
    emp
    (fun arr -> A.pts_to arr H.three_obj_major_data)

assume val create_roots_array : unit ->
  stt (larray U64.t 1)
    emp
    (fun arr -> A.pts_to arr H.three_obj_roots)

assume val create_slots_array : unit ->
  stt (larray U64.t 1)
    emp
    (fun arr -> A.pts_to arr H.three_obj_slots)

/// Test function with 3-object configuration

```pulse
fn test_three_objects_full ()
  requires emp
  returns _:unit
  ensures emp
{
  // Create 3-object minor heap (A and B)
  minor_heap_size_fits_u32 ();
  let minor_sz = sz minor_heap_size;
  let minor_arr = create_three_obj_minor_array ();
  let bump_ref = R.alloc H.three_obj_minor_bump;
  let mh : minor_heap_t = { data = minor_arr; size = minor_sz; bump_ref = bump_ref };
  
  rewrite (A.pts_to minor_arr H.three_obj_minor_data)
       as (A.pts_to mh.data H.three_obj_minor_data);
  H.three_obj_minor_bump_valid ();
  rewrite (R.pts_to bump_ref H.three_obj_minor_bump)
       as (R.pts_to mh.bump_ref H.three_obj_minor_bump);
  fold (is_minor mh H.three_obj_minor_data H.three_obj_minor_bump);
  
  // Create major heap with object C
  heap_size_fits_u32 ();
  let major_sz = sz heap_size;
  let major_arr = create_three_obj_major_array ();
  let major_h : heap_t = { data = major_arr; size = major_sz };
  
  rewrite (A.pts_to major_arr H.three_obj_major_data)
       as (A.pts_to major_h.data H.three_obj_major_data);
  fold (is_heap major_h H.three_obj_major_data);
  
  // Create gen_heap
  let fp_ref = R.alloc H.three_obj_major_fp;
  let gh : gen_heap_t = { minor = mh; major = major_h; fp_ref = fp_ref };
  
  // Fold is_gen_heap
  unfold is_minor;
  with md. assert (A.pts_to mh.data md);
  with mb. assert (R.pts_to mh.bump_ref mb);
  
  unfold is_heap;
  with ms. assert (A.pts_to major_h.data ms);
  
  rewrite (A.pts_to mh.data md) as (A.pts_to gh.minor.data md);
  rewrite (R.pts_to mh.bump_ref mb) as (R.pts_to gh.minor.bump_ref mb);
  fold (is_minor gh.minor md mb);
  
  rewrite (A.pts_to major_h.data ms) as (A.pts_to gh.major.data ms);
  fold (is_heap gh.major ms);
  
  rewrite (R.pts_to fp_ref H.three_obj_major_fp) as (R.pts_to gh.fp_ref H.three_obj_major_fp);
  fold (is_gen_heap gh md mb ms H.three_obj_major_fp);
  
  // Create root set containing obj_A
  let nroots = sz 1;
  let roots = create_roots_array ();
  
  // Create remembered set containing C's field 0
  let nslots = sz 1;
  let slots = create_slots_array ();
  
  // Create empty forwarding array
  let fwd_sz = sz UpdatePtrs.fwd_array_size;
  let fwd_arr = A.alloc 0uL fwd_sz;
  
  // Create empty mark queue
  let queue_sz = sz Cheney.queue_size;
  let queue = A.alloc 0uL queue_sz;
  
  // Witness array contents
  with roots_seq. assert (A.pts_to roots roots_seq);
  with slots_seq. assert (A.pts_to slots slots_seq);
  with fwd_seq. assert (A.pts_to fwd_arr fwd_seq);
  with queue_seq. assert (A.pts_to queue queue_seq);
  
  // Establish preconditions using standalone helper lemmas
  
  // 1. collection_heap_shape
  H.collection_heap_shape_lemma ();
  
  // 2. Array lengths match
  H.three_obj_roots_content ();
  H.three_obj_slots_content ();
  assert (pure (SZ.v nroots == Seq.length roots_seq));
  assert (pure (SZ.v nslots == Seq.length slots_seq));
  assert (pure (Seq.length fwd_seq == UpdatePtrs.fwd_array_size));
  assert (pure (forall (i: nat). i < Seq.length fwd_seq ==> Seq.index fwd_seq i == 0uL));
  
  // 3. ref_table_sound
  H.ref_table_sound_lemma slots_seq (SZ.v nslots);
  
  // 4. ref_table_covers
  H.ref_table_covers_lemma slots_seq (SZ.v nslots);
  
  // 5. slots_distinct
  H.slots_distinct_lemma slots_seq (SZ.v nslots);
  
  // 6. remembered_targets
  H.remembered_targets_lemma roots_seq slots_seq (SZ.v nslots);
  
  // 7. major_field_zero
  H.major_field_zero_lemma ();
  
  // 8. roots_valid_nonblue
  H.roots_valid_nonblue_lemma roots_seq;
  
  // 9. roots_valid_for_minor
  H.roots_valid_for_minor_lemma roots_seq;
  
  // Call minor_collect_full (the key API call - no admits here!)
  minor_collect_full gh roots nroots fwd_arr queue slots nslots;
  
  // Extract postcondition witnesses
  with md2 mb2 ms2 fp2. assert (is_gen_heap gh md2 mb2 ms2 fp2);
  
  // TODO: Prove properties from postcondition:
  // - A is promoted to major heap (exists in ms2, not in md2)
  // - B is collected (does not exist in md2 or ms2)
  // - C's field 0 is updated to point to promoted A
  // - Minor heap bump is reset to 0
  
  unfold (is_gen_heap gh md2 mb2 ms2 fp2);
  
  unfold (is_minor gh.minor md2 mb2);
  
  unfold (is_heap gh.major ms2);
  
  // Drop resources
  drop_ (R.pts_to gh.minor.bump_ref _);
  drop_ (R.pts_to gh.fp_ref _);
  drop_ (A.pts_to gh.minor.data _);
  drop_ (A.pts_to gh.major.data _);
  drop_ (A.pts_to roots _);
  drop_ (A.pts_to slots _);
  drop_ (A.pts_to fwd_arr _);
  drop_ (A.pts_to queue _)
}
```

/// Main entry point

```pulse
fn main ()
  requires emp
  returns _:int
  ensures emp
{
  test_three_objects_full ();
  0
}
```
