(*
   GC.Gen.SPOT.Helpers — Helper Assumptions for Building Test Heaps
   
   For SPOT testing, we assume the existence of functions that construct
   heaps with specific object structures. This is analogous to having a
   test harness or heap builder library.
   
   In a production system, these would be implemented by:
   - Writing object headers at specific offsets
   - Linking objects in the free list
   - Proving heap invariants hold
   
   For a SPOT, we focus on testing the GC logic, not initialization.
*)

module GC.Gen.SPOT.Helpers

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.HeapInvariant
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module MinorCollectForwarding = GC.Gen.MinorCollectForwarding
module ReachabilityBridge = GC.Gen.ReachabilityBridge
module Header = GC.Lib.Header
module GenInv = GC.Gen.HeapInvariant

module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Seq = FStar.Seq

// Color shorthands
let white = Header.White
let black = Header.Black

/// ---------------------------------------------------------------------------
/// Minor Heap with Two Objects
/// ---------------------------------------------------------------------------

///----------------------------------------------------------------------------
/// Minor Heap with Two Objects
/// ---------------------------------------------------------------------------

/// Construct a minor heap containing two objects A and B:
/// - A at offset 0: wosize=1, tag=0, color=white
/// - B at offset 16: wosize=1, tag=0, color=white
/// - Bump pointer at 32 (past both objects)
assume val minor_with_two_objects : heap_bytes:Seq.seq U8.t{
  Seq.length heap_bytes == minor_heap_size
}

/// Address of object A in minor heap
assume val addr_A : obj_addr

/// Address of object B in minor heap  
assume val addr_B : obj_addr

/// Bump pointer value after allocating A and B
assume val bump_after_two : U64.t

/// The minor state with two objects
let minor_state_two : minor_state = {
  data = minor_with_two_objects;
  bump = bump_after_two
}

/// This minor state satisfies minor_heap_shape
assume val minor_two_objects_shape : squash (
  GenInv.minor_heap_shape minor_state_two)

/// ---------------------------------------------------------------------------
/// Major Heap with One Object Pointing to Minor
/// ---------------------------------------------------------------------------

/// Construct a major heap containing one object C:
/// - C at some address: wosize=1, tag=0, color=black, field[0] points to A
/// - Valid free list starting at fp
assume val major_with_one_object : 
  target:U64.t{is_val_addr target} ->  // The address C.field[0] points to (will be A)
  (major_heap:heap &
   addr_C:obj_addr &
   fp:U64.t &
   squash (
     // Object C exists with field pointing to target
     (let hdr_C = read_word major_heap (hd_address addr_C) in
      getWosize hdr_C == 1UL /\
      getTag hdr_C == 0UL /\
      getColor hdr_C == black) /\
     (let field_C_0 = read_word major_heap (f_address (addr_C, 0)) in
      field_C_0 == target) /\
     // Major heap satisfies major_heap_shape
     GenInv.major_heap_shape major_heap fp
   ))

/// ---------------------------------------------------------------------------
/// Combined Heap Configuration
/// ---------------------------------------------------------------------------

/// Build the complete initial heap state for the SPOT:
/// - Minor: objects A and B
/// - Major: object C pointing to A
/// - Roots: [A]
/// - Remembered set: [address of C.field[0]]
assume val build_spot_heap : unit -> (
  minor:minor_state &
  major:heap &
  fp:U64.t &
  roots:Seq.seq U64.t &
  slots:Seq.seq U64.t &
  squash (
    // Minor heap valid
    minor == minor_state_two /\
    GenInv.minor_heap_shape minor /\
    // Major heap valid
    GenInv.major_heap_shape major fp /\
    // Collection heap shape
    GenInv.collection_heap_shape minor major fp /\
    // Roots contain A
    Seq.length roots == 1 /\
    Seq.index roots 0 == addr_A /\
    // Remembered set contains C's field address
    Seq.length slots == 1 /\
    Seq.index slots 0 == f_address (addr_A, 0)
  ))

/// Preconditions for minor_collect_full hold on this heap
assume val spot_heap_preconditions : unit -> Lemma (
  let minor = get_minor () in
  let major = get_major () in
  let fp = get_fp () in
  let roots = get_roots () in
  let slots = get_slots () in
  let fwd = Seq.create UpdatePtrs.fwd_array_size 0UL in
  GenInv.collection_heap_shape minor major fp /\
  UpdatePtrs.ref_table_sound major slots 1 /\
  UpdatePtrs.ref_table_covers_minor_ptrs major slots 1 /\
  UpdatePtrs.slots_pairwise_distinct slots 1 /\
  MinorCollectForwarding.remembered_targets_in_roots major roots slots 1 /\
  ReachabilityBridge.major_field_zero_no_minor minor major /\
  ReachabilityBridge.roots_valid_nonblue roots major /\
  MinorCollectForwarding.roots_valid_for_minor_collection minor major roots /\
  Seq.length roots == 1 /\
  Seq.length fwd == UpdatePtrs.fwd_array_size /\
  (forall (i:nat). i < Seq.length fwd ==> Seq.index fwd i == 0UL)
)
