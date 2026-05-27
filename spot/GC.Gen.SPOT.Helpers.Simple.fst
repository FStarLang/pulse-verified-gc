(*
   GC.Gen.SPOT.Helpers.Simple — Helper Assumptions for Building Test Heaps
   
   For SPOT testing, we assume the existence of heap configurations with
   specific object structures. This separates testing GC logic from heap initialization.
*)

module GC.Gen.SPOT.Helpers.Simple

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Gen.Base
open GC.Gen.MinorHeap
module GenInv = GC.Gen.HeapInvariant

module U64 = FStar.UInt64
module Seq = FStar.Seq

/// ---------------------------------------------------------------------------
/// Minor Heap with Two Objects
/// ---------------------------------------------------------------------------

/// Minor heap bytes containing two objects A and B
assume val minor_with_two_objects : Seq.seq FStar.UInt8.t

/// Minor heap size constraint
assume val minor_size_valid : squash (
  Seq.length minor_with_two_objects == minor_heap_size)

/// Address of object A in minor heap (reachable)
assume val addr_A : obj_addr

/// Address of object B in minor heap (unreachable)  
assume val addr_B : obj_addr

/// Bump pointer after allocating A and B
assume val bump_after_two : U64.t

/// The minor state with two objects
let minor_state_two : minor_state = {
  data = minor_with_two_objects;
  bump = bump_after_two
}

/// Minor heap satisfies heap shape
assume val minor_heap_valid : squash (
  GenInv.minor_heap_shape minor_state_two)

/// ---------------------------------------------------------------------------
/// Major Heap with One Object Pointing to Minor
/// ---------------------------------------------------------------------------

/// Major heap containing object C
assume val major_with_C : heap

/// Address of object C in the major heap
assume val addr_C : obj_addr

/// Free pointer for the major heap
assume val fp_major : U64.t

/// Major heap satisfies heap shape
assume val major_heap_valid : squash (
  GenInv.major_heap_shape major_with_C fp_major)

/// Address of C's field[0] (assumed to be properly computed)
assume val c_field_0_addr : hp_addr

/// C's field[0] points to A  
assume val c_points_to_a : squash (
  read_word major_with_C c_field_0_addr == addr_A)

/// ---------------------------------------------------------------------------
/// Combined Configuration
/// ---------------------------------------------------------------------------

/// Root set contains A
let roots_with_A : Seq.seq U64.t = Seq.create 1 addr_A

/// Remembered set contains C's field address
let slots_with_C_field : Seq.seq U64.t = 
  Seq.create 1 (c_field_0_addr <: U64.t)

/// The complete heap satisfies collection_heap_shape
assume val collection_heap_valid : squash (
  GenInv.collection_heap_shape minor_state_two major_with_C fp_major)
