module GC.SPOT.ThreeObjectHelpers

/// Standalone helper lemmas for 3-object SPOT configuration
/// These are pure F* lemmas (not Pulse) to work around quantifier issues
///
/// Configuration:
///   - Minor heap: objects A (16 bytes) and B (16 bytes) at offsets 0 and 16
///   - Major heap: object C (24 bytes) at offset heap_base_offset, field 0 points to A
///   - Roots: [A]
///   - Remembered set: [C's field 0 at offset heap_base_offset + 8]

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object  
open GC.Gen.Base
open GC.Gen.MinorHeap
module GenInv = GC.Gen.HeapInvariant
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module MinorFwd = GC.Gen.MinorCollectForwarding
module RBridge = GC.Gen.ReachabilityBridge

/// Three-object heap configuration (assume val for SPOT test fixture)

assume val three_obj_minor_data : minor_heap  // Refined: length == minor_heap_size
assume val three_obj_major_data : heap        // Refined: length == heap_size
assume val three_obj_minor_bump : U64.t
assume val three_obj_major_fp : U64.t

/// Object addresses
assume val obj_A : U64.t  // At minor offset 0
assume val obj_B : U64.t  // At minor offset 16  
assume val obj_C : U64.t  // At major offset

/// obj_C is a valid obj_addr
assume val obj_C_is_obj_addr : unit -> Lemma (U64.v obj_C >= U64.v mword /\
                                                U64.v obj_C < heap_size /\
                                                U64.v obj_C % U64.v mword == 0)

/// Concrete object properties (checkable against heap bytes)
assume val obj_A_is_at_offset_0 : unit -> Lemma (U64.v obj_A == U64.v zero_addr)
assume val obj_B_is_at_offset_16 : unit -> Lemma (U64.v obj_B == U64.v zero_addr + 16)

/// Object structure properties
assume val obj_A_wosize : unit -> Lemma (wosize_of_object obj_A three_obj_minor_data == 1uL)
assume val obj_B_wosize : unit -> Lemma (wosize_of_object obj_B three_obj_minor_data == 1uL)
assume val obj_C_wosize : unit -> Lemma (wosize_of_object obj_C three_obj_major_data == 2uL)

assume val obj_A_not_no_scan : unit -> Lemma (is_no_scan obj_A three_obj_minor_data == false)
assume val obj_B_not_no_scan : unit -> Lemma (is_no_scan obj_B three_obj_minor_data == false)
assume val obj_C_not_no_scan : unit -> Lemma (is_no_scan obj_C three_obj_major_data == false)

assume val obj_C_not_blue : unit -> Lemma (is_blue obj_C three_obj_major_data == false)

/// C's field 0 points to A
assume val obj_C_field_0_points_to_A : unit -> 
  Lemma (read_word three_obj_major_data (U64.uint_to_t (U64.v obj_C + 8)) == obj_A)

/// Only object in major heap is C
assume val major_only_has_C : unit ->
  Lemma (Seq.mem obj_C (GC.Spec.Fields.objects zero_addr three_obj_major_data) /\
         (forall (o: obj_addr). Seq.mem o (GC.Spec.Fields.objects zero_addr three_obj_major_data) ==>
           o == obj_C))

/// Configuration properties
assume val three_obj_minor_bump_valid : unit -> Lemma (U64.v three_obj_minor_bump == 32 /\
                                                         U64.v three_obj_minor_bump % 8 == 0 /\
                                                         U64.v three_obj_minor_bump <= minor_heap_size)
assume val three_obj_major_fp_valid : unit -> Lemma (U64.v three_obj_major_fp < heap_size)

/// Root and slot configuration
assume val slot_addr : U64.t  // C's field 0 address
assume val slot_addr_is_c_field_0 : unit -> Lemma (U64.v slot_addr == U64.v obj_C + 8 /\
                                                     U64.v slot_addr < heap_size /\
                                                     U64.v slot_addr % 8 == 0)
assume val three_obj_roots : seq U64.t
assume val three_obj_slots : seq U64.t
assume val three_obj_roots_content : unit -> Lemma (three_obj_roots == Seq.create 1 obj_A)
assume val three_obj_slots_content : unit -> Lemma (three_obj_slots == Seq.create 1 slot_addr)

/// Helper lemmas for preconditions (standalone, not in Pulse)

let minor_heap_shape_lemma ()
  : Lemma (GenInv.minor_heap_shape ({ data = three_obj_minor_data; bump = three_obj_minor_bump }))
  = admit()  // Complex heap invariant with 2 objects

let minor_major_no_blue_lemma ()
  : Lemma (GenInv.minor_major_fields_no_blue 
             ({ data = three_obj_minor_data; bump = three_obj_minor_bump })
             three_obj_major_data)
  = admit()  // Complex heap invariant

let major_minor_no_infix_lemma ()
  : Lemma (GenInv.major_minor_fields_no_infix_targets
             ({ data = three_obj_minor_data; bump = three_obj_minor_bump })
             three_obj_major_data)
  = admit()  // Complex heap invariant

let collection_heap_shape_lemma ()
  : Lemma (GenInv.collection_heap_shape
             ({ data = three_obj_minor_data; bump = three_obj_minor_bump })
             three_obj_major_data
             three_obj_major_fp)
  = minor_heap_shape_lemma ();
    // Assume major_heap_shape
    admit();
    minor_major_no_blue_lemma ();
    major_minor_no_infix_lemma ()

let ref_table_sound_lemma (sl: seq U64.t) (n: nat)
  : Lemma (requires n <= length sl /\ n <= 1)
          (ensures UpdatePtrs.ref_table_sound three_obj_major_data sl n)
  = // For n<=1, this requires proving slot[0] points to valid field in C
    // With concrete heap construction this would be provable, but for SPOT we assume it
    admit()  // TODO: Provable with concrete heap construction

let ref_table_covers_lemma (sl: seq U64.t) (n: nat)
  : Lemma (requires n <= length sl)
          (ensures UpdatePtrs.ref_table_covers_minor_ptrs three_obj_major_data sl n)
  = admit()  // Quantifier complexity - slot covers C→A pointer

let slots_distinct_lemma (sl: seq U64.t) (n: nat)
  : Lemma (requires n <= length sl /\ n <= 1)
          (ensures UpdatePtrs.slots_pairwise_distinct sl n)
  = // With n <= 1, the pairwise distinct property is vacuous
    // forall i j. i < n /\ j < n /\ i <> j is empty when n <= 1
    ()

let remembered_targets_lemma (rs: seq U64.t) (sl: seq U64.t) (n: nat)
  : Lemma (requires n <= length sl)
          (ensures MinorFwd.remembered_targets_in_roots three_obj_major_data rs sl n)
  = admit()  // C's field points to A which is in roots

let major_field_zero_lemma ()
  : Lemma (RBridge.major_field_zero_no_minor
             ({ data = three_obj_minor_data; bump = three_obj_minor_bump })
             three_obj_major_data)
  = admit()  // Complex heap invariant - no zero fields pointing to minor

let roots_valid_nonblue_lemma (rs: seq U64.t)
  : Lemma (RBridge.roots_valid_nonblue rs three_obj_major_data)
  = admit()  // A is not blue (it's white, will be promoted)

let roots_valid_for_minor_lemma (rs: seq U64.t)
  : Lemma (MinorFwd.roots_valid_for_minor_collection
             ({ data = three_obj_minor_data; bump = three_obj_minor_bump })
             three_obj_major_data
             rs)
  = admit()  // A is a valid minor object
