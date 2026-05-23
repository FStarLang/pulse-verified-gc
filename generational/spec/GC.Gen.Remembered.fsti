/// ---------------------------------------------------------------------------
/// GC.Gen.Remembered — Remembered set via major heap scanning
/// ---------------------------------------------------------------------------
///
/// For minor collection, we need to identify all major-heap objects that
/// contain pointers into the minor heap (inter-generational pointers).
/// These serve as additional roots for the minor collection.
///
/// Initial approach: scan the entire major heap linearly.
/// Future: write barrier that records stores into a card table.

module GC.Gen.Remembered

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap

/// ---------------------------------------------------------------------------
/// Types
/// ---------------------------------------------------------------------------

/// A remembered reference: (major_obj_addr, field_index) pair
/// indicating that major_obj_addr's field at index field_index
/// points into the minor heap.
noeq
type remembered_ref = {
  rem_obj   : obj_addr; // major-heap object containing the pointer
  rem_field : nat;      // 1-based field index within that object
  rem_target: U64.t;   // the minor-heap address being pointed to
}

/// ---------------------------------------------------------------------------
/// Scanning Spec
/// ---------------------------------------------------------------------------

/// Scan a single major-heap object for minor-heap pointers.
/// Returns the list of minor addresses referenced by this object's fields.
val scan_object_for_minor_refs (major: heap) (obj: obj_addr)
  : GTot (seq remembered_ref)

/// Scan the entire major heap for inter-generational pointers.
/// Walks all objects in the major heap and collects minor-heap references.
val scan_major_for_minor_refs (major: heap)
  : GTot (seq remembered_ref)

/// Extract just the minor-heap target addresses (the additional roots)
val minor_roots_from_major (major: heap)
  : GTot (seq U64.t)

/// ---------------------------------------------------------------------------
/// Correctness
/// ---------------------------------------------------------------------------

/// The scan finds ALL inter-generational pointers: if a major-heap object
/// has a field pointing into the minor heap, it appears in the result.
val scan_complete (major: heap) (obj: obj_addr) (field_idx: nat)
  : Lemma (requires
             well_formed_heap major /\
             Seq.mem obj (objects zero_addr major) /\
             field_idx >= 1 /\ field_idx < U64.v (wosize_of_object obj major) /\
             U64.v obj + field_idx * 8 + 8 <= heap_size /\
             (U64.v obj + field_idx * 8) % 8 == 0 /\
             is_minor_object_addr (read_word major (U64.uint_to_t (U64.v obj + field_idx * 8))))
           (ensures
             Seq.mem (read_word major (U64.uint_to_t (U64.v obj + field_idx * 8)))
                     (minor_roots_from_major major))

/// Soundness of the scan: every root returned by `minor_roots_from_major`
/// comes from an actual non-field-0 object field in the major heap.
val minor_roots_from_major_sound (major: heap) (v: U64.t)
  : Lemma (requires Seq.mem v (minor_roots_from_major major))
          (ensures
            exists (obj: obj_addr) (field_idx: nat).
              Seq.mem obj (objects zero_addr major) /\
              field_idx >= 1 /\
              field_idx < U64.v (wosize_of_object obj major) /\
              U64.v obj + field_idx * 8 + 8 <= heap_size /\
              (U64.v obj + field_idx * 8) % 8 == 0 /\
              read_word major (U64.uint_to_t (U64.v obj + field_idx * 8)) == v /\
              is_minor_object_addr v)
