/// ---------------------------------------------------------------------------
/// GC.Gen.ChunkedUpdate -- pointer rewriting over chunked major heaps
/// ---------------------------------------------------------------------------
///
/// Chunked-major analogue of the dense `GC.Gen.Promote.update_*` operations.
/// After Cheney promotion has populated a forwarding map, these functions
/// rewrite major fields that still contain minor pointers to their forwarded
/// major addresses.

module GC.Gen.ChunkedUpdate

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.Promote

module MH = GC.Spec.MajorHeap

val obj_in_single_chunk_range
  : obj:obj_addr -> Tot prop

val objects_in_single_chunk_range
  : objs:seq obj_addr -> idx:nat -> Tot prop

/// Checked major field slot address used by pointer update.
val chunked_update_field_slot
  : src:obj_addr -> i:nat -> GTot (option hp_addr)

val chunked_update_field_slot_zero
  : obj:obj_addr ->
    Lemma
      (requires U64.v obj + U64.v mword <= heap_size)
      (ensures chunked_update_field_slot obj 0 == Some obj)

/// Object metadata readers over an active chunked major heap.
val chunked_header_of_object
  : mh:MH.major_heap -> obj:obj_addr -> GTot (option U64.t)

val chunked_wosize_nat_of_object
  : mh:MH.major_heap -> obj:obj_addr -> GTot nat

val chunked_wosize_nat_header
  : mh:MH.major_heap -> obj:obj_addr -> hdr:U64.t ->
    Lemma
      (requires MH.read_word_in_major mh (hd_address obj) == Some hdr)
      (ensures
        chunked_wosize_nat_of_object mh obj == U64.v (getWosize hdr))

val chunked_is_blue
  : mh:MH.major_heap -> obj:obj_addr -> GTot bool

val chunked_is_blue_header
  : mh:MH.major_heap -> obj:obj_addr -> hdr:U64.t ->
    Lemma
      (requires MH.read_word_in_major mh (hd_address obj) == Some hdr)
      (ensures chunked_is_blue mh obj == (getColor hdr = GC.Lib.Header.Blue))

val chunked_is_no_scan
  : mh:MH.major_heap -> obj:obj_addr -> GTot bool

/// Two word slots do not overlap.
val chunked_words_disjoint
  : a:hp_addr -> b:hp_addr -> Tot prop

/// Rewrite one field slot if it contains a forwarded minor pointer.
val chunked_update_field
  : mh:MH.major_heap -> field_addr:hp_addr -> fwd:forwarding_map ->
    GTot MH.major_heap

/// A checked update slot for an active object is a payload word in the same
/// chunk as the object's header.
val chunked_update_field_slot_in_object_chunk
  : mh:MH.major_heap -> obj:obj_addr -> i:nat -> field_addr:hp_addr ->
    Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        i < chunked_wosize_nat_of_object mh obj /\
        chunked_update_field_slot obj i == Some field_addr)
      (ensures
        (let idx = MH.lookup_chunk_index_value mh (hd_address obj) in
        MH.lookup_chunk_index mh (hd_address obj) == Some idx /\
        idx < Seq.length mh /\
        MH.word_in_chunk (Seq.index mh idx) (hd_address obj) /\
        MH.word_in_chunk (Seq.index mh idx) field_addr /\
        MH.lookup_chunk_index mh field_addr == Some idx /\
        U64.v obj <= U64.v field_addr /\
        U64.v field_addr + U64.v mword <=
          U64.v obj +
            MH.object_wosize_in_chunk (Seq.index mh idx) obj *
              U64.v mword))

/// Updating one payload field of a known active major object preserves the
/// chunked major-heap shape and active object enumeration.
val chunked_update_field_preserves_wf_and_major_objects
  : mh:MH.major_heap -> obj:obj_addr -> i:nat -> field_addr:hp_addr ->
    fwd:forwarding_map ->
    Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        i < chunked_wosize_nat_of_object mh obj /\
        chunked_update_field_slot obj i == Some field_addr)
      (ensures
        MH.well_formed_major_heap (chunked_update_field mh field_addr fwd) /\
        MH.major_objects (chunked_update_field mh field_addr fwd) ==
          MH.major_objects mh /\
        chunked_header_of_object (chunked_update_field mh field_addr fwd) obj ==
          chunked_header_of_object mh obj)

/// Updating one field slot preserves reads from disjoint word slots.
val chunked_update_field_preserves_wf_and_read_disjoint
  : mh:MH.major_heap -> field_addr:hp_addr -> addr:hp_addr ->
    old:U64.t -> fwd:forwarding_map ->
    Lemma
      (requires
        MH.well_formed_major_heap mh /\
        MH.read_word_in_major mh addr == Some old /\
        chunked_words_disjoint field_addr addr)
      (ensures
        MH.well_formed_major_heap
          (chunked_update_field mh field_addr fwd) /\
        MH.read_word_in_major
          (chunked_update_field mh field_addr fwd) addr == Some old)

/// Update pointers in one object's fields.
val chunked_update_object_pointers
  : mh:MH.major_heap -> obj:obj_addr -> wosize:nat -> fwd:forwarding_map ->
    i:nat -> GTot MH.major_heap

/// Base case: no fields remain.
val chunked_update_object_pointers_done
  : mh:MH.major_heap -> obj:obj_addr -> wosize:nat -> fwd:forwarding_map ->
    i:nat ->
    Lemma
      (requires i >= wosize)
      (ensures chunked_update_object_pointers mh obj wosize fwd i == mh)

/// One valid-slot recursive step.
val chunked_update_object_pointers_step
  : mh:MH.major_heap -> obj:obj_addr -> wosize:nat -> fwd:forwarding_map ->
    i:nat -> field_addr:hp_addr ->
    Lemma
      (requires i < wosize /\
                chunked_update_field_slot obj i == Some field_addr)
      (ensures
        chunked_update_object_pointers mh obj wosize fwd i ==
        chunked_update_object_pointers
          (chunked_update_field mh field_addr fwd) obj wosize fwd (i + 1))

/// Invalid first slot stops the dense-compatible worker.
val chunked_update_object_pointers_invalid_slot
  : mh:MH.major_heap -> obj:obj_addr -> wosize:nat -> fwd:forwarding_map ->
    i:nat ->
    Lemma
      (requires i < wosize /\
                chunked_update_field_slot obj i == None)
      (ensures chunked_update_object_pointers mh obj wosize fwd i == mh)

/// Updating all remaining fields of one active major object preserves major
/// heap well-formedness and active object enumeration.
val chunked_update_object_pointers_preserves_wf_and_major_objects
  : mh:MH.major_heap -> obj:obj_addr -> wosize:nat ->
    fwd:forwarding_map -> i:nat ->
    Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        wosize == chunked_wosize_nat_of_object mh obj)
      (ensures
        (let mh' = chunked_update_object_pointers mh obj wosize fwd i in
        MH.well_formed_major_heap mh' /\
        MH.major_objects mh' == MH.major_objects mh /\
        chunked_header_of_object mh' obj == chunked_header_of_object mh obj))

/// Updating all remaining fields of one object preserves a read whose word slot
/// is disjoint from every remaining candidate field slot.
val chunked_update_object_pointers_preserves_read_disjoint
  : mh:MH.major_heap -> obj:obj_addr -> wosize:nat ->
    fwd:forwarding_map -> i:nat -> addr:hp_addr -> old:U64.t ->
    Lemma
      (requires
        MH.well_formed_major_heap mh /\
        MH.read_word_in_major mh addr == Some old /\
        (forall (k:nat) (field_addr:hp_addr).
          i <= k /\ k < wosize /\
          chunked_update_field_slot obj k == Some field_addr ==>
          chunked_words_disjoint field_addr addr))
      (ensures
        (let mh' = chunked_update_object_pointers mh obj wosize fwd i in
        MH.well_formed_major_heap mh' /\
        MH.read_word_in_major mh' addr == Some old))

/// Updating all remaining fields of one object preserves the header read of an
/// active object.
val chunked_update_object_pointers_preserves_header_read
  : mh:MH.major_heap -> obj:obj_addr -> wosize:nat ->
    fwd:forwarding_map -> i:nat -> h:obj_addr -> hdr:U64.t ->
    Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem h (MH.major_objects mh) /\
        wosize == chunked_wosize_nat_of_object mh obj /\
        MH.read_word_in_major mh (hd_address h) == Some hdr)
      (ensures
        (let mh' = chunked_update_object_pointers mh obj wosize fwd i in
        MH.well_formed_major_heap mh' /\
        MH.major_objects mh' == MH.major_objects mh /\
        MH.read_word_in_major mh' (hd_address h) == Some hdr))

/// Remaining explicit object-list entries are active in the current major heap.
val chunked_objects_members
  : mh:MH.major_heap -> objs:seq obj_addr -> idx:nat -> Tot prop

/// Update all objects in an explicit object list from index `idx`.
val chunked_update_all_objects_aux
  : mh:MH.major_heap -> objs:seq obj_addr -> fwd:forwarding_map -> idx:nat ->
    GTot MH.major_heap

/// Explicit-list update preserves major heap well-formedness and active object
/// enumeration when all remaining entries are active objects.
val chunked_update_all_objects_aux_preserves_wf_and_major_objects
  : mh:MH.major_heap -> objs:seq obj_addr -> fwd:forwarding_map -> idx:nat ->
    Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_objects_members mh objs idx)
      (ensures
        (let mh' = chunked_update_all_objects_aux mh objs fwd idx in
        MH.well_formed_major_heap mh' /\
        MH.major_objects mh' == MH.major_objects mh))

/// Update all pointers in active chunked major objects.
val chunked_update_major_pointers
  : mh:MH.major_heap -> fwd:forwarding_map -> GTot MH.major_heap

/// Top-level update preserves major heap well-formedness and active object
/// enumeration.
val chunked_update_major_pointers_preserves_wf_and_major_objects
  : mh:MH.major_heap -> fwd:forwarding_map ->
    Lemma
      (requires MH.well_formed_major_heap mh)
      (ensures
        MH.well_formed_major_heap (chunked_update_major_pointers mh fwd) /\
        MH.major_objects (chunked_update_major_pointers mh fwd) ==
          MH.major_objects mh)

/// Top-level update preserves the header read of any active object.
val chunked_update_major_pointers_preserves_header
  : mh:MH.major_heap -> fwd:forwarding_map -> h:obj_addr -> hdr:U64.t ->
    Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem h (MH.major_objects mh) /\
        MH.read_word_in_major mh (hd_address h) == Some hdr)
      (ensures
        MH.read_word_in_major
          (chunked_update_major_pointers mh fwd) (hd_address h) ==
        Some hdr)

/// Top-level update preserves a payload field of an active blue object.
val chunked_update_major_pointers_preserves_blue_field
  : mh:MH.major_heap -> fwd:forwarding_map -> h:obj_addr -> j:nat ->
    field_addr:hp_addr -> old:U64.t ->
    Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem h (MH.major_objects mh) /\
        chunked_is_blue mh h /\
        j < chunked_wosize_nat_of_object mh h /\
        chunked_update_field_slot h j == Some field_addr /\
        MH.read_word_in_major mh field_addr == Some old)
      (ensures
        MH.read_word_in_major
          (chunked_update_major_pointers mh fwd) field_addr == Some old)

/// Single-chunk metadata compatibility with the existing dense heap readers.
val chunked_is_blue_single_chunk_compat
  : g:heap -> obj:obj_addr ->
    Lemma
      (requires obj_in_single_chunk_range obj)
      (ensures
        chunked_is_blue (MH.single_chunk_major_heap g) obj ==
        is_blue obj g)

val chunked_is_no_scan_single_chunk_compat
  : g:heap -> obj:obj_addr ->
    Lemma
      (requires obj_in_single_chunk_range obj)
      (ensures
        chunked_is_no_scan (MH.single_chunk_major_heap g) obj ==
        is_no_scan obj g)

val chunked_wosize_nat_single_chunk_compat
  : g:heap -> obj:obj_addr ->
    Lemma
      (requires obj_in_single_chunk_range obj)
      (ensures
        chunked_wosize_nat_of_object (MH.single_chunk_major_heap g) obj ==
        U64.v (wosize_of_object obj g))

/// Single-field update compatibility with the dense update semantics.
val chunked_update_field_single_chunk_compat
  : g:heap -> field_addr:hp_addr -> fwd:forwarding_map ->
    Lemma
      (requires U64.v field_addr >= U64.v zero_addr /\
                U64.v field_addr + U64.v mword <= heap_size)
      (ensures
        chunked_update_field (MH.single_chunk_major_heap g) field_addr fwd ==
        MH.single_chunk_major_heap
          (let field_val = to_minor_offset (read_word g field_addr) in
           if is_minor_pointer field_val then
             let new_val = fwd field_val in
             if new_val <> 0UL then write_word g field_addr new_val else g
           else g))

/// Object-level update compatibility.
val chunked_update_object_pointers_single_chunk_compat
  : g:heap -> obj:obj_addr -> wosize:nat -> fwd:forwarding_map -> i:nat ->
    Lemma
      (requires obj_in_single_chunk_range obj)
      (ensures
        chunked_update_object_pointers
          (MH.single_chunk_major_heap g) obj wosize fwd i ==
        MH.single_chunk_major_heap
          (update_object_pointers g obj wosize fwd i))

/// Explicit-list all-object update compatibility.
val chunked_update_all_objects_aux_single_chunk_compat
  : g:heap -> objs:seq obj_addr -> fwd:forwarding_map -> idx:nat ->
    Lemma
      (requires objects_in_single_chunk_range objs idx)
      (ensures
        chunked_update_all_objects_aux
          (MH.single_chunk_major_heap g) objs fwd idx ==
        MH.single_chunk_major_heap
          (update_all_objects_aux g objs fwd idx))

/// Top-level major-pointer update compatibility.
val chunked_update_major_pointers_single_chunk_compat
  : g:heap -> fwd:forwarding_map ->
    Lemma
      (ensures
        chunked_update_major_pointers (MH.single_chunk_major_heap g) fwd ==
        MH.single_chunk_major_heap (update_major_pointers g fwd))
