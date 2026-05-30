module GC.SPOT.ConcreteMajor

module U64 = FStar.UInt64

open GC.Spec.Base

module SpecHeap = GC.Spec.Heap
module SpecObj = GC.Spec.Object
module SpecFields = GC.Spec.Fields
module GenInv = GC.Gen.HeapInvariant
module Layout = GC.SPOT.Layout

val spot_major_room : prop

val spot_c
  : (r:unit{spot_major_room}) ->
    Tot (c:obj_addr{U64.v c + GC.SPOT.Layout.c_to_a_field_index * 8 + 8 <= heap_size})
val spot_c_field0 : (r:unit{spot_major_room}) -> Tot hp_addr
val spot_c_field1 : (r:unit{spot_major_room}) -> Tot hp_addr
val spot_free_header : (r:unit{spot_major_room}) -> Tot hp_addr
val spot_free_obj : (r:unit{spot_major_room}) -> Tot obj_addr
val spot_free_wosize : (r:unit{spot_major_room}) -> Tot (n:nat{n < pow2 54})

val spot_major_heap : (r:unit{spot_major_room}) -> Tot heap
val spot_major_fp : (r:unit{spot_major_room}) -> Tot U64.t

val spot_major_layout_facts
  : r:unit{spot_major_room} ->
    Lemma (ensures
      U64.v (spot_c r) == U64.v zero_addr + 8 /\
      U64.v (spot_c_field0 r) == U64.v (spot_c r) /\
      U64.v (spot_c_field1 r) == U64.v (spot_c r) + 8 /\
      U64.v (spot_free_header r) == U64.v zero_addr + 24 /\
      U64.v (spot_free_obj r) == U64.v zero_addr + 32 /\
      U64.v (spot_major_fp r) == U64.v (spot_free_obj r) /\
      spot_free_wosize r >= 1)

val spot_major_c_reads
  : r:unit{spot_major_room} ->
    Lemma (ensures (
      let major = spot_major_heap r in
      SpecObj.wosize_of_object (spot_c r) major == U64.uint_to_t Layout.c_wosize /\
      SpecHeap.read_word major (spot_c_field0 r) == 0UL /\
      SpecHeap.read_word major (spot_c_field1 r) == Layout.a_minor /\
      ~(SpecObj.is_blue (spot_c r) major) /\
      ~(SpecObj.is_gray (spot_c r) major) /\
      ~(SpecObj.is_black (spot_c r) major) /\
      ~(SpecObj.is_infix (spot_c r) major) /\
      ~(SpecObj.is_no_scan (spot_c r) major)))

val spot_major_free_reads
  : r:unit{spot_major_room} ->
    Lemma (ensures (
      let major = spot_major_heap r in
      SpecObj.wosize_of_object (spot_free_obj r) major ==
        U64.uint_to_t (spot_free_wosize r) /\
      SpecHeap.read_word major (spot_free_obj r) == 0UL /\
      SpecObj.is_blue (spot_free_obj r) major /\
      ~(SpecObj.is_gray (spot_free_obj r) major) /\
      ~(SpecObj.is_black (spot_free_obj r) major) /\
      ~(SpecObj.is_infix (spot_free_obj r) major) /\
      ~(SpecObj.is_no_scan (spot_free_obj r) major)))

val spot_major_objects
  : r:unit{spot_major_room} ->
    Lemma (ensures
      SpecFields.objects zero_addr (spot_major_heap r) ==
        FStar.Seq.cons (spot_c r)
          (FStar.Seq.cons (spot_free_obj r) FStar.Seq.empty))

val spot_major_c_mem
  : r:unit{spot_major_room} ->
    Lemma (ensures
      FStar.Seq.mem (spot_c r)
        (SpecFields.objects zero_addr (spot_major_heap r)))

val spot_major_free_mem
  : r:unit{spot_major_room} ->
    Lemma (ensures
      FStar.Seq.mem (spot_free_obj r)
        (SpecFields.objects zero_addr (spot_major_heap r)))

val spot_major_object_cases
  : r:unit{spot_major_room} -> obj:obj_addr ->
    Lemma (requires FStar.Seq.mem obj (SpecFields.objects zero_addr (spot_major_heap r)))
          (ensures obj == spot_c r \/ obj == spot_free_obj r)

val spot_major_free_field_read
  : r:unit{spot_major_room} -> j:nat ->
    Lemma (requires j < spot_free_wosize r /\
                    U64.v (spot_free_obj r) + j * 8 + 8 <= heap_size)
          (ensures
            SpecHeap.read_word (spot_major_heap r)
              (U64.uint_to_t (U64.v (spot_free_obj r) + j * 8)) == 0UL)

val spot_major_heap_shape
  : r:unit{spot_major_room} ->
    Lemma (ensures GenInv.major_heap_shape (spot_major_heap r) (spot_major_fp r))
