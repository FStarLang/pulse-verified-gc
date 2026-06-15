module GC.Spec.ChunkedMark.Preservation

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module Header = GC.Lib.Header
module MH = GC.Spec.MajorHeap
module RangePres = GC.Spec.ChunkedSweepCoalesce.RangePreservation

val stack_objects_in_major
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : GTot prop

val stack_objects_in_major_elim
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  : Lemma
      (requires
        stack_objects_in_major mh st /\
        Seq.mem obj st)
      (ensures Seq.mem obj (MH.major_objects mh))

val stack_objects_in_major_tail
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        stack_objects_in_major mh st)
      (ensures stack_objects_in_major mh (Seq.tail st))

val stack_objects_in_major_empty
  (mh: MH.major_heap)
  : Lemma
      (ensures stack_objects_in_major mh Seq.empty)

val stack_objects_in_major_cons
  (mh: MH.major_heap)
  (obj: obj_addr)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.mem obj (MH.major_objects mh) /\
        stack_objects_in_major mh st)
      (ensures stack_objects_in_major mh (Seq.cons obj st))

val stack_objects_in_major_preserved_by_major_objects
  (mh mh': MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        stack_objects_in_major mh st /\
        MH.major_objects mh' == MH.major_objects mh)
      (ensures stack_objects_in_major mh' st)

val chunked_set_object_color_member_preserves_major_objects
  (mh: MH.major_heap)
  (obj: obj_addr)
  (color: Header.color_sem)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        MH.major_objects
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_set_object_color
            mh obj color) ==
        MH.major_objects mh)

val chunked_make_gray_preserves_major_objects
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        MH.major_objects (GC.Spec.ChunkedMark.Defs.chunked_make_gray mh obj) ==
        MH.major_objects mh)

val chunked_make_black_preserves_major_objects
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        MH.major_objects (GC.Spec.ChunkedMark.Defs.chunked_make_black mh obj) ==
        MH.major_objects mh)

val chunked_set_object_color_member_read_header
  (mh: MH.major_heap)
  (obj: obj_addr)
  (color: Header.color_sem)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        (match GC.Spec.ChunkedSweepCoalesce.Defs.chunked_read_header mh obj with
         | Some hdr ->
           GC.Spec.ChunkedSweepCoalesce.Defs.chunked_read_header
             (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_set_object_color
               mh obj color) obj ==
           Some (GC.Spec.Object.colorHeader hdr color)
         | None -> False))

val chunked_set_object_color_preserves_wosize_of_object
  (mh: MH.major_heap)
  (obj target: obj_addr)
  (color: Header.color_sem)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_set_object_color
           mh obj color) target ==
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
          mh target)

val chunked_set_object_color_preserves_get_field
  (mh: MH.major_heap)
  (obj target: obj_addr)
  (color: Header.color_sem)
  (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v i <=
          U64.v
            (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
              mh target))
      (ensures
        GC.Spec.ChunkedMark.Defs.chunked_get_field
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_set_object_color
            mh obj color)
          target i ==
        GC.Spec.ChunkedMark.Defs.chunked_get_field mh target i)

val chunked_set_object_color_preserves_field_read
  (mh: MH.major_heap)
  (obj target: obj_addr)
  (color: Header.color_sem)
  (i: U64.t{U64.v i >= 1})
  (field_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v i <=
          U64.v
            (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
              mh target) /\
        U64.v field_addr ==
          U64.v (hd_address target) + U64.v mword * U64.v i /\
        MH.read_word_in_major mh field_addr == Some old)
      (ensures
        MH.read_word_in_major
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_set_object_color
            mh obj color)
          field_addr == Some old)

val chunked_set_object_color_preserves_field_read_back
  (mh: MH.major_heap)
  (obj target: obj_addr)
  (color: Header.color_sem)
  (i: U64.t{U64.v i >= 1})
  (field_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v i <=
          U64.v
            (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
              mh target) /\
        U64.v field_addr ==
          U64.v (hd_address target) + U64.v mword * U64.v i /\
        MH.read_word_in_major
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_set_object_color
            mh obj color)
          field_addr == Some old)
      (ensures MH.read_word_in_major mh field_addr == Some old)

val chunked_set_object_color_preserves_ranges
  (mh: MH.major_heap)
  (obj: obj_addr)
  (color: Header.color_sem)
  : Lemma
      (ensures
        RangePres.same_chunk_ranges mh
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_set_object_color
            mh obj color))

val chunked_set_object_color_member_sets_color
  (mh: MH.major_heap)
  (obj: obj_addr)
  (color: Header.color_sem)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_color_of_object
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_set_object_color
            mh obj color) obj ==
        Some color)

val chunked_make_gray_makes_gray
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_color_of_object
          (GC.Spec.ChunkedMark.Defs.chunked_make_gray mh obj) obj ==
        Some Header.Gray)

val chunked_make_gray_preserves_wosize_of_object
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
          (GC.Spec.ChunkedMark.Defs.chunked_make_gray mh obj) target ==
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
          mh target)

val chunked_make_gray_preserves_get_field
  (mh: MH.major_heap)
  (obj target: obj_addr)
  (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v i <=
          U64.v
            (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
              mh target))
      (ensures
        GC.Spec.ChunkedMark.Defs.chunked_get_field
          (GC.Spec.ChunkedMark.Defs.chunked_make_gray mh obj)
          target i ==
        GC.Spec.ChunkedMark.Defs.chunked_get_field mh target i)

val chunked_make_gray_preserves_field_read
  (mh: MH.major_heap)
  (obj target: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (field_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v i <=
          U64.v
            (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
              mh target) /\
        U64.v field_addr ==
          U64.v (hd_address target) + U64.v mword * U64.v i /\
        MH.read_word_in_major mh field_addr == Some old)
      (ensures
        MH.read_word_in_major
          (GC.Spec.ChunkedMark.Defs.chunked_make_gray mh obj)
          field_addr == Some old)

val chunked_make_gray_preserves_field_read_back
  (mh: MH.major_heap)
  (obj target: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (field_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v i <=
          U64.v
            (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
              mh target) /\
        U64.v field_addr ==
          U64.v (hd_address target) + U64.v mword * U64.v i /\
        MH.read_word_in_major
          (GC.Spec.ChunkedMark.Defs.chunked_make_gray mh obj)
          field_addr == Some old)
      (ensures MH.read_word_in_major mh field_addr == Some old)

val chunked_make_gray_preserves_ranges
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (ensures
        RangePres.same_chunk_ranges mh
          (GC.Spec.ChunkedMark.Defs.chunked_make_gray mh obj))

val chunked_make_black_makes_black
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black
          (GC.Spec.ChunkedMark.Defs.chunked_make_black mh obj) obj)

val chunked_make_black_preserves_wosize_of_object
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
          (GC.Spec.ChunkedMark.Defs.chunked_make_black mh obj) target ==
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
          mh target)

val chunked_make_black_preserves_get_field
  (mh: MH.major_heap)
  (obj target: obj_addr)
  (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v i <=
          U64.v
            (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
              mh target))
      (ensures
        GC.Spec.ChunkedMark.Defs.chunked_get_field
          (GC.Spec.ChunkedMark.Defs.chunked_make_black mh obj)
          target i ==
        GC.Spec.ChunkedMark.Defs.chunked_get_field mh target i)

val chunked_make_black_preserves_ranges
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (ensures
        RangePres.same_chunk_ranges mh
          (GC.Spec.ChunkedMark.Defs.chunked_make_black mh obj))

val chunked_make_gray_not_blue
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        ~(GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_blue
          (GC.Spec.ChunkedMark.Defs.chunked_make_gray mh obj) obj))

val chunked_make_black_not_blue
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        ~(GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_blue
          (GC.Spec.ChunkedMark.Defs.chunked_make_black mh obj) obj))

val chunked_make_gray_preserves_other_blue_status
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires obj <> target)
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_blue
          (GC.Spec.ChunkedMark.Defs.chunked_make_gray mh obj) target ==
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_blue mh target)

val chunked_make_black_preserves_other_blue_status
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires obj <> target)
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_blue
          (GC.Spec.ChunkedMark.Defs.chunked_make_black mh obj) target ==
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_blue mh target)

val chunked_make_gray_not_white
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        ~(GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_white
          (GC.Spec.ChunkedMark.Defs.chunked_make_gray mh obj) obj))

val chunked_make_black_not_white
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        ~(GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_white
          (GC.Spec.ChunkedMark.Defs.chunked_make_black mh obj) obj))

val chunked_make_gray_preserves_other_white_status
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires obj <> target)
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_white
          (GC.Spec.ChunkedMark.Defs.chunked_make_gray mh obj) target ==
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_white mh target)

val chunked_make_black_preserves_other_white_status
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires obj <> target)
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_white
          (GC.Spec.ChunkedMark.Defs.chunked_make_black mh obj) target ==
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_white mh target)

val chunked_make_gray_preserves_no_scan_status
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        GC.Spec.ChunkedMark.Defs.chunked_is_no_scan
          (GC.Spec.ChunkedMark.Defs.chunked_make_gray mh obj) target ==
        GC.Spec.ChunkedMark.Defs.chunked_is_no_scan mh target)

val chunked_make_black_preserves_no_scan_status
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        GC.Spec.ChunkedMark.Defs.chunked_is_no_scan
          (GC.Spec.ChunkedMark.Defs.chunked_make_black mh obj) target ==
        GC.Spec.ChunkedMark.Defs.chunked_is_no_scan mh target)

val chunked_make_gray_preserves_tag_of_object
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_tag_of_object
          (GC.Spec.ChunkedMark.Defs.chunked_make_gray mh obj) target ==
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_tag_of_object mh target)

val chunked_make_black_preserves_tag_of_object
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_tag_of_object
          (GC.Spec.ChunkedMark.Defs.chunked_make_black mh obj) target ==
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_tag_of_object mh target)

val chunked_make_gray_preserves_infix_status
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_infix
          (GC.Spec.ChunkedMark.Defs.chunked_make_gray mh obj) target ==
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_infix mh target)

val chunked_make_black_preserves_infix_status
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_infix
          (GC.Spec.ChunkedMark.Defs.chunked_make_black mh obj) target ==
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_infix mh target)

val chunked_set_object_color_preserves_other_black
  (mh: MH.major_heap)
  (obj target: obj_addr)
  (color: Header.color_sem)
  : Lemma
      (requires
        obj <> target /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh target)
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_set_object_color
            mh obj color) target)

val chunked_set_object_color_preserves_other_black_back
  (mh: MH.major_heap)
  (obj target: obj_addr)
  (color: Header.color_sem)
  : Lemma
      (requires
        obj <> target /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_set_object_color
            mh obj color) target)
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh target)

val chunked_set_object_color_preserves_other_black_status
  (mh: MH.major_heap)
  (obj target: obj_addr)
  (color: Header.color_sem)
  : Lemma
      (requires obj <> target)
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_set_object_color
            mh obj color) target ==
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh target)

val chunked_set_object_color_preserves_other_gray
  (mh: MH.major_heap)
  (obj target: obj_addr)
  (color: Header.color_sem)
  : Lemma
      (requires
        obj <> target /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_color_of_object
          mh target ==
        Some Header.Gray)
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_color_of_object
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_set_object_color
            mh obj color) target ==
        Some Header.Gray)

val chunked_set_object_color_preserves_other_gray_back
  (mh: MH.major_heap)
  (obj target: obj_addr)
  (color: Header.color_sem)
  : Lemma
      (requires
        obj <> target /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_color_of_object
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_set_object_color
            mh obj color) target ==
        Some Header.Gray)
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_color_of_object
          mh target ==
        Some Header.Gray)

val chunked_make_gray_preserves_other_black
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires
        obj <> target /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh target)
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black
          (GC.Spec.ChunkedMark.Defs.chunked_make_gray mh obj) target)

val chunked_make_gray_preserves_other_black_status
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires obj <> target)
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black
          (GC.Spec.ChunkedMark.Defs.chunked_make_gray mh obj) target ==
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh target)

val chunked_make_gray_preserves_other_gray_back
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires
        obj <> target /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_color_of_object
          (GC.Spec.ChunkedMark.Defs.chunked_make_gray mh obj) target ==
        Some Header.Gray)
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_color_of_object
          mh target ==
        Some Header.Gray)

val chunked_make_gray_preserves_other_gray
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires
        obj <> target /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_color_of_object
          mh target ==
        Some Header.Gray)
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_color_of_object
          (GC.Spec.ChunkedMark.Defs.chunked_make_gray mh obj) target ==
        Some Header.Gray)

val chunked_make_black_preserves_other_black_status
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires obj <> target)
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black
          (GC.Spec.ChunkedMark.Defs.chunked_make_black mh obj) target ==
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh target)

val chunked_make_black_preserves_other_gray
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires
        obj <> target /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_color_of_object
          mh target ==
        Some Header.Gray)
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_color_of_object
          (GC.Spec.ChunkedMark.Defs.chunked_make_black mh obj) target ==
        Some Header.Gray)

val chunked_make_black_preserves_other_gray_back
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires
        obj <> target /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_color_of_object
          (GC.Spec.ChunkedMark.Defs.chunked_make_black mh obj) target ==
        Some Header.Gray)
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_color_of_object
          mh target ==
        Some Header.Gray)

val chunked_set_object_color_member_preserves_well_formed
  (mh: MH.major_heap)
  (obj: obj_addr)
  (color: Header.color_sem)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        MH.well_formed_major_heap
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_set_object_color
            mh obj color))

val chunked_make_gray_preserves_well_formed
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        MH.well_formed_major_heap
          (GC.Spec.ChunkedMark.Defs.chunked_make_gray mh obj))

val chunked_make_black_preserves_well_formed
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        MH.well_formed_major_heap
          (GC.Spec.ChunkedMark.Defs.chunked_make_black mh obj))

val chunked_push_children_preservation_ready
  (mh: MH.major_heap)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : GTot prop

val chunked_push_children_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_push_children_preservation_ready mh obj i ws)
      (ensures
        (let (mh', _) =
          GC.Spec.ChunkedMark.Defs.chunked_push_children mh st obj i ws in
         MH.major_objects mh' == MH.major_objects mh))

val chunked_push_children_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_push_children_preservation_ready mh obj i ws)
      (ensures
        (let (mh', _) =
          GC.Spec.ChunkedMark.Defs.chunked_push_children mh st obj i ws in
         MH.well_formed_major_heap mh'))

val chunked_push_children_preserves_black
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj target: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Lemma
      (requires
        chunked_push_children_preservation_ready mh obj i ws /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh target)
      (ensures
        (let (mh', _) =
          GC.Spec.ChunkedMark.Defs.chunked_push_children mh st obj i ws in
         GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh' target))

val chunked_mark_step_empty_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires Seq.length st = 0)
      (ensures
        (let (mh', _) = GC.Spec.ChunkedMark.Defs.chunked_mark_step mh st in
         MH.major_objects mh' == MH.major_objects mh))

val chunked_mark_step_empty_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st = 0 /\
        MH.well_formed_major_heap mh)
      (ensures
        (let (mh', _) = GC.Spec.ChunkedMark.Defs.chunked_mark_step mh st in
         MH.well_formed_major_heap mh'))

val chunked_mark_step_empty_preserves_stack_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st = 0 /\
        stack_objects_in_major mh st)
      (ensures
        (let (mh', st') = GC.Spec.ChunkedMark.Defs.chunked_mark_step mh st in
         stack_objects_in_major mh' st'))

val chunked_mark_step_no_scan_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        Seq.mem (Seq.head st) (MH.major_objects mh) /\
        GC.Spec.ChunkedMark.Defs.chunked_is_no_scan mh (Seq.head st))
      (ensures
        (let (mh', _) = GC.Spec.ChunkedMark.Defs.chunked_mark_step mh st in
         MH.major_objects mh' == MH.major_objects mh))

val chunked_mark_step_no_scan_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        Seq.mem (Seq.head st) (MH.major_objects mh) /\
        GC.Spec.ChunkedMark.Defs.chunked_is_no_scan mh (Seq.head st))
      (ensures
        (let (mh', _) = GC.Spec.ChunkedMark.Defs.chunked_mark_step mh st in
         MH.well_formed_major_heap mh'))

val chunked_mark_step_no_scan_preserves_stack_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        stack_objects_in_major mh st /\
        GC.Spec.ChunkedMark.Defs.chunked_is_no_scan mh (Seq.head st))
      (ensures
        (let (mh', st') = GC.Spec.ChunkedMark.Defs.chunked_mark_step mh st in
         stack_objects_in_major mh' st'))

val chunked_mark_step_scan_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        Seq.mem (Seq.head st) (MH.major_objects mh) /\
        ~(GC.Spec.ChunkedMark.Defs.chunked_is_no_scan mh (Seq.head st)) /\
        (let obj = Seq.head st in
         let mh' = GC.Spec.ChunkedMark.Defs.chunked_make_black mh obj in
         let ws =
           GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object mh obj in
         chunked_push_children_preservation_ready mh' obj 1UL ws))
      (ensures
        (let (mh', _) = GC.Spec.ChunkedMark.Defs.chunked_mark_step mh st in
         MH.major_objects mh' == MH.major_objects mh))

val chunked_mark_step_scan_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        Seq.mem (Seq.head st) (MH.major_objects mh) /\
        ~(GC.Spec.ChunkedMark.Defs.chunked_is_no_scan mh (Seq.head st)) /\
        (let obj = Seq.head st in
         let mh' = GC.Spec.ChunkedMark.Defs.chunked_make_black mh obj in
         let ws =
           GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object mh obj in
         chunked_push_children_preservation_ready mh' obj 1UL ws))
      (ensures
        (let (mh', _) = GC.Spec.ChunkedMark.Defs.chunked_mark_step mh st in
         MH.well_formed_major_heap mh'))

val chunked_mark_step_preservation_ready
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : GTot prop

val chunked_mark_step_marks_head_black
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        chunked_mark_step_preservation_ready mh st)
      (ensures
        (let (mh', _) = GC.Spec.ChunkedMark.Defs.chunked_mark_step mh st in
         GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh' (Seq.head st)))

val chunked_mark_step_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_step_preservation_ready mh st)
      (ensures
        (let (mh', _) = GC.Spec.ChunkedMark.Defs.chunked_mark_step mh st in
         MH.major_objects mh' == MH.major_objects mh))

val chunked_mark_step_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_step_preservation_ready mh st)
      (ensures
        (let (mh', _) = GC.Spec.ChunkedMark.Defs.chunked_mark_step mh st in
         MH.well_formed_major_heap mh'))

val chunked_mark_aux_preservation_ready
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (fuel: nat)
  : GTot prop

val chunked_mark_aux_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_aux_preservation_ready mh st fuel)
      (ensures
        MH.major_objects (GC.Spec.ChunkedMark.Defs.chunked_mark_aux mh st fuel) ==
        MH.major_objects mh)

val chunked_mark_aux_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_aux_preservation_ready mh st fuel)
      (ensures
        MH.well_formed_major_heap
          (GC.Spec.ChunkedMark.Defs.chunked_mark_aux mh st fuel))

val chunked_mark_preservation_ready
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : GTot prop

val chunked_mark_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_preservation_ready mh st)
      (ensures
        MH.major_objects (GC.Spec.ChunkedMark.Defs.chunked_mark mh st) ==
        MH.major_objects mh)

val chunked_mark_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_preservation_ready mh st)
      (ensures
        MH.well_formed_major_heap
          (GC.Spec.ChunkedMark.Defs.chunked_mark mh st))
