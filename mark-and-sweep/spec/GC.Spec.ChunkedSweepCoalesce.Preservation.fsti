module GC.Spec.ChunkedSweepCoalesce.Preservation

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module Header = GC.Lib.Header
module Obj = GC.Spec.Object
module MarkDefs = GC.Spec.ChunkedMark.Defs

val major_write_word_or_same_preserves_other_read
  (mh: MH.major_heap)
  (write_addr: hp_addr)
  (value: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (U64.v write_addr + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v write_addr))
      (ensures
        MH.read_word_in_major
          (GC.Spec.MajorAllocator.major_write_word_or_same
            mh write_addr value)
          read_addr == Some old)

val major_write_word_or_same_read_same
  (mh: MH.major_heap)
  (write_addr: hp_addr)
  (value: U64.t)
  (idx: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        MH.lookup_chunk_index mh write_addr == Some idx /\
        MH.word_in_chunk (Seq.index mh idx) write_addr)
      (ensures
        MH.read_word_in_major
          (GC.Spec.MajorAllocator.major_write_word_or_same
            mh write_addr value)
          write_addr == Some value)

val chunked_set_object_color_preserves_self_wosize
  (mh: MH.major_heap)
  (obj: obj_addr)
  (color: Header.color_sem)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_read_header mh obj ==
          Some hdr)
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_set_object_color
            mh obj color)
          obj ==
        Obj.getWosize hdr)

val chunked_make_white_preserves_self_wosize
  (mh: MH.major_heap)
  (obj: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_read_header mh obj ==
          Some hdr)
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_make_white mh obj)
          obj ==
        Obj.getWosize hdr)

val chunked_make_blue_preserves_self_wosize
  (mh: MH.major_heap)
  (obj: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_read_header mh obj ==
          Some hdr)
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_make_blue mh obj)
          obj ==
        Obj.getWosize hdr)

val chunked_set_object_color_preserves_other_read
  (mh: MH.major_heap)
  (obj: obj_addr)
  (color: Header.color_sem)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (U64.v (hd_address obj) + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v (hd_address obj)))
      (ensures
        MH.read_word_in_major
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_set_object_color
            mh obj color)
          read_addr == Some old)

val chunked_zero_fields_preserves_read_before
  (mh: MH.major_heap)
  (addr: U64.t)
  (n: nat)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        U64.v read_addr + U64.v mword <= U64.v addr)
      (ensures
        MH.read_word_in_major
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_zero_fields mh addr n)
          read_addr == Some old)

val chunked_zero_fields_preserves_read_after
  (mh: MH.major_heap)
  (addr: U64.t)
  (n: nat)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        U64.v addr + n * U64.v mword <= U64.v read_addr)
      (ensures
        MH.read_word_in_major
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_zero_fields mh addr n)
          read_addr == Some old)

val chunked_flush_blue_preserves_read_before
  (mh: MH.major_heap)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        U64.v read_addr + U64.v mword * 2 <= U64.v first_blue)
      (ensures
        MH.read_word_in_major
          (fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_flush_blue
            mh first_blue run_words fp))
          read_addr == Some old)

val chunked_flush_blue_preserves_read_after
  (mh: MH.major_heap)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (run_words = 0 \/
         U64.v first_blue + (run_words - 1) * U64.v mword <= U64.v read_addr))
      (ensures
        MH.read_word_in_major
          (fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_flush_blue
            mh first_blue run_words fp))
          read_addr == Some old)

val chunked_flush_blue_preserves_other_read
  (mh: MH.major_heap)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (run_words = 0 \/
         U64.v read_addr + U64.v mword * 2 <= U64.v first_blue \/
         U64.v first_blue + (run_words - 1) * U64.v mword <= U64.v read_addr))
      (ensures
        MH.read_word_in_major
          (fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_flush_blue
            mh first_blue run_words fp))
          read_addr == Some old)

val chunked_make_white_preserves_other_read
  (mh: MH.major_heap)
  (obj: obj_addr)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (U64.v (hd_address obj) + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v (hd_address obj)))
      (ensures
        MH.read_word_in_major
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_make_white mh obj)
          read_addr == Some old)

val chunked_make_blue_preserves_other_read
  (mh: MH.major_heap)
  (obj: obj_addr)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (U64.v (hd_address obj) + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v (hd_address obj)))
      (ensures
        MH.read_word_in_major
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_make_blue mh obj)
          read_addr == Some old)

val chunked_flush_blue_make_white_preserves_other_read
  (mh: MH.major_heap)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  (obj: obj_addr)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (run_words = 0 \/
         U64.v read_addr + U64.v mword * 2 <= U64.v first_blue \/
         U64.v first_blue + (run_words - 1) * U64.v mword <= U64.v read_addr) /\
        (U64.v (hd_address obj) + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v (hd_address obj)))
      (ensures
        MH.read_word_in_major
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_make_white
            (fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_flush_blue
              mh first_blue run_words fp))
            obj)
          read_addr == Some old)

val chunked_sweep_object_preserves_other_read
  (mh: MH.major_heap)
  (obj: obj_addr)
  (fp: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (U64.v (hd_address obj) + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v (hd_address obj)) /\
        (U64.v obj + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v obj))
      (ensures
        MH.read_word_in_major
          (fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_sweep_object
            mh obj fp))
          read_addr == Some old)

val chunked_sweep_aux_preserves_other_read
  (mh: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (fp: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (forall (obj: obj_addr). Seq.mem obj objs ==>
          (U64.v (hd_address obj) + U64.v mword <= U64.v read_addr \/
           U64.v read_addr + U64.v mword <= U64.v (hd_address obj)) /\
          (U64.v obj + U64.v mword <= U64.v read_addr \/
           U64.v read_addr + U64.v mword <= U64.v obj)))
      (ensures
        MH.read_word_in_major
          (fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_sweep_aux
            mh objs fp))
          read_addr == Some old)

val chunked_fused_aux_read_frame_ready
  (source: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (read_addr: hp_addr)
  : Tot prop

val chunked_fused_aux_read_frame_ready_from_all_after
  (source: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (read_addr: hp_addr)
  : Lemma
      (requires
        (run_words = 0 \/
         U64.v read_addr + U64.v mword * 2 <= U64.v first_blue) /\
        (forall (obj: obj_addr). Seq.mem obj objs ==>
          U64.v read_addr + U64.v mword * 2 <= U64.v obj))
      (ensures
        chunked_fused_aux_read_frame_ready
          source objs first_blue run_words read_addr)

val chunked_fused_aux_live_read_frame_ready
  (source: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (target: obj_addr)
  (read_addr: hp_addr)
  : Tot prop

val chunked_fused_aux_read_frame_ready_from_live_target
  (source: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (target: obj_addr)
  (read_addr: hp_addr)
  : Lemma
      (requires
        chunked_fused_aux_live_read_frame_ready
          source objs first_blue run_words target read_addr)
      (ensures
        chunked_fused_aux_read_frame_ready
          source objs first_blue run_words read_addr)

val chunked_fused_aux_live_read_frame_ready_from_chunk
  (source: MH.major_heap)
  (c: MH.heap_chunk)
  (target: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (field_addr: hp_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        Seq.mem target (MH.objects_in_chunk c) /\
        (forall (o: obj_addr). Seq.mem o (MH.objects_in_chunk c) ==>
          U64.v (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
                   source o) ==
          MH.object_wosize_in_chunk c o) /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_read_header
          source target == Some hdr /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black
          source target /\
        U64.v i <= U64.v (Obj.getWosize hdr) /\
        U64.v (Obj.getWosize hdr) == MH.object_wosize_in_chunk c target /\
        U64.v (hd_address target) + U64.v mword * U64.v i +
          U64.v mword <= heap_size /\
        field_addr == U64.add (hd_address target) (U64.mul mword i))
      (ensures
        chunked_fused_aux_live_read_frame_ready
          source (MH.objects_in_chunk c) 0UL 0 target field_addr)

val chunked_fused_aux_preserves_other_read
  (source work: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major work read_addr == Some old /\
        chunked_fused_aux_read_frame_ready
          source objs first_blue run_words read_addr)
      (ensures
        MH.read_word_in_major
          (fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_fused_aux
            source work objs first_blue run_words fp))
          read_addr == Some old)

val chunked_fused_aux_preserves_get_field_read_some
  (source work: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (field_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        U64.v (hd_address obj) + U64.v mword * U64.v i + U64.v mword <=
          heap_size /\
        field_addr == U64.add (hd_address obj) (U64.mul mword i) /\
        MH.read_word_in_major work field_addr == Some old /\
        chunked_fused_aux_read_frame_ready
          source objs first_blue run_words field_addr)
      (ensures
        MarkDefs.chunked_get_field
          (fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_fused_aux
            source work objs first_blue run_words fp))
          obj i ==
        MarkDefs.chunked_get_field work obj i)

val chunked_fused_aux_preserves_get_field_from_live_target
  (source work: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (field_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        U64.v (hd_address obj) + U64.v mword * U64.v i + U64.v mword <=
          heap_size /\
        field_addr == U64.add (hd_address obj) (U64.mul mword i) /\
        MH.read_word_in_major work field_addr == Some old /\
        chunked_fused_aux_live_read_frame_ready
          source objs first_blue run_words obj field_addr)
      (ensures
        MarkDefs.chunked_get_field
          (fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_fused_aux
            source work objs first_blue run_words fp))
          obj i ==
        MarkDefs.chunked_get_field work obj i)
