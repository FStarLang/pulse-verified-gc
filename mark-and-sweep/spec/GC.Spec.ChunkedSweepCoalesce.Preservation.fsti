module GC.Spec.ChunkedSweepCoalesce.Preservation

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module Header = GC.Lib.Header
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
