module GC.Spec.ChunkedSweepCoalesce.VertexPreservation

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module Obj = GC.Spec.Object
module SpecMajorAlloc = GC.Spec.MajorAllocator
module Defs = GC.Spec.ChunkedSweepCoalesce.Defs

val objects_in_chunk_from_write_after_member_preserves
  (c: MH.heap_chunk)
  (start: hp_addr)
  (obj: obj_addr)
  (addr: hp_addr)
  (value: U64.t)
  : Lemma
      (requires
        Seq.mem obj (MH.objects_in_chunk_from c start) /\
        MH.word_in_chunk c addr /\
        U64.v (hd_address obj) +
          (1 + MH.object_wosize_in_chunk c obj) * U64.v mword <=
          U64.v addr)
      (ensures
        Seq.mem obj
          (MH.objects_in_chunk_from
            (MH.write_word_in_chunk c addr value) start))

val chunked_merged_block_step
  (c: MH.heap_chunk)
  (fb: obj_addr)
  (run_words: pos)
  (start: hp_addr)
  (x: obj_addr)
  : Lemma
      (requires
        U64.v fb >= U64.v mword /\
        U64.v fb < heap_size /\
        U64.v fb < MH.chunk_end c /\
        U64.v fb % U64.v mword == 0 /\
        U64.v fb + (run_words - 1) * U64.v mword == U64.v start /\
        run_words - 1 < pow2 54 /\
        run_words - 1 < pow2 64 /\
        U64.v start <= MH.chunk_end c /\
        MH.word_in_chunk c (hd_address fb) /\
        MH.read_word_in_chunk c (hd_address fb) ==
          Obj.makeHeader
            (U64.uint_to_t (run_words - 1)) GC.Lib.Header.Blue 0UL /\
        (U64.v start < MH.chunk_end c ==>
          Seq.mem x (MH.objects_in_chunk_from c start)))
      (ensures
        Seq.mem fb (MH.objects_in_chunk_from c (hd_address fb)) /\
        (U64.v start < MH.chunk_end c ==>
          Seq.mem x (MH.objects_in_chunk_from c (hd_address fb))))

val major_write_word_or_same_after_member_preserves_chunk_member
  (mh: MH.major_heap)
  (idx: nat)
  (obj: obj_addr)
  (addr: hp_addr)
  (value: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem obj (MH.objects_in_chunk (Seq.index mh idx)) /\
        MH.word_in_chunk (Seq.index mh idx) addr /\
        U64.v (hd_address obj) +
          (1 + MH.object_wosize_in_chunk (Seq.index mh idx) obj) *
            U64.v mword <=
          U64.v addr)
      (ensures
        MH.well_formed_major_heap
          (SpecMajorAlloc.major_write_word_or_same mh addr value) /\
        idx <
          Seq.length
            (SpecMajorAlloc.major_write_word_or_same mh addr value) /\
        Seq.mem obj
          (MH.objects_in_chunk
            (Seq.index
              (SpecMajorAlloc.major_write_word_or_same mh addr value)
              idx)) /\
        MH.object_wosize_in_chunk
          (Seq.index
            (SpecMajorAlloc.major_write_word_or_same mh addr value)
            idx)
          obj ==
        MH.object_wosize_in_chunk (Seq.index mh idx) obj /\
        MH.chunk_start
          (Seq.index
            (SpecMajorAlloc.major_write_word_or_same mh addr value)
            idx) ==
        MH.chunk_start (Seq.index mh idx) /\
        MH.chunk_end
          (Seq.index
            (SpecMajorAlloc.major_write_word_or_same mh addr value)
            idx) ==
        MH.chunk_end (Seq.index mh idx))

val major_write_word_or_same_after_member_preserves_vertex
  (mh: MH.major_heap)
  (idx: nat)
  (obj: obj_addr)
  (addr: hp_addr)
  (value: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem obj (MH.objects_in_chunk (Seq.index mh idx)) /\
        MH.word_in_chunk (Seq.index mh idx) addr /\
        U64.v (hd_address obj) +
          (1 + MH.object_wosize_in_chunk (Seq.index mh idx) obj) *
           U64.v mword <=
          U64.v addr)
      (ensures
        Seq.mem obj
          (MH.major_objects
           (SpecMajorAlloc.major_write_word_or_same mh addr value)))

val chunked_zero_fields_after_member_preserves_chunk_member
  (mh: MH.major_heap)
  (idx: nat)
  (obj: obj_addr)
  (addr: U64.t)
  (n: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem obj (MH.objects_in_chunk (Seq.index mh idx)) /\
        U64.v addr % U64.v mword == 0 /\
        U64.v addr + n * U64.v mword <= MH.chunk_end (Seq.index mh idx) /\
        U64.v (hd_address obj) +
          (1 + MH.object_wosize_in_chunk (Seq.index mh idx) obj) *
           U64.v mword <=
          U64.v addr)
      (ensures
        MH.well_formed_major_heap (Defs.chunked_zero_fields mh addr n) /\
        idx < Seq.length (Defs.chunked_zero_fields mh addr n) /\
        Seq.mem obj
          (MH.objects_in_chunk
           (Seq.index (Defs.chunked_zero_fields mh addr n) idx)) /\
        MH.object_wosize_in_chunk
          (Seq.index (Defs.chunked_zero_fields mh addr n) idx)
          obj ==
        MH.object_wosize_in_chunk (Seq.index mh idx) obj)

val chunked_flush_blue_after_member_preserves_chunk_member
  (mh: MH.major_heap)
  (idx: nat)
  (obj: obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem obj (MH.objects_in_chunk (Seq.index mh idx)) /\
        (run_words <> 0 /\
         ~(U64.v first_blue < U64.v mword) /\
         ~(U64.v first_blue >= heap_size) /\
         ~(U64.v first_blue % U64.v mword <> 0) /\
         run_words - 1 < pow2 54 ==>
          (let fb : obj_addr = first_blue in
           let hd = hd_address fb in
           MH.word_in_chunk (Seq.index mh idx) hd /\
           U64.v (hd_address obj) +
             (1 + MH.object_wosize_in_chunk (Seq.index mh idx) obj) *
               U64.v mword <=
             U64.v hd /\
           U64.v hd + run_words * U64.v mword <=
             MH.chunk_end (Seq.index mh idx))))
      (ensures
        (let final = fst (Defs.chunked_flush_blue mh first_blue run_words fp) in
        MH.well_formed_major_heap final /\
        idx < Seq.length final /\
        Seq.mem obj (MH.objects_in_chunk (Seq.index final idx)) /\
        MH.object_wosize_in_chunk (Seq.index final idx) obj ==
        MH.object_wosize_in_chunk (Seq.index mh idx) obj))

val chunked_make_white_preserves_chunk_member
  (mh: MH.major_heap)
  (idx: nat)
  (obj: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem obj (MH.objects_in_chunk (Seq.index mh idx)) /\
        Defs.chunked_read_header mh obj == Some hdr)
      (ensures
        MH.well_formed_major_heap (Defs.chunked_make_white mh obj) /\
        idx < Seq.length (Defs.chunked_make_white mh obj) /\
        Seq.mem obj
         (MH.objects_in_chunk
           (Seq.index (Defs.chunked_make_white mh obj) idx)) /\
        MH.object_wosize_in_chunk
         (Seq.index (Defs.chunked_make_white mh obj) idx)
         obj ==
        MH.object_wosize_in_chunk (Seq.index mh idx) obj /\
        MH.chunk_start (Seq.index (Defs.chunked_make_white mh obj) idx) ==
        MH.chunk_start (Seq.index mh idx) /\
        MH.chunk_end (Seq.index (Defs.chunked_make_white mh obj) idx) ==
        MH.chunk_end (Seq.index mh idx))

val chunked_make_white_after_member_preserves_chunk_member
  (mh: MH.major_heap)
  (idx: nat)
  (protected: obj_addr)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem protected (MH.objects_in_chunk (Seq.index mh idx)) /\
        MH.word_in_chunk (Seq.index mh idx) (hd_address obj) /\
        U64.v (hd_address protected) +
         (1 + MH.object_wosize_in_chunk (Seq.index mh idx) protected) *
           U64.v mword <=
         U64.v (hd_address obj))
      (ensures
        MH.well_formed_major_heap (Defs.chunked_make_white mh obj) /\
        idx < Seq.length (Defs.chunked_make_white mh obj) /\
        Seq.mem protected
         (MH.objects_in_chunk
           (Seq.index (Defs.chunked_make_white mh obj) idx)) /\
        MH.object_wosize_in_chunk
         (Seq.index (Defs.chunked_make_white mh obj) idx)
         protected ==
        MH.object_wosize_in_chunk (Seq.index mh idx) protected /\
        MH.chunk_start (Seq.index (Defs.chunked_make_white mh obj) idx) ==
        MH.chunk_start (Seq.index mh idx) /\
        MH.chunk_end (Seq.index (Defs.chunked_make_white mh obj) idx) ==
        MH.chunk_end (Seq.index mh idx))

val major_write_word_or_same_payload_preserves_objects_from
  (mh: MH.major_heap)
  (idx: nat)
  (start: hp_addr)
  (blk: obj_addr)
  (addr: hp_addr)
  (value: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem blk (MH.objects_in_chunk_from (Seq.index mh idx) start) /\
        MH.word_in_chunk (Seq.index mh idx) addr /\
        U64.v blk <= U64.v addr /\
        U64.v addr + U64.v mword <=
          U64.v blk +
            MH.object_wosize_in_chunk (Seq.index mh idx) blk *
              U64.v mword)
      (ensures
        (let mh' = SpecMajorAlloc.major_write_word_or_same mh addr value in
        MH.well_formed_major_heap mh' /\
        idx < Seq.length mh' /\
        MH.objects_in_chunk_from (Seq.index mh' idx) start ==
        MH.objects_in_chunk_from (Seq.index mh idx) start /\
        MH.object_wosize_in_chunk (Seq.index mh' idx) blk ==
        MH.object_wosize_in_chunk (Seq.index mh idx) blk /\
        MH.chunk_start (Seq.index mh' idx) ==
        MH.chunk_start (Seq.index mh idx) /\
        MH.chunk_end (Seq.index mh' idx) ==
        MH.chunk_end (Seq.index mh idx)))

val chunked_zero_fields_payload_preserves_objects_from
  (mh: MH.major_heap)
  (idx: nat)
  (start: hp_addr)
  (blk: obj_addr)
  (addr: U64.t)
  (n: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem blk (MH.objects_in_chunk_from (Seq.index mh idx) start) /\
        U64.v addr % U64.v mword == 0 /\
        U64.v blk <= U64.v addr /\
        U64.v addr + n * U64.v mword <=
          U64.v blk +
            MH.object_wosize_in_chunk (Seq.index mh idx) blk *
              U64.v mword)
      (ensures
        (let mh' = Defs.chunked_zero_fields mh addr n in
        MH.well_formed_major_heap mh' /\
        idx < Seq.length mh' /\
        MH.objects_in_chunk_from (Seq.index mh' idx) start ==
        MH.objects_in_chunk_from (Seq.index mh idx) start /\
        MH.object_wosize_in_chunk (Seq.index mh' idx) blk ==
        MH.object_wosize_in_chunk (Seq.index mh idx) blk /\
        MH.chunk_start (Seq.index mh' idx) ==
        MH.chunk_start (Seq.index mh idx) /\
        MH.chunk_end (Seq.index mh' idx) ==
        MH.chunk_end (Seq.index mh idx)))

val chunked_flush_blue_prefix_preserves_objects_from
  (mh: MH.major_heap)
  (idx: nat)
  (fb: obj_addr)
  (run_words: pos)
  (start: hp_addr)
  (target: obj_addr)
  (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        U64.v fb < MH.chunk_end (Seq.index mh idx) /\
        U64.v fb + (run_words - 1) * U64.v mword == U64.v start /\
        run_words - 1 < pow2 54 /\
        run_words - 1 < pow2 64 /\
        U64.v start <= MH.chunk_end (Seq.index mh idx) /\
        MH.word_in_chunk (Seq.index mh idx) (hd_address fb) /\
        Seq.mem target
          (MH.objects_in_chunk_from (Seq.index mh idx) start))
      (ensures
        (let final = fst (Defs.chunked_flush_blue mh fb run_words fp) in
        MH.well_formed_major_heap final /\
        idx < Seq.length final /\
        Seq.mem target
          (MH.objects_in_chunk_from
            (Seq.index final idx) (hd_address fb)) /\
        MH.chunk_start (Seq.index final idx) ==
        MH.chunk_start (Seq.index mh idx) /\
        MH.chunk_end (Seq.index final idx) ==
        MH.chunk_end (Seq.index mh idx)))
