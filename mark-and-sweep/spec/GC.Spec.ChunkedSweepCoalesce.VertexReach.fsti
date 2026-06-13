module GC.Spec.ChunkedSweepCoalesce.VertexReach

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module Obj = GC.Spec.Object
module Defs = GC.Spec.ChunkedSweepCoalesce.Defs
module SpecMajorAlloc = GC.Spec.MajorAllocator

val seq_mem_eq (#a:eqtype) (s t: Seq.seq a) (x: a)
  : Lemma
      (requires s == t /\ Seq.mem x s)
      (ensures Seq.mem x t)

val objects_in_chunk_from_write_member_header_preserves_member
    (c: MH.heap_chunk)
    (start: hp_addr)
    (obj: obj_addr)
    (value: U64.t)
  : Lemma
      (requires
        Seq.mem obj (MH.objects_in_chunk_from c start) /\
        MH.word_in_chunk c (hd_address obj) /\
        U64.v (hd_address obj) +
          (U64.v (Obj.getWosize value) + 1) * U64.v mword <=
          MH.chunk_end c /\
        U64.v (hd_address obj) +
          (U64.v (Obj.getWosize value) + 1) * U64.v mword < pow2 64)
      (ensures
        Seq.mem obj
          (MH.objects_in_chunk_from
            (MH.write_word_in_chunk c (hd_address obj) value) start))

val major_write_member_header_preserves_chunk_member
    (mh: MH.major_heap)
    (idx: nat)
    (obj: obj_addr)
    (value: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem obj (MH.objects_in_chunk (Seq.index mh idx)) /\
        MH.word_in_chunk (Seq.index mh idx) (hd_address obj) /\
        U64.v (hd_address obj) +
          (U64.v (Obj.getWosize value) + 1) * U64.v mword <=
          MH.chunk_end (Seq.index mh idx) /\
        U64.v (hd_address obj) +
          (U64.v (Obj.getWosize value) + 1) * U64.v mword < pow2 64)
      (ensures
        (let mh' = SpecMajorAlloc.major_write_word_or_same
                    mh (hd_address obj) value in
         MH.well_formed_major_heap mh' /\
         idx < Seq.length mh' /\
         Seq.mem obj (MH.objects_in_chunk (Seq.index mh' idx)) /\
         MH.chunk_start (Seq.index mh' idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index mh' idx) ==
         MH.chunk_end (Seq.index mh idx)))

val major_heap_eq_preserves_objects_from_member
    (mh1 mh2: MH.major_heap)
    (idx: nat)
    (start: hp_addr)
    (obj: obj_addr)
  : Lemma
      (requires
        mh1 == mh2 /\
        idx < Seq.length mh2 /\
        Seq.mem obj (MH.objects_in_chunk_from (Seq.index mh2 idx) start))
      (ensures
        idx < Seq.length mh1 /\
        Seq.mem obj (MH.objects_in_chunk_from (Seq.index mh1 idx) start))

val major_write_member_header_preserves_objects_from_member
    (mh: MH.major_heap)
    (idx: nat)
    (start: hp_addr)
    (obj: obj_addr)
    (value: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem obj (MH.objects_in_chunk_from (Seq.index mh idx) start) /\
        MH.word_in_chunk (Seq.index mh idx) (hd_address obj) /\
        U64.v (hd_address obj) +
          (U64.v (Obj.getWosize value) + 1) * U64.v mword <=
          MH.chunk_end (Seq.index mh idx) /\
        U64.v (hd_address obj) +
          (U64.v (Obj.getWosize value) + 1) * U64.v mword < pow2 64)
      (ensures
        (let mh' = SpecMajorAlloc.major_write_word_or_same
                    mh (hd_address obj) value in
         MH.well_formed_major_heap mh' /\
         idx < Seq.length mh' /\
         Seq.mem obj (MH.objects_in_chunk_from (Seq.index mh' idx) start) /\
         MH.chunk_start (Seq.index mh' idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index mh' idx) ==
         MH.chunk_end (Seq.index mh idx)))

val major_write_member_header_same_wosize_preserves_objects_from
    (mh: MH.major_heap)
    (idx: nat)
    (start: hp_addr)
    (obj: obj_addr)
    (value: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem obj (MH.objects_in_chunk_from (Seq.index mh idx) start) /\
        MH.word_in_chunk (Seq.index mh idx) (hd_address obj) /\
        U64.v (Obj.getWosize value) ==
          MH.object_wosize_in_chunk (Seq.index mh idx) obj)
      (ensures
        (let mh' = SpecMajorAlloc.major_write_word_or_same
                    mh (hd_address obj) value in
         MH.well_formed_major_heap mh' /\
         idx < Seq.length mh' /\
         MH.objects_in_chunk_from (Seq.index mh' idx) start ==
         MH.objects_in_chunk_from (Seq.index mh idx) start /\
         MH.object_wosize_in_chunk (Seq.index mh' idx) obj ==
         MH.object_wosize_in_chunk (Seq.index mh idx) obj /\
         MH.chunk_start (Seq.index mh' idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index mh' idx) ==
         MH.chunk_end (Seq.index mh idx)))

val major_write_word_or_same_before_preserves_objects_from
    (mh: MH.major_heap)
    (idx: nat)
    (start: hp_addr)
    (addr: hp_addr)
    (value: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        MH.word_in_chunk (Seq.index mh idx) addr /\
        U64.v addr + U64.v mword <= U64.v start)
      (ensures
        (let mh' = SpecMajorAlloc.major_write_word_or_same mh addr value in
         MH.well_formed_major_heap mh' /\
         idx < Seq.length mh' /\
         MH.objects_in_chunk_from (Seq.index mh' idx) start ==
         MH.objects_in_chunk_from (Seq.index mh idx) start /\
         MH.chunk_start (Seq.index mh' idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index mh' idx) ==
         MH.chunk_end (Seq.index mh idx)))

val chunked_zero_fields_before_preserves_objects_from
    (mh: MH.major_heap)
    (idx: nat)
    (start: hp_addr)
    (addr: U64.t)
    (n: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        U64.v addr % U64.v mword == 0 /\
        (n <> 0 ==> U64.v addr >= MH.chunk_start (Seq.index mh idx)) /\
        U64.v addr + n * U64.v mword <= U64.v start /\
        U64.v addr + n * U64.v mword <= MH.chunk_end (Seq.index mh idx))
      (ensures
        (let mh' = Defs.chunked_zero_fields mh addr n in
         MH.well_formed_major_heap mh' /\
         idx < Seq.length mh' /\
         MH.objects_in_chunk_from (Seq.index mh' idx) start ==
         MH.objects_in_chunk_from (Seq.index mh idx) start /\
         MH.chunk_start (Seq.index mh' idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index mh' idx) ==
         MH.chunk_end (Seq.index mh idx)))
