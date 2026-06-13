module GC.Spec.ChunkedSweepCoalesce.VertexReachPrefix

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module Obj = GC.Spec.Object
module Defs = GC.Spec.ChunkedSweepCoalesce.Defs

val base_member_and_header_member_implies_base_member
    (final: MH.major_heap)
    (idx: nat)
    (base: hp_addr)
    (fb: obj_addr)
    (target: obj_addr)
  : Lemma
      (requires
        idx < Seq.length final /\
        Seq.mem fb (MH.objects_in_chunk_from (Seq.index final idx) base) /\
        Seq.mem target
          (MH.objects_in_chunk_from (Seq.index final idx) (hd_address fb)))
      (ensures
        Seq.mem target (MH.objects_in_chunk_from (Seq.index final idx) base))

val chunked_flush_blue_prefix_preserves_base_member
    (mh: MH.major_heap)
    (idx: nat)
    (base: hp_addr)
    (fb: obj_addr)
    (run_words: pos)
    (start: hp_addr)
    (target: obj_addr)
    (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem fb (MH.objects_in_chunk_from (Seq.index mh idx) base) /\
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
         Seq.mem target (MH.objects_in_chunk_from (Seq.index final idx) base) /\
         MH.chunk_start (Seq.index final idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index final idx) ==
         MH.chunk_end (Seq.index mh idx)))

val chunked_flush_blue_then_make_white_head_preserves_base_member
    (mh: MH.major_heap)
    (idx: nat)
    (base: hp_addr)
    (target: obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
    (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem target (MH.objects_in_chunk_from (Seq.index mh idx) base) /\
        Defs.chunked_read_header mh target == Some hdr /\
        (run_words = 0 \/
         (~(U64.v first_blue < U64.v mword) /\
          ~(U64.v first_blue >= heap_size) /\
          ~(U64.v first_blue % U64.v mword <> 0) /\
          run_words - 1 < pow2 54 /\
          run_words - 1 < pow2 64 /\
          U64.v first_blue + (run_words - 1) * U64.v mword ==
            U64.v (hd_address target) /\
          (let fb : obj_addr = first_blue in
           Seq.mem fb (MH.objects_in_chunk_from (Seq.index mh idx) base) /\
           U64.v fb < MH.chunk_end (Seq.index mh idx) /\
           U64.v (hd_address target) <= MH.chunk_end (Seq.index mh idx) /\
           MH.word_in_chunk (Seq.index mh idx) (hd_address fb) /\
           Seq.mem target
             (MH.objects_in_chunk_from
               (Seq.index mh idx) (hd_address target))))))
      (ensures
        (let flushed = Defs.chunked_flush_blue mh first_blue run_words fp in
         let work' = fst flushed in
         let work'' = Defs.chunked_make_white work' target in
         MH.well_formed_major_heap work'' /\
         idx < Seq.length work'' /\
         Seq.mem target
           (MH.objects_in_chunk_from (Seq.index work'' idx) base) /\
         MH.object_wosize_in_chunk (Seq.index work'' idx) target ==
         U64.v (Obj.getWosize hdr) /\
         MH.chunk_start (Seq.index work'' idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index work'' idx) ==
         MH.chunk_end (Seq.index mh idx)))
