module GC.Spec.ChunkedSweepCoalesce.VertexPreservation

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module Obj = GC.Spec.Object

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
