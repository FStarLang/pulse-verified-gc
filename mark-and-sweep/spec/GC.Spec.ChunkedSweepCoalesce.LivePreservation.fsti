module GC.Spec.ChunkedSweepCoalesce.LivePreservation

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module Obj = GC.Spec.Object

val chunked_fused_aux_black_head_preserves_wosize
  (source work: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  (target: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        Seq.length objs > 0 /\
        Seq.head objs == target /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black
          source target /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_read_header
          work target == Some hdr /\
        (run_words = 0 \/
         U64.v first_blue + (run_words - 1) * U64.v mword <=
           U64.v (hd_address target)) /\
        (forall (o: obj_addr). Seq.mem o (Seq.tail objs) ==>
          U64.v (hd_address target) + U64.v mword * 2 <= U64.v o))
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
          (fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_fused_aux
            source work objs first_blue run_words fp))
          target ==
        Obj.getWosize hdr)
