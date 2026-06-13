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

val chunked_fused_aux_black_head_preserves_vertex_from_chunk
    (source work: MH.major_heap)
    (idx: nat)
    (c: MH.heap_chunk)
    (start: hp_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
    (target: obj_addr)
    (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap work /\
        idx < Seq.length work /\
        MH.chunk_start (Seq.index work idx) == MH.chunk_start c /\
        MH.chunk_end (Seq.index work idx) == MH.chunk_end c /\
        Seq.mem target (MH.objects_in_chunk_from c start) /\
        Seq.length (MH.objects_in_chunk_from c start) > 0 /\
        Seq.head (MH.objects_in_chunk_from c start) == target /\
        hd_address target == start /\
        Seq.mem target
          (MH.objects_in_chunk_from (Seq.index work idx) c.base) /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_read_header
          work target == Some hdr /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black source target /\
        U64.v (Obj.getWosize hdr) == MH.object_wosize_in_chunk c target /\
        (forall (o: obj_addr). Seq.mem o (MH.objects_in_chunk_from c start) ==>
          U64.v (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
                   source o) ==
          MH.object_wosize_in_chunk c o) /\
        (run_words = 0 \/
         (~(U64.v first_blue < U64.v mword) /\
          ~(U64.v first_blue >= heap_size) /\
          ~(U64.v first_blue % U64.v mword <> 0) /\
          run_words - 1 < pow2 54 /\
          run_words - 1 < pow2 64 /\
          U64.v first_blue + (run_words - 1) * U64.v mword ==
            U64.v start /\
          (let fb : obj_addr = first_blue in
           Seq.mem fb
             (MH.objects_in_chunk_from (Seq.index work idx) c.base) /\
           U64.v fb < MH.chunk_end (Seq.index work idx) /\
           U64.v start <= MH.chunk_end (Seq.index work idx) /\
           MH.word_in_chunk (Seq.index work idx) (hd_address fb) /\
           Seq.mem target
             (MH.objects_in_chunk_from (Seq.index work idx) start)))))
      (ensures
        (let final =
          fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_fused_aux
            source work (MH.objects_in_chunk_from c start)
            first_blue run_words fp) in
         MH.well_formed_major_heap final /\
         idx < Seq.length final /\
         Seq.mem target
           (MH.objects_in_chunk_from (Seq.index final idx) c.base) /\
         GC.Spec.ChunkedMajorGC.Graph.chunked_major_vertex final target /\
         MH.chunk_start (Seq.index final idx) ==
         MH.chunk_start (Seq.index work idx) /\
         MH.chunk_end (Seq.index final idx) ==
         MH.chunk_end (Seq.index work idx)))

val chunked_fused_aux_live_wosize_preserved_from_chunk
  (source: MH.major_heap)
  (c: MH.heap_chunk)
  (fp: U64.t)
  (target: obj_addr)
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
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black source target /\
        U64.v (Obj.getWosize hdr) == MH.object_wosize_in_chunk c target)
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
          (fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_fused_aux
            source source (MH.objects_in_chunk c) 0UL 0 fp))
          target ==
        Obj.getWosize hdr)

val chunked_fused_aux_live_vertex_preserved_from_chunk
  (source: MH.major_heap)
  (idx: nat)
  (fp: U64.t)
  (target: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        idx < Seq.length source /\
        Seq.mem target (MH.objects_in_chunk (Seq.index source idx)) /\
        (forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
                   source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o) /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_read_header
          source target == Some hdr /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black source target /\
        U64.v (Obj.getWosize hdr) ==
          MH.object_wosize_in_chunk (Seq.index source idx) target)
      (ensures
        (let c = Seq.index source idx in
         let final =
           fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_fused_aux
             source source (MH.objects_in_chunk c) 0UL 0 fp) in
         MH.well_formed_major_heap final /\
         idx < Seq.length final /\
         Seq.mem target
           (MH.objects_in_chunk_from (Seq.index final idx) c.base) /\
         GC.Spec.ChunkedMajorGC.Graph.chunked_major_vertex final target /\
         MH.chunk_start (Seq.index final idx) ==
         MH.chunk_start (Seq.index source idx) /\
         MH.chunk_end (Seq.index final idx) ==
         MH.chunk_end (Seq.index source idx)))

val chunked_fused_aux_live_field_preserved_from_chunk
  (source: MH.major_heap)
  (idx: nat)
  (fp: U64.t)
  (target: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        idx < Seq.length source /\
        Seq.mem target (MH.objects_in_chunk (Seq.index source idx)) /\
        (forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
                   source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o) /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_read_header
          source target == Some hdr /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black source target /\
        U64.v (Obj.getWosize hdr) ==
          MH.object_wosize_in_chunk (Seq.index source idx) target)
      (ensures
        (let final =
          fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_fused_aux
            source source (MH.objects_in_chunk (Seq.index source idx))
            0UL 0 fp) in
         GC.Spec.ChunkedMajorGC.Graph.chunked_major_field_preserved
           source final target))

val chunked_fused_aux_live_subgraph_preserved_from_chunk
  (source: MH.major_heap)
  (idx: nat)
  (fp: U64.t)
  (live: obj_addr -> prop)
  (live_hdr: obj_addr -> U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        idx < Seq.length source /\
        (forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
                   source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o) /\
        (forall (target: obj_addr).
          live target ==>
          Seq.mem target (MH.objects_in_chunk (Seq.index source idx)) /\
          GC.Spec.ChunkedSweepCoalesce.Defs.chunked_read_header
            source target == Some (live_hdr target) /\
          GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black source target /\
          U64.v (Obj.getWosize (live_hdr target)) ==
            MH.object_wosize_in_chunk (Seq.index source idx) target))
      (ensures
        (let final =
          fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_fused_aux
            source source (MH.objects_in_chunk (Seq.index source idx))
            0UL 0 fp) in
         GC.Spec.ChunkedMajorGC.Graph.chunked_major_live_subgraph_preserved
           source final live))

val chunked_set_object_color_preserves_major_objects
  (mh: MH.major_heap)
  (idx: nat)
  (obj: obj_addr)
  (color: GC.Lib.Header.color_sem)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        MH.lookup_chunk_index mh (hd_address obj) == Some idx /\
        Seq.mem obj (MH.major_objects mh) /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_read_header
          mh obj == Some hdr)
      (ensures
        MH.major_objects
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_set_object_color
            mh obj color) ==
        MH.major_objects mh)

val chunked_make_white_preserves_major_objects
  (mh: MH.major_heap)
  (idx: nat)
  (obj: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        MH.lookup_chunk_index mh (hd_address obj) == Some idx /\
        Seq.mem obj (MH.major_objects mh) /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_read_header
          mh obj == Some hdr)
      (ensures
        MH.major_objects
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_make_white mh obj) ==
        MH.major_objects mh)

val chunked_make_blue_preserves_major_objects
  (mh: MH.major_heap)
  (idx: nat)
  (obj: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        MH.lookup_chunk_index mh (hd_address obj) == Some idx /\
        Seq.mem obj (MH.major_objects mh) /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_read_header
          mh obj == Some hdr)
      (ensures
        MH.major_objects
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_make_blue mh obj) ==
        MH.major_objects mh)
