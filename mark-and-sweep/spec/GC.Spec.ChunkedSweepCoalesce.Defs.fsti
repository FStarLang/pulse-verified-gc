module GC.Spec.ChunkedSweepCoalesce.Defs

open FStar.Seq

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module Obj = GC.Spec.Object
module Header = GC.Lib.Header
module MH = GC.Spec.MajorHeap

val chunked_read_header
  (mh: MH.major_heap) (obj: obj_addr)
  : GTot (option U64.t)

val chunked_color_of_object
  (mh: MH.major_heap) (obj: obj_addr)
  : GTot (option Obj.color)

val chunked_wosize_of_object
  (mh: MH.major_heap) (obj: obj_addr)
  : GTot Obj.wosize

val chunked_tag_of_object
  (mh: MH.major_heap) (obj: obj_addr)
  : GTot U64.t

val chunked_is_white
  (mh: MH.major_heap) (obj: obj_addr)
  : GTot bool

val chunked_is_blue
  (mh: MH.major_heap) (obj: obj_addr)
  : GTot bool

val chunked_is_black
  (mh: MH.major_heap) (obj: obj_addr)
  : GTot bool

val chunked_is_infix
  (mh: MH.major_heap) (obj: obj_addr)
  : GTot bool

val chunked_set_object_color
  (mh: MH.major_heap) (obj: obj_addr) (color: Header.color_sem)
  : GTot MH.major_heap

val chunked_make_white
  (mh: MH.major_heap) (obj: obj_addr)
  : GTot MH.major_heap

val chunked_make_blue
  (mh: MH.major_heap) (obj: obj_addr)
  : GTot MH.major_heap

val chunked_sweep_object
  (mh: MH.major_heap) (obj: obj_addr) (fp: U64.t)
  : GTot (MH.major_heap & U64.t)

val chunked_sweep_aux
  (mh: MH.major_heap) (objs: seq obj_addr) (fp: U64.t)
  : GTot (MH.major_heap & U64.t)

val chunked_sweep_chunks
  (source_chunks: MH.major_heap) (work: MH.major_heap) (fp: U64.t)
  : GTot (MH.major_heap & U64.t)

val chunked_sweep
  (mh: MH.major_heap) (fp: U64.t)
  : GTot (MH.major_heap & U64.t)

val chunked_zero_fields
  (mh: MH.major_heap) (addr: U64.t) (n: nat)
  : GTot MH.major_heap

val chunked_flush_blue
  (mh: MH.major_heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : GTot (MH.major_heap & U64.t)

val chunked_fused_aux
  (source: MH.major_heap) (work: MH.major_heap) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : GTot (MH.major_heap & U64.t)

val chunked_fused_sweep_coalesce_chunks
  (source_chunks: MH.major_heap) (source: MH.major_heap)
  (work: MH.major_heap) (fp: U64.t)
  : GTot (MH.major_heap & U64.t)

val chunked_fused_sweep_coalesce
  (mh: MH.major_heap)
  : GTot (MH.major_heap & U64.t)

val chunked_sweep_aux_empty
  (mh: MH.major_heap) (fp: U64.t)
  : Lemma (chunked_sweep_aux mh Seq.empty fp == (mh, fp))

val chunked_sweep_aux_step
  (mh: MH.major_heap) (objs: seq obj_addr) (fp: U64.t)
  : Lemma
      (requires Seq.length objs > 0)
      (ensures
        (let obj = Seq.head objs in
         let (mh', fp') = chunked_sweep_object mh obj fp in
         chunked_sweep_aux mh objs fp ==
         chunked_sweep_aux mh' (Seq.tail objs) fp'))

val chunked_fused_aux_empty
  (source work: MH.major_heap) (first_blue: U64.t) (run_words: nat)
  (fp: U64.t)
  : Lemma
      (chunked_fused_aux source work Seq.empty first_blue run_words fp ==
       chunked_flush_blue work first_blue run_words fp)

val chunked_fused_aux_black_step
  (source work: MH.major_heap) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
      (requires Seq.length objs > 0 /\
                chunked_is_black source (Seq.head objs))
      (ensures
        (let obj = Seq.head objs in
         let rest = Seq.tail objs in
         let (work', fp') = chunked_flush_blue work first_blue run_words fp in
         let work'' = chunked_make_white work' obj in
         chunked_fused_aux source work objs first_blue run_words fp ==
         chunked_fused_aux source work'' rest 0UL 0 fp'))

val chunked_fused_aux_nonblack_step
  (source work: MH.major_heap) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
      (requires Seq.length objs > 0 /\
                ~(chunked_is_black source (Seq.head objs)))
      (ensures
        (let obj = Seq.head objs in
         let rest = Seq.tail objs in
         let ws = U64.v (chunked_wosize_of_object source obj) in
         let new_first : U64.t = if run_words = 0 then obj else first_blue in
         chunked_fused_aux source work objs first_blue run_words fp ==
         chunked_fused_aux source work rest new_first (run_words + ws + 1) fp))

val chunked_fused_sweep_coalesce_chunks_empty
  (source work: MH.major_heap) (fp: U64.t)
  : Lemma
      (chunked_fused_sweep_coalesce_chunks Seq.empty source work fp ==
       (work, fp))

val chunked_fused_sweep_coalesce_chunks_step
  (source_chunks source work: MH.major_heap) (fp: U64.t)
  : Lemma
      (requires Seq.length source_chunks > 0)
      (ensures
        (let c = Seq.head source_chunks in
         let (work', fp') =
           chunked_fused_aux source work (MH.objects_in_chunk c) 0UL 0 fp
         in
         chunked_fused_sweep_coalesce_chunks source_chunks source work fp ==
         chunked_fused_sweep_coalesce_chunks
           (Seq.tail source_chunks) source work' fp'))
