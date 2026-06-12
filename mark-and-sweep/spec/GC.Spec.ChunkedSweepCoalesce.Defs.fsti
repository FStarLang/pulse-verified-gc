module GC.Spec.ChunkedSweepCoalesce.Defs

open FStar.Seq

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module Obj = GC.Spec.Object
module Header = GC.Lib.Header
module MH = GC.Spec.MajorHeap
module SpecMajorAlloc = GC.Spec.MajorAllocator

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

val chunked_read_header_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (chunked_read_header (MH.single_chunk_major_heap g) obj ==
       Some (read_word g (hd_address obj)))

val chunked_color_of_object_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (chunked_color_of_object (MH.single_chunk_major_heap g) obj ==
       Some (Obj.color_of_object obj g))

val chunked_wosize_of_object_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (chunked_wosize_of_object (MH.single_chunk_major_heap g) obj ==
       Obj.wosize_of_object obj g)

val chunked_tag_of_object_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (chunked_tag_of_object (MH.single_chunk_major_heap g) obj ==
       Obj.tag_of_object obj g)

val chunked_is_white_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (chunked_is_white (MH.single_chunk_major_heap g) obj ==
       Obj.is_white obj g)

val chunked_is_blue_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (chunked_is_blue (MH.single_chunk_major_heap g) obj ==
       Obj.is_blue obj g)

val chunked_is_black_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (chunked_is_black (MH.single_chunk_major_heap g) obj ==
       Obj.is_black obj g)

val chunked_is_infix_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (chunked_is_infix (MH.single_chunk_major_heap g) obj ==
       Obj.is_infix obj g)

val chunked_sweep_aux_empty
  (mh: MH.major_heap) (fp: U64.t)
  : Lemma (chunked_sweep_aux mh Seq.empty fp == (mh, fp))

val chunked_sweep_step:
  mh:MH.major_heap ->
  fp:U64.t ->
  Lemma (chunked_sweep mh fp == chunked_sweep_chunks mh mh fp)

val chunked_set_object_color_some:
  mh:MH.major_heap ->
  obj:obj_addr ->
  color:Header.color_sem ->
  hdr:U64.t ->
  Lemma
    (requires chunked_read_header mh obj == Some hdr)
    (ensures
      chunked_set_object_color mh obj color ==
      SpecMajorAlloc.major_write_word_or_same
        mh (hd_address obj) (Obj.colorHeader hdr color))

val chunked_set_object_color_none:
  mh:MH.major_heap ->
  obj:obj_addr ->
  color:Header.color_sem ->
  Lemma
    (requires chunked_read_header mh obj == None)
    (ensures chunked_set_object_color mh obj color == mh)

val chunked_make_white_step:
  mh:MH.major_heap ->
  obj:obj_addr ->
  Lemma
    (chunked_make_white mh obj ==
     chunked_set_object_color mh obj Header.White)

val chunked_make_blue_step:
  mh:MH.major_heap ->
  obj:obj_addr ->
  Lemma
    (chunked_make_blue mh obj ==
     chunked_set_object_color mh obj Header.Blue)

val chunked_sweep_object_infix_step:
  mh:MH.major_heap ->
  obj:obj_addr ->
  fp:U64.t ->
  Lemma
    (requires chunked_is_infix mh obj)
    (ensures chunked_sweep_object mh obj fp == (mh, fp))

val chunked_sweep_object_white_step:
  mh:MH.major_heap ->
  obj:obj_addr ->
  fp:U64.t ->
  Lemma
    (requires ~(chunked_is_infix mh obj) /\
              chunked_is_white mh obj)
    (ensures
      chunked_sweep_object mh obj fp ==
      (let ws = chunked_wosize_of_object mh obj in
       let hd = hd_address obj in
       let mh' =
         if U64.v ws > 0 && U64.v hd + U64.v mword * 2 <= heap_size
         then SpecMajorAlloc.major_write_word_or_same mh obj fp
         else mh
       in
       (chunked_make_blue mh' obj, obj)))

val chunked_sweep_object_black_step:
  mh:MH.major_heap ->
  obj:obj_addr ->
  fp:U64.t ->
  Lemma
    (requires ~(chunked_is_infix mh obj) /\
              ~(chunked_is_white mh obj) /\
              chunked_is_black mh obj)
    (ensures
      chunked_sweep_object mh obj fp ==
      (chunked_make_white mh obj, fp))

val chunked_sweep_object_other_step:
  mh:MH.major_heap ->
  obj:obj_addr ->
  fp:U64.t ->
  Lemma
    (requires ~(chunked_is_infix mh obj) /\
              ~(chunked_is_white mh obj) /\
              ~(chunked_is_black mh obj))
    (ensures chunked_sweep_object mh obj fp == (mh, fp))

val chunked_sweep_aux_step
  (mh: MH.major_heap) (objs: seq obj_addr) (fp: U64.t)
  : Lemma
      (requires Seq.length objs > 0)
      (ensures
        (let obj = Seq.head objs in
         let (mh', fp') = chunked_sweep_object mh obj fp in
         chunked_sweep_aux mh objs fp ==
         chunked_sweep_aux mh' (Seq.tail objs) fp'))

val chunked_sweep_chunks_empty
  (work: MH.major_heap) (fp: U64.t)
  : Lemma (chunked_sweep_chunks Seq.empty work fp == (work, fp))

val chunked_sweep_chunks_step
  (source_chunks work: MH.major_heap) (fp: U64.t)
  : Lemma
      (requires Seq.length source_chunks > 0)
      (ensures
        (let c = Seq.head source_chunks in
         let (work', fp') =
           chunked_sweep_aux work (MH.objects_in_chunk c) fp in
         chunked_sweep_chunks source_chunks work fp ==
         chunked_sweep_chunks (Seq.tail source_chunks) work' fp'))

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
