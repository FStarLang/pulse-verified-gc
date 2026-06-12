module GC.Spec.ChunkedSweepCoalesce.Compat

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module Header = GC.Lib.Header
module MH = GC.Spec.MajorHeap
module Obj = GC.Spec.Object
module Fields = GC.Spec.Fields
module Defs = GC.Spec.ChunkedSweepCoalesce.Defs
module SpecAlloc = GC.Spec.Allocator
module SpecCoalesce = GC.Spec.Coalesce
module SpecSweep = GC.Spec.Sweep
module DenseFused = GC.Spec.SweepCoalesce.Defs

val chunked_make_white_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (Defs.chunked_make_white (MH.single_chunk_major_heap g) obj ==
       MH.single_chunk_major_heap (Obj.makeWhite obj g))

val chunked_make_blue_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (Defs.chunked_make_blue (MH.single_chunk_major_heap g) obj ==
       MH.single_chunk_major_heap (Obj.makeBlue obj g))

val chunked_sweep_object_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  (fp: U64.t)
  : Lemma
      (Defs.chunked_sweep_object (MH.single_chunk_major_heap g) obj fp ==
       (let (g', fp') = SpecSweep.sweep_object g obj fp in
        (MH.single_chunk_major_heap g', fp')))

val chunked_sweep_aux_single_chunk_compat
  (g: heap)
  (objs: Seq.seq obj_addr)
  (fp: U64.t)
  : Lemma
      (requires
        (forall (o: obj_addr). Seq.mem o objs ==> U64.v o >= U64.v zero_addr + U64.v mword))
      (ensures
        Defs.chunked_sweep_aux (MH.single_chunk_major_heap g) objs fp ==
        (let (g', fp') = SpecSweep.sweep_aux g objs fp in
         (MH.single_chunk_major_heap g', fp')))

val chunked_sweep_single_chunk_compat
  (g: heap)
  (fp: U64.t)
  : Lemma
      (Defs.chunked_sweep (MH.single_chunk_major_heap g) fp ==
       (let (g', fp') = SpecSweep.sweep g fp in
        (MH.single_chunk_major_heap g', fp')))

val chunked_zero_fields_single_chunk_compat
  (g: heap)
  (addr: U64.t)
  (n: nat)
  : Lemma
      (requires n = 0 \/ U64.v addr >= U64.v zero_addr)
      (ensures
        Defs.chunked_zero_fields (MH.single_chunk_major_heap g) addr n ==
        MH.single_chunk_major_heap (SpecAlloc.zero_fields g addr n))

val chunked_flush_blue_single_chunk_compat
  (g: heap)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  : Lemma
      (requires
        run_words = 0 \/
        U64.v first_blue >= U64.v zero_addr + U64.v mword)
      (ensures
        Defs.chunked_flush_blue
          (MH.single_chunk_major_heap g) first_blue run_words fp ==
        (let (g', fp') =
          SpecCoalesce.flush_blue g first_blue run_words fp in
         (MH.single_chunk_major_heap g', fp')))

val chunked_fused_aux_single_chunk_compat
  (source work: heap)
  (objs: Seq.seq obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  : Lemma
      (requires
        (forall (o: obj_addr). Seq.mem o objs ==> U64.v o >= U64.v zero_addr + U64.v mword) /\
        (run_words = 0 \/
         U64.v first_blue >= U64.v zero_addr + U64.v mword))
      (ensures
        Defs.chunked_fused_aux
          (MH.single_chunk_major_heap source)
          (MH.single_chunk_major_heap work)
          objs first_blue run_words fp ==
        (let (work', fp') =
          DenseFused.fused_aux source work objs first_blue run_words fp in
         (MH.single_chunk_major_heap work', fp')))

val chunked_fused_sweep_coalesce_single_chunk_compat
  (g: heap)
  : Lemma
      (Defs.chunked_fused_sweep_coalesce (MH.single_chunk_major_heap g) ==
       (let (g', fp') = DenseFused.fused_sweep_coalesce g in
        (MH.single_chunk_major_heap g', fp')))
