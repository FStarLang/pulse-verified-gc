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
module SpecSweep = GC.Spec.Sweep

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
