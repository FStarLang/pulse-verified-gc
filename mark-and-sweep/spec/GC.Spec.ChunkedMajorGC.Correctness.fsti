module GC.Spec.ChunkedMajorGC.Correctness

module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module DenseCorrectness = GC.Spec.Correctness

val chunked_no_gray_or_black_objects
  (mh: MH.major_heap)
  : prop

val chunked_gc_postcondition
  (mh: MH.major_heap)
  : prop

val chunked_gc_postcondition_intro
  (mh: MH.major_heap)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_no_gray_or_black_objects mh)
      (ensures chunked_gc_postcondition mh)

val chunked_gc_postcondition_elim
  (mh: MH.major_heap)
  : Lemma
      (requires chunked_gc_postcondition mh)
      (ensures
        MH.well_formed_major_heap mh /\
        chunked_no_gray_or_black_objects mh)

val chunked_no_gray_or_black_single_chunk_from_dense
  (g: heap)
  : Lemma
      (requires DenseCorrectness.gc_postcondition g)
      (ensures
        chunked_no_gray_or_black_objects
          (MH.single_chunk_major_heap g))

val chunked_gc_postcondition_single_chunk_from_dense
  (g: heap)
  : Lemma
      (requires DenseCorrectness.gc_postcondition g)
      (ensures
        chunked_gc_postcondition (MH.single_chunk_major_heap g))

