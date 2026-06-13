module GC.Spec.ChunkedMajorGC.Correctness

module Seq = FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap

module Obj = GC.Spec.Object
module Fields = GC.Spec.Fields
module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module DenseCorrectness = GC.Spec.Correctness

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let chunked_no_gray_or_black_objects (mh: MH.major_heap) : prop =
  forall (x: obj_addr). Seq.mem x (MH.major_objects mh) ==>
    SweepDefs.chunked_is_white mh x \/ SweepDefs.chunked_is_blue mh x

let chunked_gc_postcondition (mh: MH.major_heap) : prop =
  MH.well_formed_major_heap mh /\
  chunked_no_gray_or_black_objects mh

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let fields_object_after_zero_addr (g: heap) (x: obj_addr)
  : Lemma
      (requires Seq.mem x (Fields.objects zero_addr g))
      (ensures U64.v x >= U64.v zero_addr + U64.v mword)
  =
  Fields.objects_addresses_gt_start zero_addr g x
#pop-options

let chunked_gc_postcondition_intro (mh: MH.major_heap)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_no_gray_or_black_objects mh)
      (ensures chunked_gc_postcondition mh)
  = ()

let chunked_gc_postcondition_elim (mh: MH.major_heap)
  : Lemma
      (requires chunked_gc_postcondition mh)
      (ensures
        MH.well_formed_major_heap mh /\
        chunked_no_gray_or_black_objects mh)
  = ()

let chunked_no_gray_or_black_single_chunk_from_dense (g: heap)
  : Lemma
      (requires DenseCorrectness.gc_postcondition g)
      (ensures
        chunked_no_gray_or_black_objects
          (MH.single_chunk_major_heap g))
  =
  DenseCorrectness.gc_postcondition_elim g;
  MH.single_chunk_major_objects_compat g;
  let aux (x: obj_addr)
    : Lemma
        (requires Seq.mem x (MH.major_objects (MH.single_chunk_major_heap g)))
        (ensures
          SweepDefs.chunked_is_white (MH.single_chunk_major_heap g) x \/
          SweepDefs.chunked_is_blue (MH.single_chunk_major_heap g) x)
    =
    assert (Seq.mem x (Fields.objects zero_addr g));
    fields_object_after_zero_addr g x;
    SweepDefs.chunked_is_white_single_chunk_compat g x;
    SweepDefs.chunked_is_blue_single_chunk_compat g x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let chunked_gc_postcondition_single_chunk_from_dense (g: heap)
  : Lemma
      (requires DenseCorrectness.gc_postcondition g)
      (ensures
        chunked_gc_postcondition (MH.single_chunk_major_heap g))
  =
  DenseCorrectness.gc_postcondition_elim g;
  MH.single_chunk_major_heap_wf g;
  chunked_no_gray_or_black_single_chunk_from_dense g
