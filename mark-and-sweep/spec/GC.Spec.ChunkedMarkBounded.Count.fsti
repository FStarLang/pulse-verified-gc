module GC.Spec.ChunkedMarkBounded.Count

module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs

val chunked_count_non_black_in_preserved_by_black_status
  (mh mh': MH.major_heap)
  (objs: Seq.seq obj_addr)
  : Lemma
      (requires
        (forall (obj: obj_addr).
          Seq.mem obj objs ==>
            SweepDefs.chunked_is_black mh' obj ==
            SweepDefs.chunked_is_black mh obj))
      (ensures
        BDefs.chunked_count_non_black_in mh' objs ==
        BDefs.chunked_count_non_black_in mh objs)

val chunked_count_non_black_preserved_by_black_status
  (mh mh': MH.major_heap)
  : Lemma
      (requires
        MH.major_objects mh' == MH.major_objects mh /\
        (forall (obj: obj_addr).
          Seq.mem obj (MH.major_objects mh) ==>
            SweepDefs.chunked_is_black mh' obj ==
            SweepDefs.chunked_is_black mh obj))
      (ensures
        BDefs.chunked_count_non_black mh' ==
        BDefs.chunked_count_non_black mh)

val chunked_count_non_black_in_black_status_flip_le
  (mh mh': MH.major_heap)
  (objs: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        SweepDefs.chunked_is_black mh' target /\
        (forall (obj: obj_addr).
          Seq.mem obj objs /\ obj <> target ==>
            SweepDefs.chunked_is_black mh' obj ==
            SweepDefs.chunked_is_black mh obj))
      (ensures
        BDefs.chunked_count_non_black_in mh' objs <=
        BDefs.chunked_count_non_black_in mh objs)

val chunked_count_non_black_in_black_status_flip_decreases
  (mh mh': MH.major_heap)
  (objs: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        Seq.mem target objs /\
        ~(SweepDefs.chunked_is_black mh target) /\
        SweepDefs.chunked_is_black mh' target /\
        (forall (obj: obj_addr).
          Seq.mem obj objs /\ obj <> target ==>
            SweepDefs.chunked_is_black mh' obj ==
            SweepDefs.chunked_is_black mh obj))
      (ensures
        BDefs.chunked_count_non_black_in mh' objs <
        BDefs.chunked_count_non_black_in mh objs)

val chunked_is_gray_not_black
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires BDefs.chunked_is_gray mh obj)
      (ensures ~(SweepDefs.chunked_is_black mh obj))
