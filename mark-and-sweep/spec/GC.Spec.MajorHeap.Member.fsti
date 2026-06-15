module GC.Spec.MajorHeap.Member

module Seq = FStar.Seq
module MH = GC.Spec.MajorHeap

open GC.Spec.Base

val major_objects_member_at_index_small:
  mh:MH.major_heap ->
  idx:nat ->
  x:obj_addr ->
  Lemma
    (requires
      idx < Seq.length mh /\
      Seq.mem x (MH.objects_in_chunk (Seq.index mh idx)))
    (ensures Seq.mem x (MH.major_objects mh))

val major_objects_member_at_equal_index_small:
  mh:MH.major_heap ->
  idx:nat ->
  c:MH.heap_chunk ->
  x:obj_addr ->
  Lemma
    (requires
      idx < Seq.length mh /\
      Seq.index mh idx == c /\
      Seq.mem x (MH.objects_in_chunk c))
    (ensures Seq.mem x (MH.major_objects mh))
