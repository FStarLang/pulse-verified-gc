module GC.Spec.MajorHeap.FieldRead

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object

module U64 = FStar.UInt64
module MH = GC.Spec.MajorHeap

val major_objects_member_payload_read_some:
  mh:MH.major_heap ->
  x:obj_addr ->
  hdr:U64.t ->
  field_addr:hp_addr ->
  Lemma
    (requires
      MH.well_formed_major_heap mh /\
      Seq.mem x (MH.major_objects mh) /\
      MH.read_word_in_major mh (hd_address x) == Some hdr /\
      U64.v x <= U64.v field_addr /\
      U64.v field_addr + U64.v mword <=
        U64.v x + U64.v (getWosize hdr) * U64.v mword)
    (ensures
      (match MH.read_word_in_major mh field_addr with
       | Some _ -> True
       | None -> False))
