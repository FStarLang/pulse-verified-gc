module GC.Spec.MajorHeap.FieldRead

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object

module U64 = FStar.UInt64
module Obj = GC.Spec.Object
module MH = GC.Spec.MajorHeap

#push-options "--z3rlimit 10 --split_queries always --fuel 0 --ifuel 0"
let major_objects_member_payload_read_some
  (mh: MH.major_heap) (x: obj_addr) (hdr: U64.t) (field_addr: hp_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem x (MH.major_objects mh) /\
        MH.read_word_in_major mh (hd_address x) == Some hdr /\
        U64.v x <= U64.v field_addr /\
        U64.v field_addr + U64.v mword <=
          U64.v x + U64.v (Obj.getWosize hdr) * U64.v mword)
      (ensures
        (match MH.read_word_in_major mh field_addr with
         | Some _ -> True
         | None -> False))
  =
  let xhd = hd_address x in
  MH.read_word_in_major_lookup_index mh xhd hdr;
  let idx = MH.lookup_chunk_index_value mh xhd in
  assert (MH.lookup_chunk_index mh xhd == Some idx);
  assert (idx < Seq.length mh);
  assert (MH.word_in_chunk (Seq.index mh idx) xhd);
  assert (MH.read_word_in_chunk (Seq.index mh idx) xhd == hdr);
  MH.major_objects_member_in_lookup_chunk mh idx x;
  assert (Seq.mem x (MH.objects_in_chunk (Seq.index mh idx)));
  MH.objects_in_chunk_member_header_fits (Seq.index mh idx) x;
  assert (MH.object_header_size_fits_in_chunk (Seq.index mh idx) x);
  hd_address_spec x;
  assert (U64.v xhd + U64.v mword == U64.v x);
  assert (U64.v xhd + (1 + U64.v (Obj.getWosize hdr)) * U64.v mword <=
          MH.chunk_end (Seq.index mh idx));
  FStar.Math.Lemmas.distributivity_add_left
    1 (U64.v (Obj.getWosize hdr)) (U64.v mword);
  assert ((1 + U64.v (Obj.getWosize hdr)) * U64.v mword ==
          U64.v mword + U64.v (Obj.getWosize hdr) * U64.v mword);
  assert (U64.v x + U64.v (Obj.getWosize hdr) * U64.v mword ==
          U64.v xhd + U64.v mword +
            U64.v (Obj.getWosize hdr) * U64.v mword);
  assert (U64.v field_addr >= MH.chunk_start (Seq.index mh idx));
  assert (U64.v field_addr + U64.v mword <= MH.chunk_end (Seq.index mh idx));
  assert (MH.word_in_chunk (Seq.index mh idx) field_addr);
  MH.lookup_chunk_index_word_in_chunk mh field_addr idx;
  MH.read_word_in_major_at_lookup_index mh field_addr idx
#pop-options
