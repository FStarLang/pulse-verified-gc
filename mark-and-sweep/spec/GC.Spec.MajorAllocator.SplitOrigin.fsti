module GC.Spec.MajorAllocator.SplitOrigin

module U64 = FStar.UInt64
module MH = GC.Spec.MajorHeap
module MA = GC.Spec.MajorAllocator
module Obj = GC.Spec.Object
module Header = GC.Lib.Header

open GC.Spec.Base
open GC.Spec.Heap

val major_alloc_head_split_remainder_header_blue:
  mh:MH.major_heap ->
  fp:U64.t ->
  requested_wz:nat ->
  fuel:nat ->
  Lemma
    (requires
      fuel > 1 /\
      fp <> 0UL /\
      requested_wz > 0 /\
      MH.well_formed_major_heap mh /\
      MA.major_fl_valid mh fp fuel /\
      MA.major_fl_above_zero mh fp fuel /\
      MA.major_fl_blocks_fit mh fp fuel /\
      MA.major_fl_head_wosize mh fp >= requested_wz + 2)
    (ensures
      (let r = MA.major_alloc_spec_with_fuel mh fp requested_wz fuel in
       r.major_obj_out == fp /\
       r.major_fp_out <> 0UL /\
       exists (rem_obj: obj_addr).
         r.major_fp_out == rem_obj /\
         (match MH.read_word_in_major
                  r.major_alloc_out (hd_address rem_obj) with
          | Some hdr -> Obj.getColor hdr == Header.Blue
          | None -> False)))
