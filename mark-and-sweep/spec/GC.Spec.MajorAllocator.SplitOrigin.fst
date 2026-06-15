module GC.Spec.MajorAllocator.SplitOrigin

module U64 = FStar.UInt64
module Seq = FStar.Seq
module MH = GC.Spec.MajorHeap
module MA = GC.Spec.MajorAllocator
module SplitShape = GC.Spec.MajorAllocator.SplitShape
module Alloc = GC.Spec.Allocator
module AllocCore = GC.Spec.Allocator.Lemmas.Core
module Obj = GC.Spec.Object
module Header = GC.Lib.Header

open GC.Spec.Base
open GC.Spec.Heap

#push-options "--split_queries always --z3rlimit 10 --fuel 0 --ifuel 0"
let major_alloc_head_split_remainder_header_blue
  (mh: MH.major_heap) (fp: U64.t)
  (requested_wz fuel: nat)
  : Lemma
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
  =
  MA.major_fl_above_zero_current mh fp fuel;
  assert (U64.v fp >= U64.v zero_addr + U64.v mword);
  let obj : obj_addr = fp in
  let hd = hd_address obj in
  MA.major_fl_head_wosize_current mh fp fuel;
  MA.major_fl_head_block_fits_current mh fp fuel;
  MA.major_fl_valid_link_lookup_index mh fp fuel;
  let idx = MH.lookup_chunk_index_value mh hd in
  assert (MH.lookup_chunk_index mh hd == Some idx);
  assert (idx < Seq.length mh);
  assert (MH.word_in_chunk (Seq.index mh idx) hd);
  match MH.read_word_in_major mh hd with
  | None -> assert False
  | Some hdr ->
    let block_wz = U64.v (Obj.getWosize hdr) in
    assert (MA.major_fl_head_wosize mh fp == block_wz);
    assert (block_wz < pow2 54);
    assert (block_wz >= requested_wz + 2);
    assert (block_wz - requested_wz >= 2);
    assert (requested_wz < pow2 54);
    FStar.Math.Lemmas.pow2_lt_compat 64 54;
    assert (FStar.UInt.size requested_wz 64);
    match MH.read_word_in_major mh obj with
    | None -> assert False
    | Some next_fp ->
      let c = Seq.index mh idx in
      MH.read_word_in_major_at_lookup_index mh hd idx;
      assert (MH.read_word_in_chunk c hd == hdr);
      MA.major_fl_valid_gives_mem mh fp fuel;
      assert (Seq.mem obj (MH.major_objects mh));
      MH.major_objects_member_in_lookup_chunk mh idx obj;
      assert (Seq.mem obj (MH.objects_in_chunk c));
      assert (MH.object_wosize_in_chunk c obj == block_wz);
      assert (U64.v hd + (1 + block_wz) * U64.v mword <= MH.chunk_end c);
      assert (U64.v mword == 8);
      let rem_hd_nat = U64.v hd + (1 + requested_wz) * 8 in
      let rem_obj_nat = rem_hd_nat + U64.v mword in
      assert (requested_wz + 2 <= block_wz);
      FStar.Math.Lemmas.distributivity_add_left (requested_wz + 2) 1 8;
      assert ((requested_wz + 2) * 8 + 8 == (requested_wz + 3) * 8);
      FStar.Math.Lemmas.paren_add_right (U64.v hd) ((requested_wz + 2) * 8) 8;
      FStar.Math.Lemmas.distributivity_add_left (1 + requested_wz) 1 8;
      assert ((1 + requested_wz) * 8 + 8 == (requested_wz + 2) * 8);
      assert (rem_obj_nat == U64.v hd + (requested_wz + 2) * 8);
      assert (rem_obj_nat + 8 == U64.v hd + (requested_wz + 3) * 8);
      assert (requested_wz + 3 <= 1 + block_wz);
      FStar.Math.Lemmas.lemma_mult_le_right
        8 (requested_wz + 3) (1 + block_wz);
      assert (rem_obj_nat + 8 <= U64.v hd + (1 + block_wz) * 8);
      assert (rem_obj_nat + 8 <= MH.chunk_end c);
      assert (MH.chunk_end c <= heap_size);
      assert (rem_hd_nat < heap_size);
      assert (rem_obj_nat < heap_size);
      assert (heap_size < pow2 64);
      assert (rem_hd_nat < pow2 64);
      assert (rem_obj_nat < pow2 64);
      assert (rem_obj_nat >= U64.v mword);
      hd_address_spec obj;
      MA.aligned_plus_word_product (U64.v hd) (1 + requested_wz);
      assert (rem_hd_nat % U64.v mword == 0);
      MA.aligned_plus_word_product (U64.v hd) (requested_wz + 2);
      assert (rem_obj_nat % U64.v mword == 0);
      let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
      let rem_obj : obj_addr = U64.uint_to_t rem_obj_nat in
      assert (MH.word_in_chunk c rem_hd);
      assert (MH.word_in_chunk c rem_obj);
      f_address_spec rem_hd;
      hd_f_roundtrip rem_hd;
      assert (f_address rem_hd == rem_obj);
      assert (hd_address rem_obj == rem_hd);
      let rem_wz = block_wz - requested_wz - 1 in
      assert (rem_wz < pow2 54);
      assert (FStar.UInt.size rem_wz 64);
      let rem_wz_u : x:U64.t{U64.v x < pow2 54} =
        U64.uint_to_t rem_wz in
      assert (U64.v rem_wz_u == rem_wz);
      MA.major_alloc_head_split mh obj requested_wz fuel hdr next_fp
        rem_hd rem_obj;
      let r = MA.major_alloc_spec_with_fuel mh fp requested_wz fuel in
      assert (r.major_fp_out == rem_obj);
      assert (r.major_obj_out == fp);
      let alloc_hdr =
        Alloc.make_header (U64.uint_to_t requested_wz) Alloc.white_bits 0UL in
      let mh1 = MA.major_write_word_or_same mh hd alloc_hdr in
      let rem_hdr =
        Alloc.make_header rem_wz_u Alloc.blue_bits 0UL in
      let mh2 = MA.major_write_word_or_same mh1 rem_hd rem_hdr in
      let mh3 = MA.major_write_word_or_same mh2 rem_obj next_fp in
      assert (r.major_alloc_out == mh3);
      MA.head_split_materialize_writes
        mh idx obj requested_wz next_fp rem_wz_u rem_hd rem_obj;
      MH.lookup_chunk_index_word_in_chunk mh rem_hd idx;
      assert (MH.lookup_chunk_index mh rem_hd == Some idx);
      SplitShape.head_split_preserves_lookup_word
        mh idx idx obj rem_hd requested_wz next_fp rem_wz_u rem_hd rem_obj;
      assert (MH.lookup_chunk_index mh3 rem_hd == Some idx);
      assert (Seq.index mh3 idx ==
        MH.write_word_in_chunk
          (MH.write_word_in_chunk
            (MH.write_word_in_chunk (Seq.index mh idx) hd alloc_hdr)
            rem_hd rem_hdr)
          rem_obj next_fp);
      let c1 = MH.write_word_in_chunk (Seq.index mh idx) hd alloc_hdr in
      let c2 = MH.write_word_in_chunk c1 rem_hd rem_hdr in
      let c3 = MH.write_word_in_chunk c2 rem_obj next_fp in
      MH.read_write_in_chunk_same c1 rem_hd rem_hdr;
      MH.write_word_in_chunk_preserves_range
        c1 rem_hd rem_hdr;
      MH.write_word_in_chunk_preserves_range
        c2 rem_obj next_fp;
      assert (U64.v rem_hd + U64.v mword <= U64.v rem_obj);
      MH.read_write_in_chunk_different c2 rem_obj rem_hd next_fp;
      assert (MH.read_word_in_chunk c3 rem_hd == rem_hdr);
      MH.read_word_in_major_at_lookup_index mh3 rem_hd idx;
      assert (MH.read_word_in_major mh3 rem_hd == Some rem_hdr);
      AllocCore.make_header_getColor rem_wz_u Alloc.blue_bits 0UL;
      Obj.getColor_raw rem_hdr;
      assert (Header.get_color (U64.v rem_hdr) == U64.v Alloc.blue_bits);
      assert (Obj.getColor rem_hdr == Header.Blue);
      assert (r.major_alloc_out == mh3);
      assert (hd_address rem_obj == rem_hd);
      FStar.Classical.exists_intro
        (fun rem_obj' ->
          r.major_fp_out == rem_obj' /\
          (match MH.read_word_in_major
                   r.major_alloc_out (hd_address rem_obj') with
           | Some hdr -> Obj.getColor hdr == Header.Blue
           | None -> False))
        rem_obj
#pop-options
