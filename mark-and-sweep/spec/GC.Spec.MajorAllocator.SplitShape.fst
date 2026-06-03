module GC.Spec.MajorAllocator.SplitShape

module U64 = FStar.UInt64
module Seq = FStar.Seq
module MH = GC.Spec.MajorHeap
module MA = GC.Spec.MajorAllocator
module Alloc = GC.Spec.Allocator
module Obj = GC.Spec.Object

open GC.Spec.Base
open GC.Spec.Heap

let head_split_heap
  (mh: MH.major_heap) (obj: obj_addr)
  (requested_wz: nat{requested_wz < pow2 54 /\ FStar.UInt.size requested_wz 64})
  (next_fp: U64.t) (rem_wz_u: U64.t{U64.v rem_wz_u < pow2 54})
  (rem_hd: hp_addr) (rem_obj: obj_addr)
  : GTot MH.major_heap =
  let hd = hd_address obj in
  let alloc_hdr =
    Alloc.make_header (U64.uint_to_t requested_wz) Alloc.white_bits 0UL in
  let mh1 = MA.major_write_word_or_same mh hd alloc_hdr in
  let rem_hdr =
    Alloc.make_header rem_wz_u Alloc.blue_bits 0UL in
  let mh2 = MA.major_write_word_or_same mh1 rem_hd rem_hdr in
  MA.major_write_word_or_same mh2 rem_obj next_fp

#push-options "--z3rlimit 10 --split_queries always --fuel 0 --ifuel 0"
let head_split_preserves_lookup_word
  (mh: MH.major_heap) (idx target_idx: nat) (obj: obj_addr)
  (target_addr: hp_addr)
  (requested_wz: nat{requested_wz < pow2 54 /\ FStar.UInt.size requested_wz 64})
  (next_fp: U64.t) (rem_wz_u: U64.t{U64.v rem_wz_u < pow2 54})
  (rem_hd: hp_addr) (rem_obj: obj_addr)
  : Lemma
      (requires MH.well_formed_major_heap mh /\
                idx < Seq.length mh /\
                target_idx < Seq.length mh /\
                MH.word_in_chunk (Seq.index mh idx) (hd_address obj) /\
                MH.word_in_chunk (Seq.index mh idx) rem_hd /\
                MH.word_in_chunk (Seq.index mh idx) rem_obj /\
                MH.lookup_chunk_index mh target_addr == Some target_idx /\
                MH.word_in_chunk (Seq.index mh target_idx) target_addr)
       (ensures
        (let mh' =
          head_split_heap mh obj requested_wz next_fp rem_wz_u rem_hd rem_obj in
         MH.lookup_chunk_index mh' target_addr == Some target_idx /\
         target_idx < Seq.length mh' /\
         MH.word_in_chunk (Seq.index mh' target_idx) target_addr /\
         MH.chunk_end (Seq.index mh' target_idx) ==
           MH.chunk_end (Seq.index mh target_idx)))
  =
  let c = Seq.index mh idx in
  let hd = hd_address obj in
  let alloc_hdr =
    Alloc.make_header (U64.uint_to_t requested_wz) Alloc.white_bits 0UL in
  let c1 = MH.write_word_in_chunk c hd alloc_hdr in
  let mh1 = MA.major_write_word_or_same mh hd alloc_hdr in
  let rem_hdr =
    Alloc.make_header rem_wz_u Alloc.blue_bits 0UL in
  let c2 = MH.write_word_in_chunk c1 rem_hd rem_hdr in
  let mh2 = MA.major_write_word_or_same mh1 rem_hd rem_hdr in
  let c3 = MH.write_word_in_chunk c2 rem_obj next_fp in
  let mh3 = MA.major_write_word_or_same mh2 rem_obj next_fp in
  MA.head_split_materialize_writes
    mh idx obj requested_wz next_fp rem_wz_u rem_hd rem_obj;
  assert (mh1 == Seq.upd mh idx c1);
  MA.indexed_chunk_replace_same_range_preserves_lookup_word
    mh idx target_idx c1 target_addr;
  assert (Seq.index mh1 idx == c1);
  MH.write_word_in_chunk_preserves_range c hd alloc_hdr;
  MH.write_word_in_chunk_preserves_range c1 rem_hd rem_hdr;
  MA.indexed_chunk_replace_same_range_preserves_lookup_word
    mh1 idx target_idx c2 target_addr;
  assert (Seq.index mh2 idx == c2);
  MH.write_word_in_chunk_preserves_range c2 rem_obj next_fp;
  MA.indexed_chunk_replace_same_range_preserves_lookup_word
    mh2 idx target_idx c3 target_addr;
  assert (mh3 ==
          head_split_heap mh obj requested_wz next_fp rem_wz_u rem_hd rem_obj)
#pop-options

#push-options "--z3rlimit 10 --split_queries always --fuel 0 --ifuel 0"
let selected_old_free_node_split_read_regions
  (mh: MH.major_heap) (idx: nat) (obj x: obj_addr) (old_hdr: U64.t)
  (requested_wz block_wz: nat) (rem_hd: hp_addr) (rem_obj: obj_addr)
  : Lemma
      (requires MH.well_formed_major_heap mh /\
                idx < Seq.length mh /\
                Seq.mem obj (MH.objects_in_chunk (Seq.index mh idx)) /\
                Seq.mem x (MH.major_objects mh) /\
                x <> obj /\
                MH.word_in_chunk (Seq.index mh idx) (hd_address obj) /\
                MH.read_word_in_major mh (hd_address x) == Some old_hdr /\
                U64.v (Obj.getWosize old_hdr) >= 1 /\
                MH.object_wosize_in_chunk (Seq.index mh idx) obj == block_wz /\
                requested_wz > 0 /\
                block_wz - requested_wz >= 2 /\
                U64.v rem_hd ==
                  U64.v (hd_address obj) + (1 + requested_wz) * U64.v mword /\
                U64.v rem_obj == U64.v rem_hd + U64.v mword)
       (ensures
        (let c = Seq.index mh idx in
         let hd = hd_address obj in
         let xhd = hd_address x in
         ((MH.word_in_chunk c xhd /\
           (xhd = hd \/
            U64.v xhd + U64.v mword <= U64.v hd \/
            (U64.v hd + U64.v mword <= U64.v xhd /\
             U64.v xhd + U64.v mword <= U64.v rem_hd) \/
            U64.v rem_obj + U64.v mword <= U64.v xhd)) \/
          ~(MH.chunk_contains_addr c xhd)) /\
         ((MH.word_in_chunk c x /\
           (x = hd \/
            U64.v x + U64.v mword <= U64.v hd \/
            (U64.v hd + U64.v mword <= U64.v x /\
             U64.v x + U64.v mword <= U64.v rem_hd) \/
            U64.v rem_obj + U64.v mword <= U64.v x)) \/
          ~(MH.chunk_contains_addr c x)) /\
         xhd <> hd /\
         x <> hd))
  =
  let c = Seq.index mh idx in
  let xhd = hd_address x in
  MH.read_word_in_major_lookup_index mh xhd old_hdr;
  let xidx = MH.lookup_chunk_index_value mh xhd in
  if xidx = idx then begin
    assert (MH.word_in_chunk c xhd);
    assert (MH.chunk_contains_addr c xhd);
    MH.major_objects_member_in_lookup_chunk mh idx x;
    assert (Seq.mem x (MH.objects_in_chunk c));
    assert (MH.read_word_in_chunk c xhd == old_hdr);
    assert (MH.object_wosize_in_chunk c x == U64.v (Obj.getWosize old_hdr));
    assert (MH.object_wosize_in_chunk c x >= 1);
    MA.selected_free_node_split_read_regions
      c obj x requested_wz block_wz rem_hd rem_obj;
    if xhd = hd_address obj then begin
      f_hd_roundtrip x;
      f_hd_roundtrip obj;
      assert (x == obj);
      assert False
    end;
    if x = hd_address obj then begin
      hd_address_spec obj;
      assert (U64.v obj == U64.v (hd_address obj) + U64.v mword);
      assert (U64.v x < U64.v obj);
      MH.objects_in_chunk_separated c x obj;
      assert (MH.object_wosize_in_chunk c x >= 1);
      assert (U64.v obj >
              U64.v x + MH.object_wosize_in_chunk c x * U64.v mword);
      assert (U64.v obj > U64.v x + U64.v mword);
      assert False
    end;
    MH.objects_in_chunk_member_header_fits c x;
    assert (MH.object_header_size_fits_in_chunk c x);
    hd_address_spec x;
    assert (U64.v x == U64.v xhd + U64.v mword);
    assert (U64.v xhd +
            (1 + MH.object_wosize_in_chunk c x) * U64.v mword <=
            MH.chunk_end c);
    assert (MH.object_wosize_in_chunk c x >= 1);
    assert (U64.v x + U64.v mword <= MH.chunk_end c);
    assert (MH.word_in_chunk c x)
  end else begin
    MH.lookup_chunk_index_some mh xhd xidx;
    assert (xidx <> idx);
    if idx < xidx then
      MA.chunks_pairwise_index_disjoint mh idx xidx
    else if xidx < idx then begin
      assert (xidx < idx);
      MA.chunks_pairwise_index_disjoint mh xidx idx;
      MH.chunks_disjoint_symmetric (Seq.index mh xidx) c
    end else assert False;
    if MH.chunk_contains_addr c xhd then begin
      MH.chunks_disjoint_no_shared_addr (Seq.index mh xidx) c xhd;
      assert False
    end;
    if MH.chunk_contains_addr c x then begin
      hd_address_spec x;
      assert (U64.v x == U64.v xhd + U64.v mword);
      assert (U64.v xhd < U64.v x);
      assert (MH.chunk_contains_addr (Seq.index mh xidx) xhd);
      MH.major_objects_member_in_lookup_chunk mh xidx x;
      assert (Seq.mem x (MH.objects_in_chunk (Seq.index mh xidx)));
      MH.objects_in_chunk_member_in_chunk (Seq.index mh xidx) x;
      assert (MH.chunk_contains_addr (Seq.index mh xidx) x);
      MH.chunks_disjoint_no_shared_addr c (Seq.index mh xidx) x
    end;
    if xhd = hd_address obj then begin
      f_hd_roundtrip x;
      f_hd_roundtrip obj;
      assert (x == obj);
      assert False
    end;
    if x = hd_address obj then begin
      assert (MH.chunk_contains_addr c x);
      assert False
    end
  end
#pop-options
