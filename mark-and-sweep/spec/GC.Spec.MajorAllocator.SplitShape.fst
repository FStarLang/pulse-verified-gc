module GC.Spec.MajorAllocator.SplitShape

module U64 = FStar.UInt64
module Seq = FStar.Seq
module MH = GC.Spec.MajorHeap
module MA = GC.Spec.MajorAllocator
module Alloc = GC.Spec.Allocator
module AllocHeader = GC.Spec.Allocator.Lemmas.Header
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

#push-options "--z3rlimit 20 --split_queries always --fuel 0 --ifuel 0"
let head_split_remainder_head_facts
  (mh: MH.major_heap) (idx: nat) (obj: obj_addr)
  (requested_wz: nat{requested_wz < pow2 54 /\ FStar.UInt.size requested_wz 64})
  (block_wz: nat) (next_fp: U64.t)
  (rem_wz_u: U64.t{U64.v rem_wz_u < pow2 54})
  (rem_hd: hp_addr) (rem_obj: obj_addr)
  : Lemma
      (requires
        (MH.well_formed_major_heap mh /\
         idx < Seq.length mh /\
         (let c = Seq.index mh idx in
          let hd = hd_address obj in
          MH.word_in_chunk c hd /\
          requested_wz > 0 /\
          block_wz >= requested_wz /\
          block_wz < pow2 54 /\
          block_wz - requested_wz >= 2 /\
          U64.v rem_wz_u == block_wz - requested_wz - 1 /\
          MH.word_in_chunk c rem_hd /\
          MH.word_in_chunk c rem_obj /\
          U64.v rem_hd == U64.v hd + (1 + requested_wz) * U64.v mword /\
          U64.v rem_obj == U64.v rem_hd + U64.v mword /\
          U64.v hd + (1 + block_wz) * U64.v mword <= MH.chunk_end c)))
       (ensures
        (let mh' =
          head_split_heap mh obj requested_wz next_fp rem_wz_u rem_hd rem_obj in
         let rem_hdr = Alloc.make_header rem_wz_u Alloc.blue_bits 0UL in
         MH.read_word_in_major mh' rem_hd == Some rem_hdr /\
         MH.read_word_in_major mh' rem_obj == Some next_fp /\
         MH.lookup_chunk_index mh' rem_hd == Some idx /\
         idx < Seq.length mh' /\
         MH.word_in_chunk (Seq.index mh' idx) rem_hd /\
         U64.v (Obj.getWosize rem_hdr) >= 1 /\
         U64.v rem_hd + (1 + U64.v (Obj.getWosize rem_hdr)) *
           U64.v mword <= MH.chunk_end (Seq.index mh' idx)))
  =
  let c = Seq.index mh idx in
  let hd = hd_address obj in
  let alloc_hdr =
    Alloc.make_header (U64.uint_to_t requested_wz) Alloc.white_bits 0UL in
  let c1 = MH.write_word_in_chunk c hd alloc_hdr in
  let mh1 = MA.major_write_word_or_same mh hd alloc_hdr in
  let rem_hdr = Alloc.make_header rem_wz_u Alloc.blue_bits 0UL in
  let c2 = MH.write_word_in_chunk c1 rem_hd rem_hdr in
  let mh2 = MA.major_write_word_or_same mh1 rem_hd rem_hdr in
  let c3 = MH.write_word_in_chunk c2 rem_obj next_fp in
  let mh3 = MA.major_write_word_or_same mh2 rem_obj next_fp in
  MA.head_split_materialize_writes
    mh idx obj requested_wz next_fp rem_wz_u rem_hd rem_obj;
  assert (mh3 ==
          head_split_heap mh obj requested_wz next_fp rem_wz_u rem_hd rem_obj);
  MA.well_formed_no_prior_word_in_selected_chunk mh idx rem_hd;
  MA.lookup_chunk_index_from_contains_no_prior mh rem_hd idx;
  head_split_preserves_lookup_word
    mh idx idx obj rem_hd requested_wz next_fp rem_wz_u rem_hd rem_obj;
  MA.well_formed_no_prior_word_in_selected_chunk mh idx rem_obj;
  MA.lookup_chunk_index_from_contains_no_prior mh rem_obj idx;
  head_split_preserves_lookup_word
    mh idx idx obj rem_obj requested_wz next_fp rem_wz_u rem_hd rem_obj;
  MH.read_write_in_chunk_same c1 rem_hd rem_hdr;
  assert (MH.read_word_in_chunk c2 rem_hd == rem_hdr);
  assert (rem_hd <> rem_obj);
  assert (U64.v rem_hd + U64.v mword <= U64.v rem_obj);
  MH.read_write_in_chunk_different c2 rem_obj rem_hd next_fp;
  assert (MH.read_word_in_chunk c3 rem_hd == rem_hdr);
  MH.read_write_in_chunk_same c2 rem_obj next_fp;
  assert (MH.read_word_in_chunk c3 rem_obj == next_fp);
  MH.read_word_in_major_at_lookup_index mh3 rem_hd idx;
  assert (MH.read_word_in_major mh3 rem_hd == Some rem_hdr);
  MH.read_word_in_major_at_lookup_index mh3 rem_obj idx;
  assert (MH.read_word_in_major mh3 rem_obj == Some next_fp);
  AllocHeader.make_header_getWosize rem_wz_u Alloc.blue_bits 0UL;
  assert (Obj.getWosize rem_hdr == rem_wz_u);
  assert (U64.v (Obj.getWosize rem_hdr) == U64.v rem_wz_u);
  assert (U64.v (Obj.getWosize rem_hdr) >= 1);
  let rem_wz = block_wz - requested_wz - 1 in
  assert (U64.v rem_wz_u == rem_wz);
  assert (rem_wz + 1 == block_wz - requested_wz);
  assert ((1 + requested_wz) + (rem_wz + 1) <= 1 + block_wz);
  FStar.Math.Lemmas.lemma_mult_le_right
    (U64.v mword) ((1 + requested_wz) + (rem_wz + 1)) (1 + block_wz);
  assert (((1 + requested_wz) + (rem_wz + 1)) * U64.v mword <=
          (1 + block_wz) * U64.v mword);
  FStar.Math.Lemmas.distributivity_add_left
    (1 + requested_wz) (rem_wz + 1) (U64.v mword);
  assert (((1 + requested_wz) + (rem_wz + 1)) * U64.v mword ==
          (1 + requested_wz) * U64.v mword +
          (rem_wz + 1) * U64.v mword);
  assert ((1 + requested_wz) * U64.v mword +
          (rem_wz + 1) * U64.v mword <=
          (1 + block_wz) * U64.v mword);
  FStar.Math.Lemmas.paren_add_right
    (U64.v hd) ((1 + requested_wz) * U64.v mword)
    ((rem_wz + 1) * U64.v mword);
  assert (U64.v rem_hd +
          (1 + U64.v (Obj.getWosize rem_hdr)) * U64.v mword <=
          U64.v hd + (1 + block_wz) * U64.v mword)
#pop-options

#push-options "--z3rlimit 20 --split_queries always --fuel 0 --ifuel 0"
let head_split_preserves_non_head_node_facts
  (mh: MH.major_heap) (idx: nat) (obj x: obj_addr)
  (old_hdr old_next: U64.t)
  (requested_wz: nat{requested_wz < pow2 54 /\ FStar.UInt.size requested_wz 64})
  (block_wz: nat) (next_fp: U64.t)
  (rem_wz_u: U64.t{U64.v rem_wz_u < pow2 54})
  (rem_hd: hp_addr) (rem_obj: obj_addr)
  : Lemma
      (requires
        (MH.well_formed_major_heap mh /\
         idx < Seq.length mh /\
         (let c = Seq.index mh idx in
         let xhd = hd_address x in
         let xidx = MH.lookup_chunk_index_value mh xhd in
         Seq.mem obj (MH.objects_in_chunk c) /\
         Seq.mem x (MH.major_objects mh) /\
         x <> obj /\
         MH.word_in_chunk c (hd_address obj) /\
         MH.read_word_in_major mh xhd == Some old_hdr /\
         U64.v (Obj.getWosize old_hdr) >= 1 /\
         MH.read_word_in_major mh x == Some old_next /\
         MH.object_wosize_in_chunk c obj == block_wz /\
         requested_wz > 0 /\
         block_wz >= requested_wz /\
         block_wz < pow2 54 /\
         block_wz - requested_wz >= 2 /\
         U64.v rem_wz_u == block_wz - requested_wz - 1 /\
         MH.word_in_chunk c rem_hd /\
         MH.word_in_chunk c rem_obj /\
         U64.v rem_hd ==
           U64.v (hd_address obj) + (1 + requested_wz) * U64.v mword /\
         U64.v rem_obj == U64.v rem_hd + U64.v mword /\
         U64.v (hd_address obj) + (1 + block_wz) * U64.v mword <=
           MH.chunk_end c /\
         MH.lookup_chunk_index mh xhd == Some xidx /\
         xidx < Seq.length mh /\
         MH.word_in_chunk (Seq.index mh xidx) xhd /\
         U64.v xhd + (1 + U64.v (Obj.getWosize old_hdr)) *
           U64.v mword <= MH.chunk_end (Seq.index mh xidx))))
       (ensures
        (let mh' =
          head_split_heap mh obj requested_wz next_fp rem_wz_u rem_hd rem_obj in
         let xhd = hd_address x in
         let xidx = MH.lookup_chunk_index_value mh xhd in
         Seq.mem x (MH.major_objects mh') /\
         MH.read_word_in_major mh' xhd == Some old_hdr /\
         MH.read_word_in_major mh' x == Some old_next /\
         MH.lookup_chunk_index mh' xhd == Some xidx /\
         xidx < Seq.length mh' /\
         MH.word_in_chunk (Seq.index mh' xidx) xhd /\
         U64.v xhd + (1 + U64.v (Obj.getWosize old_hdr)) *
           U64.v mword <= MH.chunk_end (Seq.index mh' xidx)))
  =
  let c = Seq.index mh idx in
  let xhd = hd_address x in
  let xidx = MH.lookup_chunk_index_value mh xhd in
  selected_old_free_node_split_read_regions
    mh idx obj x old_hdr requested_wz block_wz rem_hd rem_obj;
  MA.head_split_preserves_free_node_object
    mh idx obj x old_hdr requested_wz block_wz next_fp rem_wz_u rem_hd rem_obj;
  assert (xhd <> hd_address obj);
  MA.head_split_major_preserves_read_at
    mh idx obj xhd old_hdr requested_wz block_wz next_fp rem_wz_u rem_hd rem_obj;
  assert (x <> hd_address obj);
  MA.head_split_major_preserves_read_at
    mh idx obj x old_next requested_wz block_wz next_fp rem_wz_u rem_hd rem_obj;
  head_split_preserves_lookup_word
    mh idx xidx obj xhd requested_wz next_fp rem_wz_u rem_hd rem_obj
#pop-options

#push-options "--z3rlimit 20 --split_queries always --fuel 0 --ifuel 0"
let head_split_preserves_allocated_head_node_facts
  (mh: MH.major_heap) (idx: nat) (obj: obj_addr)
  (old_hdr old_next: U64.t)
  (requested_wz: nat{requested_wz < pow2 54 /\ FStar.UInt.size requested_wz 64})
  (block_wz: nat) (next_fp: U64.t)
  (rem_wz_u: U64.t{U64.v rem_wz_u < pow2 54})
  (rem_hd: hp_addr) (rem_obj: obj_addr)
  : Lemma
      (requires
        (MH.well_formed_major_heap mh /\
         idx < Seq.length mh /\
         (let c = Seq.index mh idx in
         let hd = hd_address obj in
         MH.lookup_chunk_index mh hd == Some idx /\
         Seq.mem obj (MH.objects_in_chunk c) /\
         MH.word_in_chunk c hd /\
         MH.read_word_in_major mh hd == Some old_hdr /\
         MH.read_word_in_chunk c hd == old_hdr /\
         U64.v (Obj.getWosize old_hdr) == block_wz /\
         U64.v (Obj.getWosize old_hdr) >= 1 /\
         MH.read_word_in_major mh obj == Some old_next /\
         MH.object_wosize_in_chunk c obj == block_wz /\
         requested_wz > 0 /\
         block_wz >= requested_wz /\
         block_wz < pow2 54 /\
         block_wz - requested_wz >= 2 /\
         U64.v rem_wz_u == block_wz - requested_wz - 1 /\
         MH.word_in_chunk c rem_hd /\
         MH.word_in_chunk c rem_obj /\
         U64.v rem_hd == U64.v hd + (1 + requested_wz) * U64.v mword /\
         U64.v rem_obj == U64.v rem_hd + U64.v mword /\
         U64.v hd + (1 + block_wz) * U64.v mword <= MH.chunk_end c)))
       (ensures
        (let mh' =
          head_split_heap mh obj requested_wz next_fp rem_wz_u rem_hd rem_obj in
         let hd = hd_address obj in
         let alloc_hdr =
           Alloc.make_header (U64.uint_to_t requested_wz) Alloc.white_bits 0UL in
         Seq.mem obj (MH.major_objects mh') /\
         MH.read_word_in_major mh' hd == Some alloc_hdr /\
         MH.read_word_in_major mh' obj == Some old_next /\
         MH.lookup_chunk_index mh' hd == Some idx /\
         idx < Seq.length mh' /\
         MH.word_in_chunk (Seq.index mh' idx) hd /\
         U64.v hd + (1 + U64.v (Obj.getWosize alloc_hdr)) *
           U64.v mword <= MH.chunk_end (Seq.index mh' idx)))
  =
  let c = Seq.index mh idx in
  let hd = hd_address obj in
  let alloc_hdr =
    Alloc.make_header (U64.uint_to_t requested_wz) Alloc.white_bits 0UL in
  MH.major_objects_member_at_index mh idx obj;
  MA.head_split_preserves_free_node_object
    mh idx obj obj old_hdr requested_wz block_wz next_fp rem_wz_u rem_hd rem_obj;
  MA.head_split_major_preserves_read_at
    mh idx obj hd old_hdr requested_wz block_wz next_fp rem_wz_u rem_hd rem_obj;
  hd_address_spec obj;
  assert (U64.v obj == U64.v hd + U64.v mword);
  assert (U64.v mword == 8);
  assert (block_wz >= requested_wz + 2);
  assert (block_wz >= 3);
  assert (U64.v obj + U64.v mword == U64.v hd + 2 * U64.v mword);
  assert (2 <= 1 + block_wz);
  FStar.Math.Lemmas.lemma_mult_le_right (U64.v mword) 2 (1 + block_wz);
  assert (U64.v obj + U64.v mword <=
          U64.v hd + (1 + block_wz) * U64.v mword);
  assert (MH.word_in_chunk c obj);
  MA.selected_free_node_split_read_regions
    c obj obj requested_wz block_wz rem_hd rem_obj;
  assert (obj <> hd);
  MA.head_split_major_preserves_read_at
    mh idx obj obj old_next requested_wz block_wz next_fp rem_wz_u rem_hd rem_obj;
  head_split_preserves_lookup_word
    mh idx idx obj hd requested_wz next_fp rem_wz_u rem_hd rem_obj;
  AllocHeader.make_header_getWosize
    (U64.uint_to_t requested_wz) Alloc.white_bits 0UL;
  assert (Obj.getWosize alloc_hdr == U64.uint_to_t requested_wz);
  assert (U64.v (Obj.getWosize alloc_hdr) == requested_wz);
  assert (1 + requested_wz <= 1 + block_wz);
  FStar.Math.Lemmas.lemma_mult_le_right
    (U64.v mword) (1 + requested_wz) (1 + block_wz);
  assert (U64.v hd + (1 + requested_wz) * U64.v mword <=
          U64.v hd + (1 + block_wz) * U64.v mword)
#pop-options

#push-options "--z3rlimit 20 --split_queries always --fuel 1 --ifuel 1"
let rec head_split_preserves_old_free_list_shape
  (mh: MH.major_heap) (idx: nat) (obj: obj_addr)
  (requested_wz: nat{requested_wz < pow2 54 /\ FStar.UInt.size requested_wz 64})
  (block_wz: nat) (next_fp: U64.t)
  (rem_wz_u: U64.t{U64.v rem_wz_u < pow2 54})
  (rem_hd: hp_addr) (rem_obj: obj_addr)
  (cur: U64.t) (fuel: nat)
  : Lemma
      (requires
        (MH.well_formed_major_heap mh /\
         idx < Seq.length mh /\
         (let c = Seq.index mh idx in
          let hd = hd_address obj in
          MH.lookup_chunk_index mh hd == Some idx /\
          Seq.mem obj (MH.objects_in_chunk c) /\
          MH.word_in_chunk c hd /\
          MH.object_wosize_in_chunk c obj == block_wz /\
          requested_wz > 0 /\
          block_wz >= requested_wz /\
          block_wz < pow2 54 /\
          block_wz - requested_wz >= 2 /\
          U64.v rem_wz_u == block_wz - requested_wz - 1 /\
          MH.word_in_chunk c rem_hd /\
          MH.word_in_chunk c rem_obj /\
          U64.v rem_hd == U64.v hd + (1 + requested_wz) * U64.v mword /\
          U64.v rem_obj == U64.v rem_hd + U64.v mword /\
          U64.v hd + (1 + block_wz) * U64.v mword <= MH.chunk_end c) /\
         MA.major_fl_valid mh cur fuel /\
         MA.major_fl_above_zero mh cur fuel /\
         MA.major_fl_blocks_fit mh cur fuel))
       (ensures
        (let mh' =
          head_split_heap mh obj requested_wz next_fp rem_wz_u rem_hd rem_obj in
         MA.major_fl_valid mh' cur fuel /\
         MA.major_fl_above_zero mh' cur fuel /\
         MA.major_fl_blocks_fit mh' cur fuel))
       (decreases fuel)
  =
  if fuel = 0 then ()
  else if cur = 0UL then ()
  else begin
    assert (fuel > 0);
    let fuel' : f:nat{f < fuel} = fuel - 1 in
    MA.major_fl_above_zero_current mh cur fuel;
    assert (U64.v cur >= U64.v zero_addr + U64.v mword);
    assert (U64.v cur >= U64.v mword);
    assert (U64.v cur < heap_size);
    assert (U64.v cur % U64.v mword == 0);
    let x : obj_addr = cur in
    let xhd = hd_address x in
    MA.major_fl_valid_gives_mem mh cur fuel;
    MA.major_fl_valid_gives_wosize mh cur fuel;
    MA.major_fl_valid_next mh cur fuel;
    MA.major_fl_blocks_fit_current mh cur fuel;
    match MH.read_word_in_major mh xhd with
    | None -> assert False
    | Some old_hdr ->
      match MH.read_word_in_major mh x with
      | None -> assert False
      | Some old_next ->
        assert (MH.read_word_in_major mh x == Some old_next);
        MA.major_fl_above_zero_next mh x fuel old_next;
        MA.major_fl_blocks_fit_next mh x fuel old_next;
        assert (MA.major_fl_valid mh old_next fuel');
        assert (MA.major_fl_above_zero mh old_next fuel');
        assert (MA.major_fl_blocks_fit mh old_next fuel');
        head_split_preserves_old_free_list_shape
          mh idx obj requested_wz block_wz next_fp rem_wz_u rem_hd rem_obj
          old_next fuel';
        let mh' =
          head_split_heap mh obj requested_wz next_fp rem_wz_u rem_hd rem_obj in
        assert (MA.major_fl_valid mh' old_next fuel');
        assert (MA.major_fl_above_zero mh' old_next fuel');
        assert (MA.major_fl_blocks_fit mh' old_next fuel');
        let c = Seq.index mh idx in
        let hd = hd_address obj in
        let hdr' =
          if x = obj then
            Alloc.make_header (U64.uint_to_t requested_wz) Alloc.white_bits 0UL
          else old_hdr in
        if x = obj then begin
          MH.read_word_in_major_at_lookup_index mh hd idx;
          assert (MH.read_word_in_chunk c hd == old_hdr);
          assert (U64.v (Obj.getWosize old_hdr) == block_wz);
          head_split_preserves_allocated_head_node_facts
            mh idx obj old_hdr old_next requested_wz block_wz next_fp
            rem_wz_u rem_hd rem_obj;
          AllocHeader.make_header_getWosize
            (U64.uint_to_t requested_wz) Alloc.white_bits 0UL;
          assert (U64.v (Obj.getWosize hdr') == requested_wz);
          assert (U64.v (Obj.getWosize hdr') >= 1)
        end else begin
          let xidx = MH.lookup_chunk_index_value mh xhd in
          head_split_preserves_non_head_node_facts
            mh idx obj x old_hdr old_next requested_wz block_wz next_fp
            rem_wz_u rem_hd rem_obj;
          assert (U64.v (Obj.getWosize hdr') >= 1)
        end;
        assert (Seq.mem x (MH.major_objects mh'));
        assert (MH.read_word_in_major mh' xhd == Some hdr');
        assert (MH.read_word_in_major mh' x == Some old_next);
        assert (old_next <> cur);
        MA.major_fl_valid_step_from_mem mh' x fuel hdr' old_next;
        MA.major_fl_above_zero_step mh' x fuel old_next;
        let xidx = MH.lookup_chunk_index_value mh xhd in
        assert (MH.lookup_chunk_index mh' xhd == Some xidx);
        assert (xidx < Seq.length mh');
        assert (MH.word_in_chunk (Seq.index mh' xidx) xhd);
        assert (U64.v xhd + (1 + U64.v (Obj.getWosize hdr')) *
                  U64.v mword <= MH.chunk_end (Seq.index mh' xidx));
        MA.major_fl_blocks_fit_step mh' x fuel hdr' old_next
  end
#pop-options

#push-options "--z3rlimit 20 --split_queries always --fuel 1 --ifuel 1"
let rec head_split_preserves_old_free_list_terminates
  (mh: MH.major_heap) (idx: nat) (obj: obj_addr)
  (requested_wz: nat{requested_wz < pow2 54 /\ FStar.UInt.size requested_wz 64})
  (block_wz: nat) (next_fp: U64.t)
  (rem_wz_u: U64.t{U64.v rem_wz_u < pow2 54})
  (rem_hd: hp_addr) (rem_obj: obj_addr)
  (cur: U64.t) (fuel: nat)
  : Lemma
      (requires
        (MH.well_formed_major_heap mh /\
         idx < Seq.length mh /\
         (let c = Seq.index mh idx in
          let hd = hd_address obj in
          MH.lookup_chunk_index mh hd == Some idx /\
          Seq.mem obj (MH.objects_in_chunk c) /\
          MH.word_in_chunk c hd /\
          MH.object_wosize_in_chunk c obj == block_wz /\
          requested_wz > 0 /\
          block_wz >= requested_wz /\
          block_wz < pow2 54 /\
          block_wz - requested_wz >= 2 /\
          U64.v rem_wz_u == block_wz - requested_wz - 1 /\
          MH.word_in_chunk c rem_hd /\
          MH.word_in_chunk c rem_obj /\
          U64.v rem_hd == U64.v hd + (1 + requested_wz) * U64.v mword /\
          U64.v rem_obj == U64.v rem_hd + U64.v mword /\
          U64.v hd + (1 + block_wz) * U64.v mword <= MH.chunk_end c) /\
         MA.major_fl_valid mh cur fuel /\
         MA.major_fl_above_zero mh cur fuel /\
         MA.major_fl_blocks_fit mh cur fuel /\
         MA.major_fl_chain_terminates mh cur fuel = true))
       (ensures
        (let mh' =
          head_split_heap mh obj requested_wz next_fp rem_wz_u rem_hd rem_obj in
         MA.major_fl_chain_terminates mh' cur fuel = true))
       (decreases fuel)
  =
  let mh' =
    head_split_heap mh obj requested_wz next_fp rem_wz_u rem_hd rem_obj in
  if fuel = 0 then begin
    if cur = 0UL ||
       U64.v cur < U64.v mword ||
       U64.v cur >= heap_size ||
       U64.v cur % U64.v mword <> 0 then
      MA.major_fl_chain_terminates_terminal mh' cur fuel
    else begin
      MA.major_fl_chain_terminates_valid_zero mh cur;
      assert False
    end
  end else if cur = 0UL then
    MA.major_fl_chain_terminates_null mh' fuel
  else begin
    assert (fuel > 0);
    let fuel' : f:nat{f < fuel} = fuel - 1 in
    MA.major_fl_above_zero_current mh cur fuel;
    assert (U64.v cur >= U64.v zero_addr + U64.v mword);
    assert (U64.v cur >= U64.v mword);
    assert (U64.v cur < heap_size);
    assert (U64.v cur % U64.v mword == 0);
    let x : obj_addr = cur in
    let xhd = hd_address x in
    MA.major_fl_valid_next mh cur fuel;
    MA.major_fl_chain_terminates_tail mh cur fuel;
    match MH.read_word_in_major mh xhd with
    | None -> assert False
    | Some old_hdr ->
      match MH.read_word_in_major mh x with
      | None -> assert False
      | Some old_next ->
        assert (MH.read_word_in_major mh x == Some old_next);
        MA.major_fl_above_zero_next mh x fuel old_next;
        MA.major_fl_blocks_fit_next mh x fuel old_next;
        assert (MA.major_fl_valid mh old_next fuel');
        assert (MA.major_fl_above_zero mh old_next fuel');
        assert (MA.major_fl_blocks_fit mh old_next fuel');
        assert (MA.major_fl_chain_terminates mh old_next fuel' = true);
        head_split_preserves_old_free_list_terminates
          mh idx obj requested_wz block_wz next_fp rem_wz_u rem_hd rem_obj
          old_next fuel';
        assert (MA.major_fl_chain_terminates mh' old_next fuel' = true);
        if x = obj then begin
          let c = Seq.index mh idx in
          let hd = hd_address obj in
          MH.read_word_in_major_at_lookup_index mh hd idx;
          assert (MH.read_word_in_chunk c hd == old_hdr);
          assert (U64.v (Obj.getWosize old_hdr) == block_wz);
          head_split_preserves_allocated_head_node_facts
            mh idx obj old_hdr old_next requested_wz block_wz next_fp
            rem_wz_u rem_hd rem_obj
        end else
          head_split_preserves_non_head_node_facts
            mh idx obj x old_hdr old_next requested_wz block_wz next_fp
            rem_wz_u rem_hd rem_obj;
        assert (MH.read_word_in_major mh' x == Some old_next);
        assert
          (match MH.read_word_in_major mh' (cur <: obj_addr) with
           | Some next -> MA.major_fl_chain_terminates mh' next fuel' = true
           | None -> True);
        MA.major_fl_chain_terminates_step mh' cur fuel
  end
#pop-options

#push-options "--z3rlimit 20 --split_queries always --fuel 1 --ifuel 1"
let rec head_split_preserves_old_free_list_avoids_allocated_head
  (mh: MH.major_heap) (idx: nat) (obj: obj_addr)
  (requested_wz: nat{requested_wz < pow2 54 /\ FStar.UInt.size requested_wz 64})
  (block_wz: nat) (next_fp: U64.t)
  (rem_wz_u: U64.t{U64.v rem_wz_u < pow2 54})
  (rem_hd: hp_addr) (rem_obj: obj_addr)
  (cur: U64.t) (fuel: nat)
  : Lemma
      (requires
        (MH.well_formed_major_heap mh /\
         idx < Seq.length mh /\
         (let c = Seq.index mh idx in
          let hd = hd_address obj in
          MH.lookup_chunk_index mh hd == Some idx /\
          Seq.mem obj (MH.objects_in_chunk c) /\
          MH.word_in_chunk c hd /\
          MH.object_wosize_in_chunk c obj == block_wz /\
          requested_wz > 0 /\
          block_wz >= requested_wz /\
          block_wz < pow2 54 /\
          block_wz - requested_wz >= 2 /\
          U64.v rem_wz_u == block_wz - requested_wz - 1 /\
          MH.word_in_chunk c rem_hd /\
          MH.word_in_chunk c rem_obj /\
          U64.v rem_hd == U64.v hd + (1 + requested_wz) * U64.v mword /\
          U64.v rem_obj == U64.v rem_hd + U64.v mword /\
          U64.v hd + (1 + block_wz) * U64.v mword <= MH.chunk_end c) /\
         MA.major_fl_valid mh cur fuel /\
         MA.major_fl_above_zero mh cur fuel /\
         MA.major_fl_blocks_fit mh cur fuel /\
         MA.major_fl_chain_avoids mh cur obj fuel = true))
       (ensures
        (let mh' =
          head_split_heap mh obj requested_wz next_fp rem_wz_u rem_hd rem_obj in
         MA.major_fl_chain_avoids mh' cur obj fuel = true))
       (decreases fuel)
  =
  if fuel = 0 then ()
  else if cur = 0UL then ()
  else begin
    assert (fuel > 0);
    let fuel' : f:nat{f < fuel} = fuel - 1 in
    MA.major_fl_above_zero_current mh cur fuel;
    assert (U64.v cur >= U64.v zero_addr + U64.v mword);
    assert (U64.v cur >= U64.v mword);
    assert (U64.v cur < heap_size);
    assert (U64.v cur % U64.v mword == 0);
    MA.major_fl_chain_avoids_head_ne mh cur obj fuel;
    assert (cur <> obj);
    let x : obj_addr = cur in
    let xhd = hd_address x in
    MA.major_fl_valid_gives_mem mh cur fuel;
    MA.major_fl_valid_gives_wosize mh cur fuel;
    MA.major_fl_valid_next mh cur fuel;
    MA.major_fl_blocks_fit_current mh cur fuel;
    MA.major_fl_chain_avoids_tail mh cur obj fuel;
    match MH.read_word_in_major mh xhd with
    | None -> assert False
    | Some old_hdr ->
      match MH.read_word_in_major mh x with
      | None -> assert False
      | Some old_next ->
        assert (MH.read_word_in_major mh x == Some old_next);
        MA.major_fl_above_zero_next mh x fuel old_next;
        MA.major_fl_blocks_fit_next mh x fuel old_next;
        assert (MA.major_fl_valid mh old_next fuel');
        assert (MA.major_fl_above_zero mh old_next fuel');
        assert (MA.major_fl_blocks_fit mh old_next fuel');
        assert (MA.major_fl_chain_avoids mh old_next obj fuel' = true);
        head_split_preserves_old_free_list_avoids_allocated_head
          mh idx obj requested_wz block_wz next_fp rem_wz_u rem_hd rem_obj
          old_next fuel';
        let mh' =
          head_split_heap mh obj requested_wz next_fp rem_wz_u rem_hd rem_obj in
        assert (MA.major_fl_chain_avoids mh' old_next obj fuel' = true);
        head_split_preserves_non_head_node_facts
          mh idx obj x old_hdr old_next requested_wz block_wz next_fp
          rem_wz_u rem_hd rem_obj;
        assert (MH.read_word_in_major mh' x == Some old_next);
        assert
          (match MH.read_word_in_major mh' (cur <: obj_addr) with
           | Some next -> MA.major_fl_chain_avoids mh' next obj fuel' = true
           | None -> True);
        MA.major_fl_chain_avoids_step mh' cur obj fuel
  end
#pop-options

#push-options "--z3rlimit 20 --split_queries always --fuel 1 --ifuel 1"
let rec head_split_preserves_old_free_list_avoids_other
  (mh: MH.major_heap) (idx: nat) (obj: obj_addr)
  (requested_wz: nat{requested_wz < pow2 54 /\ FStar.UInt.size requested_wz 64})
  (block_wz: nat) (next_fp: U64.t)
  (rem_wz_u: U64.t{U64.v rem_wz_u < pow2 54})
  (rem_hd: hp_addr) (rem_obj: obj_addr)
  (cur excl: U64.t) (fuel: nat)
  : Lemma
      (requires
        (MH.well_formed_major_heap mh /\
         idx < Seq.length mh /\
         (let c = Seq.index mh idx in
          let hd = hd_address obj in
          MH.lookup_chunk_index mh hd == Some idx /\
          Seq.mem obj (MH.objects_in_chunk c) /\
          MH.word_in_chunk c hd /\
          MH.object_wosize_in_chunk c obj == block_wz /\
          requested_wz > 0 /\
          block_wz >= requested_wz /\
          block_wz < pow2 54 /\
          block_wz - requested_wz >= 2 /\
          U64.v rem_wz_u == block_wz - requested_wz - 1 /\
          MH.word_in_chunk c rem_hd /\
          MH.word_in_chunk c rem_obj /\
          U64.v rem_hd == U64.v hd + (1 + requested_wz) * U64.v mword /\
          U64.v rem_obj == U64.v rem_hd + U64.v mword /\
          U64.v hd + (1 + block_wz) * U64.v mword <= MH.chunk_end c) /\
         MA.major_fl_valid mh cur fuel /\
         MA.major_fl_above_zero mh cur fuel /\
         MA.major_fl_blocks_fit mh cur fuel /\
         MA.major_fl_chain_avoids mh cur obj fuel = true /\
         MA.major_fl_chain_avoids mh cur excl fuel = true))
       (ensures
        (let mh' =
          head_split_heap mh obj requested_wz next_fp rem_wz_u rem_hd rem_obj in
         MA.major_fl_chain_avoids mh' cur excl fuel = true))
       (decreases fuel)
  =
  if fuel = 0 then ()
  else if cur = 0UL then ()
  else begin
    assert (fuel > 0);
    let fuel' : f:nat{f < fuel} = fuel - 1 in
    MA.major_fl_above_zero_current mh cur fuel;
    assert (U64.v cur >= U64.v zero_addr + U64.v mword);
    assert (U64.v cur >= U64.v mword);
    assert (U64.v cur < heap_size);
    assert (U64.v cur % U64.v mword == 0);
    MA.major_fl_chain_avoids_head_ne mh cur obj fuel;
    assert (cur <> obj);
    MA.major_fl_chain_avoids_head_ne mh cur excl fuel;
    assert (cur <> excl);
    let x : obj_addr = cur in
    let xhd = hd_address x in
    MA.major_fl_valid_gives_mem mh cur fuel;
    MA.major_fl_valid_gives_wosize mh cur fuel;
    MA.major_fl_valid_next mh cur fuel;
    MA.major_fl_blocks_fit_current mh cur fuel;
    MA.major_fl_chain_avoids_tail mh cur obj fuel;
    MA.major_fl_chain_avoids_tail mh cur excl fuel;
    match MH.read_word_in_major mh xhd with
    | None -> assert False
    | Some old_hdr ->
      match MH.read_word_in_major mh x with
      | None -> assert False
      | Some old_next ->
        assert (MH.read_word_in_major mh x == Some old_next);
        MA.major_fl_above_zero_next mh x fuel old_next;
        MA.major_fl_blocks_fit_next mh x fuel old_next;
        assert (MA.major_fl_valid mh old_next fuel');
        assert (MA.major_fl_above_zero mh old_next fuel');
        assert (MA.major_fl_blocks_fit mh old_next fuel');
        assert (MA.major_fl_chain_avoids mh old_next obj fuel' = true);
        assert (MA.major_fl_chain_avoids mh old_next excl fuel' = true);
        head_split_preserves_old_free_list_avoids_other
          mh idx obj requested_wz block_wz next_fp rem_wz_u rem_hd rem_obj
          old_next excl fuel';
        let mh' =
          head_split_heap mh obj requested_wz next_fp rem_wz_u rem_hd rem_obj in
        assert (MA.major_fl_chain_avoids mh' old_next excl fuel' = true);
        head_split_preserves_non_head_node_facts
          mh idx obj x old_hdr old_next requested_wz block_wz next_fp
          rem_wz_u rem_hd rem_obj;
        assert (MH.read_word_in_major mh' x == Some old_next);
        assert
          (match MH.read_word_in_major mh' (cur <: obj_addr) with
           | Some next -> MA.major_fl_chain_avoids mh' next excl fuel' = true
           | None -> True);
        MA.major_fl_chain_avoids_step mh' cur excl fuel
  end
#pop-options

#push-options "--z3rlimit 20 --split_queries always --fuel 0 --ifuel 0"
let major_alloc_head_split_preserves_alloc_shape
  (mh: MH.major_heap) (fp: U64.t)
  (requested_wz fuel: nat)
  : Lemma
      (requires fuel > 1 /\
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
         MH.well_formed_major_heap r.major_alloc_out /\
         MA.major_alloc_result_fp_in_objects r /\
         MA.major_fl_valid r.major_alloc_out r.major_fp_out fuel /\
         MA.major_fl_above_zero r.major_alloc_out r.major_fp_out fuel /\
         MA.major_fl_blocks_fit r.major_alloc_out r.major_fp_out fuel /\
         (MA.major_fl_chain_terminates mh fp fuel = true ==>
          MA.major_fl_chain_terminates
            r.major_alloc_out r.major_fp_out fuel = true)))
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
    assert (requested_wz < pow2 64);
    assert (FStar.UInt.size requested_wz 64);
    let req : r:nat{r == requested_wz /\
                    r < pow2 54 /\ FStar.UInt.size r 64} = requested_wz in
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
      FStar.Math.Lemmas.distributivity_add_left (1 + requested_wz) 1 8;
      assert ((1 + requested_wz) * 8 + 8 == (requested_wz + 2) * 8);
      FStar.Math.Lemmas.paren_add_right (U64.v hd) ((1 + requested_wz) * 8) 8;
      assert (rem_obj_nat == U64.v hd + (requested_wz + 2) * 8);
      assert (requested_wz + 2 <= block_wz);
      assert (requested_wz + 3 <= 1 + block_wz);
      FStar.Math.Lemmas.distributivity_add_left (requested_wz + 2) 1 8;
      assert ((requested_wz + 2) * 8 + 8 == (requested_wz + 3) * 8);
      FStar.Math.Lemmas.paren_add_right (U64.v hd) ((requested_wz + 2) * 8) 8;
      assert (rem_obj_nat + 8 == (U64.v hd + (requested_wz + 2) * 8) + 8);
      assert (rem_obj_nat + 8 == U64.v hd + ((requested_wz + 2) * 8 + 8));
      assert (rem_obj_nat + 8 == U64.v hd + (requested_wz + 3) * 8);
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
      assert (U64.v rem_hd == rem_hd_nat);
      assert (U64.v rem_obj == rem_obj_nat);
      assert (U64.v rem_obj == U64.v rem_hd + U64.v mword);
      MA.active_head_split_remainder_words_in_chunk
        c hd block_wz requested_wz rem_hd rem_obj;
      let rem_wz = block_wz - requested_wz - 1 in
      assert (rem_wz >= 1);
      assert (rem_wz < pow2 54);
      assert (rem_wz < pow2 64);
      assert (FStar.UInt.size rem_wz 64);
      let rem_wz_u : w:U64.t{U64.v w == rem_wz /\ U64.v w < pow2 54} =
        U64.uint_to_t rem_wz in
      assert (U64.v rem_wz_u == block_wz - requested_wz - 1);
      MA.major_alloc_head_split mh obj requested_wz fuel hdr next_fp rem_hd rem_obj;
      let r = MA.major_alloc_spec_with_fuel mh fp requested_wz fuel in
      assert (r.major_obj_out == fp);
      assert (r.major_fp_out == rem_obj);
      assert (r.major_fp_out <> 0UL);
      assert (r.major_alloc_out ==
              head_split_heap mh obj req next_fp rem_wz_u rem_hd rem_obj);
      MA.major_alloc_head_split_preserves_head_wosize mh fp requested_wz fuel 1;
      MA.major_alloc_head_split_link_not_self mh fp requested_wz fuel;
      assert (MH.well_formed_major_heap r.major_alloc_out);
      assert (MA.major_alloc_result_fp_in_objects r);
      MA.major_fl_valid_next mh fp fuel;
      MA.major_fl_above_zero_next mh obj fuel next_fp;
      MA.major_fl_blocks_fit_next mh obj fuel next_fp;
      let fuel' : f:nat{f < fuel} = fuel - 1 in
      assert (MA.major_fl_valid mh next_fp fuel');
      assert (MA.major_fl_above_zero mh next_fp fuel');
      assert (MA.major_fl_blocks_fit mh next_fp fuel');
      head_split_preserves_old_free_list_shape
        mh idx obj req block_wz next_fp rem_wz_u rem_hd rem_obj next_fp fuel';
      assert (MA.major_fl_valid r.major_alloc_out next_fp fuel');
      assert (MA.major_fl_above_zero r.major_alloc_out next_fp fuel');
      assert (MA.major_fl_blocks_fit r.major_alloc_out next_fp fuel');
      head_split_remainder_head_facts
        mh idx obj req block_wz next_fp rem_wz_u rem_hd rem_obj;
      let rem_hdr = Alloc.make_header rem_wz_u Alloc.blue_bits 0UL in
      assert (MH.read_word_in_major r.major_alloc_out rem_hd == Some rem_hdr);
      assert (MH.read_word_in_major r.major_alloc_out rem_obj == Some next_fp);
      assert (MH.lookup_chunk_index r.major_alloc_out rem_hd == Some idx);
      assert (idx < Seq.length r.major_alloc_out);
      assert (MH.word_in_chunk (Seq.index r.major_alloc_out idx) rem_hd);
      assert (U64.v (Obj.getWosize rem_hdr) >= 1);
      assert (U64.v rem_hd + (1 + U64.v (Obj.getWosize rem_hdr)) *
                U64.v mword <= MH.chunk_end (Seq.index r.major_alloc_out idx));
      assert (U64.v rem_obj >= U64.v zero_addr + U64.v mword);
      assert (U64.v rem_obj >= U64.v mword);
      assert (U64.v rem_obj < heap_size);
      assert (U64.v rem_obj % U64.v mword == 0);
      assert (U64.v rem_hd + U64.v mword < heap_size);
      f_address_spec rem_hd;
      assert (f_address rem_hd == rem_obj);
      hd_f_roundtrip rem_hd;
      assert (hd_address rem_obj == rem_hd);
      assert (MA.major_alloc_result_fp_link_not_self r);
      assert (next_fp <> rem_obj);
      let mem_goal = Seq.mem rem_obj (MH.major_objects r.major_alloc_out) in
      let prove_mem (new_fp: obj_addr)
        : Lemma
            (requires new_fp == r.major_fp_out /\
                      Seq.mem new_fp (MH.major_objects r.major_alloc_out))
            (ensures mem_goal)
        = assert (new_fp == rem_obj)
      in
      FStar.Classical.exists_elim mem_goal #obj_addr
        #(fun new_fp ->
            new_fp == r.major_fp_out /\
            Seq.mem new_fp (MH.major_objects r.major_alloc_out))
        ()
        (fun new_fp -> FStar.Classical.move_requires prove_mem new_fp);
      assert (Seq.mem rem_obj (MH.major_objects r.major_alloc_out));
      assert (fuel > 0);
      assert (fuel' == fuel - 1);
      assert (MA.major_fl_valid r.major_alloc_out next_fp (fuel - 1));
      assert (MA.major_fl_above_zero r.major_alloc_out next_fp (fuel - 1));
      assert (MA.major_fl_blocks_fit r.major_alloc_out next_fp (fuel - 1));
      if MA.major_fl_chain_terminates mh fp fuel then begin
        MA.major_fl_chain_terminates_tail mh fp fuel;
        assert (MA.major_fl_chain_terminates mh next_fp fuel' = true);
        head_split_preserves_old_free_list_terminates
          mh idx obj req block_wz next_fp rem_wz_u rem_hd rem_obj
          next_fp fuel';
        assert (MA.major_fl_chain_terminates
                  r.major_alloc_out next_fp fuel' = true);
        assert
          (match MH.read_word_in_major r.major_alloc_out (rem_obj <: obj_addr) with
           | Some next -> MA.major_fl_chain_terminates
                            r.major_alloc_out next (fuel - 1) = true
           | None -> True);
        MA.major_fl_chain_terminates_step
          r.major_alloc_out rem_obj fuel
      end;
      assert (MH.read_word_in_major r.major_alloc_out (hd_address rem_obj) ==
              Some rem_hdr);
      assert (MH.read_word_in_major r.major_alloc_out rem_obj == Some next_fp);
      assert (next_fp <> rem_obj);
      MA.major_fl_valid_step_from_mem
        r.major_alloc_out rem_obj fuel rem_hdr next_fp;
      MA.major_fl_above_zero_step
        r.major_alloc_out rem_obj fuel next_fp;
      assert (MH.lookup_chunk_index_value r.major_alloc_out (hd_address rem_obj) == idx);
      MA.major_fl_blocks_fit_step
        r.major_alloc_out rem_obj fuel rem_hdr next_fp;
      assert (MA.major_fl_valid r.major_alloc_out r.major_fp_out fuel);
      assert (MA.major_fl_above_zero r.major_alloc_out r.major_fp_out fuel);
      assert (MA.major_fl_blocks_fit r.major_alloc_out r.major_fp_out fuel);
      assert (r.major_obj_out == fp /\
              r.major_fp_out <> 0UL /\
              MH.well_formed_major_heap r.major_alloc_out /\
              MA.major_alloc_result_fp_in_objects r /\
              MA.major_fl_valid r.major_alloc_out r.major_fp_out fuel /\
              MA.major_fl_above_zero r.major_alloc_out r.major_fp_out fuel /\
              MA.major_fl_blocks_fit r.major_alloc_out r.major_fp_out fuel /\
              (MA.major_fl_chain_terminates mh fp fuel = true ==>
               MA.major_fl_chain_terminates
                 r.major_alloc_out r.major_fp_out fuel = true))
#pop-options

#push-options "--z3rlimit 20 --split_queries always --fuel 1 --ifuel 1"
let major_alloc_head_split_remainder_avoids_allocated_head
  (mh: MH.major_heap) (fp: U64.t)
  (requested_wz fuel: nat)
  : Lemma
      (requires fuel > 1 /\
                fp <> 0UL /\
                requested_wz > 0 /\
                MH.well_formed_major_heap mh /\
                MA.major_fl_valid mh fp fuel /\
                MA.major_fl_above_zero mh fp fuel /\
                MA.major_fl_blocks_fit mh fp fuel /\
                MA.major_fl_chain_terminates mh fp fuel = true /\
                MA.major_fl_head_wosize mh fp >= requested_wz + 2)
      (ensures
        (let r = MA.major_alloc_spec_with_fuel mh fp requested_wz fuel in
         MA.major_fl_chain_avoids
           r.major_alloc_out r.major_fp_out r.major_obj_out fuel = true))
  =
  major_alloc_head_split_preserves_alloc_shape mh fp requested_wz fuel;
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
    assert (requested_wz < pow2 64);
    assert (FStar.UInt.size requested_wz 64);
    let req : r:nat{r == requested_wz /\
                    r < pow2 54 /\ FStar.UInt.size r 64} = requested_wz in
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
      FStar.Math.Lemmas.distributivity_add_left (1 + requested_wz) 1 8;
      assert ((1 + requested_wz) * 8 + 8 == (requested_wz + 2) * 8);
      FStar.Math.Lemmas.paren_add_right (U64.v hd) ((1 + requested_wz) * 8) 8;
      assert (rem_obj_nat == U64.v hd + (requested_wz + 2) * 8);
      assert (requested_wz + 2 <= block_wz);
      assert (requested_wz + 3 <= 1 + block_wz);
      FStar.Math.Lemmas.distributivity_add_left (requested_wz + 2) 1 8;
      assert ((requested_wz + 2) * 8 + 8 == (requested_wz + 3) * 8);
      FStar.Math.Lemmas.paren_add_right (U64.v hd) ((requested_wz + 2) * 8) 8;
      assert (rem_obj_nat + 8 == (U64.v hd + (requested_wz + 2) * 8) + 8);
      assert (rem_obj_nat + 8 == U64.v hd + ((requested_wz + 2) * 8 + 8));
      assert (rem_obj_nat + 8 == U64.v hd + (requested_wz + 3) * 8);
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
      assert (U64.v rem_hd == rem_hd_nat);
      assert (U64.v rem_obj == rem_obj_nat);
      assert (U64.v rem_obj == U64.v rem_hd + U64.v mword);
      MA.active_head_split_remainder_words_in_chunk
        c hd block_wz requested_wz rem_hd rem_obj;
      let rem_wz = block_wz - requested_wz - 1 in
      assert (rem_wz >= 1);
      assert (rem_wz < pow2 54);
      assert (rem_wz < pow2 64);
      assert (FStar.UInt.size rem_wz 64);
      let rem_wz_u : w:U64.t{U64.v w == rem_wz /\ U64.v w < pow2 54} =
        U64.uint_to_t rem_wz in
      assert (U64.v rem_wz_u == block_wz - requested_wz - 1);
      MA.major_alloc_head_split mh obj requested_wz fuel hdr next_fp rem_hd rem_obj;
      let r = MA.major_alloc_spec_with_fuel mh fp requested_wz fuel in
      assert (r.major_obj_out == fp);
      assert (r.major_fp_out == rem_obj);
      assert (r.major_alloc_out ==
              head_split_heap mh obj req next_fp rem_wz_u rem_hd rem_obj);
      let fuel' : f:nat{f < fuel} = fuel - 1 in
      MA.major_fl_chain_predecessor_not_in_suffix mh fp fuel;
      assert (MA.major_fl_chain_avoids mh next_fp fp fuel' = true);
      MA.major_fl_valid_next mh fp fuel;
      MA.major_fl_above_zero_next mh obj fuel next_fp;
      MA.major_fl_blocks_fit_next mh obj fuel next_fp;
      assert (MA.major_fl_valid mh next_fp fuel');
      assert (MA.major_fl_above_zero mh next_fp fuel');
      assert (MA.major_fl_blocks_fit mh next_fp fuel');
      head_split_preserves_old_free_list_avoids_allocated_head
        mh idx obj req block_wz next_fp rem_wz_u rem_hd rem_obj next_fp fuel';
      assert (MA.major_fl_chain_avoids r.major_alloc_out next_fp fp fuel' = true);
      head_split_remainder_head_facts
        mh idx obj req block_wz next_fp rem_wz_u rem_hd rem_obj;
      let rem_hdr = Alloc.make_header rem_wz_u Alloc.blue_bits 0UL in
      assert (MH.read_word_in_major r.major_alloc_out rem_obj == Some next_fp);
      assert (U64.v rem_obj >= U64.v mword);
      assert (U64.v rem_obj < heap_size);
      assert (U64.v rem_obj % U64.v mword == 0);
      assert (U64.v fp == U64.v hd + U64.v mword);
      assert (requested_wz + 2 > 1);
      assert (U64.v fp < U64.v rem_obj);
      assert (rem_obj <> fp);
      assert
        (match MH.read_word_in_major r.major_alloc_out (rem_obj <: obj_addr) with
         | Some next -> MA.major_fl_chain_avoids r.major_alloc_out next fp fuel' = true
         | None -> True);
      MA.major_fl_chain_avoids_step r.major_alloc_out rem_obj fp fuel;
      assert (r.major_obj_out == fp);
      assert (r.major_fp_out == rem_obj);
      assert (MA.major_fl_chain_avoids
                r.major_alloc_out r.major_fp_out r.major_obj_out fuel = true)
#pop-options

#push-options "--z3rlimit 20 --split_queries always --fuel 1 --ifuel 1"
let major_alloc_head_split_remainder_avoids_other
  (mh: MH.major_heap) (fp excl: U64.t)
  (requested_wz fuel: nat)
  : Lemma
      (requires fuel > 1 /\
                fp <> 0UL /\
                requested_wz > 0 /\
                MH.well_formed_major_heap mh /\
                MA.major_fl_valid mh fp fuel /\
                MA.major_fl_above_zero mh fp fuel /\
                MA.major_fl_blocks_fit mh fp fuel /\
                MA.major_fl_chain_terminates mh fp fuel = true /\
                MA.major_fl_chain_avoids mh fp excl fuel = true /\
                MA.major_fl_head_wosize mh fp >= requested_wz + 2 /\
                (MA.major_alloc_spec_with_fuel mh fp requested_wz fuel).major_fp_out
                  <> excl)
      (ensures
        (let r = MA.major_alloc_spec_with_fuel mh fp requested_wz fuel in
         MA.major_fl_chain_avoids
           r.major_alloc_out r.major_fp_out excl fuel = true))
  =
  major_alloc_head_split_preserves_alloc_shape mh fp requested_wz fuel;
  MA.major_fl_above_zero_current mh fp fuel;
  assert (U64.v fp >= U64.v zero_addr + U64.v mword);
  assert (U64.v fp >= U64.v mword);
  assert (U64.v fp < heap_size);
  assert (U64.v fp % U64.v mword == 0);
  MA.major_fl_chain_avoids_head_ne mh fp excl fuel;
  assert (fp <> excl);
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
    assert (requested_wz < pow2 64);
    assert (FStar.UInt.size requested_wz 64);
    let req : r:nat{r == requested_wz /\
                    r < pow2 54 /\ FStar.UInt.size r 64} = requested_wz in
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
      FStar.Math.Lemmas.distributivity_add_left (1 + requested_wz) 1 8;
      assert ((1 + requested_wz) * 8 + 8 == (requested_wz + 2) * 8);
      FStar.Math.Lemmas.paren_add_right (U64.v hd) ((1 + requested_wz) * 8) 8;
      assert (rem_obj_nat == U64.v hd + (requested_wz + 2) * 8);
      assert (requested_wz + 2 <= block_wz);
      assert (requested_wz + 3 <= 1 + block_wz);
      FStar.Math.Lemmas.distributivity_add_left (requested_wz + 2) 1 8;
      assert ((requested_wz + 2) * 8 + 8 == (requested_wz + 3) * 8);
      FStar.Math.Lemmas.paren_add_right (U64.v hd) ((requested_wz + 2) * 8) 8;
      assert (rem_obj_nat + 8 == (U64.v hd + (requested_wz + 2) * 8) + 8);
      assert (rem_obj_nat + 8 == U64.v hd + ((requested_wz + 2) * 8 + 8));
      assert (rem_obj_nat + 8 == U64.v hd + (requested_wz + 3) * 8);
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
      assert (U64.v rem_hd == rem_hd_nat);
      assert (U64.v rem_obj == rem_obj_nat);
      assert (U64.v rem_obj == U64.v rem_hd + U64.v mword);
      MA.active_head_split_remainder_words_in_chunk
        c hd block_wz requested_wz rem_hd rem_obj;
      let rem_wz = block_wz - requested_wz - 1 in
      assert (rem_wz >= 1);
      assert (rem_wz < pow2 54);
      assert (rem_wz < pow2 64);
      assert (FStar.UInt.size rem_wz 64);
      let rem_wz_u : w:U64.t{U64.v w == rem_wz /\ U64.v w < pow2 54} =
        U64.uint_to_t rem_wz in
      assert (U64.v rem_wz_u == block_wz - requested_wz - 1);
      MA.major_alloc_head_split mh obj requested_wz fuel hdr next_fp rem_hd rem_obj;
      let r = MA.major_alloc_spec_with_fuel mh fp requested_wz fuel in
      assert (r.major_obj_out == fp);
      assert (r.major_fp_out == rem_obj);
      assert (r.major_alloc_out ==
              head_split_heap mh obj req next_fp rem_wz_u rem_hd rem_obj);
      assert (rem_obj <> excl);
      let fuel' : f:nat{f < fuel} = fuel - 1 in
      MA.major_fl_chain_predecessor_not_in_suffix mh fp fuel;
      assert (MA.major_fl_chain_avoids mh next_fp fp fuel' = true);
      MA.major_fl_chain_avoids_tail mh fp excl fuel;
      assert (MA.major_fl_chain_avoids mh next_fp excl fuel' = true);
      MA.major_fl_valid_next mh fp fuel;
      MA.major_fl_above_zero_next mh obj fuel next_fp;
      MA.major_fl_blocks_fit_next mh obj fuel next_fp;
      assert (MA.major_fl_valid mh next_fp fuel');
      assert (MA.major_fl_above_zero mh next_fp fuel');
      assert (MA.major_fl_blocks_fit mh next_fp fuel');
      head_split_preserves_old_free_list_avoids_other
        mh idx obj req block_wz next_fp rem_wz_u rem_hd rem_obj next_fp excl fuel';
      assert (MA.major_fl_chain_avoids r.major_alloc_out next_fp excl fuel' = true);
      head_split_remainder_head_facts
        mh idx obj req block_wz next_fp rem_wz_u rem_hd rem_obj;
      assert (MH.read_word_in_major r.major_alloc_out rem_obj == Some next_fp);
      assert (U64.v rem_obj >= U64.v mword);
      assert (U64.v rem_obj < heap_size);
      assert (U64.v rem_obj % U64.v mword == 0);
      assert
        (match MH.read_word_in_major r.major_alloc_out (rem_obj <: obj_addr) with
         | Some next -> MA.major_fl_chain_avoids r.major_alloc_out next excl fuel' = true
         | None -> True);
      MA.major_fl_chain_avoids_step r.major_alloc_out rem_obj excl fuel;
      assert (MA.major_fl_chain_avoids
                r.major_alloc_out r.major_fp_out excl fuel = true)
#pop-options
