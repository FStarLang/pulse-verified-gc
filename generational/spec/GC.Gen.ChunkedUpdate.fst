/// ---------------------------------------------------------------------------
/// GC.Gen.ChunkedUpdate -- pointer rewriting over chunked major heaps
/// ---------------------------------------------------------------------------

module GC.Gen.ChunkedUpdate

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Gen.Base
open GC.Gen.Promote

module MH = GC.Spec.MajorHeap
module SpecMajorAlloc = GC.Spec.MajorAllocator

let obj_in_single_chunk_range (obj: obj_addr) : Tot prop =
  U64.v obj >= U64.v zero_addr + U64.v mword

let rec objects_in_single_chunk_range (objs: seq obj_addr) (idx: nat)
  : Tot prop (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then True
    else
      obj_in_single_chunk_range (Seq.index objs idx) /\
      objects_in_single_chunk_range objs (idx + 1)

let chunked_update_field_slot (src: obj_addr) (i: nat)
  : GTot (option hp_addr)
  = let field_offset = U64.v src + i * 8 in
    if field_offset + 8 > heap_size || field_offset % 8 <> 0 then
      None
    else
      Some (U64.uint_to_t field_offset <: hp_addr)

let chunked_update_field_slot_zero (obj: obj_addr)
  : Lemma
      (requires U64.v obj + U64.v mword <= heap_size)
      (ensures chunked_update_field_slot obj 0 == Some obj)
  =
  assert (U64.v mword == 8);
  assert (0 * 8 == 0);
  assert (U64.v obj + 0 * 8 == U64.v obj);
  assert (U64.v obj + 0 * 8 + 8 <= heap_size);
  assert (~(U64.v obj + 0 * 8 + 8 > heap_size));
  assert ((U64.v obj + 0 * 8) % 8 == 0);
  assert (~((U64.v obj + 0 * 8) % 8 <> 0));
  assert (U64.v (U64.uint_to_t (U64.v obj)) == U64.v obj);
  assert (U64.uint_to_t (U64.v obj) == obj)

let chunked_header_of_object (mh: MH.major_heap) (obj: obj_addr)
  : GTot (option U64.t)
  = MH.read_word_in_major mh (hd_address obj)

let chunked_wosize_nat_of_object (mh: MH.major_heap) (obj: obj_addr)
  : GTot nat
  = match chunked_header_of_object mh obj with
    | Some hdr -> U64.v (getWosize hdr)
    | None -> 0

let chunked_wosize_nat_header
  (mh: MH.major_heap) (obj: obj_addr) (hdr: U64.t)
  : Lemma
      (requires MH.read_word_in_major mh (hd_address obj) == Some hdr)
      (ensures
        chunked_wosize_nat_of_object mh obj == U64.v (getWosize hdr))
  =
  assert (chunked_header_of_object mh obj == Some hdr)

let chunked_is_blue (mh: MH.major_heap) (obj: obj_addr)
  : GTot bool
  = match chunked_header_of_object mh obj with
    | Some hdr -> getColor hdr = Blue
    | None -> false

let chunked_is_blue_header
  (mh: MH.major_heap) (obj: obj_addr) (hdr: U64.t)
  : Lemma
      (requires MH.read_word_in_major mh (hd_address obj) == Some hdr)
      (ensures chunked_is_blue mh obj == (getColor hdr = Blue))
  =
  assert (chunked_header_of_object mh obj == Some hdr)

let chunked_is_no_scan (mh: MH.major_heap) (obj: obj_addr)
  : GTot bool
  = match chunked_header_of_object mh obj with
    | Some hdr -> U64.v (getTag hdr) >= U64.v no_scan_tag
    | None -> false

let chunked_words_disjoint (a b: hp_addr) : Tot prop =
  U64.v a + U64.v mword <= U64.v b \/
  U64.v b + U64.v mword <= U64.v a

let chunked_update_field (mh: MH.major_heap) (field_addr: hp_addr)
                         (fwd: forwarding_map)
  : GTot MH.major_heap
  = match MH.read_word_in_major mh field_addr with
    | None -> mh
    | Some raw ->
      let field_val = to_minor_offset raw in
      if is_minor_pointer field_val then
        let new_val = fwd field_val in
        if new_val <> 0UL then
          SpecMajorAlloc.major_write_word_or_same mh field_addr new_val
        else
          mh
      else
        mh

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let chunked_update_field_slot_in_object_chunk
  (mh: MH.major_heap) (obj: obj_addr) (i: nat) (field_addr: hp_addr)
  : Lemma
      (requires
       MH.well_formed_major_heap mh /\
       Seq.mem obj (MH.major_objects mh) /\
       i < chunked_wosize_nat_of_object mh obj /\
       chunked_update_field_slot obj i == Some field_addr)
      (ensures
       (let idx = MH.lookup_chunk_index_value mh (hd_address obj) in
       MH.lookup_chunk_index mh (hd_address obj) == Some idx /\
       idx < Seq.length mh /\
       MH.word_in_chunk (Seq.index mh idx) (hd_address obj) /\
       MH.word_in_chunk (Seq.index mh idx) field_addr /\
       MH.lookup_chunk_index mh field_addr == Some idx /\
       U64.v obj <= U64.v field_addr /\
       U64.v field_addr + U64.v mword <=
         U64.v obj +
           MH.object_wosize_in_chunk (Seq.index mh idx) obj *
             U64.v mword))
  =
  MH.major_objects_member_header_read_some mh obj;
  match MH.read_word_in_major mh (hd_address obj) with
  | None -> assert False
  | Some hdr ->
    let idx = MH.lookup_chunk_index_value mh (hd_address obj) in
    MH.read_word_in_major_lookup_index mh (hd_address obj) hdr;
    assert (MH.lookup_chunk_index mh (hd_address obj) == Some idx);
    assert (idx < Seq.length mh);
    let c = Seq.index mh idx in
    assert (MH.word_in_chunk c (hd_address obj));
    assert (MH.read_word_in_chunk c (hd_address obj) == hdr);
    MH.major_objects_member_in_lookup_chunk mh idx obj;
    assert (Seq.mem obj (MH.objects_in_chunk c));
    MH.objects_in_chunk_member_header_fits c obj;
    let wz = U64.v (getWosize hdr) in
    assert (chunked_wosize_nat_of_object mh obj == wz);
    assert (i < wz);
    assert (MH.object_wosize_in_chunk c obj == wz);
    let field_offset = U64.v obj + i * U64.v mword in
    assert (U64.v mword == 8);
    assert (field_offset == U64.v obj + i * 8);
    assert (U64.v field_addr == field_offset);
    assert (U64.v obj <= U64.v field_addr);
    assert (i + 1 <= wz);
    FStar.Math.Lemmas.lemma_mult_le_right (U64.v mword) (i + 1) wz;
    FStar.Math.Lemmas.distributivity_add_left i 1 (U64.v mword);
    assert (i * U64.v mword + U64.v mword ==
           (i + 1) * U64.v mword);
    FStar.Math.Lemmas.paren_add_right
      (U64.v obj) (i * U64.v mword) (U64.v mword);
    assert (field_offset + U64.v mword ==
           U64.v obj + (i + 1) * U64.v mword);
    assert (U64.v field_addr + U64.v mword ==
           U64.v obj + (i + 1) * U64.v mword);
    assert ((i + 1) * U64.v mword <= wz * U64.v mword);
    assert (U64.v field_addr + U64.v mword <=
           U64.v obj + MH.object_wosize_in_chunk c obj * U64.v mword);
    MH.major_object_payload_word_in_lookup_chunk mh idx obj field_addr
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let chunked_update_field_slot_disjoint_from_header
  (mh: MH.major_heap) (src: obj_addr) (i: nat) (field_addr: hp_addr)
  (h: obj_addr)
  : Lemma
      (requires
       MH.well_formed_major_heap mh /\
       Seq.mem src (MH.major_objects mh) /\
       Seq.mem h (MH.major_objects mh) /\
       src <> h /\
       i < chunked_wosize_nat_of_object mh src /\
       chunked_update_field_slot src i == Some field_addr)
      (ensures chunked_words_disjoint field_addr (hd_address h))
  =
  chunked_update_field_slot_in_object_chunk mh src i field_addr;
  let sidx = MH.lookup_chunk_index_value mh (hd_address src) in
  assert (MH.lookup_chunk_index mh (hd_address src) == Some sidx);
  assert (sidx < Seq.length mh);
  assert (MH.word_in_chunk (Seq.index mh sidx) field_addr);
  MH.major_objects_member_header_read_some mh h;
  match MH.read_word_in_major mh (hd_address h) with
  | None -> assert False
  | Some hhdr ->
    let hidx = MH.lookup_chunk_index_value mh (hd_address h) in
    MH.read_word_in_major_lookup_index mh (hd_address h) hhdr;
    assert (MH.lookup_chunk_index mh (hd_address h) == Some hidx);
    assert (hidx < Seq.length mh);
    assert (MH.word_in_chunk (Seq.index mh hidx) (hd_address h));
    if sidx = hidx then begin
      let c = Seq.index mh sidx in
      assert (Seq.index mh hidx == c);
      MH.major_objects_member_in_lookup_chunk mh sidx src;
      MH.major_objects_member_in_lookup_chunk mh hidx h;
      assert (Seq.mem src (MH.objects_in_chunk c));
      assert (Seq.mem h (MH.objects_in_chunk c));
      if U64.v src < U64.v h then begin
       MH.objects_in_chunk_separated c src h;
       let wz = MH.object_wosize_in_chunk c src in
       assert (U64.v field_addr + U64.v mword <=
               U64.v src + wz * U64.v mword);
       assert (U64.v src % U64.v mword == 0);
       SpecMajorAlloc.aligned_plus_word_product (U64.v src) wz;
       assert ((U64.v src + wz * U64.v mword) % U64.v mword == 0);
       assert (U64.v h % U64.v mword == 0);
       MH.word_aligned_gt_at_least_mword
         (U64.v h) (U64.v src + wz * U64.v mword);
       hd_address_spec h;
       assert (U64.v (hd_address h) + U64.v mword == U64.v h);
       assert (U64.v src + wz * U64.v mword <= U64.v (hd_address h));
       assert (U64.v field_addr + U64.v mword <= U64.v (hd_address h))
      end else begin
       if U64.v h < U64.v src then begin
         hd_address_spec h;
         assert (U64.v (hd_address h) + U64.v mword == U64.v h);
         assert (U64.v h <= U64.v src);
         assert (U64.v src <= U64.v field_addr);
         assert (U64.v (hd_address h) + U64.v mword <= U64.v field_addr)
       end else
         assert False
      end
    end else begin
      MH.chunks_pairwise_disjoint_index mh sidx hidx;
      MH.chunks_disjoint_words_disjoint
       (Seq.index mh sidx) (Seq.index mh hidx) field_addr (hd_address h)
    end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let chunked_update_field_slots_disjoint_distinct
  (mh: MH.major_heap)
  (src: obj_addr) (i: nat) (src_field: hp_addr)
  (dst: obj_addr) (j: nat) (dst_field: hp_addr)
  : Lemma
      (requires
       MH.well_formed_major_heap mh /\
       Seq.mem src (MH.major_objects mh) /\
       Seq.mem dst (MH.major_objects mh) /\
       src <> dst /\
       i < chunked_wosize_nat_of_object mh src /\
       j < chunked_wosize_nat_of_object mh dst /\
       chunked_update_field_slot src i == Some src_field /\
       chunked_update_field_slot dst j == Some dst_field)
      (ensures chunked_words_disjoint src_field dst_field)
  =
  chunked_update_field_slot_in_object_chunk mh src i src_field;
  chunked_update_field_slot_in_object_chunk mh dst j dst_field;
  let sidx = MH.lookup_chunk_index_value mh (hd_address src) in
  let didx = MH.lookup_chunk_index_value mh (hd_address dst) in
  assert (MH.lookup_chunk_index mh (hd_address src) == Some sidx);
  assert (MH.lookup_chunk_index mh (hd_address dst) == Some didx);
  assert (sidx < Seq.length mh);
  assert (didx < Seq.length mh);
  assert (MH.word_in_chunk (Seq.index mh sidx) src_field);
  assert (MH.word_in_chunk (Seq.index mh didx) dst_field);
  if sidx = didx then begin
    let c = Seq.index mh sidx in
    assert (Seq.index mh didx == c);
    MH.major_objects_member_in_lookup_chunk mh sidx src;
    MH.major_objects_member_in_lookup_chunk mh didx dst;
    assert (Seq.mem src (MH.objects_in_chunk c));
    assert (Seq.mem dst (MH.objects_in_chunk c));
    if U64.v src < U64.v dst then begin
      MH.objects_in_chunk_separated c src dst;
      let wz = MH.object_wosize_in_chunk c src in
      assert (U64.v src_field + U64.v mword <=
             U64.v src + wz * U64.v mword);
      assert (U64.v src % U64.v mword == 0);
      SpecMajorAlloc.aligned_plus_word_product (U64.v src) wz;
      assert ((U64.v src + wz * U64.v mword) % U64.v mword == 0);
      assert (U64.v dst % U64.v mword == 0);
      MH.word_aligned_gt_at_least_mword
       (U64.v dst) (U64.v src + wz * U64.v mword);
      hd_address_spec dst;
      assert (U64.v (hd_address dst) + U64.v mword == U64.v dst);
      assert (U64.v src + wz * U64.v mword <= U64.v (hd_address dst));
      assert (U64.v src_field + U64.v mword <= U64.v (hd_address dst));
      assert (U64.v (hd_address dst) + U64.v mword <= U64.v dst_field);
      assert (U64.v src_field + U64.v mword <= U64.v dst_field)
    end else begin
      if U64.v dst < U64.v src then begin
       MH.objects_in_chunk_separated c dst src;
       let wz = MH.object_wosize_in_chunk c dst in
       assert (U64.v dst_field + U64.v mword <=
               U64.v dst + wz * U64.v mword);
       assert (U64.v dst % U64.v mword == 0);
       SpecMajorAlloc.aligned_plus_word_product (U64.v dst) wz;
       assert ((U64.v dst + wz * U64.v mword) % U64.v mword == 0);
       assert (U64.v src % U64.v mword == 0);
       MH.word_aligned_gt_at_least_mword
         (U64.v src) (U64.v dst + wz * U64.v mword);
       hd_address_spec src;
       assert (U64.v (hd_address src) + U64.v mword == U64.v src);
       assert (U64.v dst + wz * U64.v mword <= U64.v (hd_address src));
       assert (U64.v dst_field + U64.v mword <= U64.v (hd_address src));
       assert (U64.v (hd_address src) + U64.v mword <= U64.v src_field);
       assert (U64.v dst_field + U64.v mword <= U64.v src_field)
      end else
       assert False
    end
  end else begin
    MH.chunks_pairwise_disjoint_index mh sidx didx;
    MH.chunks_disjoint_words_disjoint
      (Seq.index mh sidx) (Seq.index mh didx) src_field dst_field
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let chunked_update_field_preserves_wf_and_major_objects
  (mh: MH.major_heap) (obj: obj_addr) (i: nat) (field_addr: hp_addr)
  (fwd: forwarding_map)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        i < chunked_wosize_nat_of_object mh obj /\
        chunked_update_field_slot obj i == Some field_addr)
      (ensures
        MH.well_formed_major_heap (chunked_update_field mh field_addr fwd) /\
        MH.major_objects (chunked_update_field mh field_addr fwd) ==
          MH.major_objects mh /\
        chunked_header_of_object (chunked_update_field mh field_addr fwd) obj ==
          chunked_header_of_object mh obj)
  =
  MH.major_objects_member_header_read_some mh obj;
  match MH.read_word_in_major mh (hd_address obj) with
  | None -> assert False
  | Some hdr ->
    let hidx = MH.lookup_chunk_index_value mh (hd_address obj) in
    MH.read_word_in_major_lookup_index mh (hd_address obj) hdr;
    assert (MH.lookup_chunk_index mh (hd_address obj) == Some hidx);
    assert (hidx < Seq.length mh);
    let c = Seq.index mh hidx in
    assert (MH.word_in_chunk c (hd_address obj));
    assert (MH.read_word_in_chunk c (hd_address obj) == hdr);
    MH.major_objects_member_in_lookup_chunk mh hidx obj;
    assert (Seq.mem obj (MH.objects_in_chunk c));
    MH.objects_in_chunk_member_header_fits c obj;
    let wz = U64.v (getWosize hdr) in
    assert (chunked_wosize_nat_of_object mh obj == wz);
    assert (i < wz);
    assert (MH.object_wosize_in_chunk c obj == wz);
    let field_offset = U64.v obj + i * U64.v mword in
    assert (U64.v mword == 8);
    assert (field_offset == U64.v obj + i * 8);
    assert (U64.v field_addr == field_offset);
    hd_address_spec obj;
    assert (U64.v obj == U64.v (hd_address obj) + U64.v mword);
    assert (U64.v obj <= U64.v field_addr);
    assert (U64.v field_addr + U64.v mword ==
            field_offset + U64.v mword);
    assert (i + 1 <= wz);
    FStar.Math.Lemmas.lemma_mult_le_right (U64.v mword) (i + 1) wz;
    FStar.Math.Lemmas.distributivity_add_left i 1 (U64.v mword);
    assert (i * U64.v mword + U64.v mword ==
            (i + 1) * U64.v mword);
    FStar.Math.Lemmas.paren_add_right
      (U64.v obj) (i * U64.v mword) (U64.v mword);
    assert (field_offset + U64.v mword ==
            U64.v obj + (i + 1) * U64.v mword);
    assert (U64.v field_addr + U64.v mword ==
            U64.v obj + (i + 1) * U64.v mword);
    assert ((i + 1) * U64.v mword <= wz * U64.v mword);
    assert (U64.v field_addr + U64.v mword <=
            U64.v obj + MH.object_wosize_in_chunk c obj * U64.v mword);
    assert (MH.object_header_size_fits_in_chunk c obj);
    assert (MH.chunk_start c <= U64.v (hd_address obj));
    assert (U64.v (hd_address obj) <= U64.v field_addr);
    assert (MH.chunk_start c <= U64.v field_addr);
    assert (U64.v (hd_address obj) +
            (1 + wz) * U64.v mword <= MH.chunk_end c);
    assert (U64.v (hd_address obj) + U64.v mword == U64.v obj);
    FStar.Math.Lemmas.distributivity_add_left 1 wz (U64.v mword);
    assert ((1 + wz) * U64.v mword ==
            U64.v mword + wz * U64.v mword);
    FStar.Math.Lemmas.paren_add_right
      (U64.v (hd_address obj)) (U64.v mword) (wz * U64.v mword);
    assert (U64.v obj + wz * U64.v mword ==
            U64.v (hd_address obj) + (1 + wz) * U64.v mword);
    assert (U64.v field_addr + U64.v mword <=
            U64.v obj + wz * U64.v mword);
    assert (U64.v field_addr + U64.v mword <= MH.chunk_end c);
    assert (U64.v field_addr % U64.v mword == 0);
    assert (MH.word_in_chunk c field_addr);
    MH.lookup_chunk_index_word_in_chunk mh field_addr hidx;
    assert (MH.lookup_chunk_index mh field_addr == Some hidx);
    MH.read_word_in_major_at_lookup_index mh field_addr hidx;
    match MH.read_word_in_major mh field_addr with
    | None -> assert False
    | Some raw ->
      let field_val = to_minor_offset raw in
      if is_minor_pointer field_val then begin
        let new_val = fwd field_val in
        if new_val <> 0UL then begin
          let c' = MH.write_word_in_chunk c field_addr new_val in
          MH.write_word_at_index_preserves_wf mh field_addr new_val hidx;
          MH.major_objects_write_member_payload_preserves
            mh hidx obj field_addr new_val;
          MH.write_word_in_major_at_lookup_index mh field_addr new_val hidx;
          assert (MH.write_word_in_major mh field_addr new_val ==
                  Some (Seq.upd mh hidx c'));
          SpecMajorAlloc.major_write_word_or_same_some
            mh (Seq.upd mh hidx c') field_addr new_val;
          assert (chunked_update_field mh field_addr fwd ==
                  Seq.upd mh hidx c');
          assert (MH.well_formed_major_heap
                    (chunked_update_field mh field_addr fwd));
          assert (MH.major_objects
                    (chunked_update_field mh field_addr fwd) ==
                  MH.major_objects mh);
          assert (U64.v (hd_address obj) + U64.v mword <= U64.v field_addr);
          assert (field_addr <> hd_address obj);
          MH.read_write_in_chunk_different
            c field_addr (hd_address obj) new_val;
          MH.write_word_in_chunk_preserves_range c field_addr new_val;
          assert (MH.word_in_chunk c' (hd_address obj));
          assert (MH.read_word_in_chunk c' (hd_address obj) == hdr);
          assert (Seq.index (Seq.upd mh hidx c') hidx == c');
          MH.lookup_chunk_index_word_in_chunk
            (Seq.upd mh hidx c') (hd_address obj) hidx;
          MH.read_word_in_major_at_lookup_index
            (Seq.upd mh hidx c') (hd_address obj) hidx;
          assert (MH.read_word_in_major (Seq.upd mh hidx c') (hd_address obj) ==
                  Some hdr);
          assert (chunked_header_of_object
                    (chunked_update_field mh field_addr fwd) obj ==
                  chunked_header_of_object mh obj)
        end
      end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let chunked_update_field_preserves_wf_and_read_disjoint
  (mh: MH.major_heap) (field_addr addr: hp_addr)
  (old: U64.t) (fwd: forwarding_map)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        MH.read_word_in_major mh addr == Some old /\
        chunked_words_disjoint field_addr addr)
      (ensures
        MH.well_formed_major_heap
          (chunked_update_field mh field_addr fwd) /\
        MH.read_word_in_major
          (chunked_update_field mh field_addr fwd) addr == Some old)
  =
  match MH.read_word_in_major mh field_addr with
  | None -> ()
  | Some raw ->
    let field_val = to_minor_offset raw in
    if is_minor_pointer field_val then begin
      let new_val = fwd field_val in
      if new_val <> 0UL then begin
        MH.read_word_in_major_lookup_index mh addr old;
        let ridx = MH.lookup_chunk_index_value mh addr in
        assert (MH.lookup_chunk_index mh addr == Some ridx);
        assert (ridx < Seq.length mh);
        let rc = Seq.index mh ridx in
        assert (MH.word_in_chunk rc addr);
        assert (MH.read_word_in_chunk rc addr == old);
        MH.read_word_in_major_lookup_index mh field_addr raw;
        let widx = MH.lookup_chunk_index_value mh field_addr in
        assert (MH.lookup_chunk_index mh field_addr == Some widx);
        assert (widx < Seq.length mh);
        let wc = Seq.index mh widx in
        assert (MH.word_in_chunk wc field_addr);
        let wc' = MH.write_word_in_chunk wc field_addr new_val in
        MH.write_word_at_index_preserves_wf mh field_addr new_val widx;
        MH.write_word_in_major_at_lookup_index mh field_addr new_val widx;
        assert (MH.write_word_in_major mh field_addr new_val ==
                Some (Seq.upd mh widx wc'));
        SpecMajorAlloc.major_write_word_or_same_some
          mh (Seq.upd mh widx wc') field_addr new_val;
        assert (chunked_update_field mh field_addr fwd ==
                Seq.upd mh widx wc');
        let mh' = Seq.upd mh widx wc' in
        assert (MH.well_formed_major_heap mh');
        if ridx = widx then begin
          assert (rc == wc);
          assert (Seq.index mh' ridx == wc');
          assert (field_addr <> addr);
          MH.read_write_in_chunk_different wc field_addr addr new_val;
          MH.write_word_in_chunk_preserves_range wc field_addr new_val;
          assert (MH.word_in_chunk wc' addr);
          assert (MH.read_word_in_chunk wc' addr == old)
        end else begin
          assert (Seq.index mh' ridx == rc);
          assert (MH.word_in_chunk (Seq.index mh' ridx) addr);
          assert (MH.read_word_in_chunk (Seq.index mh' ridx) addr == old)
        end;
        MH.lookup_chunk_index_word_in_chunk mh' addr ridx;
        MH.read_word_in_major_at_lookup_index mh' addr ridx;
        assert (MH.read_word_in_major mh' addr == Some old)
      end
    end
#pop-options

let rec chunked_update_object_pointers (mh: MH.major_heap) (obj: obj_addr)
                                       (wosize: nat) (fwd: forwarding_map)
                                       (i: nat)
  : GTot MH.major_heap (decreases (wosize - i))
  = if i >= wosize then mh
    else
      match chunked_update_field_slot obj i with
      | None -> mh
      | Some field_addr ->
        let mh' = chunked_update_field mh field_addr fwd in
        chunked_update_object_pointers mh' obj wosize fwd (i + 1)

let chunked_update_object_pointers_done
  (mh: MH.major_heap) (obj: obj_addr) (wosize: nat)
  (fwd: forwarding_map) (i: nat)
  : Lemma
      (requires i >= wosize)
      (ensures chunked_update_object_pointers mh obj wosize fwd i == mh)
  = ()

let chunked_update_object_pointers_step
  (mh: MH.major_heap) (obj: obj_addr) (wosize: nat)
  (fwd: forwarding_map) (i: nat) (field_addr: hp_addr)
  : Lemma
      (requires i < wosize /\
                chunked_update_field_slot obj i == Some field_addr)
      (ensures
        chunked_update_object_pointers mh obj wosize fwd i ==
        chunked_update_object_pointers
          (chunked_update_field mh field_addr fwd) obj wosize fwd (i + 1))
  = ()

let chunked_update_object_pointers_invalid_slot
  (mh: MH.major_heap) (obj: obj_addr) (wosize: nat)
  (fwd: forwarding_map) (i: nat)
  : Lemma
      (requires i < wosize /\
                chunked_update_field_slot obj i == None)
      (ensures chunked_update_object_pointers mh obj wosize fwd i == mh)
  = ()

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let rec chunked_update_object_pointers_preserves_wf_and_major_objects
  (mh: MH.major_heap) (obj: obj_addr) (wosize: nat)
  (fwd: forwarding_map) (i: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        wosize == chunked_wosize_nat_of_object mh obj)
      (ensures
        (let mh' = chunked_update_object_pointers mh obj wosize fwd i in
        MH.well_formed_major_heap mh' /\
        MH.major_objects mh' == MH.major_objects mh /\
        chunked_header_of_object mh' obj == chunked_header_of_object mh obj))
      (decreases (wosize - i))
  =
  if i >= wosize then
    ()
  else begin
    match chunked_update_field_slot obj i with
    | None -> ()
    | Some field_addr ->
      chunked_update_field_preserves_wf_and_major_objects
        mh obj i field_addr fwd;
      let mh1 = chunked_update_field mh field_addr fwd in
      assert (MH.well_formed_major_heap mh1);
      assert (MH.major_objects mh1 == MH.major_objects mh);
      assert (Seq.mem obj (MH.major_objects mh1));
      assert (chunked_header_of_object mh1 obj ==
              chunked_header_of_object mh obj);
      assert (chunked_wosize_nat_of_object mh1 obj ==
              chunked_wosize_nat_of_object mh obj);
      assert (wosize == chunked_wosize_nat_of_object mh1 obj);
      chunked_update_object_pointers_preserves_wf_and_major_objects
        mh1 obj wosize fwd (i + 1);
      assert (MH.major_objects
                (chunked_update_object_pointers mh1 obj wosize fwd (i + 1)) ==
              MH.major_objects mh1);
      assert (MH.major_objects
                (chunked_update_object_pointers mh obj wosize fwd i) ==
              MH.major_objects mh);
      assert (chunked_header_of_object
                (chunked_update_object_pointers mh obj wosize fwd i) obj ==
              chunked_header_of_object mh obj)
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let rec chunked_update_object_pointers_preserves_read_disjoint
  (mh: MH.major_heap) (obj: obj_addr) (wosize: nat)
  (fwd: forwarding_map) (i: nat) (addr: hp_addr) (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        MH.read_word_in_major mh addr == Some old /\
        (forall (k: nat) (field_addr: hp_addr).
          i <= k /\ k < wosize /\
          chunked_update_field_slot obj k == Some field_addr ==>
          chunked_words_disjoint field_addr addr))
      (ensures
        (let mh' = chunked_update_object_pointers mh obj wosize fwd i in
        MH.well_formed_major_heap mh' /\
        MH.read_word_in_major mh' addr == Some old))
      (decreases (wosize - i))
  =
  if i >= wosize then
    ()
  else begin
    match chunked_update_field_slot obj i with
    | None -> ()
    | Some field_addr ->
      assert (chunked_words_disjoint field_addr addr);
      chunked_update_field_preserves_wf_and_read_disjoint
        mh field_addr addr old fwd;
      let mh1 = chunked_update_field mh field_addr fwd in
      assert (MH.well_formed_major_heap mh1);
      assert (MH.read_word_in_major mh1 addr == Some old);
      let tail_disjoint (k: nat) (field_addr': hp_addr)
        : Lemma
            (requires
              i + 1 <= k /\ k < wosize /\
              chunked_update_field_slot obj k == Some field_addr')
            (ensures chunked_words_disjoint field_addr' addr)
        = ()
      in
      FStar.Classical.forall_intro
        (fun k -> FStar.Classical.forall_intro
          (FStar.Classical.move_requires (tail_disjoint k)));
      assert (forall (k: nat) (field_addr': hp_addr).
        i + 1 <= k /\ k < wosize /\
        chunked_update_field_slot obj k == Some field_addr' ==>
        chunked_words_disjoint field_addr' addr);
      chunked_update_object_pointers_preserves_read_disjoint
        mh1 obj wosize fwd (i + 1) addr old
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let chunked_update_object_pointers_preserves_header_read
  (mh: MH.major_heap) (obj: obj_addr) (wosize: nat)
  (fwd: forwarding_map) (i: nat) (h: obj_addr) (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem h (MH.major_objects mh) /\
        wosize == chunked_wosize_nat_of_object mh obj /\
        MH.read_word_in_major mh (hd_address h) == Some hdr)
      (ensures
        (let mh' = chunked_update_object_pointers mh obj wosize fwd i in
        MH.well_formed_major_heap mh' /\
        MH.major_objects mh' == MH.major_objects mh /\
        MH.read_word_in_major mh' (hd_address h) == Some hdr))
  =
  chunked_update_object_pointers_preserves_wf_and_major_objects
    mh obj wosize fwd i;
  if obj = h then begin
    assert (chunked_header_of_object
              (chunked_update_object_pointers mh obj wosize fwd i) h ==
            chunked_header_of_object mh h);
    assert (chunked_header_of_object mh h == Some hdr)
  end else begin
    let disjoint (k: nat) (field_addr: hp_addr)
      : Lemma
          (requires
            i <= k /\ k < wosize /\
            chunked_update_field_slot obj k == Some field_addr)
          (ensures chunked_words_disjoint field_addr (hd_address h))
      = chunked_update_field_slot_disjoint_from_header
          mh obj k field_addr h
    in
    FStar.Classical.forall_intro
      (fun k -> FStar.Classical.forall_intro
        (FStar.Classical.move_requires (disjoint k)));
    assert (forall (k: nat) (field_addr: hp_addr).
      i <= k /\ k < wosize /\
      chunked_update_field_slot obj k == Some field_addr ==>
      chunked_words_disjoint field_addr (hd_address h));
    chunked_update_object_pointers_preserves_read_disjoint
      mh obj wosize fwd i (hd_address h) hdr
  end
#pop-options

let rec chunked_objects_members (mh: MH.major_heap) (objs: seq obj_addr)
                                (idx: nat)
  : Tot prop (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then True
    else
      Seq.mem (Seq.index objs idx) (MH.major_objects mh) /\
      chunked_objects_members mh objs (idx + 1)

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"
let rec chunked_objects_members_transfer
  (mh mh': MH.major_heap) (objs: seq obj_addr) (idx: nat)
  : Lemma
      (requires
        chunked_objects_members mh objs idx /\
        MH.major_objects mh' == MH.major_objects mh)
      (ensures chunked_objects_members mh' objs idx)
      (decreases (Seq.length objs - idx))
  =
  if idx >= Seq.length objs then ()
  else
    chunked_objects_members_transfer mh mh' objs (idx + 1)
#pop-options

let rec chunked_update_all_objects_aux (mh: MH.major_heap) (objs: seq obj_addr)
                                       (fwd: forwarding_map) (idx: nat)
  : GTot MH.major_heap (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then mh
    else
      let obj = Seq.index objs idx in
      if chunked_is_blue mh obj then
        chunked_update_all_objects_aux mh objs fwd (idx + 1)
      else if chunked_is_no_scan mh obj then
        chunked_update_all_objects_aux mh objs fwd (idx + 1)
      else
        let wz = chunked_wosize_nat_of_object mh obj in
        let mh' = chunked_update_object_pointers mh obj wz fwd 0 in
        chunked_update_all_objects_aux mh' objs fwd (idx + 1)

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let rec chunked_update_all_objects_aux_preserves_wf_and_major_objects
  (mh: MH.major_heap) (objs: seq obj_addr) (fwd: forwarding_map) (idx: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_objects_members mh objs idx)
      (ensures
        (let mh' = chunked_update_all_objects_aux mh objs fwd idx in
        MH.well_formed_major_heap mh' /\
        MH.major_objects mh' == MH.major_objects mh))
      (decreases (Seq.length objs - idx))
  =
  if idx >= Seq.length objs then
    ()
  else begin
    let obj = Seq.index objs idx in
    assert (Seq.mem obj (MH.major_objects mh));
    assert (chunked_objects_members mh objs (idx + 1));
    if chunked_is_blue mh obj then
      chunked_update_all_objects_aux_preserves_wf_and_major_objects
        mh objs fwd (idx + 1)
    else if chunked_is_no_scan mh obj then
      chunked_update_all_objects_aux_preserves_wf_and_major_objects
        mh objs fwd (idx + 1)
    else begin
      let wz = chunked_wosize_nat_of_object mh obj in
      chunked_update_object_pointers_preserves_wf_and_major_objects
        mh obj wz fwd 0;
      let mh1 = chunked_update_object_pointers mh obj wz fwd 0 in
      assert (MH.well_formed_major_heap mh1);
      assert (MH.major_objects mh1 == MH.major_objects mh);
      chunked_objects_members_transfer mh mh1 objs (idx + 1);
      chunked_update_all_objects_aux_preserves_wf_and_major_objects
        mh1 objs fwd (idx + 1);
      assert (MH.major_objects
                (chunked_update_all_objects_aux mh1 objs fwd (idx + 1)) ==
              MH.major_objects mh1);
      assert (MH.major_objects
                (chunked_update_all_objects_aux mh objs fwd idx) ==
              MH.major_objects mh)
    end
  end

let chunked_update_major_pointers (mh: MH.major_heap) (fwd: forwarding_map)
  : GTot MH.major_heap
  = chunked_update_all_objects_aux mh (MH.major_objects mh) fwd 0

let rec chunked_major_objects_members_from (mh: MH.major_heap) (idx: nat)
  : Lemma
      (requires idx <= Seq.length (MH.major_objects mh))
      (ensures chunked_objects_members mh (MH.major_objects mh) idx)
      (decreases (Seq.length (MH.major_objects mh) - idx))
  =
  if idx >= Seq.length (MH.major_objects mh) then
    ()
  else begin
    FStar.Seq.Properties.lemma_index_is_nth (MH.major_objects mh) idx;
    assert (Seq.mem (Seq.index (MH.major_objects mh) idx)
              (MH.major_objects mh));
    chunked_major_objects_members_from mh (idx + 1)
  end

let chunked_major_objects_members (mh: MH.major_heap)
  : Lemma
      (ensures chunked_objects_members mh (MH.major_objects mh) 0)
  = chunked_major_objects_members_from mh 0

let chunked_update_major_pointers_preserves_wf_and_major_objects
  (mh: MH.major_heap) (fwd: forwarding_map)
  : Lemma
      (requires MH.well_formed_major_heap mh)
      (ensures
        MH.well_formed_major_heap (chunked_update_major_pointers mh fwd) /\
        MH.major_objects (chunked_update_major_pointers mh fwd) ==
          MH.major_objects mh)
  =
  chunked_major_objects_members mh;
  chunked_update_all_objects_aux_preserves_wf_and_major_objects
    mh (MH.major_objects mh) fwd 0
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let rec chunked_update_all_objects_aux_preserves_header
  (mh: MH.major_heap) (objs: seq obj_addr) (fwd: forwarding_map)
  (idx: nat) (h: obj_addr) (hdr: U64.t)
  : Lemma
      (requires
    MH.well_formed_major_heap mh /\
    chunked_objects_members mh objs idx /\
    Seq.mem h (MH.major_objects mh) /\
    MH.read_word_in_major mh (hd_address h) == Some hdr)
      (ensures
    (let mh' = chunked_update_all_objects_aux mh objs fwd idx in
    MH.well_formed_major_heap mh' /\
    MH.major_objects mh' == MH.major_objects mh /\
    MH.read_word_in_major mh' (hd_address h) == Some hdr))
      (decreases (Seq.length objs - idx))
  =
  if idx >= Seq.length objs then
    ()
  else begin
    let obj = Seq.index objs idx in
    assert (Seq.mem obj (MH.major_objects mh));
    assert (chunked_objects_members mh objs (idx + 1));
    if chunked_is_blue mh obj then begin
      chunked_update_all_objects_aux_preserves_header
    mh objs fwd (idx + 1) h hdr
    end else if chunked_is_no_scan mh obj then begin
      chunked_update_all_objects_aux_preserves_header
    mh objs fwd (idx + 1) h hdr
    end else begin
      let wz = chunked_wosize_nat_of_object mh obj in
      chunked_update_object_pointers_preserves_header_read
    mh obj wz fwd 0 h hdr;
      let mh1 = chunked_update_object_pointers mh obj wz fwd 0 in
      assert (MH.well_formed_major_heap mh1);
      assert (MH.major_objects mh1 == MH.major_objects mh);
      assert (Seq.mem h (MH.major_objects mh1));
      assert (MH.read_word_in_major mh1 (hd_address h) == Some hdr);
      chunked_objects_members_transfer mh mh1 objs (idx + 1);
      chunked_update_all_objects_aux_preserves_header
    mh1 objs fwd (idx + 1) h hdr;
      assert (MH.major_objects
            (chunked_update_all_objects_aux mh1 objs fwd (idx + 1)) ==
          MH.major_objects mh1);
      assert (MH.read_word_in_major
            (chunked_update_all_objects_aux mh1 objs fwd (idx + 1))
            (hd_address h) == Some hdr)
    end
  end

let chunked_update_major_pointers_preserves_header
  (mh: MH.major_heap) (fwd: forwarding_map) (h: obj_addr) (hdr: U64.t)
  : Lemma
      (requires
    MH.well_formed_major_heap mh /\
    Seq.mem h (MH.major_objects mh) /\
    MH.read_word_in_major mh (hd_address h) == Some hdr)
      (ensures
    MH.read_word_in_major
      (chunked_update_major_pointers mh fwd) (hd_address h) ==
    Some hdr)
  =
  chunked_major_objects_members mh;
  chunked_update_all_objects_aux_preserves_header
    mh (MH.major_objects mh) fwd 0 h hdr

let rec chunked_update_all_objects_aux_preserves_blue_field
  (mh: MH.major_heap) (objs: seq obj_addr) (fwd: forwarding_map)
  (idx: nat) (h: obj_addr) (j: nat) (field_addr: hp_addr) (old: U64.t)
  : Lemma
      (requires
    MH.well_formed_major_heap mh /\
    chunked_objects_members mh objs idx /\
    Seq.mem h (MH.major_objects mh) /\
    chunked_is_blue mh h /\
    j < chunked_wosize_nat_of_object mh h /\
    chunked_update_field_slot h j == Some field_addr /\
    MH.read_word_in_major mh field_addr == Some old)
      (ensures
    (let mh' = chunked_update_all_objects_aux mh objs fwd idx in
    MH.well_formed_major_heap mh' /\
    MH.major_objects mh' == MH.major_objects mh /\
    MH.read_word_in_major mh' field_addr == Some old))
      (decreases (Seq.length objs - idx))
  =
  if idx >= Seq.length objs then
    ()
  else begin
    let obj = Seq.index objs idx in
    assert (Seq.mem obj (MH.major_objects mh));
    assert (chunked_objects_members mh objs (idx + 1));
    if chunked_is_blue mh obj then begin
      chunked_update_all_objects_aux_preserves_blue_field
    mh objs fwd (idx + 1) h j field_addr old
    end else if chunked_is_no_scan mh obj then begin
      chunked_update_all_objects_aux_preserves_blue_field
    mh objs fwd (idx + 1) h j field_addr old
    end else begin
      if obj = h then
    assert False;
      let wz = chunked_wosize_nat_of_object mh obj in
      let disjoint (k: nat) (field_addr': hp_addr)
    : Lemma
        (requires
          0 <= k /\ k < wz /\
          chunked_update_field_slot obj k == Some field_addr')
        (ensures chunked_words_disjoint field_addr' field_addr)
    = chunked_update_field_slots_disjoint_distinct
        mh obj k field_addr' h j field_addr
      in
      FStar.Classical.forall_intro
    (fun k -> FStar.Classical.forall_intro
      (FStar.Classical.move_requires (disjoint k)));
      assert (forall (k: nat) (field_addr': hp_addr).
    0 <= k /\ k < wz /\
    chunked_update_field_slot obj k == Some field_addr' ==>
    chunked_words_disjoint field_addr' field_addr);
      chunked_update_object_pointers_preserves_wf_and_major_objects
    mh obj wz fwd 0;
      chunked_update_object_pointers_preserves_read_disjoint
    mh obj wz fwd 0 field_addr old;
      let mh1 = chunked_update_object_pointers mh obj wz fwd 0 in
      assert (MH.well_formed_major_heap mh1);
      assert (MH.major_objects mh1 == MH.major_objects mh);
      assert (Seq.mem h (MH.major_objects mh1));
      assert (MH.read_word_in_major mh1 field_addr == Some old);
      match MH.read_word_in_major mh (hd_address h) with
      | None -> assert False
      | Some hhdr ->
    chunked_update_object_pointers_preserves_header_read
      mh obj wz fwd 0 h hhdr;
    assert (MH.read_word_in_major mh1 (hd_address h) == Some hhdr);
    assert (chunked_header_of_object mh1 h == chunked_header_of_object mh h);
    assert (chunked_is_blue mh1 h == chunked_is_blue mh h);
    assert (chunked_is_blue mh1 h);
    assert (chunked_wosize_nat_of_object mh1 h ==
            chunked_wosize_nat_of_object mh h);
    assert (j < chunked_wosize_nat_of_object mh1 h);
    chunked_objects_members_transfer mh mh1 objs (idx + 1);
    chunked_update_all_objects_aux_preserves_blue_field
      mh1 objs fwd (idx + 1) h j field_addr old;
    assert (MH.major_objects
              (chunked_update_all_objects_aux mh1 objs fwd (idx + 1)) ==
            MH.major_objects mh1);
    assert (MH.read_word_in_major
              (chunked_update_all_objects_aux mh1 objs fwd (idx + 1))
              field_addr == Some old)
    end
  end

let chunked_update_major_pointers_preserves_blue_field
  (mh: MH.major_heap) (fwd: forwarding_map) (h: obj_addr) (j: nat)
  (field_addr: hp_addr) (old: U64.t)
  : Lemma
      (requires
    MH.well_formed_major_heap mh /\
    Seq.mem h (MH.major_objects mh) /\
    chunked_is_blue mh h /\
    j < chunked_wosize_nat_of_object mh h /\
    chunked_update_field_slot h j == Some field_addr /\
    MH.read_word_in_major mh field_addr == Some old)
      (ensures
    MH.read_word_in_major
      (chunked_update_major_pointers mh fwd) field_addr == Some old)
  =
  chunked_major_objects_members mh;
  chunked_update_all_objects_aux_preserves_blue_field
    mh (MH.major_objects mh) fwd 0 h j field_addr old
#pop-options

let chunked_is_blue_single_chunk_compat (g: heap) (obj: obj_addr)
  : Lemma
      (requires obj_in_single_chunk_range obj)
      (ensures
        chunked_is_blue (MH.single_chunk_major_heap g) obj ==
        is_blue obj g)
  = hd_address_bounds obj;
    hd_address_spec obj;
    assert (U64.v mword == 8);
    assert (U64.v (hd_address obj) >= U64.v zero_addr);
    MH.single_chunk_read_word_compat g (hd_address obj);
    color_of_object_spec obj g;
    is_blue_iff obj g

let chunked_is_no_scan_single_chunk_compat (g: heap) (obj: obj_addr)
  : Lemma
      (requires obj_in_single_chunk_range obj)
      (ensures
        chunked_is_no_scan (MH.single_chunk_major_heap g) obj ==
        is_no_scan obj g)
  = hd_address_bounds obj;
    hd_address_spec obj;
    assert (U64.v mword == 8);
    assert (U64.v (hd_address obj) >= U64.v zero_addr);
    MH.single_chunk_read_word_compat g (hd_address obj);
    tag_of_object_spec obj g;
    is_no_scan_spec obj g

let chunked_wosize_nat_single_chunk_compat (g: heap) (obj: obj_addr)
  : Lemma
      (requires obj_in_single_chunk_range obj)
      (ensures
        chunked_wosize_nat_of_object (MH.single_chunk_major_heap g) obj ==
        U64.v (wosize_of_object obj g))
  = hd_address_bounds obj;
    hd_address_spec obj;
    assert (U64.v mword == 8);
    assert (U64.v (hd_address obj) >= U64.v zero_addr);
    MH.single_chunk_read_word_compat g (hd_address obj);
    wosize_of_object_spec obj g

let chunked_update_field_single_chunk_compat
  (g: heap)
  (field_addr: hp_addr)
  (fwd: forwarding_map)
  : Lemma
      (requires U64.v field_addr >= U64.v zero_addr /\
                U64.v field_addr + U64.v mword <= heap_size)
      (ensures
        chunked_update_field (MH.single_chunk_major_heap g) field_addr fwd ==
        MH.single_chunk_major_heap
          (let field_val = to_minor_offset (read_word g field_addr) in
           if is_minor_pointer field_val then
             let new_val = fwd field_val in
             if new_val <> 0UL then write_word g field_addr new_val else g
           else g))
  = MH.single_chunk_read_word_compat g field_addr;
    let field_val = to_minor_offset (read_word g field_addr) in
    if is_minor_pointer field_val then begin
      let new_val = fwd field_val in
      if new_val <> 0UL then
        SpecMajorAlloc.major_write_word_or_same_single_chunk_compat
          g field_addr new_val
    end

let rec chunked_update_object_pointers_single_chunk_compat
  (g: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map) (i: nat)
  : Lemma
      (requires obj_in_single_chunk_range obj)
      (ensures
        chunked_update_object_pointers
          (MH.single_chunk_major_heap g) obj wosize fwd i ==
        MH.single_chunk_major_heap
          (update_object_pointers g obj wosize fwd i))
      (decreases (wosize - i))
  = if i >= wosize then ()
    else begin
      let field_offset = U64.v obj + i * 8 in
      if field_offset + 8 > heap_size || field_offset % 8 <> 0 then begin
        assert (chunked_update_field_slot obj i == None)
      end else begin
        let field_addr : hp_addr = U64.uint_to_t field_offset in
        assert (U64.v field_addr == field_offset);
        assert (U64.v field_addr >= U64.v zero_addr);
        assert (chunked_update_field_slot obj i == Some field_addr);
        chunked_update_field_single_chunk_compat g field_addr fwd;
        let field_val = to_minor_offset (read_word g field_addr) in
        if is_minor_pointer field_val then begin
          let new_val = fwd field_val in
          if new_val <> 0UL then
            chunked_update_object_pointers_single_chunk_compat
              (write_word g field_addr new_val) obj wosize fwd (i + 1)
          else
            chunked_update_object_pointers_single_chunk_compat
              g obj wosize fwd (i + 1)
        end else
          chunked_update_object_pointers_single_chunk_compat
            g obj wosize fwd (i + 1)
      end
    end

let rec chunked_update_all_objects_aux_single_chunk_compat
  (g: heap) (objs: seq obj_addr) (fwd: forwarding_map) (idx: nat)
  : Lemma
      (requires objects_in_single_chunk_range objs idx)
      (ensures
        chunked_update_all_objects_aux
          (MH.single_chunk_major_heap g) objs fwd idx ==
        MH.single_chunk_major_heap
          (update_all_objects_aux g objs fwd idx))
      (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      let obj = Seq.index objs idx in
      assert (obj_in_single_chunk_range obj);
      assert (objects_in_single_chunk_range objs (idx + 1));
      chunked_is_blue_single_chunk_compat g obj;
      if is_blue obj g then
        chunked_update_all_objects_aux_single_chunk_compat
          g objs fwd (idx + 1)
      else begin
        chunked_is_no_scan_single_chunk_compat g obj;
        if is_no_scan obj g then
          chunked_update_all_objects_aux_single_chunk_compat
            g objs fwd (idx + 1)
        else begin
          chunked_wosize_nat_single_chunk_compat g obj;
          let wz = U64.v (wosize_of_object obj g) in
          chunked_update_object_pointers_single_chunk_compat
            g obj wz fwd 0;
          let g' = update_object_pointers g obj wz fwd 0 in
          chunked_update_all_objects_aux_single_chunk_compat
            g' objs fwd (idx + 1)
        end
      end
    end

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let objects_zero_addr_index_in_single_chunk_range (g: heap)
                                                    (k: nat{k < Seq.length (objects zero_addr g)})
  : Lemma
      (ensures obj_in_single_chunk_range (Seq.index (objects zero_addr g) k))
  =
    let obj = Seq.index (objects zero_addr g) k in
    FStar.Seq.Properties.lemma_index_is_nth (objects zero_addr g) k;
    assert (Seq.mem obj (objects zero_addr g));
    objects_addresses_gt_start zero_addr g obj;
    assert (U64.v obj > U64.v zero_addr);
    assert (U64.v obj % U64.v mword == 0);
    assert (U64.v zero_addr % U64.v mword == 0);
    MH.word_aligned_gt_at_least_mword (U64.v obj) (U64.v zero_addr);
    assert (U64.v obj >= U64.v zero_addr + U64.v mword)
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let rec objects_zero_addr_in_single_chunk_range_from (g: heap) (idx: nat)
  : Lemma
      (requires idx <= Seq.length (objects zero_addr g))
      (ensures objects_in_single_chunk_range (objects zero_addr g) idx)
      (decreases (Seq.length (objects zero_addr g) - idx))
  = if idx >= Seq.length (objects zero_addr g) then ()
    else begin
      let kk : k':nat{k' < Seq.length (objects zero_addr g)} = idx in
      objects_zero_addr_index_in_single_chunk_range g kk;
      objects_zero_addr_in_single_chunk_range_from g (idx + 1)
    end
#pop-options

let objects_zero_addr_in_single_chunk_range (g: heap)
  : Lemma
      (ensures objects_in_single_chunk_range (objects zero_addr g) 0)
  = objects_zero_addr_in_single_chunk_range_from g 0

let chunked_update_major_pointers_single_chunk_compat
  (g: heap) (fwd: forwarding_map)
  : Lemma
      (ensures
        chunked_update_major_pointers (MH.single_chunk_major_heap g) fwd ==
        MH.single_chunk_major_heap (update_major_pointers g fwd))
  = MH.single_chunk_major_objects_compat g;
    objects_zero_addr_in_single_chunk_range g;
    chunked_update_all_objects_aux_single_chunk_compat
      g (objects zero_addr g) fwd 0
