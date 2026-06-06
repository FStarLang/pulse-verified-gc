/// ---------------------------------------------------------------------------
/// GC.Gen.ChunkedPromote -- Chunked-major promotion specification
/// ---------------------------------------------------------------------------

module GC.Gen.ChunkedPromote

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Lib.Header
open GC.Gen.MinorHeap

module MH = GC.Spec.MajorHeap
module SpecAlloc = GC.Spec.Allocator
module SpecMajorAlloc = GC.Spec.MajorAllocator
module Promote = GC.Gen.Promote
module WriteBody = GC.Gen.WriteBodyLemmas

let rec chunked_copy_fields
  (minor: minor_state) (mh: MH.major_heap)
  (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  : GTot MH.major_heap
    (decreases (n - i))
  =
  if i >= n then mh
  else
    let field_val = minor_read_field minor src_obj i in
    let dst_offset = U64.v dst_obj + i * U64.v mword in
    if dst_offset + U64.v mword > heap_size ||
       dst_offset % U64.v mword <> 0 then
      mh
    else
      let mh' =
        SpecMajorAlloc.major_write_word_or_same
          mh (U64.uint_to_t dst_offset) field_val in
      chunked_copy_fields minor mh' src_obj dst_obj (i + 1) n

let chunked_copy_fields_base
  (minor: minor_state) (mh: MH.major_heap)
  (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  : Lemma (requires i >= n)
          (ensures chunked_copy_fields minor mh src_obj dst_obj i n == mh)
  = ()

let chunked_copy_fields_step
  (minor: minor_state) (mh: MH.major_heap)
  (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  : Lemma
      (requires i < n /\
                U64.v dst_obj + i * U64.v mword + U64.v mword <= heap_size /\
                (U64.v dst_obj + i * U64.v mword) % U64.v mword == 0)
      (ensures
        chunked_copy_fields minor mh src_obj dst_obj i n ==
        chunked_copy_fields minor
          (SpecMajorAlloc.major_write_word_or_same mh
            (U64.uint_to_t (U64.v dst_obj + i * U64.v mword))
            (minor_read_field minor src_obj i))
          src_obj dst_obj (i + 1) n)
  = ()

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
private let rec write_word_in_major_read_frame
  (mh: MH.major_heap) (write_addr target: hp_addr)
  (value old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh target == Some old /\
        (U64.v target + U64.v mword <= U64.v write_addr \/
         U64.v write_addr + U64.v mword <= U64.v target))
      (ensures
        (match MH.write_word_in_major mh write_addr value with
         | None -> True
         | Some mh' -> MH.read_word_in_major mh' target == Some old))
      (decreases Seq.length mh)
  =
  if Seq.length mh = 0 then
    assert False
  else begin
    let c = Seq.head mh in
    let tl = Seq.tail mh in
    assert (Seq.index mh 0 == c);
    assert (Seq.equal mh (Seq.cons c tl));
    Seq.lemma_eq_elim mh (Seq.cons c tl);
    if MH.word_in_chunk c write_addr then begin
      let c' = MH.write_word_in_chunk c write_addr value in
      assert (MH.write_word_in_major mh write_addr value ==
              Some (Seq.cons c' tl));
      MH.write_word_in_chunk_preserves_range c write_addr value;
      if MH.chunk_contains_addr c target then begin
        assert (MH.lookup_chunk mh target == Some c);
        assert (MH.read_word_in_major mh target ==
                (if MH.word_in_chunk c target
                 then Some (MH.read_word_in_chunk c target)
                 else None));
        assert (MH.word_in_chunk c target);
        assert (MH.read_word_in_chunk c target == old);
        MH.write_word_in_chunk_preserves_word c write_addr value target;
        assert (MH.word_in_chunk c' target);
        if write_addr = target then begin
          assert (U64.v write_addr == U64.v target);
          assert False
        end;
        MH.read_write_in_chunk_different c write_addr target value;
        assert (MH.read_word_in_chunk c' target == old);
        assert (MH.lookup_chunk (Seq.cons c' tl) target == Some c');
        assert (MH.read_word_in_major (Seq.cons c' tl) target == Some old)
      end else begin
        assert (~(MH.chunk_contains_addr c' target));
        MH.read_word_add_chunk_miss tl c target;
        assert (MH.read_word_in_major tl target == Some old);
        MH.read_word_add_chunk_miss tl c' target;
        assert (MH.read_word_in_major (Seq.cons c' tl) target ==
                MH.read_word_in_major tl target)
      end
    end else begin
      assert (MH.write_word_in_major mh write_addr value ==
              (match MH.write_word_in_major tl write_addr value with
               | None -> None
               | Some tl' -> Some (Seq.cons c tl')));
      match MH.write_word_in_major tl write_addr value with
      | None -> ()
      | Some tl' ->
        if MH.chunk_contains_addr c target then begin
          assert (MH.lookup_chunk mh target == Some c);
          assert (MH.read_word_in_major mh target ==
                  (if MH.word_in_chunk c target
                   then Some (MH.read_word_in_chunk c target)
                   else None));
          assert (MH.word_in_chunk c target);
          assert (MH.read_word_in_chunk c target == old);
          assert (MH.read_word_in_major (Seq.cons c tl') target == Some old)
        end else begin
          MH.read_word_add_chunk_miss tl c target;
          assert (MH.read_word_in_major tl target == Some old);
          write_word_in_major_read_frame tl write_addr target value old;
          assert (MH.read_word_in_major tl' target == Some old);
          MH.read_word_add_chunk_miss tl' c target;
          assert (MH.read_word_in_major (Seq.cons c tl') target == Some old)
        end
    end
  end

let major_write_word_or_same_read_frame
  (mh: MH.major_heap) (write_addr target: hp_addr)
  (value old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh target == Some old /\
        (U64.v target + U64.v mword <= U64.v write_addr \/
         U64.v write_addr + U64.v mword <= U64.v target))
      (ensures
        MH.read_word_in_major
          (SpecMajorAlloc.major_write_word_or_same mh write_addr value)
          target == Some old)
  =
  write_word_in_major_read_frame mh write_addr target value old;
  match MH.write_word_in_major mh write_addr value with
  | None -> SpecMajorAlloc.major_write_word_or_same_none mh write_addr value
  | Some mh' ->
    SpecMajorAlloc.major_write_word_or_same_some mh mh' write_addr value

let major_write_word_or_same_read_same
  (mh: MH.major_heap) (write_addr: hp_addr) (value: U64.t)
  (idx: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        MH.lookup_chunk_index mh write_addr == Some idx /\
        MH.word_in_chunk (Seq.index mh idx) write_addr)
      (ensures
        MH.read_word_in_major
          (SpecMajorAlloc.major_write_word_or_same mh write_addr value)
          write_addr == Some value)
  =
  let c = Seq.index mh idx in
  MH.write_word_in_major_at_lookup_index mh write_addr value idx;
  MH.write_word_at_index_preserves_wf mh write_addr value idx;
  let c' = MH.write_word_in_chunk c write_addr value in
  assert (MH.write_word_in_major mh write_addr value ==
          Some (Seq.upd mh idx c'));
  SpecMajorAlloc.major_write_word_or_same_some
    mh (Seq.upd mh idx c') write_addr value;
  MH.read_write_in_chunk_same c write_addr value;
  assert (MH.read_word_in_chunk c' write_addr == value);
  MH.write_word_in_chunk_preserves_word c write_addr value write_addr;
  assert (MH.word_in_chunk c' write_addr);
  MH.lookup_chunk_index_word_in_chunk (Seq.upd mh idx c') write_addr idx;
  assert (MH.lookup_chunk_index (Seq.upd mh idx c') write_addr == Some idx);
  MH.read_word_in_major_at_lookup_index (Seq.upd mh idx c') write_addr idx;
  assert (MH.read_word_in_major (Seq.upd mh idx c') write_addr == Some value)

let rec chunked_copy_fields_frame_before
  (minor: minor_state) (mh: MH.major_heap)
  (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  (target: hp_addr) (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh target == Some old /\
        U64.v target + U64.v mword <=
          U64.v dst_obj + i * U64.v mword)
      (ensures
        MH.read_word_in_major
          (chunked_copy_fields minor mh src_obj dst_obj i n)
          target == Some old)
      (decreases (n - i))
  =
  if i >= n then
    chunked_copy_fields_base minor mh src_obj dst_obj i n
  else begin
    let dst_offset = U64.v dst_obj + i * U64.v mword in
    if dst_offset + U64.v mword > heap_size ||
       dst_offset % U64.v mword <> 0 then
      ()
    else begin
      assert (dst_offset < heap_size);
      let write_addr : hp_addr = U64.uint_to_t dst_offset in
      assert (U64.v write_addr == dst_offset);
      let mh' =
        SpecMajorAlloc.major_write_word_or_same
          mh write_addr (minor_read_field minor src_obj i) in
      major_write_word_or_same_read_frame
        mh write_addr target (minor_read_field minor src_obj i) old;
      chunked_copy_fields_step minor mh src_obj dst_obj i n;
      assert (MH.read_word_in_major mh' target == Some old);
      assert (U64.v target + U64.v mword <=
              U64.v dst_obj + (i + 1) * U64.v mword);
      chunked_copy_fields_frame_before
        minor mh' src_obj dst_obj (i + 1) n target old
    end
  end

let rec chunked_copy_fields_frame_after
  (minor: minor_state) (mh: MH.major_heap)
  (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  (target: hp_addr) (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh target == Some old /\
        U64.v dst_obj + n * U64.v mword <= U64.v target)
      (ensures
        MH.read_word_in_major
          (chunked_copy_fields minor mh src_obj dst_obj i n)
          target == Some old)
      (decreases (n - i))
  =
  if i >= n then
    chunked_copy_fields_base minor mh src_obj dst_obj i n
  else begin
    let dst_offset = U64.v dst_obj + i * U64.v mword in
    if dst_offset + U64.v mword > heap_size ||
       dst_offset % U64.v mword <> 0 then
      ()
    else begin
      assert (dst_offset < heap_size);
      let write_addr : hp_addr = U64.uint_to_t dst_offset in
      assert (U64.v write_addr == dst_offset);
      assert (i + 1 <= n);
      assert (U64.v write_addr + U64.v mword ==
              U64.v dst_obj + (i + 1) * U64.v mword);
      assert (U64.v write_addr + U64.v mword <=
              U64.v dst_obj + n * U64.v mword);
      assert (U64.v write_addr + U64.v mword <= U64.v target);
      let mh' =
        SpecMajorAlloc.major_write_word_or_same
          mh write_addr (minor_read_field minor src_obj i) in
      major_write_word_or_same_read_frame
        mh write_addr target (minor_read_field minor src_obj i) old;
      chunked_copy_fields_step minor mh src_obj dst_obj i n;
      assert (MH.read_word_in_major mh' target == Some old);
      chunked_copy_fields_frame_after
        minor mh' src_obj dst_obj (i + 1) n target old
    end
  end

let rec chunked_copy_fields_field_effect
  (minor: minor_state) (mh: MH.major_heap)
  (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat) (j: nat)
  (idx: nat) (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        U64.v dst_obj >= U64.v mword /\
        U64.v dst_obj < heap_size /\
        U64.v dst_obj % U64.v mword == 0 /\
        i <= j /\ j < n /\
        idx < Seq.length mh /\
        MH.lookup_chunk_index mh (hd_address (dst_obj <: obj_addr)) == Some idx /\
        Seq.mem (dst_obj <: obj_addr) (MH.major_objects mh) /\
        MH.read_word_in_major mh (hd_address (dst_obj <: obj_addr)) ==
          Some hdr /\
        n <= U64.v (getWosize hdr))
      (ensures
        (let result = chunked_copy_fields minor mh src_obj dst_obj i n in
         let addr_nat = U64.v dst_obj + j * U64.v mword in
         addr_nat + U64.v mword <= heap_size /\
         addr_nat % U64.v mword == 0 /\
         MH.read_word_in_major result (U64.uint_to_t addr_nat) ==
           Some (minor_read_field minor src_obj j)))
      (decreases n - i)
  =
  let dst : obj_addr = dst_obj in
  let hd = hd_address dst in
  assert (i < n);
  let c = Seq.index mh idx in
  MH.lookup_chunk_index_some mh hd idx;
  assert (MH.chunk_contains_addr c hd);
  MH.read_word_in_major_at_lookup_index mh hd idx;
  assert (MH.word_in_chunk c hd);
  assert (MH.read_word_in_chunk c hd == hdr);
  MH.major_objects_member_in_lookup_chunk mh idx dst;
  assert (Seq.mem dst (MH.objects_in_chunk c));
  MH.objects_in_chunk_member_header_fits c dst;
  assert (MH.object_header_size_fits_in_chunk c dst);
  assert (MH.object_wosize_in_chunk c dst == U64.v (getWosize hdr));
  let dst_offset = U64.v dst_obj + i * U64.v mword in
  assert (U64.v mword == 8);
  SpecMajorAlloc.aligned_plus_word_product (U64.v dst_obj) i;
  assert (dst_offset % U64.v mword == 0);
  assert (i + 1 <= n);
  FStar.Math.Lemmas.lemma_mult_le_right
    (U64.v mword) (i + 1) n;
  FStar.Math.Lemmas.distributivity_add_left i 1 (U64.v mword);
  assert (i * U64.v mword + U64.v mword ==
          (i + 1) * U64.v mword);
  FStar.Math.Lemmas.paren_add_right
    (U64.v dst_obj) (i * U64.v mword) (U64.v mword);
  assert (dst_offset + U64.v mword ==
          U64.v dst_obj + (i + 1) * U64.v mword);
  assert (dst_offset + U64.v mword <= U64.v dst_obj + n * U64.v mword);
  assert (dst_offset + U64.v mword <=
          U64.v dst_obj + U64.v (getWosize hdr) * U64.v mword);
  hd_address_spec dst;
  assert (U64.v hd + U64.v mword == U64.v dst_obj);
  FStar.Math.Lemmas.distributivity_add_left
    1 (U64.v (getWosize hdr)) (U64.v mword);
  assert ((1 + U64.v (getWosize hdr)) * U64.v mword ==
          U64.v mword + U64.v (getWosize hdr) * U64.v mword);
  FStar.Math.Lemmas.paren_add_right
    (U64.v hd) (U64.v mword)
    (U64.v (getWosize hdr) * U64.v mword);
  assert (U64.v dst_obj + U64.v (getWosize hdr) * U64.v mword ==
          U64.v hd + (1 + U64.v (getWosize hdr)) * U64.v mword);
  assert (dst_offset + U64.v mword <= MH.chunk_end c);
  assert (dst_offset < heap_size);
  let write_addr : hp_addr = U64.uint_to_t dst_offset in
  assert (U64.v write_addr == dst_offset);
  assert (MH.word_in_chunk c write_addr);
  MH.lookup_chunk_index_word_in_chunk mh write_addr idx;
  assert (MH.lookup_chunk_index mh write_addr == Some idx);
  let value = minor_read_field minor src_obj i in
  MH.major_objects_write_member_payload_preserves
    mh idx dst write_addr value;
  MH.write_word_in_major_at_lookup_index mh write_addr value idx;
  let c' = MH.write_word_in_chunk c write_addr value in
  assert (MH.write_word_in_major mh write_addr value ==
          Some (Seq.upd mh idx c'));
  SpecMajorAlloc.major_write_word_or_same_some
    mh (Seq.upd mh idx c') write_addr value;
  let mh' = SpecMajorAlloc.major_write_word_or_same mh write_addr value in
  assert (mh' == Seq.upd mh idx c');
  assert (MH.major_objects mh' == MH.major_objects mh);
  MH.write_word_at_index_preserves_wf mh write_addr value idx;
  assert (MH.well_formed_major_heap mh');
  major_write_word_or_same_read_frame mh write_addr hd value hdr;
  assert (MH.read_word_in_major mh' hd == Some hdr);
  MH.write_word_in_chunk_preserves_word c write_addr value hd;
  assert (MH.word_in_chunk c' hd);
  MH.lookup_chunk_index_word_in_chunk mh' hd idx;
  assert (idx < Seq.length mh');
  assert (Seq.mem dst (MH.major_objects mh'));
  let target_nat = U64.v dst_obj + j * U64.v mword in
  SpecMajorAlloc.aligned_plus_word_product (U64.v dst_obj) j;
  assert (target_nat % U64.v mword == 0);
  FStar.Math.Lemmas.lemma_mult_le_right
    (U64.v mword) (j + 1) n;
  FStar.Math.Lemmas.distributivity_add_left j 1 (U64.v mword);
  assert (j * U64.v mword + U64.v mword ==
          (j + 1) * U64.v mword);
  FStar.Math.Lemmas.paren_add_right
    (U64.v dst_obj) (j * U64.v mword) (U64.v mword);
  assert (target_nat + U64.v mword ==
          U64.v dst_obj + (j + 1) * U64.v mword);
  assert (target_nat + U64.v mword <= U64.v dst_obj + n * U64.v mword);
  FStar.Math.Lemmas.lemma_mult_le_right
    (U64.v mword) n (U64.v (getWosize hdr));
  assert (n * U64.v mword <= U64.v (getWosize hdr) * U64.v mword);
  assert (target_nat + U64.v mword <=
          U64.v dst_obj + U64.v (getWosize hdr) * U64.v mword);
  assert (target_nat + U64.v mword <= MH.chunk_end c);
  assert (target_nat < heap_size);
  let target_addr : hp_addr = U64.uint_to_t target_nat in
  assert (U64.v target_addr == target_nat);
  MH.major_object_payload_word_in_lookup_chunk mh idx dst target_addr;
  assert (MH.word_in_chunk c target_addr);
  assert (MH.lookup_chunk_index mh target_addr == Some idx);
  MH.read_word_in_major_at_lookup_index mh target_addr idx;
  let old = MH.read_word_in_chunk c target_addr in
  assert (MH.read_word_in_major mh target_addr == Some old);
  chunked_copy_fields_step minor mh src_obj dst_obj i n;
  assert (chunked_copy_fields minor mh src_obj dst_obj i n ==
          chunked_copy_fields minor mh' src_obj dst_obj (i + 1) n);
  if j = i then begin
    assert (target_nat == dst_offset);
    assert (target_addr == write_addr);
    major_write_word_or_same_read_same mh write_addr value idx;
    assert (MH.read_word_in_major mh' target_addr == Some value);
    assert (U64.v target_addr + U64.v mword <=
            U64.v dst_obj + (i + 1) * U64.v mword);
    chunked_copy_fields_frame_before
      minor mh' src_obj dst_obj (i + 1) n target_addr value;
    assert (value == minor_read_field minor src_obj j)
  end else begin
    assert (i < j);
    FStar.Math.Lemmas.lemma_mult_le_right
      (U64.v mword) (i + 1) j;
    assert (dst_offset + U64.v mword <= target_nat);
    major_write_word_or_same_read_frame
      mh write_addr target_addr value old;
    assert (MH.read_word_in_major mh' target_addr == Some old);
    assert (i + 1 <= j);
    chunked_copy_fields_field_effect
      minor mh' src_obj dst_obj (i + 1) n j idx hdr
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
let rec chunked_copy_fields_preserves_major_objects
  (minor: minor_state) (mh: MH.major_heap)
  (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  (idx: nat) (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        U64.v dst_obj >= U64.v mword /\
        U64.v dst_obj < heap_size /\
        U64.v dst_obj % U64.v mword == 0 /\
        i <= n /\
        idx < Seq.length mh /\
        MH.lookup_chunk_index mh (hd_address (dst_obj <: obj_addr)) == Some idx /\
        Seq.mem (dst_obj <: obj_addr) (MH.major_objects mh) /\
        MH.read_word_in_major mh (hd_address (dst_obj <: obj_addr)) ==
          Some hdr /\
        n <= U64.v (getWosize hdr))
      (ensures
        (let mh' = chunked_copy_fields minor mh src_obj dst_obj i n in
         MH.well_formed_major_heap mh' /\
         MH.major_objects mh' == MH.major_objects mh /\
         MH.read_word_in_major mh' (hd_address (dst_obj <: obj_addr)) ==
           Some hdr))
      (decreases n - i)
  =
  let dst : obj_addr = dst_obj in
  let hd = hd_address dst in
  if i >= n then
    chunked_copy_fields_base minor mh src_obj dst_obj i n
  else begin
    assert (i < n);
    let c = Seq.index mh idx in
    MH.lookup_chunk_index_some mh hd idx;
    assert (MH.chunk_contains_addr c hd);
    MH.read_word_in_major_at_lookup_index mh hd idx;
    assert (MH.word_in_chunk c hd);
    assert (MH.read_word_in_chunk c hd == hdr);
    MH.major_objects_member_in_lookup_chunk mh idx dst;
    assert (Seq.mem dst (MH.objects_in_chunk c));
    MH.objects_in_chunk_member_header_fits c dst;
    assert (MH.object_header_size_fits_in_chunk c dst);
    assert (MH.object_wosize_in_chunk c dst == U64.v (getWosize hdr));
    let dst_offset = U64.v dst_obj + i * U64.v mword in
    assert (U64.v mword == 8);
    SpecMajorAlloc.aligned_plus_word_product (U64.v dst_obj) i;
    assert (dst_offset % U64.v mword == 0);
    assert (i + 1 <= n);
    FStar.Math.Lemmas.lemma_mult_le_right
      (U64.v mword) (i + 1) n;
    FStar.Math.Lemmas.distributivity_add_left i 1 (U64.v mword);
    assert (i * U64.v mword + U64.v mword ==
            (i + 1) * U64.v mword);
    FStar.Math.Lemmas.paren_add_right
      (U64.v dst_obj) (i * U64.v mword) (U64.v mword);
    assert (dst_offset + U64.v mword ==
            U64.v dst_obj + (i + 1) * U64.v mword);
    assert (dst_offset + U64.v mword <= U64.v dst_obj + n * U64.v mword);
    assert (dst_offset + U64.v mword <=
            U64.v dst_obj + U64.v (getWosize hdr) * U64.v mword);
    hd_address_spec dst;
    assert (U64.v hd + U64.v mword == U64.v dst_obj);
    FStar.Math.Lemmas.distributivity_add_left
      1 (U64.v (getWosize hdr)) (U64.v mword);
    assert ((1 + U64.v (getWosize hdr)) * U64.v mword ==
            U64.v mword + U64.v (getWosize hdr) * U64.v mword);
    FStar.Math.Lemmas.paren_add_right
      (U64.v hd) (U64.v mword)
      (U64.v (getWosize hdr) * U64.v mword);
    assert (U64.v dst_obj + U64.v (getWosize hdr) * U64.v mword ==
            U64.v hd + (1 + U64.v (getWosize hdr)) * U64.v mword);
    assert (dst_offset + U64.v mword <= MH.chunk_end c);
    assert (dst_offset < heap_size);
    let write_addr : hp_addr = U64.uint_to_t dst_offset in
    assert (U64.v write_addr == dst_offset);
    assert (MH.word_in_chunk c write_addr);
    MH.lookup_chunk_index_word_in_chunk mh write_addr idx;
    assert (MH.lookup_chunk_index mh write_addr == Some idx);
    let value = minor_read_field minor src_obj i in
    MH.major_objects_write_member_payload_preserves
      mh idx dst write_addr value;
    MH.write_word_in_major_at_lookup_index mh write_addr value idx;
    let c' = MH.write_word_in_chunk c write_addr value in
    assert (MH.write_word_in_major mh write_addr value ==
            Some (Seq.upd mh idx c'));
    SpecMajorAlloc.major_write_word_or_same_some
      mh (Seq.upd mh idx c') write_addr value;
    let mh' = SpecMajorAlloc.major_write_word_or_same mh write_addr value in
    assert (mh' == Seq.upd mh idx c');
    assert (MH.major_objects mh' == MH.major_objects mh);
    MH.write_word_at_index_preserves_wf mh write_addr value idx;
    assert (MH.well_formed_major_heap mh');
    major_write_word_or_same_read_frame mh write_addr hd value hdr;
    assert (MH.read_word_in_major mh' hd == Some hdr);
    MH.write_word_in_chunk_preserves_word c write_addr value hd;
    assert (MH.word_in_chunk c' hd);
    MH.lookup_chunk_index_word_in_chunk mh' hd idx;
    assert (idx < Seq.length mh');
    assert (Seq.mem dst (MH.major_objects mh'));
    chunked_copy_fields_step minor mh src_obj dst_obj i n;
    assert (chunked_copy_fields minor mh src_obj dst_obj i n ==
            chunked_copy_fields minor mh' src_obj dst_obj (i + 1) n);
    chunked_copy_fields_preserves_major_objects
      minor mh' src_obj dst_obj (i + 1) n idx hdr;
    assert (MH.major_objects
              (chunked_copy_fields minor mh' src_obj dst_obj (i + 1) n) ==
            MH.major_objects mh')
  end
#pop-options

let chunked_set_promoted_tag (mh: MH.major_heap) (obj: U64.t) (tag: nat)
  : GTot MH.major_heap =
  if tag >= 256 then mh
  else if U64.v obj >= U64.v mword &&
          U64.v obj < heap_size &&
          U64.v obj % U64.v mword = 0 then
    let dst : obj_addr = obj in
    let hd = hd_address dst in
    match MH.read_word_in_major mh hd with
    | None -> mh
    | Some hdr ->
      let new_hdr = makeHeader (getWosize hdr) White (U64.uint_to_t tag) in
      SpecMajorAlloc.major_write_word_or_same mh hd new_hdr
  else mh

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_set_promoted_tag_read_frame
  (mh: MH.major_heap) (obj: U64.t) (tag: nat)
  (target: hp_addr) (old: U64.t)
  : Lemma
      (requires
        U64.v obj >= U64.v mword /\
        U64.v obj < heap_size /\
        U64.v obj % U64.v mword == 0 /\
        MH.read_word_in_major mh target == Some old /\
        (let dst : obj_addr = obj in
         U64.v target + U64.v mword <= U64.v (hd_address dst) \/
         U64.v (hd_address dst) + U64.v mword <= U64.v target))
      (ensures
        MH.read_word_in_major
          (chunked_set_promoted_tag mh obj tag)
          target == Some old)
  =
  let dst : obj_addr = obj in
  let hd = hd_address dst in
  if tag >= 256 then ()
  else begin
    match MH.read_word_in_major mh hd with
    | None -> ()
    | Some hdr ->
      let new_hdr = makeHeader (getWosize hdr) White (U64.uint_to_t tag) in
      major_write_word_or_same_read_frame mh hd target new_hdr old
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_set_promoted_tag_preserves_major_objects
  (mh: MH.major_heap) (obj: U64.t) (tag: nat)
  (idx: nat) (hdr: U64.t)
  : Lemma
      (requires
        tag < 256 /\
        MH.well_formed_major_heap mh /\
        U64.v obj >= U64.v mword /\
        U64.v obj < heap_size /\
        U64.v obj % U64.v mword == 0 /\
        idx < Seq.length mh /\
        MH.lookup_chunk_index mh (hd_address (obj <: obj_addr)) == Some idx /\
        Seq.mem (obj <: obj_addr) (MH.major_objects mh) /\
        MH.read_word_in_major mh (hd_address (obj <: obj_addr)) == Some hdr)
      (ensures
        (let mh' = chunked_set_promoted_tag mh obj tag in
         MH.well_formed_major_heap mh' /\
         MH.major_objects mh' == MH.major_objects mh))
  =
  let dst : obj_addr = obj in
  let hd = hd_address dst in
  let c = Seq.index mh idx in
  MH.lookup_chunk_index_some mh hd idx;
  assert (MH.chunk_contains_addr c hd);
  MH.read_word_in_major_at_lookup_index mh hd idx;
  assert (MH.word_in_chunk c hd);
  assert (MH.read_word_in_chunk c hd == hdr);
  assert (MH.object_wosize_in_chunk c dst == U64.v (getWosize hdr));
  assert (~(tag >= 256));
  let new_hdr = makeHeader (getWosize hdr) White (U64.uint_to_t tag) in
  makeHeader_getWosize (getWosize hdr) White (U64.uint_to_t tag);
  assert (getWosize new_hdr == getWosize hdr);
  MH.major_objects_write_member_header_same_wosize_preserves
    mh idx dst new_hdr;
  MH.write_word_in_major_at_lookup_index mh hd new_hdr idx;
  let c' = MH.write_word_in_chunk c hd new_hdr in
  assert (MH.write_word_in_major mh hd new_hdr == Some (Seq.upd mh idx c'));
  SpecMajorAlloc.major_write_word_or_same_some
    mh (Seq.upd mh idx c') hd new_hdr;
  assert (chunked_set_promoted_tag mh obj tag == Seq.upd mh idx c');
  MH.write_word_at_index_preserves_wf mh hd new_hdr idx
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_set_promoted_tag_header_effect
  (mh: MH.major_heap) (obj: U64.t) (tag: nat) (hdr: U64.t)
  : Lemma
      (requires
        tag < 256 /\
        MH.well_formed_major_heap mh /\
        U64.v obj >= U64.v mword /\
        U64.v obj < heap_size /\
        U64.v obj % U64.v mword == 0 /\
        Seq.mem (obj <: obj_addr) (MH.major_objects mh) /\
        MH.read_word_in_major mh (hd_address (obj <: obj_addr)) == Some hdr)
      (ensures
        (let new_hdr =
           makeHeader (getWosize hdr) GC.Lib.Header.White
             (U64.uint_to_t tag) in
         let mh' = chunked_set_promoted_tag mh obj tag in
         MH.well_formed_major_heap mh' /\
         MH.major_objects mh' == MH.major_objects mh /\
         MH.read_word_in_major mh' (hd_address (obj <: obj_addr)) ==
           Some new_hdr /\
         getWosize new_hdr == getWosize hdr /\
         getColor new_hdr == GC.Lib.Header.White /\
         getTag new_hdr == U64.uint_to_t tag))
  =
  let dst : obj_addr = obj in
  let hd = hd_address dst in
  MH.read_word_in_major_lookup_index mh hd hdr;
  let idx = MH.lookup_chunk_index_value mh hd in
  let c = Seq.index mh idx in
  assert (MH.lookup_chunk_index mh hd == Some idx);
  assert (idx < Seq.length mh);
  assert (MH.word_in_chunk c hd);
  assert (MH.read_word_in_chunk c hd == hdr);
  MH.lookup_chunk_index_some mh hd idx;
  MH.major_objects_member_in_lookup_chunk mh idx dst;
  assert (Seq.mem dst (MH.objects_in_chunk c));
  MH.objects_in_chunk_member_header_fits c dst;
  assert (MH.object_wosize_in_chunk c dst == U64.v (getWosize hdr));
  let new_hdr =
    makeHeader (getWosize hdr) GC.Lib.Header.White (U64.uint_to_t tag) in
  makeHeader_getWosize
    (getWosize hdr) GC.Lib.Header.White (U64.uint_to_t tag);
  makeHeader_getColor
    (getWosize hdr) GC.Lib.Header.White (U64.uint_to_t tag);
  makeHeader_getTag
    (getWosize hdr) GC.Lib.Header.White (U64.uint_to_t tag);
  assert (U64.v (getWosize new_hdr) == MH.object_wosize_in_chunk c dst);
  MH.major_objects_write_member_header_same_wosize_preserves
    mh idx dst new_hdr;
  MH.write_word_in_major_at_lookup_index mh hd new_hdr idx;
  let c' = MH.write_word_in_chunk c hd new_hdr in
  assert (MH.write_word_in_major mh hd new_hdr ==
          Some (Seq.upd mh idx c'));
  SpecMajorAlloc.major_write_word_or_same_some
    mh (Seq.upd mh idx c') hd new_hdr;
  assert (chunked_set_promoted_tag mh obj tag == Seq.upd mh idx c');
  MH.write_word_at_index_preserves_wf mh hd new_hdr idx;
  MH.write_word_in_chunk_preserves_word c hd new_hdr hd;
  MH.read_write_in_chunk_same c hd new_hdr;
  assert (Seq.index (Seq.upd mh idx c') idx == c');
  assert (MH.word_in_chunk (Seq.index (Seq.upd mh idx c') idx) hd);
  assert (forall k. k < idx ==>
            Seq.index (Seq.upd mh idx c') k == Seq.index mh k);
  assert (forall k. k < idx ==>
            ~(MH.chunk_contains_addr (Seq.index (Seq.upd mh idx c') k) hd));
  MH.read_word_in_major_at_index (Seq.upd mh idx c') hd idx;
  assert (MH.read_word_in_chunk c' hd == new_hdr)
#pop-options

let chunked_zero_promote_padding
  (mh: MH.major_heap) (dst: U64.t) (copied_wz: nat)
  : GTot MH.major_heap =
  if U64.v dst >= U64.v mword &&
     U64.v dst < heap_size &&
     U64.v dst % U64.v mword = 0 then
    let obj : obj_addr = dst in
    let hd = hd_address obj in
    match MH.read_word_in_major mh hd with
    | None -> mh
    | Some hdr ->
      let actual_wz = U64.v (getWosize hdr) in
      if actual_wz > copied_wz then begin
        let pad_nat = U64.v dst + copied_wz * U64.v mword in
        if pad_nat < heap_size && pad_nat % U64.v mword = 0 then begin
          SpecMajorAlloc.aligned_lt_heap_has_word_room pad_nat;
          SpecMajorAlloc.major_write_word_or_same
            mh (U64.uint_to_t pad_nat) 0UL
        end
        else mh
      end
      else mh
  else mh

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0"
let chunked_zero_promote_padding_noop
  (mh: MH.major_heap) (dst: U64.t) (copied_wz: nat) (hdr: U64.t)
  : Lemma
      (requires
        U64.v dst >= U64.v mword /\
        U64.v dst < heap_size /\
        U64.v dst % U64.v mword == 0 /\
        MH.read_word_in_major mh (hd_address (dst <: obj_addr)) ==
          Some hdr /\
        U64.v (getWosize hdr) <= copied_wz)
      (ensures
        chunked_zero_promote_padding mh dst copied_wz == mh)
  =
  let obj : obj_addr = dst in
  let hd = hd_address obj in
  assert (MH.read_word_in_major mh hd == Some hdr);
  assert (~ (U64.v (getWosize hdr) > copied_wz))
#pop-options

let chunked_promote_object_with_fuel
  (minor: minor_state) (mh: MH.major_heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (fuel: nat)
  : GTot chunked_promote_one_result =
  let alloc_res = SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
  let new_addr = alloc_res.major_obj_out in
  if new_addr = 0UL then
    { major_out = mh; fp_out = fp; new_addr = 0UL }
  else
    let copied =
      chunked_copy_fields
        minor alloc_res.major_alloc_out obj new_addr 0 wosize in
    let padded = chunked_zero_promote_padding copied new_addr wosize in
    let tag = minor_tag minor obj in
    minor_tag_bound minor obj;
    let final_major = chunked_set_promoted_tag padded new_addr tag in
    { major_out = final_major;
      fp_out = alloc_res.major_fp_out;
      new_addr = new_addr }

let chunked_promote_object_oom
  (minor: minor_state) (mh: MH.major_heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (fuel: nat)
  : Lemma
      (requires
        (SpecMajorAlloc.major_alloc_spec_with_fuel
          mh fp wosize fuel).major_obj_out == 0UL)
      (ensures
        (let res =
           chunked_promote_object_with_fuel minor mh obj fp wosize fuel in
         res.major_out == mh /\
         res.fp_out == fp /\
         res.new_addr == 0UL))
  = ()

let chunked_promote_object_success
  (minor: minor_state) (mh: MH.major_heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (fuel: nat)
  : Lemma
      (requires
        (SpecMajorAlloc.major_alloc_spec_with_fuel
          mh fp wosize fuel).major_obj_out <> 0UL)
      (ensures
        (let alloc_res =
           SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
         let res =
           chunked_promote_object_with_fuel minor mh obj fp wosize fuel in
         let copied =
           chunked_copy_fields
             minor alloc_res.major_alloc_out obj alloc_res.major_obj_out
             0 wosize in
         let padded =
           chunked_zero_promote_padding copied alloc_res.major_obj_out wosize in
         let tag = minor_tag minor obj in
         res.major_out == chunked_set_promoted_tag
                            padded alloc_res.major_obj_out tag /\
         res.fp_out == alloc_res.major_fp_out /\
         res.new_addr == alloc_res.major_obj_out))
  = ()

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
let chunked_promote_object_success_field_effect
  (minor: minor_state) (mh: MH.major_heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (fuel: nat)
  (j: nat) (field_addr: hp_addr) (idx: nat) (hdr: U64.t)
  : Lemma
      (requires
        (let alloc_res =
          SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
         let dst = alloc_res.major_obj_out in
         alloc_res.major_obj_out <> 0UL /\
         U64.v dst >= U64.v mword /\
         U64.v dst < heap_size /\
         U64.v dst % U64.v mword == 0 /\
         j < wosize /\
         U64.v field_addr == U64.v dst + j * U64.v mword /\
         MH.well_formed_major_heap alloc_res.major_alloc_out /\
         idx < Seq.length alloc_res.major_alloc_out /\
         MH.lookup_chunk_index alloc_res.major_alloc_out
          (hd_address (dst <: obj_addr)) == Some idx /\
         Seq.mem (dst <: obj_addr)
          (MH.major_objects alloc_res.major_alloc_out) /\
         MH.read_word_in_major alloc_res.major_alloc_out
          (hd_address (dst <: obj_addr)) == Some hdr /\
         U64.v (getWosize hdr) == wosize))
      (ensures
        (let alloc_res =
          SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
         let dst = alloc_res.major_obj_out in
         let res =
          chunked_promote_object_with_fuel minor mh obj fp wosize fuel in
         let addr_nat = U64.v dst + j * U64.v mword in
         res.new_addr == dst /\
         addr_nat + U64.v mword <= heap_size /\
         addr_nat % U64.v mword == 0 /\
         MH.read_word_in_major res.major_out field_addr ==
          Some (minor_read_field minor obj j)))
  =
  let alloc_res =
    SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
  let dst_u = alloc_res.major_obj_out in
  let dst : obj_addr = dst_u in
  let hd = hd_address dst in
  chunked_promote_object_success minor mh obj fp wosize fuel;
  chunked_copy_fields_field_effect
    minor alloc_res.major_alloc_out obj dst_u 0 wosize j idx hdr;
  let addr_nat = U64.v dst_u + j * U64.v mword in
  assert (addr_nat + U64.v mword <= heap_size);
  assert (addr_nat % U64.v mword == 0);
  assert (field_addr == U64.uint_to_t addr_nat);
  let copied =
    chunked_copy_fields
      minor alloc_res.major_alloc_out obj dst_u 0 wosize in
  assert (MH.read_word_in_major copied field_addr ==
         Some (minor_read_field minor obj j));
  hd_address_spec dst;
  assert (U64.v hd + U64.v mword == U64.v dst_u);
  assert (U64.v hd + U64.v mword <= U64.v dst_u + 0 * U64.v mword);
  chunked_copy_fields_frame_before
    minor alloc_res.major_alloc_out obj dst_u 0 wosize hd hdr;
  assert (MH.read_word_in_major copied hd == Some hdr);
  assert (U64.v (getWosize hdr) <= wosize);
  chunked_zero_promote_padding_noop copied dst_u wosize hdr;
  let padded = chunked_zero_promote_padding copied dst_u wosize in
  assert (padded == copied);
  let tag = minor_tag minor obj in
  minor_tag_bound minor obj;
  assert (U64.v hd + U64.v mword == U64.v dst_u);
  assert (U64.v hd + U64.v mword <= U64.v field_addr);
  chunked_set_promoted_tag_read_frame
    copied dst_u tag field_addr (minor_read_field minor obj j);
  let final_major = chunked_set_promoted_tag padded dst_u tag in
  assert (MH.read_word_in_major final_major field_addr ==
         Some (minor_read_field minor obj j));
  let res =
    chunked_promote_object_with_fuel minor mh obj fp wosize fuel in
  assert (res.major_out == final_major);
  assert (res.new_addr == dst_u)
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
let chunked_promote_object_success_header_effect
  (minor: minor_state) (mh: MH.major_heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (fuel: nat)
  (idx: nat) (hdr: U64.t)
  : Lemma
      (requires
        (let alloc_res =
          SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
         let dst = alloc_res.major_obj_out in
         alloc_res.major_obj_out <> 0UL /\
         U64.v dst >= U64.v mword /\
         U64.v dst < heap_size /\
         U64.v dst % U64.v mword == 0 /\
         MH.well_formed_major_heap alloc_res.major_alloc_out /\
         idx < Seq.length alloc_res.major_alloc_out /\
         MH.lookup_chunk_index alloc_res.major_alloc_out
          (hd_address (dst <: obj_addr)) == Some idx /\
         Seq.mem (dst <: obj_addr)
          (MH.major_objects alloc_res.major_alloc_out) /\
         MH.read_word_in_major alloc_res.major_alloc_out
          (hd_address (dst <: obj_addr)) == Some hdr /\
         U64.v (getWosize hdr) == wosize /\
         minor_tag minor obj < 256))
      (ensures
        (let alloc_res =
          SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
          let dst = alloc_res.major_obj_out in
          let res =
           chunked_promote_object_with_fuel minor mh obj fp wosize fuel in
          res.new_addr == dst /\
          MH.well_formed_major_heap res.major_out /\
          Seq.mem (dst <: obj_addr) (MH.major_objects res.major_out) /\
          (match MH.read_word_in_major res.major_out
             (hd_address (dst <: obj_addr)) with
           | Some final_hdr ->
             U64.v (getWosize final_hdr) == wosize /\
             getColor final_hdr == GC.Lib.Header.White /\
             U64.v (getTag final_hdr) == minor_tag minor obj
           | None -> False)))
  =
  let alloc_res =
    SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
  let dst_u = alloc_res.major_obj_out in
  let dst : obj_addr = dst_u in
  let hd = hd_address dst in
  chunked_promote_object_success minor mh obj fp wosize fuel;
  chunked_copy_fields_preserves_major_objects
    minor alloc_res.major_alloc_out obj dst_u 0 wosize idx hdr;
  let copied =
    chunked_copy_fields
      minor alloc_res.major_alloc_out obj dst_u 0 wosize in
  assert (MH.well_formed_major_heap copied);
  assert (MH.major_objects copied ==
          MH.major_objects alloc_res.major_alloc_out);
  assert (Seq.mem dst (MH.major_objects copied));
  assert (MH.read_word_in_major copied hd == Some hdr);
  assert (U64.v (getWosize hdr) <= wosize);
  chunked_zero_promote_padding_noop copied dst_u wosize hdr;
  let padded = chunked_zero_promote_padding copied dst_u wosize in
  assert (padded == copied);
  let tag = minor_tag minor obj in
  minor_tag_bound minor obj;
  chunked_set_promoted_tag_header_effect copied dst_u tag hdr;
  let final_major = chunked_set_promoted_tag padded dst_u tag in
  let new_hdr =
    makeHeader (getWosize hdr) GC.Lib.Header.White (U64.uint_to_t tag) in
  assert (MH.well_formed_major_heap final_major);
  assert (Seq.mem dst (MH.major_objects final_major));
  assert (MH.read_word_in_major final_major hd == Some new_hdr);
  makeHeader_getWosize
    (getWosize hdr) GC.Lib.Header.White (U64.uint_to_t tag);
  makeHeader_getColor
    (getWosize hdr) GC.Lib.Header.White (U64.uint_to_t tag);
  makeHeader_getTag
    (getWosize hdr) GC.Lib.Header.White (U64.uint_to_t tag);
  let res = chunked_promote_object_with_fuel minor mh obj fp wosize fuel in
  assert (res.major_out == final_major);
  assert (res.new_addr == dst_u)
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
private let rec chunked_copy_fields_single_chunk_compat
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  : Lemma
      (requires U64.v dst_obj >= U64.v zero_addr)
      (ensures
        chunked_copy_fields
          minor (MH.single_chunk_major_heap major) src_obj dst_obj i n ==
        MH.single_chunk_major_heap
          (WriteBody.copy_fields minor major src_obj dst_obj i n))
      (decreases (n - i))
  =
  if i >= n then
    WriteBody.copy_fields_base minor major src_obj dst_obj i n
  else begin
    let dst_offset = U64.v dst_obj + i * U64.v mword in
    if dst_offset + U64.v mword > heap_size ||
       dst_offset % U64.v mword <> 0 then
      WriteBody.copy_fields_oob minor major src_obj dst_obj i n
    else begin
      let addr : hp_addr = U64.uint_to_t dst_offset in
      let field_val = minor_read_field minor src_obj i in
      assert (U64.v addr >= U64.v zero_addr);
      SpecMajorAlloc.major_write_word_or_same_single_chunk_compat
        major addr field_val;
      WriteBody.copy_fields_step minor major src_obj dst_obj i n;
      chunked_copy_fields_single_chunk_compat
        minor (write_word major addr field_val)
        src_obj dst_obj (i + 1) n
    end
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
private let chunked_set_promoted_tag_single_chunk_compat
  (major: heap) (obj: U64.t) (tag: nat)
  : Lemma
      (requires tag < 256 /\
                U64.v obj >= U64.v zero_addr + U64.v mword /\
                U64.v obj < heap_size /\
                U64.v obj % U64.v mword == 0)
      (ensures
        chunked_set_promoted_tag
          (MH.single_chunk_major_heap major) obj tag ==
        MH.single_chunk_major_heap
          (Promote.set_promoted_tag major obj tag))
  =
  let dst : obj_addr = obj in
  hd_address_spec dst;
  hd_address_bounds dst;
  assert (U64.v (hd_address dst) >= U64.v zero_addr);
  MH.single_chunk_read_word_compat major (hd_address dst);
  let hdr = read_word major (hd_address dst) in
  SpecMajorAlloc.major_write_word_or_same_single_chunk_compat
    major (hd_address dst) (makeHeader (getWosize hdr) White (U64.uint_to_t tag));
  Promote.set_promoted_tag_unfold major dst tag

private let chunked_zero_promote_padding_single_chunk_compat
  (major: heap) (dst: U64.t) (copied_wz: nat)
  : Lemma
      (requires U64.v dst >= U64.v zero_addr + U64.v mword /\
                U64.v dst < heap_size /\
                U64.v dst % U64.v mword == 0)
      (ensures
        chunked_zero_promote_padding
          (MH.single_chunk_major_heap major) dst copied_wz ==
        MH.single_chunk_major_heap
          (Promote.zero_promote_padding major dst copied_wz))
  =
  let obj : obj_addr = dst in
  hd_address_spec obj;
  hd_address_bounds obj;
  assert (U64.v (hd_address obj) >= U64.v zero_addr);
  MH.single_chunk_read_word_compat major (hd_address obj);
  let actual_wz = U64.v (wosize_of_object obj major) in
  wosize_of_object_spec obj major;
  if actual_wz > copied_wz then begin
    let pad_nat = U64.v dst + copied_wz * U64.v mword in
    if pad_nat < heap_size && pad_nat % U64.v mword = 0 then begin
      SpecMajorAlloc.aligned_lt_heap_has_word_room pad_nat;
      let pad_addr : hp_addr = U64.uint_to_t pad_nat in
      assert (U64.v pad_addr >= U64.v zero_addr);
      SpecMajorAlloc.major_write_word_or_same_single_chunk_compat
        major pad_addr 0UL;
      Promote.zero_promote_padding_write major obj copied_wz
    end
  end else
    Promote.zero_promote_padding_noop major obj copied_wz
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_promote_object_with_fuel_single_chunk_compat
  (minor: minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (fuel: nat)
  : Lemma
      (requires fuel == SpecAlloc.alloc_search_fuel /\
                (let alloc_res = SpecAlloc.alloc_spec major fp wosize in
                 alloc_res.obj_out <> 0UL ==>
                 U64.v alloc_res.obj_out >= U64.v zero_addr + U64.v mword /\
                 U64.v alloc_res.obj_out < heap_size /\
                 U64.v alloc_res.obj_out % U64.v mword == 0))
      (ensures
        (let chunked =
           chunked_promote_object_with_fuel
             minor (MH.single_chunk_major_heap major) obj fp wosize fuel in
         let dense = Promote.promote_object minor major obj fp wosize in
         chunked.major_out == MH.single_chunk_major_heap dense.major_out /\
         chunked.fp_out == dense.fp_out /\
         chunked.new_addr == dense.new_addr))
  =
  assert (SpecAlloc.alloc_spec major fp wosize ==
          SpecAlloc.alloc_spec_with_fuel major fp wosize fuel);
  SpecMajorAlloc.major_alloc_spec_with_fuel_single_chunk_compat
    major fp wosize fuel;
  let dense_alloc = SpecAlloc.alloc_spec major fp wosize in
  let chunked_alloc =
    SpecMajorAlloc.major_alloc_spec_with_fuel
      (MH.single_chunk_major_heap major) fp wosize fuel in
  assert (chunked_alloc ==
          SpecMajorAlloc.major_result_of_alloc_result dense_alloc);
  if dense_alloc.obj_out = 0UL then
    Promote.promote_object_oom minor major obj fp wosize
  else begin
    Promote.promote_object_success minor major obj fp wosize;
    let new_addr = dense_alloc.obj_out in
    assert (U64.v new_addr >= U64.v zero_addr + U64.v mword);
    assert (U64.v new_addr < heap_size);
    assert (U64.v new_addr % U64.v mword == 0);
    chunked_copy_fields_single_chunk_compat
      minor dense_alloc.heap_out obj new_addr 0 wosize;
    let copied_dense =
      WriteBody.copy_fields
        minor dense_alloc.heap_out obj new_addr 0 wosize in
    chunked_zero_promote_padding_single_chunk_compat
      copied_dense new_addr wosize;
    let padded_dense =
      Promote.zero_promote_padding copied_dense new_addr wosize in
    minor_tag_bound minor obj;
    chunked_set_promoted_tag_single_chunk_compat
      padded_dense new_addr (minor_tag minor obj)
  end
#pop-options
