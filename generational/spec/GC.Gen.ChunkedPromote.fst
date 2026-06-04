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
