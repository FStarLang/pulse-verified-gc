/// ---------------------------------------------------------------------------
/// GC.Gen.ChunkedPromote -- Chunked-major promotion specification
/// ---------------------------------------------------------------------------
///
/// This module is the chunked-major counterpart of the dense
/// `GC.Gen.Promote.promote_object` operation.  It is intentionally parallel to
/// the dense API while Cheney is still being ported from `heap` to
/// `GC.Spec.MajorHeap.major_heap`.

module GC.Gen.ChunkedPromote

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Gen.MinorHeap

module MH = GC.Spec.MajorHeap
module SpecAlloc = GC.Spec.Allocator
module SpecMajorAlloc = GC.Spec.MajorAllocator
module Promote = GC.Gen.Promote

noeq
type chunked_promote_one_result = {
  major_out : MH.major_heap;
  fp_out    : U64.t;
  new_addr  : U64.t;
}

/// Copy `n` fields from a minor object to a chunked-major destination.
///
/// The out-of-bounds/misalignment guard matches dense `copy_fields`: the first
/// bad destination slot halts the whole copy.  A well-formed destination word
/// that misses all active chunks is a no-op via `major_write_word_or_same`.
val chunked_copy_fields
  : minor:minor_state -> mh:MH.major_heap ->
    src_obj:U64.t -> dst_obj:U64.t -> i:nat -> n:nat ->
    GTot MH.major_heap

val chunked_copy_fields_base
  : minor:minor_state -> mh:MH.major_heap ->
    src_obj:U64.t -> dst_obj:U64.t -> i:nat -> n:nat ->
    Lemma (requires i >= n)
          (ensures chunked_copy_fields minor mh src_obj dst_obj i n == mh)

val chunked_copy_fields_step
  : minor:minor_state -> mh:MH.major_heap ->
    src_obj:U64.t -> dst_obj:U64.t -> i:nat -> n:nat ->
    Lemma
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

val major_write_word_or_same_read_frame
  : mh:MH.major_heap -> write_addr:hp_addr -> target:hp_addr ->
    value:U64.t -> old:U64.t ->
    Lemma
      (requires
        MH.read_word_in_major mh target == Some old /\
        (U64.v target + U64.v mword <= U64.v write_addr \/
         U64.v write_addr + U64.v mword <= U64.v target))
      (ensures
        MH.read_word_in_major
          (SpecMajorAlloc.major_write_word_or_same mh write_addr value)
          target == Some old)

val major_write_word_or_same_read_same
  : mh:MH.major_heap -> write_addr:hp_addr -> value:U64.t ->
    idx:nat ->
    Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        MH.lookup_chunk_index mh write_addr == Some idx /\
        MH.word_in_chunk (Seq.index mh idx) write_addr)
      (ensures
        MH.read_word_in_major
          (SpecMajorAlloc.major_write_word_or_same mh write_addr value)
          write_addr == Some value)

val chunked_copy_fields_frame_before
  : minor:minor_state -> mh:MH.major_heap ->
    src_obj:U64.t -> dst_obj:U64.t -> i:nat -> n:nat ->
    target:hp_addr -> old:U64.t ->
    Lemma
      (requires
        MH.read_word_in_major mh target == Some old /\
        U64.v target + U64.v mword <=
          U64.v dst_obj + i * U64.v mword)
      (ensures
        MH.read_word_in_major
          (chunked_copy_fields minor mh src_obj dst_obj i n)
          target == Some old)

val chunked_copy_fields_frame_after
  : minor:minor_state -> mh:MH.major_heap ->
    src_obj:U64.t -> dst_obj:U64.t -> i:nat -> n:nat ->
    target:hp_addr -> old:U64.t ->
    Lemma
      (requires
        MH.read_word_in_major mh target == Some old /\
        U64.v dst_obj + n * U64.v mword <= U64.v target)
      (ensures
        MH.read_word_in_major
          (chunked_copy_fields minor mh src_obj dst_obj i n)
          target == Some old)

val chunked_copy_fields_field_effect
  : minor:minor_state -> mh:MH.major_heap ->
    src_obj:U64.t -> dst_obj:U64.t -> i:nat -> n:nat -> j:nat ->
    idx:nat -> hdr:U64.t ->
    Lemma
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

val chunked_copy_fields_preserves_major_objects
  : minor:minor_state -> mh:MH.major_heap ->
    src_obj:U64.t -> dst_obj:U64.t -> i:nat -> n:nat ->
    idx:nat -> hdr:U64.t ->
    Lemma
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

val chunked_set_promoted_tag
  : mh:MH.major_heap -> obj:U64.t -> tag:nat -> GTot MH.major_heap

val chunked_set_promoted_tag_read_frame
  : mh:MH.major_heap -> obj:U64.t -> tag:nat ->
    target:hp_addr -> old:U64.t ->
    Lemma
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

val chunked_set_promoted_tag_preserves_major_objects
  : mh:MH.major_heap -> obj:U64.t -> tag:nat -> idx:nat -> hdr:U64.t ->
    Lemma
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

val chunked_zero_promote_padding
  : mh:MH.major_heap -> dst:U64.t -> copied_wz:nat -> GTot MH.major_heap

val chunked_zero_promote_padding_noop
  : mh:MH.major_heap -> dst:U64.t -> copied_wz:nat -> hdr:U64.t ->
    Lemma
      (requires
        U64.v dst >= U64.v mword /\
        U64.v dst < heap_size /\
        U64.v dst % U64.v mword == 0 /\
        MH.read_word_in_major mh (hd_address (dst <: obj_addr)) ==
          Some hdr /\
        U64.v (getWosize hdr) <= copied_wz)
      (ensures
        chunked_zero_promote_padding mh dst copied_wz == mh)

val chunked_promote_object_with_fuel
  : minor:minor_state -> mh:MH.major_heap -> obj:U64.t ->
    fp:U64.t -> wosize:nat{wosize > 0} -> fuel:nat ->
    GTot chunked_promote_one_result

val chunked_promote_object_oom
  : minor:minor_state -> mh:MH.major_heap -> obj:U64.t ->
    fp:U64.t -> wosize:nat{wosize > 0} -> fuel:nat ->
    Lemma
      (requires
        (SpecMajorAlloc.major_alloc_spec_with_fuel
          mh fp wosize fuel).major_obj_out == 0UL)
      (ensures
        (let res =
           chunked_promote_object_with_fuel minor mh obj fp wosize fuel in
         res.major_out == mh /\
         res.fp_out == fp /\
         res.new_addr == 0UL))

val chunked_promote_object_success
  : minor:minor_state -> mh:MH.major_heap -> obj:U64.t ->
    fp:U64.t -> wosize:nat{wosize > 0} -> fuel:nat ->
    Lemma
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

/// Single-chunk compatibility with dense `promote_object`, for callers that can
/// show the dense allocator returned an active major address when it succeeded.
val chunked_promote_object_with_fuel_single_chunk_compat
  : minor:minor_state -> major:heap -> obj:U64.t ->
    fp:U64.t -> wosize:nat{wosize > 0} -> fuel:nat ->
    Lemma
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
