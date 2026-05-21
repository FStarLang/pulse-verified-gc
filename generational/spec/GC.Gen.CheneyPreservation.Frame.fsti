/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyPreservation.Frame — Old-object frame lemmas for Cheney BFS
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyPreservation.Frame

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Cheney

module Allocator = GC.Spec.Allocator
module AllocLemmas = GC.Spec.Allocator.Lemmas

val promote_object_frame_old_field_derived
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (src: obj_addr) (idx: nat)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      (let res = promote_object minor major obj fp wz in
       res.new_addr <> 0UL) /\
      Seq.mem src (objects zero_addr major) /\
      AllocLemmas.chain_avoids major fp src (heap_size / U64.v mword) = true /\
      (src <> (Allocator.alloc_spec major fp wz).obj_out) /\
      idx < U64.v (wosize_of_object src major) /\
      U64.v src + idx * 8 + 8 <= heap_size /\
      (U64.v src + idx * 8) % 8 == 0)
    (ensures
      (let res = promote_object minor major obj fp wz in
       let field_addr : hp_addr = U64.uint_to_t (U64.v src + idx * 8) in
       read_word res.major_out field_addr == read_word major field_addr))

val promote_object_frame_old_header_derived
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (src: obj_addr)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      (let res = promote_object minor major obj fp wz in
       res.new_addr <> 0UL) /\
      Seq.mem src (objects zero_addr major) /\
      (src <> (Allocator.alloc_spec major fp wz).obj_out))
    (ensures
      (let res = promote_object minor major obj fp wz in
       read_word res.major_out (hd_address src) == read_word major (hd_address src)))

val cheney_promote_frame_old_fields
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr) (j: nat)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    Seq.mem obj (objects zero_addr major) /\
                    is_blue obj major = false /\
                    j < U64.v (wosize_of_object obj major) /\
                    U64.v obj + j * 8 + 8 <= heap_size /\
                    minor_infix_wf minor)
          (ensures (let res = cheney_promote minor major fp roots in
                    read_word res.major_final (U64.uint_to_t (U64.v obj + j * 8))
                    == read_word major (U64.uint_to_t (U64.v obj + j * 8))))

val cheney_promote_frame_old_header
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    Seq.mem obj (objects zero_addr major) /\
                    is_blue obj major = false /\
                    minor_infix_wf minor)
          (ensures (let res = cheney_promote minor major fp roots in
                    read_word res.major_final (hd_address obj)
                    == read_word major (hd_address obj)))
