module GC.Gen.PromoteUpdate.Header

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Reachability
open GC.Gen.Remembered
open GC.Gen.Promote
open GC.Gen.WriteBodyLemmas

module AllocLemmas = GC.Spec.Allocator.Lemmas

val update_all_objects_aux_preserves_header
  (major: heap) (objs: seq obj_addr) (fwd: forwarding_map) (idx: nat) (h: obj_addr)
  : Lemma (requires
      well_formed_heap_part1 major /\
      objs == objects zero_addr major /\
      Seq.mem h objs)
    (ensures read_word (update_all_objects_aux major objs fwd idx) (hd_address h) ==
             read_word major (hd_address h))
    (decreases (Seq.length objs - idx))

val update_major_pointers_preserves_header (major: heap) (fwd: forwarding_map) (h: obj_addr)
  : Lemma (requires well_formed_heap_part1 major /\ Seq.mem h (objects zero_addr major))
    (ensures read_word (update_major_pointers major fwd) (hd_address h) ==
             read_word major (hd_address h))

val update_major_pointers_preserves_blue_field
  (major: heap) (fwd: forwarding_map) (h: obj_addr) (j: nat)
  : Lemma (requires well_formed_heap_part1 major /\
                    Seq.mem h (objects zero_addr major) /\
                    is_blue h major /\
                    j < U64.v (wosize_of_object h major) /\
                    U64.v h + j * 8 + 8 <= heap_size /\
                    (U64.v h + j * 8) % 8 == 0)
    (ensures (let field_addr = U64.uint_to_t (U64.v h + j * 8) in
              read_word (update_major_pointers major fwd) field_addr ==
              read_word major field_addr))

val update_major_pointers_preserves_wfh_part4 (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\ well_formed_heap_part4 major)
    (ensures well_formed_heap_part4 (update_major_pointers major fwd))

val update_major_pointers_preserves_wfh_part3 (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\ well_formed_heap_part4 major)
    (ensures well_formed_heap_part3 (update_major_pointers major fwd))

/// Instantiate the blue_fields_closed opaque predicate for a specific object and field
val blue_fields_closed_inst (major: heap) (src: obj_addr) (j: nat)
  : Lemma (requires blue_fields_closed major /\
                    Seq.mem src (objects zero_addr major) /\ is_blue src major /\
                    j < U64.v (wosize_of_object src major) /\
                    U64.v src + j * 8 + 8 <= heap_size)
          (ensures (let v = read_word major (U64.uint_to_t (U64.v src + j * 8)) in
                    is_pointer v ==> Seq.mem (v <: obj_addr) (objects zero_addr major)))
