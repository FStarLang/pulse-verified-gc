/// ---------------------------------------------------------------------------
/// GC.Gen.PromoteUpdate.Aux — Auxiliary update_all_objects lemmas
/// ---------------------------------------------------------------------------

module GC.Gen.PromoteUpdate.Aux

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
module WriteBody = GC.Gen.WriteBodyLemmas

val update_all_objects_aux_preserves_objects
  (major: heap) (objs: seq obj_addr) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires well_formed_heap_part1 major /\ objs == objects zero_addr major)
    (ensures objects zero_addr (update_all_objects_aux major objs fwd idx) == objs)
    (decreases (Seq.length objs - idx))

val update_major_pointers_preserves_objects (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major)
    (ensures objects zero_addr (update_major_pointers major fwd) == objects zero_addr major)

val update_all_objects_aux_preserves_wfh_part1
  (major: heap) (objs: seq obj_addr) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires well_formed_heap_part1 major /\ objs == objects zero_addr major)
    (ensures well_formed_heap_part1 (update_all_objects_aux major objs fwd idx))
    (decreases (Seq.length objs - idx))

val update_major_pointers_preserves_wfh_part1 (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major)
    (ensures well_formed_heap_part1 (update_major_pointers major fwd))

val update_all_objects_aux_step (major: heap) (objs: seq obj_addr)
                                (fwd: forwarding_map) (idx: nat)
  : Lemma (requires idx < Seq.length objs /\ well_formed_heap_part1 major /\
                    objs == objects zero_addr major /\
                    is_blue (Seq.index objs idx) major = false /\
                    is_no_scan (Seq.index objs idx) major = false)
          (ensures (let obj = Seq.index objs idx in
                    let wz = U64.v (wosize_of_object obj major) in
                    update_all_objects_aux major objs fwd idx ==
                    update_all_objects_aux (update_object_pointers major obj wz fwd 0) objs fwd (idx + 1)))

val update_all_objects_aux_skip_blue (major: heap) (objs: seq obj_addr)
                                     (fwd: forwarding_map) (idx: nat)
  : Lemma (requires idx < Seq.length objs /\
                    is_blue (Seq.index objs idx) major)
          (ensures update_all_objects_aux major objs fwd idx ==
                   update_all_objects_aux major objs fwd (idx + 1))

val update_all_objects_aux_skip_no_scan (major: heap) (objs: seq obj_addr)
                                        (fwd: forwarding_map) (idx: nat)
  : Lemma (requires idx < Seq.length objs /\
                    is_blue (Seq.index objs idx) major = false /\
                    is_no_scan (Seq.index objs idx) major)
          (ensures update_all_objects_aux major objs fwd idx ==
                   update_all_objects_aux major objs fwd (idx + 1))

val update_all_objects_aux_done (major: heap) (objs: seq obj_addr)
                                (fwd: forwarding_map) (idx: nat)
  : Lemma (requires idx >= Seq.length objs)
          (ensures update_all_objects_aux major objs fwd idx == major)

val update_major_pointers_unfold (major: heap) (fwd: forwarding_map)
  : Lemma (update_major_pointers major fwd ==
           update_all_objects_aux major (objects zero_addr major) fwd 0)
