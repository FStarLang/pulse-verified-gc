/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyPreservation.NonBlueOrigin
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyPreservation.NonBlueOrigin

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

module AllocLemmas = GC.Spec.Allocator.Lemmas

val promote_object_nonblue_other_reflects_pre
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (target: obj_addr)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      (promote_object minor major obj fp wz).new_addr <> 0UL /\
      Seq.mem target (objects zero_addr (promote_object minor major obj fp wz).major_out) /\
      is_blue target (promote_object minor major obj fp wz).major_out = false /\
      target <> (promote_object minor major obj fp wz).new_addr)
    (ensures
      Seq.mem target (objects zero_addr major) /\
      is_blue target major = false)

val cheney_promote_nonblue_origin
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor /\
                    (let res = cheney_promote minor major fp roots in
                     Seq.mem obj (objects zero_addr res.major_final) /\
                     is_blue obj res.major_final = false /\
                     ~(Seq.mem obj (objects zero_addr major) /\
                       is_blue obj major = false)))
          (ensures (let res = cheney_promote minor major fp roots in
                    exists (x: U64.t). res.fwd_map x == obj /\ is_minor_pointer x))
