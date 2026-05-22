/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyPreservation.Forwarding -- forwarding classification interface
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyPreservation.Forwarding

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.PromoteUpdate
open GC.Gen.Cheney

module Allocator = GC.Spec.Allocator
module AllocLemmas = GC.Spec.Allocator.Lemmas

let fwd_classified (cs: cheney_state) : prop =
  forall (x: U64.t). cs.cs_fwd x <> 0UL ==>
    (U64.v (cs.cs_fwd x) >= U64.v mword /\
     U64.v (cs.cs_fwd x) < heap_size /\
     U64.v (cs.cs_fwd x) % U64.v mword == 0 /\
     (Seq.mem ((cs.cs_fwd x) <: obj_addr) (objects zero_addr cs.cs_major) \/
      (is_infix (cs.cs_fwd x) cs.cs_major /\
       (exists (p: obj_addr).
         Seq.mem p (objects zero_addr cs.cs_major) /\
         is_blue p cs.cs_major = false /\
         U64.v (cs.cs_fwd x) - 8 >= U64.v p /\
         U64.v (cs.cs_fwd x) <=
           U64.v p + U64.v (wosize_of_object p cs.cs_major) * 8))))

let infix_fwd_ready (minor: minor_state) (cs: cheney_state) : prop =
  forall (addr: U64.t).
    is_infix_in_minor minor addr ==>
    (let parent = infix_parent minor addr in
     cs.cs_fwd parent <> 0UL ==>
     U64.v (cs.cs_fwd parent) >= U64.v mword ==>
     U64.v (cs.cs_fwd parent) < heap_size ==>
     U64.v (cs.cs_fwd parent) % U64.v mword == 0 ==>
     U64.v addr >= U64.v parent ==>
     (let fwd_parent : obj_addr = cs.cs_fwd parent in
      let delta = U64.v addr - U64.v parent in
      U64.v fwd_parent + delta < heap_size ==>
      (let sum_v = U64.v fwd_parent + delta in
       sum_v >= U64.v mword /\
       sum_v % U64.v mword == 0 /\
       (let sum : obj_addr = U64.uint_to_t sum_v in
        is_infix sum cs.cs_major /\
        Seq.mem fwd_parent (objects zero_addr cs.cs_major) /\
        is_blue fwd_parent cs.cs_major = false /\
        sum_v - 8 >= U64.v fwd_parent /\
        sum_v <= U64.v fwd_parent +
          U64.v (wosize_of_object fwd_parent cs.cs_major) * 8))))

let fwd_valid_or_infix (fwd: forwarding_map) (g: heap) : prop =
  forall (x: U64.t). fwd x <> 0UL ==>
    (U64.v (fwd x) >= U64.v mword /\
     U64.v (fwd x) < heap_size /\
     U64.v (fwd x) % U64.v mword == 0 /\
     (Seq.mem ((fwd x) <: obj_addr) (objects zero_addr g) \/
      is_infix (fwd x) g))

/// Forwarding entries whose source is not a minor infix sub-object are ordinary
/// major objects.  Infix entries are deliberately excluded: they are interior
/// pointers into a promoted closure, not members of `objects zero_addr g`.
let fwd_noninfix_targets_valid (minor: minor_state) (fwd: forwarding_map)
                               (g: heap) : prop =
  forall (x: U64.t). fwd x <> 0UL /\ ~(is_infix_in_minor minor x) ==>
    U64.v (fwd x) >= U64.v mword /\
    U64.v (fwd x) < heap_size /\
    U64.v (fwd x) % U64.v mword == 0 /\
    Seq.mem ((fwd x) <: obj_addr) (objects zero_addr g)

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

val cheney_forward_normal_preserves_cob
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp)
          (ensures (let cs' = cheney_forward_normal minor cs addr in
                    chain_objects_blue cs'.cs_major cs'.cs_fp))

val cheney_forward_one_preserves_cob
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor)
          (ensures (let cs' = cheney_forward_one minor cs addr in
                    chain_objects_blue cs'.cs_major cs'.cs_fp))

val cheney_forward_fields_preserves_cob
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (i: nat) (wosize: nat)
  : Lemma
    (requires well_formed_heap_part1 cs.cs_major /\
              AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
              AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
              chain_objects_blue cs.cs_major cs.cs_fp /\
              minor_infix_wf minor)
    (ensures (let cs' = cheney_forward_fields minor cs parent i wosize in
              chain_objects_blue cs'.cs_major cs'.cs_fp))

val cheney_forward_roots_preserves_cob
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (ridx: nat)
  : Lemma
    (requires well_formed_heap_part1 cs.cs_major /\
              AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
              AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
              chain_objects_blue cs.cs_major cs.cs_fp /\
              minor_infix_wf minor)
    (ensures (let cs' = cheney_forward_roots minor cs roots ridx in
              chain_objects_blue cs'.cs_major cs'.cs_fp))

val promote_preserves_is_infix_frame
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (target: obj_addr) (parent_obj: obj_addr)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp /\
      is_infix target major /\
      Seq.mem parent_obj (objects zero_addr major) /\
      is_blue parent_obj major = false /\
      U64.v (hd_address target) >= U64.v parent_obj /\
      U64.v (hd_address target) + 8 <= U64.v parent_obj + U64.v (wosize_of_object parent_obj major) * 8)
    (ensures
      (let res = promote_object minor major obj fp wz in
       is_infix target res.major_out))

val promote_object_new_addr_in_objects_not_blue
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  : Lemma
    (requires well_formed_heap_part1 major /\
              AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
              AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
              (promote_object minor major obj fp wz).new_addr <> 0UL)
    (ensures
      (let res = promote_object minor major obj fp wz in
       U64.v res.new_addr >= U64.v mword /\
       U64.v res.new_addr < heap_size /\
       U64.v res.new_addr % U64.v mword == 0 /\
        (let na : obj_addr = res.new_addr in
         Seq.mem na (objects zero_addr res.major_out) /\
         is_blue na res.major_out = false)))

val promote_object_new_addr_wosize_ge
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (dst: obj_addr)
  : Lemma
    (requires well_formed_heap_part1 major /\
              AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
              AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
              (let res = promote_object minor major obj fp wz in
               res.new_addr <> 0UL /\ dst == res.new_addr))
    (ensures
      (let res = promote_object minor major obj fp wz in
       U64.v (wosize_of_object dst res.major_out) >= wz))

val cheney_forward_normal_preserves_fwd_classified
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires fwd_classified cs /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp)
          (ensures fwd_classified (cheney_forward_normal minor cs addr))

val cheney_forward_normal_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword))
          (ensures (let cs' = cheney_forward_normal minor cs addr in
                    well_formed_heap_part1 cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp (heap_size / U64.v mword)))

val cheney_forward_roots_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword))
          (ensures (let cs' = cheney_forward_roots minor cs roots idx in
                    well_formed_heap_part1 cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp (heap_size / U64.v mword)))

val cheney_forward_normal_preserves_infix_fwd_ready
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires infix_fwd_ready minor cs /\
                    fwd_classified cs /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor)
          (ensures infix_fwd_ready minor (cheney_forward_normal minor cs addr))

val cheney_forward_one_preserves_infix_fwd_ready
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires infix_fwd_ready minor cs /\
                    fwd_classified cs /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures infix_fwd_ready minor (cheney_forward_one minor cs addr))

val cheney_forward_one_preserves_fwd_classified
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires fwd_classified cs /\
                    infix_fwd_ready minor cs /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_classified (cheney_forward_one minor cs addr))

val cheney_forward_fields_preserves_fwd_classified
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (i: nat) (wosize: nat)
  : Lemma (requires fwd_classified cs /\
                    infix_fwd_ready minor cs /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_classified (cheney_forward_fields minor cs parent i wosize) /\
                   infix_fwd_ready minor (cheney_forward_fields minor cs parent i wosize))

val cheney_forward_roots_preserves_fwd_classified
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (ridx: nat)
  : Lemma (requires fwd_classified cs /\
                    infix_fwd_ready minor cs /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_classified (cheney_forward_roots minor cs roots ridx) /\
                   infix_fwd_ready minor (cheney_forward_roots minor cs roots ridx))

val cheney_scan_preserves_fwd_classified
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires fwd_classified cs /\
                    infix_fwd_ready minor cs /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_classified (cheney_scan minor cs scan fuel))

val cheney_promote_fwd_valid_or_infix
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_valid_or_infix (cheney_promote minor major fp roots).fwd_map
                                      (cheney_promote minor major fp roots).major_final)

val cheney_promote_fwd_noninfix_targets_valid
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_noninfix_targets_valid
            minor
            (cheney_promote minor major fp roots).fwd_map
            (cheney_promote minor major fp roots).major_final)
