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
        // The copied infix header still encodes the offset back to the parent,
        // so `resolve_object sum` is `fwd_parent`; and the parent is a closure.
        // Together with the containment bounds below these are exactly
        // `GC.Spec.Object.infix_addr_conds`.
        U64.v (wosize_of_object sum cs.cs_major) == minor_wosize minor addr /\
        is_closure fwd_parent cs.cs_major /\
        Seq.mem fwd_parent (objects zero_addr cs.cs_major) /\
        is_blue fwd_parent cs.cs_major = false /\
        sum_v - 8 >= U64.v fwd_parent /\
        sum_v < U64.v fwd_parent +
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
      AllocLemmas.fl_valid major fp heap_words /\
      AllocLemmas.fl_chain_terminates major fp heap_words /\
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
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp)
          (ensures (let cs' = cheney_forward_normal minor cs addr in
                    chain_objects_blue cs'.cs_major cs'.cs_fp))

val cheney_forward_one_preserves_cob
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor)
          (ensures (let cs' = cheney_forward_one minor cs addr in
                    chain_objects_blue cs'.cs_major cs'.cs_fp))

val cheney_forward_fields_preserves_cob
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (i: nat) (wosize: nat)
  : Lemma
    (requires well_formed_heap_part1 cs.cs_major /\
              AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
              AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
              chain_objects_blue cs.cs_major cs.cs_fp /\
              minor_infix_wf minor)
    (ensures (let cs' = cheney_forward_fields minor cs parent i wosize in
              chain_objects_blue cs'.cs_major cs'.cs_fp))

val cheney_forward_roots_preserves_cob
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (ridx: nat)
  : Lemma
    (requires well_formed_heap_part1 cs.cs_major /\
              AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
              AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
              chain_objects_blue cs.cs_major cs.cs_fp /\
              minor_infix_wf minor)
    (ensures (let cs' = cheney_forward_roots minor cs roots ridx in
              chain_objects_blue cs'.cs_major cs'.cs_fp))

let infix_fwd_ready_pre (minor: minor_state) (cs: cheney_state) (addr: U64.t) : prop =
  is_infix_in_minor minor addr /\
  (let parent = infix_parent minor addr in
   cs.cs_fwd parent <> 0UL /\
   U64.v (cs.cs_fwd parent) >= U64.v mword /\
   U64.v (cs.cs_fwd parent) < heap_size /\
   U64.v (cs.cs_fwd parent) % U64.v mword == 0 /\
   U64.v addr >= U64.v parent /\
   (let fwd_parent : obj_addr = cs.cs_fwd parent in
    let delta = U64.v addr - U64.v parent in
    U64.v fwd_parent + delta < heap_size))

let infix_fwd_ready_post
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  (_: squash (infix_fwd_ready_pre minor cs addr))
  : prop =
  let parent = infix_parent minor addr in
  let fwd_parent : obj_addr = cs.cs_fwd parent in
  let delta = U64.v addr - U64.v parent in
  let sum_v = U64.v fwd_parent + delta in
  sum_v >= U64.v mword /\
  sum_v % U64.v mword == 0 /\
  (let sum : obj_addr = U64.uint_to_t sum_v in
   is_infix sum cs.cs_major /\
   U64.v (wosize_of_object sum cs.cs_major) == minor_wosize minor addr /\
   is_closure fwd_parent cs.cs_major /\
   Seq.mem fwd_parent (objects zero_addr cs.cs_major) /\
   is_blue fwd_parent cs.cs_major = false /\
   sum_v - 8 >= U64.v fwd_parent /\
   sum_v < U64.v fwd_parent +
     U64.v (wosize_of_object fwd_parent cs.cs_major) * 8)

val infix_fwd_ready_elim (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
      (requires infix_fwd_ready minor cs /\
                infix_fwd_ready_pre minor cs addr)
      (ensures infix_fwd_ready_post minor cs addr ())

val promote_preserves_is_infix_frame
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (target: obj_addr) (parent_obj: obj_addr)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp heap_words /\
      AllocLemmas.fl_chain_terminates major fp heap_words /\
      chain_objects_blue major fp /\
      is_infix target major /\
      Seq.mem parent_obj (objects zero_addr major) /\
      is_blue parent_obj major = false /\
      U64.v (hd_address target) >= U64.v parent_obj /\
      U64.v (hd_address target) + 8 <= U64.v parent_obj + U64.v (wosize_of_object parent_obj major) * 8)
    (ensures
      (let res = promote_object minor major obj fp wz in
       is_infix target res.major_out /\
       // The whole header word is framed, so the encoded infix offset --
       // and hence `resolve_object target` -- is unchanged too.
       read_word res.major_out (hd_address target) == read_word major (hd_address target) /\
       wosize_of_object target res.major_out == wosize_of_object target major))

val promote_object_new_addr_in_objects_not_blue
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  : Lemma
    (requires well_formed_heap_part1 major /\
              AllocLemmas.fl_valid major fp heap_words /\
              AllocLemmas.fl_chain_terminates major fp heap_words /\
              (promote_object minor major obj fp wz).new_addr <> 0UL)
    (ensures
      (let res = promote_object minor major obj fp wz in
       U64.v res.new_addr >= U64.v mword /\
       U64.v res.new_addr < heap_size /\
       U64.v res.new_addr % U64.v mword == 0 /\
        (let na : obj_addr = res.new_addr in
         Seq.mem na (objects zero_addr res.major_out) /\
         is_blue na res.major_out = false)))

/// The promoted copy carries the source minor object's tag: `promote_object`
/// finishes with `set_promoted_tag _ new_addr (minor_tag minor obj)`.
/// Needed to see that the promotion of a *closure* is still a closure, which is
/// what makes an interior pointer into the copy satisfy `infix_addr_conds`.
val promote_object_new_addr_tag
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  : Lemma
    (requires well_formed_heap_part1 major /\
              AllocLemmas.fl_valid major fp heap_words /\
              AllocLemmas.fl_chain_terminates major fp heap_words /\
              (promote_object minor major obj fp wz).new_addr <> 0UL)
    (ensures
      (let res = promote_object minor major obj fp wz in
       U64.v res.new_addr >= U64.v mword /\
       U64.v res.new_addr < heap_size /\
       U64.v res.new_addr % U64.v mword == 0 /\
        (let na : obj_addr = res.new_addr in
         U64.v (tag_of_object na res.major_out) == minor_tag minor obj)))

val promote_object_new_addr_wosize_ge
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (dst: obj_addr)
  : Lemma
    (requires well_formed_heap_part1 major /\
              AllocLemmas.fl_valid major fp heap_words /\
              AllocLemmas.fl_chain_terminates major fp heap_words /\
              (let res = promote_object minor major obj fp wz in
               res.new_addr <> 0UL /\ dst == res.new_addr))
    (ensures
      (let res = promote_object minor major obj fp wz in
       U64.v (wosize_of_object dst res.major_out) >= wz))

val cheney_forward_normal_preserves_fwd_classified
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires fwd_classified cs /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp)
          (ensures fwd_classified (cheney_forward_normal minor cs addr))

val cheney_forward_normal_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures (let cs' = cheney_forward_normal minor cs addr in
                    well_formed_heap_part1 cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp heap_words))

val cheney_forward_roots_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures (let cs' = cheney_forward_roots minor cs roots idx in
                    well_formed_heap_part1 cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp heap_words))

val cheney_forward_normal_preserves_infix_fwd_ready
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires infix_fwd_ready minor cs /\
                    fwd_classified cs /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor)
          (ensures infix_fwd_ready minor (cheney_forward_normal minor cs addr))

val cheney_forward_one_preserves_infix_fwd_ready
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires infix_fwd_ready minor cs /\
                    fwd_classified cs /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures infix_fwd_ready minor (cheney_forward_one minor cs addr))

val cheney_forward_one_preserves_fwd_classified
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires fwd_classified cs /\
                    infix_fwd_ready minor cs /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_classified (cheney_forward_one minor cs addr))

val cheney_forward_fields_preserves_fwd_classified
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (i: nat) (wosize: nat)
  : Lemma (requires fwd_classified cs /\
                    infix_fwd_ready minor cs /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
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
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
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
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_classified (cheney_scan minor cs scan fuel) /\
                   infix_fwd_ready minor (cheney_scan minor cs scan fuel))

val cheney_promote_fwd_valid_or_infix
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_valid_or_infix (cheney_promote minor major fp roots).fwd_map
                                      (cheney_promote minor major fp roots).major_final)

/// ---------------------------------------------------------------------------
/// Infix forwarding entries relate to their parent's entry
/// ---------------------------------------------------------------------------

/// `cheney_forward_one` records an infix entry as `fwd parent + (x - parent)`
/// (mirroring `caml_oldify_one`'s `*p += offset`).  `infix_fwd_ready` says the
/// *derived* address is well formed; this says the recorded entry *is* that
/// derived address, which is what lets a client combine the two.
let fwd_infix_delta (minor: minor_state) (fwd: forwarding_map) : prop =
  forall (x: U64.t).
    is_infix_in_minor minor x /\ fwd x <> 0UL ==>
    (let parent = infix_parent minor x in
     fwd parent <> 0UL /\
     U64.v x >= U64.v parent /\
     U64.v (fwd x) == U64.v (fwd parent) + (U64.v x - U64.v parent))

val cheney_promote_fwd_infix_delta
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires minor_wf minor /\ minor_infix_wf minor)
          (ensures fwd_infix_delta minor
            (cheney_promote minor major fp roots).fwd_map)

/// Every infix forwarding target is a well-formed interior pointer of the final
/// major heap: it resolves to an enumerated closure that contains it.  This is
/// exactly what `well_formed_heap_part2`/`part3` demand of a field value, and
/// it is the reason minor-heap infix pointers need no longer be forbidden.
let fwd_infix_targets_wf (minor: minor_state) (fwd: forwarding_map) (g: heap) : prop =
  forall (x: U64.t).
    is_infix_in_minor minor x /\ fwd x <> 0UL ==>
    U64.v (fwd x) >= U64.v mword /\
    U64.v (fwd x) < heap_size /\
    U64.v (fwd x) % U64.v mword == 0 /\
    (let t : obj_addr = fwd x in
     Seq.mem (resolve_object t g) (objects zero_addr g) /\
     is_blue (resolve_object t g) g = false /\
     infix_addr_wf g (objects zero_addr g) t)

val cheney_promote_fwd_noninfix_targets_valid
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_noninfix_targets_valid
            minor
            (cheney_promote minor major fp roots).fwd_map
            (cheney_promote minor major fp roots).major_final)

val cheney_promote_fwd_infix_targets_wf
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_infix_targets_wf
            minor
            (cheney_promote minor major fp roots).fwd_map
            (cheney_promote minor major fp roots).major_final)
