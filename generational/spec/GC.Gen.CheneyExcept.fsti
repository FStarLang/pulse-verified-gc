/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyExcept -- the minor collection keeps its shape, except the
/// objects pending free
/// ---------------------------------------------------------------------------
///
/// `pf` is the major heap's set of objects pending free (known dead, not yet
/// reclaimed).  A minor collection never reclaims anything and promotion
/// allocates in free blocks, so `pf` is the same before and after it; what
/// changes is the set of not-freed objects (`not_freed g pf`, read off the
/// heap), which promotion grows by the promoted objects.
///
/// In major-heap terms a minor collection is two kinds of event, and each
/// keeps `well_formed_heap_except` for `pf`:
///
/// * **promotion** (`cheney_promote`: allocation from the free list plus
///   `copy_fields`) adds new not-freed objects, the images of the promoted
///   nursery objects, and writes nothing else
///   (`cheney_promote_preserves_wfh_except`);
/// * **the pointer update** (`update_pointers_except`) writes fields of
///   not-freed objects only, each one either unchanged or rewritten to a
///   forwarding target that is itself not freed
///   (`update_pointers_except_preserves_wfh_except`).
///
/// Neither reads a field of a free or pending-free block, so pending objects
/// may point anywhere (into free blocks included).  Together, with the
/// free-list facts, the whole collection keeps `collection_shape_except`
/// (`cheney_collect_except_preserves_shape`).  The stop-the-world theorem
/// (`GC.Gen.CheneyPreservation.cheney_collect_preserves_collection_heap_shape`)
/// is its instance at `no_pending`.

module GC.Gen.CheneyExcept

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
module GenInv = GC.Gen.HeapInvariant

/// What a minor collection assumes of the major heap and the nursery for the
/// facts below (the promotion-side part of `collection_heap_shape`).
let promote_pre (minor: minor_state) (major: heap) (fp: U64.t) : prop =
  well_formed_heap_part1 major /\ well_formed_heap_part4 major /\
  AllocLemmas.fl_valid major fp heap_words /\
  AllocLemmas.fl_chain_terminates major fp heap_words /\
  chain_objects_blue major fp /\
  minor_infix_wf minor /\
  minor_wf minor

/// The stop-the-world collection is the instance with nothing pending.
val cheney_collect_spec_except_no_pending
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (cheney_collect_spec_except minor major fp roots no_pending ==
           cheney_collect_spec minor major fp roots)

/// ---------------------------------------------------------------------------
/// The not-freed objects across the two events
/// ---------------------------------------------------------------------------

/// The pointer update changes neither the walk nor any header, so it keeps
/// the not-freed objects and the pending set's admissibility.
val update_walk_not_freed
  (major: heap) (upd pf: obj_addr -> prop) (fwd: forwarding_map) (x: obj_addr)
  : Lemma (requires well_formed_heap_part1 major)
          (ensures not_freed (update_walk major upd fwd) pf x <==> not_freed major pf x)

val update_walk_preserves_pending_ok
  (major: heap) (upd pf: obj_addr -> prop) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\ pending_ok major pf)
          (ensures pending_ok (update_walk major upd fwd) pf)

/// Promotion keeps every not-freed object not freed.
val cheney_promote_keeps_not_freed
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (pf: obj_addr -> prop) (x: obj_addr)
  : Lemma (requires promote_pre minor major fp /\ not_freed major pf x)
          (ensures not_freed (cheney_promote minor major fp roots).major_final pf x)

/// The image of a promoted nursery object is not freed: it is a fresh block,
/// so it is not pending.
val cheney_promote_image_not_freed
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (pf: obj_addr -> prop) (v: U64.t) (x: obj_addr)
  : Lemma (requires promote_pre minor major fp /\ pending_ok major pf /\
                    Seq.mem v (minor_objects minor) /\
                    (cheney_promote minor major fp roots).fwd_map v == x)
          (ensures not_freed (cheney_promote minor major fp roots).major_final pf x)

/// A not-freed object after promotion was not freed before, or is the image
/// of a promoted nursery object.
val cheney_promote_not_freed_origin
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (pf: obj_addr -> prop) (x: obj_addr)
  : Lemma (requires promote_pre minor major fp /\
                    not_freed (cheney_promote minor major fp roots).major_final pf x)
          (ensures not_freed major pf x \/
                   (exists (v: U64.t). Seq.mem v (minor_objects minor) /\
                                  (cheney_promote minor major fp roots).fwd_map v == x))

/// Promotion keeps the pending set admissible: pending objects are untouched.
val cheney_promote_pending_ok
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (pf: obj_addr -> prop)
  : Lemma (requires promote_pre minor major fp /\ pending_ok major pf)
          (ensures pending_ok (cheney_promote minor major fp roots).major_final pf)

/// ---------------------------------------------------------------------------
/// Well-formedness except the pending objects, field by field
/// ---------------------------------------------------------------------------

/// Introduce parts 2 and 3 except the pending objects from a per-field closure
/// property of the not-freed objects.
val wfh_except_from_field_closure (g: heap) (pf: obj_addr -> prop)
  (field_closure: (src: obj_addr) -> (j: nat) ->
    Lemma (requires not_freed g pf src /\
                    fields_constrained g src /\
                    j < U64.v (wosize_of_object src g) /\
                    U64.v src + j * 8 + 8 <= heap_size)
          (ensures (let v = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
                    is_pointer v ==>
                    not_freed g pf (resolve_object (v <: obj_addr) g) /\
                    infix_addr_wf g (objects zero_addr g) (v <: obj_addr))))
  : Lemma (requires well_formed_heap_part1 g)
          (ensures well_formed_heap_part2_except g pf /\
                   well_formed_heap_part3_except g pf)

/// Eliminate parts 2 and 3 except the pending objects at a single field.
val wfh_except_field (g: heap) (pf: obj_addr -> prop) (src: obj_addr) (j: nat)
  : Lemma (requires well_formed_heap_except g pf /\ not_freed g pf src /\
                    fields_constrained g src /\
                    j < U64.v (wosize_of_object src g) /\
                    U64.v src + j * 8 + 8 <= heap_size /\
                    is_pointer (read_word g (U64.uint_to_t (U64.v src + j * 8))))
          (ensures (let v : obj_addr = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
                    not_freed g pf (resolve_object v g) /\
                    infix_addr_wf g (objects zero_addr g) v))

/// ---------------------------------------------------------------------------
/// Event 1: promotion
/// ---------------------------------------------------------------------------

/// Promotion keeps well-formedness except the pending objects.  An old
/// not-freed object's fields and headers are untouched; a promoted object's
/// fields are its nursery fields, which point at not-freed major objects
/// (`minor_major_fields_not_freed`) or into the nursery (not major pointers).
val cheney_promote_preserves_wfh_except
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (pf: obj_addr -> prop)
  : Lemma (requires promote_pre minor major fp /\
                    pending_ok major pf /\
                    well_formed_heap_except major pf /\
                    GenInv.minor_major_fields_not_freed minor major pf)
          (ensures well_formed_heap_except (cheney_promote minor major fp roots).major_final pf)

/// ---------------------------------------------------------------------------
/// Event 2: the pointer update
/// ---------------------------------------------------------------------------

/// Every forwarding target is a well-formed pointer into a not-freed object.
let fwd_targets_not_freed (g: heap) (pf: obj_addr -> prop) (fwd: forwarding_map) : prop =
  forall (v: U64.t). fwd v <> 0UL ==>
    U64.v (fwd v) >= U64.v mword /\
    U64.v (fwd v) < heap_size /\
    U64.v (fwd v) % U64.v mword == 0 /\
    not_freed g pf (resolve_object ((fwd v) <: obj_addr) g) /\
    infix_addr_wf g (objects zero_addr g) ((fwd v) <: obj_addr)

/// The update leaves the header of a field target alone: an ordinary target's
/// header is an object header, and an infix target's sits in a field of its
/// closure but can never look like a nursery pointer (`infix_tag` makes it odd).
val update_walk_frame_target_header
  (g: heap) (upd: obj_addr -> prop) (fwd: forwarding_map) (h: obj_addr)
  : Lemma
    (requires
      well_formed_heap_part1 g /\
      (~(is_infix h g) ==> Seq.mem h (objects zero_addr g)) /\
      (is_infix h g ==>
        (let w = U64.v (wosize_of_object h g) in
         let p = U64.v h - w * 8 in
         w >= 2 /\ p >= 8 /\ p < heap_size /\ p % 8 == 0 /\
         Seq.mem (U64.uint_to_t p <: obj_addr) (objects zero_addr g) /\
         w < U64.v (wosize_of_object (U64.uint_to_t p) g))))
    (ensures read_word (update_walk g upd fwd) (hd_address h) ==
             read_word g (hd_address h))

/// The pointer update keeps well-formedness except the pending objects: every
/// field it writes belongs to a not-freed object and receives a not-freed
/// target.
val update_pointers_except_preserves_wfh_except
  (g: heap) (pf: obj_addr -> prop) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_except g pf /\ fwd_targets_not_freed g pf fwd)
          (ensures well_formed_heap_except (update_pointers_except g pf fwd) pf)

/// Cheney's forwarding map points at the promoted objects (or interior
/// pointers into them), none of which is pending.
val cheney_promote_fwd_targets_not_freed
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (pf: obj_addr -> prop)
  : Lemma (requires promote_pre minor major fp /\ pending_ok major pf)
          (ensures (let prom = cheney_promote minor major fp roots in
                    fwd_targets_not_freed prom.major_final pf prom.fwd_map))

/// ---------------------------------------------------------------------------
/// The whole collection
/// ---------------------------------------------------------------------------

/// **The minor collection keeps its shape, except the objects pending free.**
/// For any pending set the caller vouches for (`collection_shape_except`), the
/// collection leaves a heap of the same shape for the same pending set, with an
/// empty nursery.
val cheney_collect_except_preserves_shape
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (pf: obj_addr -> prop)
  : Lemma (requires GenInv.collection_shape_except minor major fp pf)
          (ensures (let res = cheney_collect_spec_except minor major fp roots pf in
                    GenInv.collection_shape_except res.mc_minor res.mc_major res.mc_fp pf))
