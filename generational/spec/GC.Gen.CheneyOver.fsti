/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyOver -- the minor collection keeps its shape over a live set
/// ---------------------------------------------------------------------------
///
/// In major-heap terms a minor collection is two kinds of event, and each
/// keeps `well_formed_heap_over` for the live set it updates:
///
/// * **promotion** (`cheney_promote`: allocation from the free list plus
///   `copy_fields`) adds new live objects, the images of the promoted nursery
///   objects, and writes nothing else: the live set grows to
///   `promoted_live minor live fwd` (`cheney_promote_preserves_wfh_over`);
/// * **the pointer update** (`update_live_pointers`) writes fields of live
///   objects only, each one either unchanged or rewritten to a forwarding
///   target that is itself live (`update_live_pointers_preserves_wfh_over`).
///
/// Neither reads a field of a non-live block, so garbage may point anywhere
/// (into free blocks included).  Together, with the free-list facts, the whole
/// collection keeps `collection_shape_over` for the post-promotion live set
/// (`cheney_collect_over_preserves_shape`).  The stop-the-world theorem
/// (`GC.Gen.CheneyPreservation.cheney_collect_preserves_collection_heap_shape`)
/// is its instance at `idle_live`.

module GC.Gen.CheneyOver

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
module CL = GC.Gen.CheneyLive

/// ---------------------------------------------------------------------------
/// Well-formedness over a live set, field by field
/// ---------------------------------------------------------------------------

/// Introduce parts 2 and 3 over a live set from a per-field closure property
/// of the live objects.
val wfh_over_from_field_closure (g: heap) (live: obj_addr -> prop)
  (field_closure: (src: obj_addr) -> (j: nat) ->
    Lemma (requires live src /\ Seq.mem src (objects zero_addr g) /\
                    fields_constrained g src /\
                    j < U64.v (wosize_of_object src g) /\
                    U64.v src + j * 8 + 8 <= heap_size)
          (ensures (let v = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
                    is_pointer v ==>
                    live (resolve_object (v <: obj_addr) g) /\
                    infix_addr_wf g (objects zero_addr g) (v <: obj_addr))))
  : Lemma (requires well_formed_heap_part1 g /\ live_ok g live)
          (ensures well_formed_heap_part2_over g live /\
                   well_formed_heap_part3_over g live)

/// Eliminate parts 2 and 3 over a live set at a single field.
val wfh_over_field (g: heap) (live: obj_addr -> prop) (src: obj_addr) (j: nat)
  : Lemma (requires well_formed_heap_over g live /\ live_ok g live /\ live src /\
                    fields_constrained g src /\
                    j < U64.v (wosize_of_object src g) /\
                    U64.v src + j * 8 + 8 <= heap_size /\
                    is_pointer (read_word g (U64.uint_to_t (U64.v src + j * 8))))
          (ensures (let v : obj_addr = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
                    live (resolve_object v g) /\
                    infix_addr_wf g (objects zero_addr g) v))

/// ---------------------------------------------------------------------------
/// Event 1: promotion
/// ---------------------------------------------------------------------------

/// Promotion keeps well-formedness over the live set, extended with the
/// promoted objects.  An old live object's fields and headers are untouched; a
/// promoted object's fields are its nursery fields, which point at live major
/// objects (`minor_major_fields_live`) or into the nursery (not major
/// pointers).
val cheney_promote_preserves_wfh_over
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (live: obj_addr -> prop)
  : Lemma (requires CL.promote_pre minor major fp /\
                    live_ok major live /\
                    well_formed_heap_over major live /\
                    GenInv.minor_major_fields_live minor live)
          (ensures (let prom = cheney_promote minor major fp roots in
                    well_formed_heap_over prom.major_final
                      (promoted_live minor live prom.fwd_map)))

/// ---------------------------------------------------------------------------
/// Event 2: the pointer update over a live set
/// ---------------------------------------------------------------------------

/// Every forwarding target is a well-formed pointer into a live object.
let fwd_targets_live (g: heap) (live: obj_addr -> prop) (fwd: forwarding_map) : prop =
  forall (v: U64.t). fwd v <> 0UL ==>
    U64.v (fwd v) >= U64.v mword /\
    U64.v (fwd v) < heap_size /\
    U64.v (fwd v) % U64.v mword == 0 /\
    live (resolve_object ((fwd v) <: obj_addr) g) /\
    infix_addr_wf g (objects zero_addr g) ((fwd v) <: obj_addr)

/// The update leaves the header of a field target alone: an ordinary target's
/// header is an object header, and an infix target's sits in a field of its
/// closure but can never look like a nursery pointer (`infix_tag` makes it odd).
val update_live_pointers_frame_target_header
  (g: heap) (live: obj_addr -> prop) (fwd: forwarding_map) (h: obj_addr)
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
    (ensures read_word (update_live_pointers g live fwd) (hd_address h) ==
             read_word g (hd_address h))

/// The pointer update keeps well-formedness over the live set it walks: every
/// field it writes belongs to a live object and receives a live target.
val update_live_pointers_preserves_wfh_over
  (g: heap) (live: obj_addr -> prop) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_over g live /\ live_ok g live /\
                    fwd_targets_live g live fwd)
          (ensures well_formed_heap_over (update_live_pointers g live fwd) live)

/// Cheney's forwarding map points at the promoted objects (or interior
/// pointers into them), all of which are in the post-promotion live set.
val cheney_promote_fwd_targets_live
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (live: obj_addr -> prop)
  : Lemma (requires CL.promote_pre minor major fp)
          (ensures (let prom = cheney_promote minor major fp roots in
                    fwd_targets_live prom.major_final
                      (promoted_live minor live prom.fwd_map) prom.fwd_map))

/// ---------------------------------------------------------------------------
/// The whole collection
/// ---------------------------------------------------------------------------

/// **The minor collection keeps its shape over a live set.**  For any live set
/// the caller vouches for (`collection_shape_over`), the collection over that
/// set leaves a heap of the same shape for the live set extended with the
/// promoted objects, with an empty nursery.
val cheney_collect_over_preserves_shape
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (live: obj_addr -> prop)
  : Lemma (requires GenInv.collection_shape_over minor major fp live)
          (ensures (let res = cheney_collect_spec_over minor major fp roots live in
                    let prom = cheney_promote minor major fp roots in
                    GenInv.collection_shape_over res.mc_minor res.mc_major res.mc_fp
                      (promoted_live minor live prom.fwd_map)))
