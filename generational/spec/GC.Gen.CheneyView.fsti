/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyView -- the minor collection keeps its shape on a view
/// ---------------------------------------------------------------------------
///
/// `v` is a view of the major heap: the blocks the invariant counts as objects
/// (`GC.Spec.Fields.view`).  The theorems below hold for any admissible view
/// (`view_ok`: it counts only allocated blocks and is read off the walk and
/// the headers) that counts the blocks promotion creates
/// (`promotion_in_view`).
///
/// In major-heap terms a minor collection is two kinds of event, and each
/// keeps `well_formed_view v`:
///
/// * **promotion** (`cheney_promote`: allocation from the free list plus
///   `copy_fields`) adds new blocks to the view, the images of the promoted
///   nursery objects, and writes nothing else
///   (`cheney_promote_preserves_wf_view`);
/// * **the pointer update** (`update_pointers_view`) writes fields of blocks
///   of the view only, each one either unchanged or rewritten to a forwarding
///   target that is itself in the view
///   (`update_pointers_view_preserves_wf_view`).
///
/// Neither reads a field of a block outside the view, so such a block may
/// point anywhere (into free blocks included).  Together, with the free-list
/// facts, the whole collection keeps `collection_shape_view`
/// (`cheney_collect_view_preserves_shape`).  The stop-the-world theorem
/// (`GC.Gen.CheneyPreservation.cheney_collect_preserves_collection_heap_shape`)
/// is its instance at `allocated`.

module GC.Gen.CheneyView

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
  blocks_fit major /\ no_infix_block major /\
  AllocLemmas.fl_valid major fp heap_words /\
  AllocLemmas.fl_chain_terminates major fp heap_words /\
  chain_objects_blue major fp /\
  minor_infix_wf minor /\
  minor_wf minor

/// The blocks promotion creates are in the view.
let promotion_in_view (v: view) (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) : prop =
  fresh_in_view v major (cheney_promote minor major fp roots).major_final

val allocated_promotion_in_view
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (promotion_in_view allocated minor major fp roots)

/// The stop-the-world collection is the `allocated` instance.
val cheney_collect_spec_view_allocated
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (cheney_collect_spec_view allocated minor major fp roots ==
           cheney_collect_spec minor major fp roots)

/// ---------------------------------------------------------------------------
/// The view across the two events
/// ---------------------------------------------------------------------------

/// The pointer update changes neither the walk nor any header, so it keeps
/// the view.
val update_walk_keeps_view
  (v: view) (major: heap) (upd: obj_addr -> GTot bool) (fwd: forwarding_map) (x: obj_addr)
  : Lemma (requires view_ok v /\ blocks_fit major)
          (ensures v (update_walk major upd fwd) x == v major x)

/// Promotion keeps every block of the view in it.
val cheney_promote_keeps_view
  (v: view) (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (x: obj_addr)
  : Lemma (requires view_ok v /\ promote_pre minor major fp /\ v major x)
          (ensures v (cheney_promote minor major fp roots).major_final x)

/// The image of a promoted nursery object is in the view: it is a fresh block.
val cheney_promote_image_in_view
  (v: view) (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (m: U64.t) (x: obj_addr)
  : Lemma (requires promote_pre minor major fp /\ promotion_in_view v minor major fp roots /\
                    Seq.mem m (minor_objects minor) /\
                    (cheney_promote minor major fp roots).fwd_map m == x)
          (ensures v (cheney_promote minor major fp roots).major_final x)

/// A block of the view after promotion was in it before, or is the image of
/// a promoted nursery object.
val cheney_promote_view_origin
  (v: view) (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (x: obj_addr)
  : Lemma (requires view_ok v /\ promote_pre minor major fp /\
                    v (cheney_promote minor major fp roots).major_final x)
          (ensures v major x \/
                   (exists (m: U64.t). Seq.mem m (minor_objects minor) /\
                                  (cheney_promote minor major fp roots).fwd_map m == x))

/// The pointer clauses at a single field.
val wf_view_field (v: view) (g: heap) (src: obj_addr) (j: nat)
  : Lemma (requires view_ok v /\ well_formed_view v g /\ v g src /\ ~(is_no_scan src g) /\
                    j < U64.v (wosize_of_object src g) /\
                    U64.v src + j * 8 + 8 <= heap_size /\
                    is_pointer (read_word g (U64.uint_to_t (U64.v src + j * 8))))
          (ensures (let w : obj_addr = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
                    v g (resolve_object w g) /\
                    infix_addr_wf g (objects zero_addr g) w))

/// ---------------------------------------------------------------------------
/// Event 1: promotion
/// ---------------------------------------------------------------------------

/// Promotion keeps well-formedness on the view.  An old block's fields and
/// header are untouched; a promoted object's fields are its nursery fields,
/// which point into the view (`minor_major_fields_in_view`) or into the
/// nursery (not major pointers).
val cheney_promote_preserves_wf_view
  (v: view) (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t)
  : Lemma (requires view_ok v /\ promote_pre minor major fp /\
                    well_formed_view v major /\
                    GenInv.minor_major_fields_in_view v minor major)
          (ensures well_formed_view v (cheney_promote minor major fp roots).major_final)

/// ---------------------------------------------------------------------------
/// Event 2: the pointer update
/// ---------------------------------------------------------------------------

/// Every forwarding target is a well-formed pointer into the view.
let fwd_targets_in_view (v: view) (g: heap) (fwd: forwarding_map) : prop =
  forall (m: U64.t). fwd m <> 0UL ==>
    U64.v (fwd m) >= U64.v mword /\
    U64.v (fwd m) < heap_size /\
    U64.v (fwd m) % U64.v mword == 0 /\
    v g (resolve_object ((fwd m) <: obj_addr) g) /\
    infix_addr_wf g (objects zero_addr g) ((fwd m) <: obj_addr)

/// The update leaves the header of a field target alone: an ordinary target's
/// header is an object header, and an infix target's sits in a field of its
/// closure but can never look like a nursery pointer (`infix_tag` makes it odd).
val update_walk_frame_target_header
  (g: heap) (upd: obj_addr -> GTot bool) (fwd: forwarding_map) (h: obj_addr)
  : Lemma
    (requires
      blocks_fit g /\
      (~(is_infix h g) ==> Seq.mem h (objects zero_addr g)) /\
      (is_infix h g ==>
        (let w = U64.v (wosize_of_object h g) in
         let p = U64.v h - w * 8 in
         w >= 2 /\ p >= 8 /\ p < heap_size /\ p % 8 == 0 /\
         Seq.mem (U64.uint_to_t p <: obj_addr) (objects zero_addr g) /\
         w < U64.v (wosize_of_object (U64.uint_to_t p) g))))
    (ensures read_word (update_walk g upd fwd) (hd_address h) ==
             read_word g (hd_address h))

/// The pointer update keeps well-formedness on the view: every field it
/// writes belongs to a block of the view and receives a target in the view.
val update_pointers_view_preserves_wf_view
  (v: view) (g: heap) (fwd: forwarding_map)
  : Lemma (requires view_ok v /\ well_formed_view v g /\ fwd_targets_in_view v g fwd)
          (ensures well_formed_view v (update_pointers_view v g fwd))

/// Cheney's forwarding map points at the promoted objects (or interior
/// pointers into them), all of them in the view.
val cheney_promote_fwd_targets_in_view
  (v: view) (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t)
  : Lemma (requires promote_pre minor major fp /\ promotion_in_view v minor major fp roots)
          (ensures (let prom = cheney_promote minor major fp roots in
                    fwd_targets_in_view v prom.major_final prom.fwd_map))

/// ---------------------------------------------------------------------------
/// The whole collection
/// ---------------------------------------------------------------------------

/// **The minor collection keeps its shape on a view.**  For any view the
/// caller vouches for (`collection_shape_view`) that counts the promoted
/// blocks, the collection leaves a heap of the same shape on the same view,
/// with an empty nursery.
val cheney_collect_view_preserves_shape
  (v: view) (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t)
  : Lemma (requires GenInv.collection_shape_view v minor major fp /\
                    promotion_in_view v minor major fp roots)
          (ensures (let res = cheney_collect_spec_view v minor major fp roots in
                    GenInv.collection_shape_view v res.mc_minor res.mc_major res.mc_fp))
