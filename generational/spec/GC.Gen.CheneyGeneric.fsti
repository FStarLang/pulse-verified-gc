/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyGeneric -- the minor collection keeps its shape given what counts as free
/// ---------------------------------------------------------------------------
///
/// `free` says which major blocks count as free (`GC.Spec.Fields.free_def`).
/// The theorems below hold for any admissible definition of free
/// (`free_def_ok`: blue blocks are free, and what is free is read off the walk
/// and the headers) under which the blocks the allocator creates are not free
/// (`GC.Gen.Promote.allocations_not_free`); they derive that no promoted copy
/// is free.
///
/// In major-heap terms a minor collection is two kinds of event, and each
/// keeps `well_formed_heap_with free`:
///
/// * **promotion** (`cheney_promote`: allocation from the free list plus
///   `copy_fields`) adds new non-free blocks, the images of the promoted
///   nursery objects, and writes nothing else
///   (`cheney_promote_preserves_wf_with`);
/// * **the pointer update** (`update_pointers_with`) writes fields of non-free
///   blocks only, each one either unchanged or rewritten to a forwarding
///   target that is itself not free
///   (`update_pointers_with_preserves_wf`).
///
/// Neither reads a field of a free block, so such a block may
/// point anywhere (into free blocks included).  Together, with the free-list
/// facts, the whole collection keeps `collection_shape_with`
/// (`cheney_collect_with_preserves_shape`).  The stop-the-world theorem
/// (`GC.Gen.CheneyPreservation.cheney_collect_preserves_collection_heap_shape`)
/// is its instance at `free_stw`.

module GC.Gen.CheneyGeneric

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

/// The stop-the-world collection is the `free_stw` instance.
val cheney_collect_spec_with_stw
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (cheney_collect_spec_with Idle free_stw minor major fp roots ==
           cheney_collect_spec minor major fp roots)

/// ---------------------------------------------------------------------------
/// What is free across the two events
/// ---------------------------------------------------------------------------

/// The pointer update changes neither the walk nor any header, so it keeps
/// what is free.
val update_walk_keeps_in_use
  (free: free_def) (major: heap) (upd: obj_addr -> GTot bool) (fwd: forwarding_map) (x: obj_addr)
  : Lemma (requires free_def_ok free /\ blocks_fit major)
          (ensures in_use free (update_walk major upd fwd) x == in_use free major x)

/// Promotion keeps every non-free block non-free.
val cheney_promote_keeps_in_use (ph: gc_phase)
  (free: free_def) (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (x: obj_addr)
  : Lemma (requires free_def_ok free /\ promote_pre minor major fp /\ in_use free major x)
          (ensures in_use free (cheney_promote ph minor major fp roots).major_final x)

/// The image of a promoted nursery object is not free: it is a block the
/// allocator created (`allocations_not_free`), and nothing rewrites its
/// header afterwards.
val cheney_promote_image_not_free (ph: gc_phase)
  (free: free_def) (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (m: U64.t) (x: obj_addr)
  : Lemma (requires free_def_ok free /\ allocations_not_free ph free /\ promote_pre minor major fp /\
                    Seq.mem m (minor_objects minor) /\
                    (cheney_promote ph minor major fp roots).fwd_map m == x)
          (ensures in_use free (cheney_promote ph minor major fp roots).major_final x)

/// A non-free block after promotion was one before, or is the image of
/// a promoted nursery object.
val cheney_promote_in_use_origin (ph: gc_phase)
  (free: free_def) (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (x: obj_addr)
  : Lemma (requires free_def_ok free /\ promote_pre minor major fp /\
                    in_use free (cheney_promote ph minor major fp roots).major_final x)
          (ensures in_use free major x \/
                   (exists (m: U64.t). Seq.mem m (minor_objects minor) /\
                                  (cheney_promote ph minor major fp roots).fwd_map m == x))

/// ---------------------------------------------------------------------------
/// Event 1: promotion
/// ---------------------------------------------------------------------------

/// Promotion keeps well-formedness given what counts as free.  An old block's fields and
/// header are untouched; a promoted object's fields are its nursery fields,
/// which point to non-free blocks (`minor_major_fields_not_free`) or into the
/// nursery (not major pointers).
val cheney_promote_preserves_wf_with (ph: gc_phase)
  (free: free_def) (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t)
  : Lemma (requires free_def_ok free /\ promote_pre minor major fp /\
                    well_formed_heap_with free major /\
                    GenInv.minor_major_fields_not_free free minor major)
          (ensures well_formed_heap_with free (cheney_promote ph minor major fp roots).major_final)

/// ---------------------------------------------------------------------------
/// Event 2: the pointer update
/// ---------------------------------------------------------------------------

/// Every forwarding target is a well-formed pointer to a non-free block.
let fwd_targets_not_free (free: free_def) (g: heap) (fwd: forwarding_map) : prop =
  forall (m: U64.t). fwd m <> 0UL ==>
    U64.v (fwd m) >= U64.v mword /\
    U64.v (fwd m) < heap_size /\
    U64.v (fwd m) % U64.v mword == 0 /\
    in_use free g (resolve_object ((fwd m) <: obj_addr) g) /\
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

/// The pointer update keeps well-formedness given what counts as free: every field it
/// writes belongs to a non-free block and receives a non-free target.
val update_pointers_with_preserves_wf
  (free: free_def) (g: heap) (fwd: forwarding_map)
  : Lemma (requires free_def_ok free /\ well_formed_heap_with free g /\ fwd_targets_not_free free g fwd)
          (ensures well_formed_heap_with free (update_pointers_with free g fwd))

/// Cheney's forwarding map points at the promoted objects (or interior
/// pointers into them), all of them not free.
val cheney_promote_fwd_targets_not_free (ph: gc_phase)
  (free: free_def) (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t)
  : Lemma (requires free_def_ok free /\ allocations_not_free ph free /\ promote_pre minor major fp)
          (ensures (let prom = cheney_promote ph minor major fp roots in
                    fwd_targets_not_free free prom.major_final prom.fwd_map))

/// ---------------------------------------------------------------------------
/// The whole collection
/// ---------------------------------------------------------------------------

/// **The minor collection keeps its shape given what counts as free.**  For
/// any definition of free the caller vouches for (`collection_shape_with`,
/// which includes `allocations_not_free`), the collection leaves a heap of the same shape with the same definition of free,
/// with an empty nursery.
val cheney_collect_with_preserves_shape (ph: gc_phase)
  (free: free_def) (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t)
  : Lemma (requires GenInv.collection_shape_with ph free minor major fp)
          (ensures (let res = cheney_collect_spec_with ph free minor major fp roots in
                    GenInv.collection_shape_with ph free res.mc_minor res.mc_major res.mc_fp))
