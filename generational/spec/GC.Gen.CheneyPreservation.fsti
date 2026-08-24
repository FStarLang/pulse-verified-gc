/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyPreservation — Additional Cheney BFS preservation lemmas
/// ---------------------------------------------------------------------------
///
/// Separated from GC.Gen.Cheney to avoid Z3 context pollution: adding val
/// declarations to Cheney.fsti causes GC.Gen.Impl.Cheney.fst to fail verification.
/// The Pulse implementation imports this module explicitly for post-minor
/// heap-shape preservation facts.

module GC.Gen.CheneyPreservation

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

module AllocLemmas = GC.Spec.Allocator.Lemmas
module Mark = GC.Spec.Mark
module MarkBounded = GC.Spec.MarkBounded
module GenInv = GC.Gen.HeapInvariant
module FreeListShape = GC.Gen.FreeListShape

/// Cheney promotion preserves no_black_objects.
///
/// Promoted objects get white_bits headers; pre-existing objects' colors are
/// unchanged (alloc_spec and copy_fields only modify the allocated block and
/// free-list headers, never coloring an object black).
val cheney_promote_preserves_no_black
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    Mark.no_black_objects major /\
                    minor_infix_wf minor)
           (ensures (let res = cheney_promote minor major fp roots in
                     Mark.no_black_objects res.major_final))

val cheney_collect_preserves_no_black
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    Mark.no_black_objects major /\
                    minor_infix_wf minor)
          (ensures Mark.no_black_objects
            (cheney_collect_spec minor major fp roots).mc_major)

val cheney_collect_preserves_fp_pointer_or_zero
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires GenInv.collection_heap_shape minor major fp)
          (ensures FreeListShape.fp_pointer_or_zero
            (cheney_collect_spec minor major fp roots).mc_fp)

/// All gray/black objects are present in the major gray stack.
///
/// This is the color-stack conjunct of MajorGC.gc_precondition, named so
/// Cheney promotion and the post-promotion pointer update can preserve it
/// without forcing clients to reason about Cheney's result.
let gray_black_objects_on_stack (g: heap) (st: seq obj_addr) : prop =
  forall (obj: obj_addr).
    Seq.mem obj (objects zero_addr g) /\
    (is_gray obj g \/ is_black obj g) ==> Seq.mem obj st

val cheney_promote_preserves_gray_black_objects_on_stack
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (st: seq obj_addr)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    chain_objects_blue major fp /\
                    gray_black_objects_on_stack major st /\
                    minor_infix_wf minor)
          (ensures (let res = cheney_promote minor major fp roots in
                    gray_black_objects_on_stack res.major_final st))

val update_major_pointers_preserves_gray_black_objects_on_stack
  (major: heap) (fwd: forwarding_map) (st: seq obj_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    gray_black_objects_on_stack major st)
          (ensures gray_black_objects_on_stack (update_major_pointers major fwd) st)

val cheney_collect_preserves_gray_black_objects_on_stack
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (st: seq obj_addr)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    chain_objects_blue major fp /\
                    gray_black_objects_on_stack major st /\
                    minor_infix_wf minor)
          (ensures (let res = cheney_collect_spec minor major fp roots in
                    gray_black_objects_on_stack res.mc_major st))

val cheney_promote_preserves_no_scan_invariant
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    no_scan_invariant major /\
                    minor_no_scan_invariant minor /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor)
          (ensures no_scan_invariant (cheney_promote minor major fp roots).major_final)

val cheney_promote_preserves_blue_fields_closed
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor)
          (ensures blue_fields_closed (cheney_promote minor major fp roots).major_final)

val update_major_pointers_preserves_no_scan_invariant
  (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\
                    no_scan_invariant major)
          (ensures no_scan_invariant (update_major_pointers major fwd))

val cheney_collect_preserves_no_scan_invariant
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    no_scan_invariant major /\
                    minor_no_scan_invariant minor /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    chain_objects_blue major fp /\
                     minor_infix_wf minor)
          (ensures no_scan_invariant (cheney_collect_spec minor major fp roots).mc_major)

/// ---------------------------------------------------------------------------
/// Forwarding targets classification: in objects or infix
/// ---------------------------------------------------------------------------

/// Every non-zero forwarding target produced by cheney_promote is either
/// an object in the objects list (normal forwarding) or an infix sub-object
/// in the major heap (interior pointer with tag=249).
///
/// Proof sketch (BFS induction):
///   - Normal forwarding via cheney_forward_normal: alloc_spec puts the target
///     in objects (alloc_spec_obj_in_objects_part1). Subsequent allocs preserve
///     membership (cheney_forward_one_preserves_objects).
///   - Infix forwarding: target = parent_fwd + delta. After promote_object
///     copies parent's fields, the infix header at (parent_fwd + delta - 8)
///     has tag=249. Frame: subsequent allocs write to disjoint memory
///     (promote_object_frame_old_field), preserving the infix header.
let fwd_valid_or_infix (fwd: forwarding_map) (g: heap) : prop =
  forall (x: U64.t). fwd x <> 0UL ==>
    (U64.v (fwd x) >= U64.v mword /\
     U64.v (fwd x) < heap_size /\
     U64.v (fwd x) % U64.v mword == 0 /\
     (Seq.mem ((fwd x) <: obj_addr) (objects zero_addr g) \/
      is_infix (fwd x) g))

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
/// Frame property: cheney_promote preserves fields of pre-existing non-blue objects
/// ---------------------------------------------------------------------------

/// For any non-blue object in the original major heap, its body fields are
/// unchanged after cheney_promote. This is because:
///   - Cheney BFS only writes to newly allocated regions (from the free-list)
///   - Pre-existing non-blue objects are not on the free-list
///   - promote_object_frame_old_field gives per-step field preservation
///   - BFS induction carries this through all promotion steps
val cheney_promote_frame_old_fields
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr) (j: nat)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    chain_objects_blue major fp /\
                    Seq.mem obj (objects zero_addr major) /\
                    is_blue obj major = false /\
                    j < U64.v (wosize_of_object obj major) /\
                    U64.v obj + j * 8 + 8 <= heap_size /\
                    minor_infix_wf minor)
          (ensures (let res = cheney_promote minor major fp roots in
                    read_word res.major_final (U64.uint_to_t (U64.v obj + j * 8))
                    == read_word major (U64.uint_to_t (U64.v obj + j * 8))))

/// ---------------------------------------------------------------------------
/// Header frame: cheney_promote preserves headers of pre-existing non-blue objects
/// ---------------------------------------------------------------------------

/// For any non-blue object in the original major heap, its header is unchanged
/// after cheney_promote. This is because cheney BFS only allocates from the
/// free-list chain (blue objects), never overwriting pre-existing non-blue headers.
/// Combined with frame_old_fields, this gives complete preservation of
/// pre-existing non-blue objects through promotion.
val cheney_promote_frame_old_header
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    chain_objects_blue major fp /\
                    Seq.mem obj (objects zero_addr major) /\
                    is_blue obj major = false /\
                    minor_infix_wf minor)
          (ensures (let res = cheney_promote minor major fp roots in
                    read_word res.major_final (hd_address obj)
                    == read_word major (hd_address obj)))

/// ---------------------------------------------------------------------------
/// Injectivity: non-infix forwarding targets are pairwise distinct
/// ---------------------------------------------------------------------------

/// The forwarding map is injective on non-infix targets: two different
/// source addresses cannot be forwarded to the same non-infix destination.
/// Proof: each successful cheney_forward_normal allocates from the free-list,
/// which advances after each allocation. From chain_objects_blue, existing
/// (non-blue) targets avoid the chain, hence differ from the next allocation
/// (which IS a chain node). By induction, all normal targets are distinct.
let fwd_normal_injective (fwd: forwarding_map) (g: heap) : prop =
  forall (x y: U64.t). fwd x <> 0UL /\ fwd y <> 0UL /\
    is_val_addr (fwd x) /\ is_val_addr (fwd y) /\
    is_infix (fwd x) g = false /\ is_infix (fwd y) g = false /\
    fwd x = fwd y ==> x = y

/// Non-infix forwarding targets produced by Cheney are normal objects, not
/// blue free-list nodes.  update_promoted_iter relies on this to agree with
/// update_major_pointers, which skips blue objects.
let fwd_targets_not_blue (fwd: forwarding_map) (g: heap) : prop =
  forall (x: U64.t). fwd x <> 0UL /\ is_val_addr (fwd x) /\
    is_infix (fwd x) g = false ==>
    Seq.mem ((fwd x) <: obj_addr) (objects zero_addr g) /\
    is_blue ((fwd x) <: obj_addr) g = false

/// Normal forwarding targets are freshly allocated from the old free-list
/// region, hence cannot equal a pre-existing non-blue major object.
let fwd_normal_targets_disjoint_from_old_nonblue
  (fwd: forwarding_map) (g_final: heap) (major0: heap) : prop =
  forall (x: U64.t) (y: obj_addr).
    fwd x <> 0UL /\
    is_val_addr (fwd x) /\
    is_infix (fwd x) g_final = false /\
    Seq.mem y (objects zero_addr major0) /\
    is_blue y major0 = false ==>
    fwd x <> y

val cheney_promote_fwd_normal_injective
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
           (ensures fwd_normal_injective (cheney_promote minor major fp roots).fwd_map
                                         (cheney_promote minor major fp roots).major_final)

val cheney_promote_fwd_targets_not_blue
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_targets_not_blue (cheney_promote minor major fp roots).fwd_map
                                        (cheney_promote minor major fp roots).major_final)

val cheney_promote_fwd_normal_targets_disjoint_from_old_nonblue
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_normal_targets_disjoint_from_old_nonblue
                     (cheney_promote minor major fp roots).fwd_map
                     (cheney_promote minor major fp roots).major_final
                     major)

/// ---------------------------------------------------------------------------
/// Non-blue origin: objects that become non-blue during promotion are fwd targets
/// ---------------------------------------------------------------------------

/// If an object is non-blue in major_final but was NOT a pre-existing non-blue
/// object (either wasn't in objects(major_pre) or was blue there), then it must
/// be a forwarding target — i.e., it was allocated by cheney_promote to hold
/// a promoted minor object.
///
/// Proof sketch (BFS induction): promote_object_frame_old_header_derived shows
/// only the allocated object's header changes per step. Objects whose headers
/// don't change retain their color. So: non-blue in final ∧ not-pre-nonblue → allocated → fwd target.
val cheney_promote_nonblue_origin
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
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

val cheney_collect_preserves_wfh_from_shape
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires GenInv.collection_heap_shape minor major fp)
    (ensures well_formed_heap
      (cheney_collect_spec minor major fp roots).mc_major)

val cheney_collect_preserves_no_pointer_to_blue
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires GenInv.collection_heap_shape minor major fp /\
              well_formed_heap (cheney_collect_spec minor major fp roots).mc_major)
    (ensures Mark.no_pointer_to_blue
      (cheney_collect_spec minor major fp roots).mc_major)

val cheney_collect_preserves_collection_heap_shape
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires GenInv.collection_heap_shape minor major fp)
          (ensures GenInv.collection_heap_shape
            (cheney_collect_spec minor major fp roots).mc_minor
            (cheney_collect_spec minor major fp roots).mc_major
            (cheney_collect_spec minor major fp roots).mc_fp)
