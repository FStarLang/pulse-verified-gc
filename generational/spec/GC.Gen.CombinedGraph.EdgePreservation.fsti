/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph.EdgePreservation — Edge preservation through GC
/// ---------------------------------------------------------------------------
///
/// Proves that edges in the pre-GC combined graph are preserved in the
/// post-GC major-heap graph, after applying gc_morphism to both endpoints.
///
/// Structure: modular lemmas that compose into full edge preservation.
///   Step 1: major_field_through_minor_collect (promotion + pointer update)
///   Step 2: compose with mark_preserves_get_field + sweep survival (Pillar 5)
///
/// Cases:
///   Case 4 (major→major): field unchanged through promotion + update + mark + sweep
///   Case 3 (major→minor): field rewritten by update_major_pointers to fwd(dst)
///   Case 1 (minor→minor): promoted field rewritten via field_correspondence
///   Case 2 (minor→major): promoted field preserved verbatim

module GC.Gen.CombinedGraph.EdgePreservation

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Spec.HeapModel
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Reachability
open GC.Gen.Remembered
open GC.Gen.Promote
open GC.Gen.CombinedGraph

module HeapGraph = GC.Spec.HeapGraph
module AllocLemmas = GC.Spec.Allocator.Lemmas

/// ---------------------------------------------------------------------------
/// Helper: major object addresses satisfy is_pointer_field
/// ---------------------------------------------------------------------------

/// Objects in `objects zero_addr major` have addresses >= zero_addr + mword,
/// which is the threshold for is_pointer_field. Combined with is_val_addr
/// (implies < heap_size and % 8 == 0), this gives is_pointer_field.
val major_object_is_pointer_field (major: heap) (dst: obj_addr)
  : Lemma (requires Seq.mem dst (objects zero_addr major))
          (ensures HeapGraph.is_pointer_field dst)

/// ---------------------------------------------------------------------------
/// Step 1: Field preserved through minor collection (Case 4 — major→major)
/// ---------------------------------------------------------------------------

/// For a pre-existing major object `src` that avoids the free list,
/// its field value `dst` is unchanged after the full minor_collect_spec
/// (promote_all + update_major_pointers), provided `dst` is not a
/// minor pointer with a non-zero forwarding entry.
///
/// Composes: promote_all_read_other + update_major_pointers_field_effect
val major_field_through_minor_collect
  (ms: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: obj_addr) (i: nat)
  : Lemma
    (requires
      // Object and field membership
      Seq.mem src (objects zero_addr major) /\
      i < U64.v (wosize_of_object src major) /\
      ~(is_no_scan src major) /\
      is_blue src major = false /\
      U64.v src + i * 8 + 8 <= heap_size /\
      (U64.v src + i * 8) % 8 == 0 /\
      // The field value is not a rewritable minor pointer
      (let live_set = live_set_of ms major roots in
       let prom_res = promote_all_spec ms major fp live_set in
       let field_val = read_word major (U64.uint_to_t (U64.v src + i * 8)) in
       ~(is_minor_pointer field_val /\ prom_res.fwd_map field_val <> 0UL)) /\
      // Allocator preconditions
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      AllocLemmas.chain_avoids major fp src (heap_size / U64.v mword) = true /\
      // Intermediate heap facts (provable from well_formed_heap + promotion frame)
      // These follow from promote_all preserving headers of pre-existing objects.
      (let live_set = live_set_of ms major roots in
       let prom_res = promote_all_spec ms major fp live_set in
       Seq.mem src (objects zero_addr prom_res.major_final) /\
       wosize_of_object src prom_res.major_final == wosize_of_object src major /\
       is_blue src prom_res.major_final = false /\
       is_no_scan src prom_res.major_final = false))
    (ensures
      (let minor_res = minor_collect_spec ms major fp roots in
       let field_addr = U64.uint_to_t (U64.v src + i * 8) in
       read_word minor_res.mc_major field_addr ==
         read_word major field_addr))

/// ---------------------------------------------------------------------------
/// Step 1b: Field rewritten through minor collection (Case 3 — major→minor)
/// ---------------------------------------------------------------------------

/// When a major object `src` has a field pointing to a minor object `dst`
/// that gets promoted (fwd dst <> 0UL), the field is rewritten to fwd(dst).
/// This is the "pointer forwarding" case: after GC, the major heap references
/// the promoted copy of the minor object.
///
/// Composes: promote_all_read_other + update_major_pointers_field_effect
val major_field_forwarded_by_minor_collect
  (ms: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: obj_addr) (i: nat)
  : Lemma
    (requires
      // Object and field membership
      Seq.mem src (objects zero_addr major) /\
      i < U64.v (wosize_of_object src major) /\
      ~(is_no_scan src major) /\
      is_blue src major = false /\
      U64.v src + i * 8 + 8 <= heap_size /\
      (U64.v src + i * 8) % 8 == 0 /\
      // The field value IS a minor pointer that gets forwarded
      (let live_set = live_set_of ms major roots in
       let prom_res = promote_all_spec ms major fp live_set in
       let field_val = read_word major (U64.uint_to_t (U64.v src + i * 8)) in
       is_minor_pointer field_val /\ prom_res.fwd_map field_val <> 0UL) /\
      // Allocator preconditions
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      AllocLemmas.chain_avoids major fp src (heap_size / U64.v mword) = true /\
      // Intermediate heap facts
      (let live_set = live_set_of ms major roots in
       let prom_res = promote_all_spec ms major fp live_set in
       Seq.mem src (objects zero_addr prom_res.major_final) /\
       wosize_of_object src prom_res.major_final == wosize_of_object src major /\
       is_blue src prom_res.major_final = false /\
       is_no_scan src prom_res.major_final = false))
    (ensures
      (let live_set = live_set_of ms major roots in
       let prom_res = promote_all_spec ms major fp live_set in
       let minor_res = minor_collect_spec ms major fp roots in
       let field_addr = U64.uint_to_t (U64.v src + i * 8) in
       let old_val = read_word major field_addr in
       read_word minor_res.mc_major field_addr == prom_res.fwd_map old_val))

/// ---------------------------------------------------------------------------
/// Step 1c: Promoted object field preservation (Cases 1 & 2)
/// ---------------------------------------------------------------------------

/// For a promoted minor object `obj` (with `fwd obj <> 0UL`), field `j` of
/// the promoted copy `fwd obj` in `mc_major` equals:
/// - `fwd(minor_val)` if `minor_val` is a minor pointer with `fwd(minor_val) <> 0UL` (Case 1)
/// - `minor_val` otherwise (Case 2: major pointer or un-promoted minor pointer)
///
/// This follows directly from field_correspondence (assumed as precondition).
/// Proving field_correspondence holds is a separate concern — it requires
/// composing promote_all_preserves_fields + update_major_pointers_field_effect
/// on the promoted copy's fields.
val promoted_field_through_minor_collect
  (ms: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: U64.t) (j: nat)
  : Lemma
    (requires
      (let live_set = live_set_of ms major roots in
       let prom_res = promote_all_spec ms major fp live_set in
       let mc = minor_collect_spec ms major fp roots in
       // obj is in the live set and gets promoted
       Seq.mem obj live_set /\ prom_res.fwd_map obj <> 0UL /\
       // Field within bounds
       j < minor_wosize ms obj /\
       U64.v (prom_res.fwd_map obj) + j * 8 + 8 <= heap_size /\
       U64.v (prom_res.fwd_map obj) % 8 == 0 /\
       // field_correspondence holds (proven separately)
       GC.Gen.Correctness.field_correspondence ms major mc.mc_major prom_res.fwd_map roots))
    (ensures
      (let live_set = live_set_of ms major roots in
       let prom_res = promote_all_spec ms major fp live_set in
       let mc = minor_collect_spec ms major fp roots in
       let new_addr = prom_res.fwd_map obj in
       let minor_val = minor_read_field ms obj j in
       let field_addr_v = U64.v new_addr + j * 8 in
       field_addr_v + 8 <= heap_size /\ field_addr_v % 8 == 0 /\
       (let major_val = read_word mc.mc_major (U64.uint_to_t field_addr_v <: hp_addr) in
        // Case 1: minor→minor → field becomes fwd(minor_val)
        (is_minor_pointer minor_val /\ prom_res.fwd_map minor_val <> 0UL ==>
          major_val == prom_res.fwd_map minor_val) /\
        // Case 2: minor→major → field preserved
        (~(is_minor_pointer minor_val /\ prom_res.fwd_map minor_val <> 0UL) ==>
          major_val == minor_val))))
