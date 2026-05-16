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
