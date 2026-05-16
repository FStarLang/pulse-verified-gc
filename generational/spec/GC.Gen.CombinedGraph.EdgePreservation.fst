/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph.EdgePreservation — Implementation
/// ---------------------------------------------------------------------------

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
module PromFields = GC.Gen.PromoteUpdate.PromoteFields
module PromField = GC.Gen.PromoteUpdate.Field

/// ---------------------------------------------------------------------------
/// Helper: major object addresses satisfy is_pointer_field
/// ---------------------------------------------------------------------------

/// Objects enumerated from zero_addr have addr >= zero_addr + mword (= f_address zero_addr).
/// Combined with hp_addr properties (< heap_size, % 8 == 0), this gives is_pointer_field.
#push-options "--z3rlimit 20"
let major_object_is_pointer_field (major: heap) (dst: obj_addr)
  : Lemma (requires Seq.mem dst (objects zero_addr major))
          (ensures HeapGraph.is_pointer_field dst)
  = // From obj_addr refinement: U64.v dst >= U64.v mword, < heap_size, % 8 == 0
    // From objects_addresses_gt_start: U64.v dst > U64.v zero_addr
    // Since both are word-aligned: U64.v dst >= U64.v zero_addr + 8 = U64.v zero_addr + U64.v mword
    objects_addresses_gt_start zero_addr major dst;
    assert (U64.v dst > U64.v zero_addr);
    // dst % 8 == 0 and zero_addr % 8 == 0, so dst > zero_addr implies dst >= zero_addr + 8
    assert (U64.v dst % U64.v mword == 0);
    assert (U64.v zero_addr % U64.v mword == 0);
    assert (U64.v dst >= U64.v zero_addr + U64.v mword)
    // is_pointer_field checks: v % mword == 0, v >= zero_addr + mword, v < heap_size
    // All three are satisfied.
#pop-options

/// ---------------------------------------------------------------------------
/// Step 1: Field preserved through minor collection
/// ---------------------------------------------------------------------------

/// The proof composes two steps:
/// 1. promote_all_read_other: field unchanged by promotion (writes only to new objects)
/// 2. update_major_pointers_field_effect: field unchanged when not a rewritable minor ptr
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let major_field_through_minor_collect
  (ms: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: obj_addr) (i: nat)
  : Lemma
    (requires
      Seq.mem src (objects zero_addr major) /\
      i < U64.v (wosize_of_object src major) /\
      ~(is_no_scan src major) /\
      is_blue src major = false /\
      U64.v src + i * 8 + 8 <= heap_size /\
      (U64.v src + i * 8) % 8 == 0 /\
      (let live_set = live_set_of ms major roots in
       let prom_res = promote_all_spec ms major fp live_set in
       let field_val = read_word major (U64.uint_to_t (U64.v src + i * 8)) in
       ~(is_minor_pointer field_val /\ prom_res.fwd_map field_val <> 0UL)) /\
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      AllocLemmas.chain_avoids major fp src (heap_size / U64.v mword) = true /\
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
  = let live_set = live_set_of ms major roots in
    let prom_res = promote_all_spec ms major fp live_set in
    let field_addr : hp_addr = U64.uint_to_t (U64.v src + i * 8) in

    // Unfold well_formed_heap to get well_formed_heap_part1
    reveal_opaque (`%well_formed_heap) well_formed_heap;

    // Step 1: promote_all doesn't modify this field
    // promote_all_read_other: addr within [src, src + wosize*8)
    assert (U64.v field_addr >= U64.v src);
    assert (U64.v field_addr + 8 <= U64.v src + U64.v (wosize_of_object src major) * 8);
    PromFields.promote_all_read_other ms major fp live_set src field_addr;
    assert (read_word prom_res.major_final field_addr == read_word major field_addr);

    // Step 2: update_major_pointers doesn't modify this field
    // mc_major = update_major_pointers prom_res.major_final prom_res.fwd_map
    minor_collect_spec_unfold ms major fp roots;
    let fwd = prom_res.fwd_map in

    // Invoke update_major_pointers_field_effect on prom_res.major_final
    // Using the intermediate heap facts from preconditions
    promote_all_preserves_wfh_part1 ms major fp live_set;
    PromField.update_major_pointers_field_effect prom_res.major_final fwd src i;

    // The old_val in prom_res.major_final == old_val in major (from step 1)
    // Since ~(is_minor_pointer old_val /\ fwd old_val <> 0UL), new_val == old_val
    ()
#pop-options

/// ---------------------------------------------------------------------------
/// Step 1b: Field forwarded through minor collection (Case 3)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let major_field_forwarded_by_minor_collect
  (ms: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: obj_addr) (i: nat)
  : Lemma
    (requires
      Seq.mem src (objects zero_addr major) /\
      i < U64.v (wosize_of_object src major) /\
      ~(is_no_scan src major) /\
      is_blue src major = false /\
      U64.v src + i * 8 + 8 <= heap_size /\
      (U64.v src + i * 8) % 8 == 0 /\
      (let live_set = live_set_of ms major roots in
       let prom_res = promote_all_spec ms major fp live_set in
       let field_val = read_word major (U64.uint_to_t (U64.v src + i * 8)) in
       is_minor_pointer field_val /\ prom_res.fwd_map field_val <> 0UL) /\
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      AllocLemmas.chain_avoids major fp src (heap_size / U64.v mword) = true /\
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
  = let live_set = live_set_of ms major roots in
    let prom_res = promote_all_spec ms major fp live_set in
    let field_addr : hp_addr = U64.uint_to_t (U64.v src + i * 8) in

    // Unfold well_formed_heap to get well_formed_heap_part1
    reveal_opaque (`%well_formed_heap) well_formed_heap;

    // Step 1: promote_all doesn't modify this field (writes only to newly allocated)
    assert (U64.v field_addr >= U64.v src);
    assert (U64.v field_addr + 8 <= U64.v src + U64.v (wosize_of_object src major) * 8);
    PromFields.promote_all_read_other ms major fp live_set src field_addr;
    assert (read_word prom_res.major_final field_addr == read_word major field_addr);

    // Step 2: update_major_pointers rewrites this field to fwd(old_val)
    minor_collect_spec_unfold ms major fp roots;
    let fwd = prom_res.fwd_map in

    promote_all_preserves_wfh_part1 ms major fp live_set;
    PromField.update_major_pointers_field_effect prom_res.major_final fwd src i;

    // update_major_pointers_field_effect tells us:
    //   is_minor_pointer old_val /\ fwd old_val <> 0UL ==> new_val == fwd old_val
    // Combined with step 1: old_val in prom_res.major_final == old_val in major
    // So new_val == fwd (read_word major field_addr)
    ()
#pop-options
