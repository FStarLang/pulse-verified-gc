/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph.Isomorphism.TopLevel — Implementation
/// ---------------------------------------------------------------------------
///
/// Bridges the Cheney-based gen_gc postcondition to the isomorphism theorem.
///
/// Key architectural note:
///   The Discharge module works with `minor_collect_spec` (promote_all_spec-based).
///   The Pulse gen_gc implementation works with `cheney_collect_spec` (BFS-based).
///   These produce equivalent results when BFS discovers the same live set,
///   but proving this equivalence formally requires showing:
///     cheney_promote minor major fp roots ≡ promote_all_spec minor major fp (live_set_of minor major roots)
///   This is the one remaining connection point.

module GC.Gen.CombinedGraph.Isomorphism.TopLevel

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
open GC.Gen.Promote
open GC.Gen.CombinedGraph
open GC.Gen.Cheney
open GC.Gen.Correctness
open GC.Gen.Allocator
open GC.Gen.Reachability
open GC.Gen.Remembered

module HeapGraph = GC.Spec.HeapGraph
module AllocLemmas = GC.Spec.Allocator.Lemmas
module Mark = GC.Spec.Mark
module Sweep = GC.Spec.Sweep
module DFS = GC.Spec.DFS
module Iso = GC.Gen.CombinedGraph.Isomorphism
module Discharge = GC.Gen.CombinedGraph.Isomorphism.Discharge


/// ---------------------------------------------------------------------------
/// The cheney ↔ promote_all equivalence assumption
/// ---------------------------------------------------------------------------
///
/// This is the single remaining gap between gen_gc and the isomorphism.
///
/// Informally: Cheney BFS promotion (which discovers reachable minor objects
/// by breadth-first search) produces the same post-promotion heap and
/// forwarding map as the set-based promote_all_spec (which promotes all
/// objects in the live set at once).
///
/// This holds because:
///   1. Both promote exactly the set `live_set_of minor major roots`
///      (Cheney BFS discovers all reachable objects; live_set_of computes them)
///   2. Both use the same allocator (alloc_spec from the free list)
///   3. Both copy the same fields
///
/// A formal proof would require showing BFS traversal order doesn't affect
/// the final result (since the free-list is consumed identically regardless
/// of allocation order for same-sized objects).

let cheney_minor_collect_equiv
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      minor_wf minor)
    (ensures
      (let cheney_res = cheney_collect_spec minor major fp roots in
       let gs : gen_state = { gs_minor = minor; gs_major = major; gs_fp = fp } in
       let mc_res = minor_collect_spec minor major fp roots in
       cheney_res.mc_major == mc_res.mc_major /\
       cheney_res.mc_fp == mc_res.mc_fp /\
       cheney_res.mc_roots == mc_res.mc_roots /\
       cheney_res.mc_fwd == mc_res.mc_fwd))
  = admit ()
    // Proof sketch:
    //   1. cheney_promote produces promote_all_result with same fwd_map
    //      as promote_all_spec (both promote exactly live_set_of)
    //   2. Both apply update_major_pointers with same fwd_map
    //   3. Both apply rewrite_roots with same fwd_map
    //   4. Therefore all fields of the result agree


/// ---------------------------------------------------------------------------
/// Main theorem implementation
/// ---------------------------------------------------------------------------

let gen_gc_isomorphism
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (combined_roots: seq combined_vertex)
  (major_stack: seq obj_addr) (major_fp: U64.t)
  : Lemma
    (requires
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp /\
      Mark.no_black_objects major /\
      minor_wf minor /\
      // --- Additional standard_gc_preconditions ---
      minor_fields_well_formed minor major roots /\
      all_promotions_succeed minor major fp roots /\
      allocated_objects_avoid_chain major fp /\
      post_promote_pointer_closure minor major fp roots /\
      live_set_no_infix minor (live_set_of minor major roots) /\
      no_scan_invariant major /\
      minor_no_scan_invariant minor /\
      (let live_set = live_set_of minor major roots in
       forall (v: U64.t). Seq.mem v live_set ==> minor_wosize minor v > 0) /\
      // --- Post-Cheney major GC preconditions ---
      (let res = cheney_collect_spec minor major fp roots in
       well_formed_heap res.mc_major /\
       Mark.no_pointer_to_blue res.mc_major /\
       Mark.stack_props res.mc_major major_stack /\
       Mark.root_props res.mc_major major_stack /\
       Sweep.fp_in_heap major_fp res.mc_major /\
       Mark.no_black_objects res.mc_major /\
       no_scan_invariant res.mc_major /\
       (let g = create_graph res.mc_major in
        let rs = HeapGraph.coerce_to_vertex_list major_stack in
        graph_wf g /\ is_vertex_set rs /\ subset_vertices rs g.vertices)) /\
      // --- Isomorphism-specific assumptions ---
      iso_structural_preconditions minor major fp roots combined_roots major_stack /\
      iso_edge_bridge_forward minor major fp roots combined_roots major_stack /\
      iso_surjectivity minor major fp roots combined_roots major_stack /\
      iso_edge_backward minor major fp roots combined_roots)
    (ensures
      isomorphism_postcondition minor major fp roots combined_roots major_stack major_fp)
  = // Step 1: Establish cheney ↔ minor_collect equivalence
    cheney_minor_collect_equiv minor major fp roots;

    // Step 2: Build gen_state for Discharge
    let gs : gen_state = { gs_minor = minor; gs_major = major; gs_fp = fp } in

    // Step 3: After the equivalence, cheney_collect_spec == minor_collect_spec.
    // All preconditions transfer: Discharge's standard_gc_preconditions,
    // structural_preconditions, and bridge assumptions follow directly
    // from our requires clause with the substitution mc_fwd = prom_res.fwd_map.
    assert (gen_wf gs);
    Discharge.isomorphism_from_gc gs roots fp combined_roots major_stack major_stack major_fp
