/// ---------------------------------------------------------------------------
/// GC.Gen.Correctness — Implementation of generational GC correctness
/// ---------------------------------------------------------------------------

module GC.Gen.Correctness

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Spec.HeapModel
open GC.Spec.DFS
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Allocator

module MajorCorrectness = GC.Spec.Correctness
module HeapGraph = GC.Spec.HeapGraph
module AllocLemmas = GC.Spec.Allocator.Lemmas
module Mark = GC.Spec.Mark
module Sweep = GC.Spec.Sweep

/// ---------------------------------------------------------------------------
/// Composition bridge
/// ---------------------------------------------------------------------------

/// Proof outline for minor_preserves_major_objects:
/// 1. minor_collect_spec = promote_all_spec + update_major_pointers (identity)
/// 2. promote_all_spec = promote_all_aux (recursive)
/// 3. Each step: promote_object = alloc_spec + copy_fields
/// 4. alloc_spec_preserves_objects (PROVEN in GC.Spec.Allocator.Lemmas)
///    → objects membership preserved through allocation
/// 5. copy_fields writes within allocated block → write_word_preserves_objects
///    → objects equality (hence membership) preserved
/// 6. By induction on promote_all_aux, objects membership is preserved

let minor_preserves_major_objects
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires minor_wf minor /\ well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = minor_collect_spec minor major fp roots in
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                      Seq.mem x (objects zero_addr res.mc_major)))) =
  let live_set = minor_objects minor in
  // promote_all preserves existing objects
  promote_all_preserves_objects minor major fp live_set;
  let prom_res = promote_all_spec minor major fp live_set in
  // update_major_pointers preserves objects list
  // Need well_formed_heap_part1 prom_res.major_final — proven by promote_all
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  promote_all_preserves_wfh_part1 minor major fp live_set;
  update_major_pointers_preserves_objects prom_res.major_final prom_res.fwd_map;
  // Bridge: mc_major == update_major_pointers prom_res.major_final prom_res.fwd_map
  minor_collect_spec_unfold minor major fp roots

/// ---------------------------------------------------------------------------
/// The main theorem
/// ---------------------------------------------------------------------------

let gen_gc_correct
  (gs: gen_state) (roots: seq U64.t) (gray_stack: seq obj_addr)
  (fp: U64.t)
  : Lemma (requires gen_wf gs /\
                    well_formed_heap gs.gs_major /\
                    AllocLemmas.fl_valid gs.gs_major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates gs.gs_major fp (heap_size / U64.v mword))
          (ensures (let res = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
                    let live_set = minor_objects gs.gs_minor in
                    let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
                    fwd_targets_in_objects prom_res.fwd_map live_set (Seq.length live_set) res.mc_major /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr gs.gs_major) ==>
                      Seq.mem x (objects zero_addr res.mc_major)) /\
                    minor_wf res.mc_minor /\ U64.v res.mc_minor.bump == 0 /\
                    well_formed_heap_part1 res.mc_major /\
                    well_formed_heap_part3 res.mc_major /\
                    well_formed_heap_part4 res.mc_major)) =
  let minor = gs.gs_minor in
  let major = gs.gs_major in
  assert (minor_wf minor);
  let live_set = minor_objects minor in
  // Part 1: promoted objects land in promote_all_spec's major_final
  promote_all_adds_promoted minor major fp live_set;
  let prom_res = promote_all_spec minor major fp live_set in
  // Bridge: mc_major == update_major_pointers prom_res.major_final prom_res.fwd_map
  minor_collect_spec_unfold minor major fp roots;
  // update_major_pointers preserves objects list
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  promote_all_preserves_wfh_part1 minor major fp live_set;
  promote_all_preserves_wfh_part4 minor major fp live_set;
  update_major_pointers_preserves_objects prom_res.major_final prom_res.fwd_map;
  // Now: objects(mc_major) == objects(prom_res.major_final), so fwd_targets_in_objects transfers
  // Existing major objects survive
  minor_preserves_major_objects minor major fp roots;
  // Minor heap reset
  minor_collect_resets_minor minor major fp roots;
  // well_formed_heap_part1 of mc_major
  update_major_pointers_preserves_wfh_part1 prom_res.major_final prom_res.fwd_map;
  // well_formed_heap_part4 of mc_major (no infix objects)
  update_major_pointers_preserves_wfh_part4 prom_res.major_final prom_res.fwd_map;
  // well_formed_heap_part3 (infix_wf — vacuous since part4 holds)
  update_major_pointers_preserves_wfh_part3 prom_res.major_final prom_res.fwd_map;
  ()

/// ---------------------------------------------------------------------------
/// Full well_formed_heap for post-minor major heap
/// ---------------------------------------------------------------------------

let gen_gc_correct_full
  (gs: gen_state) (roots: seq U64.t) (fp: U64.t)
  : Lemma (requires gen_wf gs /\
                    well_formed_heap gs.gs_major /\
                    AllocLemmas.fl_valid gs.gs_major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates gs.gs_major fp (heap_size / U64.v mword) /\
                    minor_fields_well_formed gs.gs_minor gs.gs_major /\
                    all_promotions_succeed gs.gs_minor gs.gs_major fp /\
                    allocated_objects_avoid_chain gs.gs_major fp /\
                    post_promote_pointer_closure gs.gs_minor gs.gs_major fp)
          (ensures (let res = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
                    well_formed_heap res.mc_major)) =
  let minor = gs.gs_minor in
  let major = gs.gs_major in
  let live_set = minor_objects minor in
  let prom_res = promote_all_spec minor major fp live_set in
  minor_collect_spec_unfold minor major fp roots;
  let res = minor_collect_spec minor major fp roots in
  // Establish parts 1, 3, 4 via gen_gc_correct
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  promote_all_preserves_wfh_part1 minor major fp live_set;
  promote_all_preserves_wfh_part4 minor major fp live_set;
  update_major_pointers_preserves_wfh_part1 prom_res.major_final prom_res.fwd_map;
  update_major_pointers_preserves_wfh_part4 prom_res.major_final prom_res.fwd_map;
  update_major_pointers_preserves_wfh_part3 prom_res.major_final prom_res.fwd_map;
  // Establish part 2 (pointer closure) via the new lemma
  promote_all_fwd_all_targets_valid minor major fp live_set;
  // post_promote_pointer_closure gives us pointer_closure_modulo_fwd on prom_res.major_final
  update_major_pointers_preserves_wfh_part2 prom_res.major_final prom_res.fwd_map;
  // Combine all 4 parts
  assert (well_formed_heap_part1 res.mc_major);
  assert (well_formed_heap_part2 res.mc_major);
  assert (well_formed_heap_part3 res.mc_major);
  assert (well_formed_heap_part4 res.mc_major)

/// ---------------------------------------------------------------------------
/// Composition: Minor collection + Major GC = Full generational correctness
/// ---------------------------------------------------------------------------

let gen_gc_composition
  (gs: gen_state) (roots: seq U64.t) (fp: U64.t)
  (major_roots: seq obj_addr) (major_stack: seq obj_addr) (major_fp: U64.t)
  : Lemma
    (requires
      gen_wf gs /\
      well_formed_heap gs.gs_major /\
      AllocLemmas.fl_valid gs.gs_major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates gs.gs_major fp (heap_size / U64.v mword) /\
      (let res = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
       well_formed_heap res.mc_major /\
       Mark.stack_props res.mc_major major_stack /\
       Mark.root_props res.mc_major major_roots /\
       Sweep.fp_in_heap major_fp res.mc_major /\
       Mark.no_black_objects res.mc_major /\
       Mark.no_pointer_to_blue res.mc_major /\
       (forall (r: obj_addr). Seq.mem r major_roots <==> Seq.mem r major_stack) /\
       (let g = create_graph res.mc_major in
        let roots' = HeapGraph.coerce_to_vertex_list major_roots in
        graph_wf g /\ is_vertex_set roots' /\ subset_vertices roots' g.vertices)))
    (ensures
      (let res = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
       let h_swept = fst (Sweep.sweep (Mark.mark res.mc_major major_stack) major_fp) in
       MajorCorrectness.full_gc_correctness res.mc_major h_swept major_roots)) =
  let res = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
  // Apply the mark-and-sweep end-to-end correctness theorem
  MajorCorrectness.full_gc_correctness_from_end_to_end
    res.mc_major major_stack major_roots major_fp
