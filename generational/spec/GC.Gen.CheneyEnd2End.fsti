/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyEnd2End — End-to-end correctness for Cheney-based gen GC
/// ---------------------------------------------------------------------------
///
/// Composes Cheney minor collection (cheney_collect_spec) with mark-and-sweep
/// major collection (mark + sweep + coalesce) into a single correctness theorem
/// stated directly over cheney_collect_spec — matching the Pulse impl's
/// postcondition.
///
/// Unlike GC.Gen.Correctness (which uses minor_collect_spec / promote_all_spec),
/// this module works directly with the Cheney BFS spec that the implementation
/// refines to, avoiding the need for an equivalence proof between the two specs.

module GC.Gen.CheneyEnd2End

open FStar.Seq
module U64 = FStar.UInt64

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
open GC.Gen.Cheney

module MajorCorrectness = GC.Spec.Correctness
module HeapGraph = GC.Spec.HeapGraph
module AllocLemmas = GC.Spec.Allocator.Lemmas
module Mark = GC.Spec.Mark
module Sweep = GC.Spec.Sweep
module CheneyCorr = GC.Gen.CheneyCorrectness

/// ---------------------------------------------------------------------------
/// Post-minor preservation: no_black_objects
/// ---------------------------------------------------------------------------

/// After Cheney collection, no objects are black in the post-minor major heap.
/// Proof sketch:
/// - Pre-existing objects: their colors are unchanged by promotion (alloc_spec
///   and copy_fields only write within newly-allocated blocks).
///   update_major_pointers only modifies field values, not headers.
/// - Promoted objects: allocated with white_bits (color = 0 = White).
val cheney_collect_no_black
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    Mark.no_black_objects major /\
                    minor_infix_wf minor)
          (ensures Mark.no_black_objects (cheney_collect_spec minor major fp roots).mc_major)

/// ---------------------------------------------------------------------------
/// Main theorem: Cheney end-to-end generational GC correctness
/// ---------------------------------------------------------------------------

/// The complete generational GC theorem stated over cheney_collect_spec:
///
/// After minor collection (Cheney BFS) followed by major collection
/// (mark + sweep + coalesce), the combined result satisfies:
///
/// 1. Full GC correctness on the major heap (mark-and-sweep 5 pillars)
/// 2. Cheney collection correctness (objects survive, wfh_part1, allocator,
///    minor reset, root rewriting)
///
/// This is the theorem the Pulse gen_gc function's postcondition references.
val cheney_gc_end_to_end
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (major_stack: seq obj_addr) (major_fp: U64.t) (cap: nat)
  : Lemma
    (requires
      // Basic structural preconditions
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp /\
      Mark.no_black_objects major /\
      minor_infix_wf minor /\
      // Post-Cheney wfh and invariants (caller must establish these)
      well_formed_heap (cheney_collect_spec minor major fp roots).mc_major /\
      Mark.no_pointer_to_blue (cheney_collect_spec minor major fp roots).mc_major /\
      // Major GC preconditions on post-minor heap
      (let res = cheney_collect_spec minor major fp roots in
       Mark.stack_props res.mc_major major_stack /\
       Mark.root_props res.mc_major major_stack /\
       Sweep.fp_in_heap major_fp res.mc_major /\
       (forall (x: obj_addr). Seq.mem x (objects zero_addr res.mc_major) /\
         (is_gray x res.mc_major \/ is_black x res.mc_major) ==> Seq.mem x major_stack) /\
       (let g = create_graph res.mc_major in
        let roots' = HeapGraph.coerce_to_vertex_list major_stack in
        graph_wf g /\ is_vertex_set roots' /\ subset_vertices roots' g.vertices) /\
       Seq.length major_stack <= cap /\ cap > 0))
    (ensures
      (let minor_res = cheney_collect_spec minor major fp roots in
       let prom = cheney_promote minor major fp roots in
       // 1. Major GC correctness (5 pillars of mark-and-sweep)
       MajorCorrectness.full_gc_correctness
         minor_res.mc_major
         (fst (Sweep.sweep (Mark.mark minor_res.mc_major major_stack) major_fp))
         major_stack /\
       // 2. Cheney minor collection correctness (from CheneyCorrectness)
       (forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
         Seq.mem x (objects zero_addr minor_res.mc_major)) /\
       well_formed_heap_part1 minor_res.mc_major /\
       AllocLemmas.fl_valid minor_res.mc_major minor_res.mc_fp (heap_size / U64.v mword) /\
       AllocLemmas.fl_chain_terminates minor_res.mc_major minor_res.mc_fp (heap_size / U64.v mword) /\
       minor_wf minor_res.mc_minor /\
       U64.v minor_res.mc_minor.bump == 0 /\
       minor_res.mc_roots == rewrite_roots roots prom.fwd_map))
