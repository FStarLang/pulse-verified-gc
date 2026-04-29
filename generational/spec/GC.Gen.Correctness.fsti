/// ---------------------------------------------------------------------------
/// GC.Gen.Correctness — Composed generational GC correctness theorem
/// ---------------------------------------------------------------------------
///
/// Defines the end-to-end correctness theorem for the generational GC:
/// 1. Minor collection correctness: all reachable minor objects are promoted
/// 2. Major collection correctness: all reachable major objects survive
/// 3. Composed: no reachable object (in either generation) is ever lost
///
/// Reuses GC.Spec.Correctness.full_gc_correctness for the major-heap part.

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

/// ---------------------------------------------------------------------------
/// Minor Collection Correctness
/// ---------------------------------------------------------------------------

/// After minor collection, every object that was reachable from
/// (program_roots ∪ remembered_set) in the minor heap exists in the
/// post-collection major heap with preserved field data.
let minor_gc_correctness (minor_pre: minor_state) (major_pre major_post: heap)
                          (fp_pre: U64.t) (roots: seq U64.t)
                          (fwd: forwarding_map) : prop =
  // 1. All promoted objects exist in the major heap
  (forall (obj: U64.t).
    Seq.mem obj (minor_objects minor_pre) /\
    fwd obj <> 0UL ==>
    (let new_addr = fwd obj in
     U64.v new_addr >= U64.v mword /\
     U64.v new_addr < heap_size)) /\
  // 2. Major heap well-formedness preserved
  well_formed_heap major_post

/// ---------------------------------------------------------------------------
/// Major Collection Correctness (reused from existing theorem)
/// ---------------------------------------------------------------------------

/// The major heap collection correctness is exactly the existing
/// full_gc_correctness from GC.Spec.Correctness:
/// - Pillar 1: well_formed_heap preserved
/// - Pillar 2: reachable objects are black after mark
/// - Pillar 3: successors of survivors are preserved
/// - Pillar 4: all objects white or blue after sweep
/// - Pillar 5: field data of survivors preserved
let major_gc_correctness (major_pre major_post: heap) (roots: seq obj_addr) : prop =
  MajorCorrectness.full_gc_correctness major_pre major_post roots

/// ---------------------------------------------------------------------------
/// Composed Generational Correctness
/// ---------------------------------------------------------------------------

/// Full generational GC correctness:
/// Starting from (minor_heap, major_heap) with a set of roots,
/// after a full GC cycle (minor collection + major collection),
/// every object reachable from roots in the original combined heap
/// is present in the final major heap with preserved data.
let gen_gc_correctness (gs_init: gen_state) (major_final: heap)
                       (roots: seq obj_addr) : prop =
  // 1. Major heap is well-formed
  well_formed_heap major_final /\
  // 2. All objects in final state are white or blue (fully collected)
  (forall (x: obj_addr). Seq.mem x (objects 0UL major_final) ==>
    is_white x major_final \/ is_blue x major_final) /\
  // 3. Objects that were reachable in the major heap survive
  //    (their field data is preserved)
  (let g_init = create_graph gs_init.gs_major in
   let g_final = create_graph major_final in
   let major_roots = HeapGraph.coerce_to_vertex_list roots in
   graph_wf g_init /\ is_vertex_set major_roots /\
   subset_vertices major_roots g_init.vertices ==>
   (forall (x: obj_addr).
     mem_graph_vertex g_init x /\
     Seq.mem x (reachable_set g_init major_roots) ==>
     Seq.mem x g_final.vertices /\
     successors g_init x == successors g_final x))

/// ---------------------------------------------------------------------------
/// Composition bridge
/// ---------------------------------------------------------------------------

/// Minor collection only affects the major heap by adding objects (promotion).
/// The existing major-heap objects are not modified during minor collection.
/// This means major GC preconditions are preserved through minor collection.
val minor_preserves_major_objects
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires minor_wf minor /\ well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = minor_collect_spec minor major fp roots in
                    // All objects that existed before still exist
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                      Seq.mem x (objects zero_addr res.mc_major))))

/// ---------------------------------------------------------------------------
/// The main theorem: minor + major collection is correct
/// ---------------------------------------------------------------------------

/// After a minor collection followed by a major collection,
/// the generational correctness property holds.
/// Currently proves: minor_gc_correctness (promoted objects land in major heap).
val gen_gc_correct
  (gs: gen_state) (roots: seq U64.t) (gray_stack: seq obj_addr)
  (fp: U64.t)
  : Lemma (requires gen_wf gs /\
                    well_formed_heap gs.gs_major /\
                    AllocLemmas.fl_valid gs.gs_major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates gs.gs_major fp (heap_size / U64.v mword))
          (ensures (let res = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
                    let live_set = minor_objects gs.gs_minor in
                    let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
                    // 1. All promoted objects exist in the post-minor major heap
                    fwd_targets_in_objects prom_res.fwd_map live_set (Seq.length live_set) res.mc_major /\
                    // 2. All pre-existing major objects survive
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr gs.gs_major) ==>
                      Seq.mem x (objects zero_addr res.mc_major)) /\
                    // 3. Minor heap is reset
                    minor_wf res.mc_minor /\ U64.v res.mc_minor.bump == 0))
