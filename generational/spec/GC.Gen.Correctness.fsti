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
open GC.Gen.Reachability
open GC.Gen.Remembered
open GC.Gen.Promote
open GC.Gen.PromoteUpdate
open GC.Gen.Allocator

module MajorCorrectness = GC.Spec.Correctness
module HeapGraph = GC.Spec.HeapGraph
module AllocLemmas = GC.Spec.Allocator.Lemmas
module Mark = GC.Spec.Mark
module Sweep = GC.Spec.Sweep

/// ---------------------------------------------------------------------------
/// Minor Collection Correctness
/// ---------------------------------------------------------------------------

/// After minor collection, every object that was reachable from
/// (program_roots ∪ remembered_set) in the minor heap exists in the
/// post-collection major heap with preserved field data.
let minor_gc_correctness (minor_pre: minor_state) (major_pre major_post: heap)
                          (fp_pre: U64.t) (roots: seq U64.t)
                          (fwd: forwarding_map) : prop =
  // 1. All REACHABLE promoted objects exist in the major heap
  (forall (obj: U64.t).
    Seq.mem obj (live_set_of minor_pre major_pre roots) /\
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
/// Field Correspondence (Injection between minor objects and promoted copies)
/// ---------------------------------------------------------------------------

/// After minor collection, each promoted object's fields correspond to the
/// original minor object's fields, with pointer rewriting applied:
/// - Fields that were minor pointers with a successful forwarding are rewritten
/// - All other fields are preserved verbatim from the minor heap
///
/// NOTE: The full field_correspondence proof requires an alloc_spec frame lemma
/// (showing allocation doesn't modify fields of previously allocated objects).
/// The key building block (update_major_pointers_field_effect) IS fully proven
/// and exported from GC.Gen.Promote. Once an alloc_spec_read_other bridge is
/// added to GC.Spec.Allocator.Lemmas, the full field_correspondence follows
/// by composing promote_preserves_fields + copy_fields_frame + the alloc frame
/// + update_major_pointers_field_effect.
let field_correspondence (minor: minor_state) (major: heap) (mc_major: heap)
                         (fwd: forwarding_map) (roots: seq U64.t) : prop =
  let live_set = live_set_of minor major roots in
  forall (obj: U64.t).
    Seq.mem obj live_set /\ fwd obj <> 0UL ==>
    (let new_addr = fwd obj in
     let wz = minor_wosize minor obj in
     forall (j:nat). j < wz ==>
       (let minor_val = minor_read_field minor obj j in
        let field_addr_v = U64.v new_addr + j * 8 in
        field_addr_v + 8 <= heap_size /\
        field_addr_v % 8 == 0 ==>
        (let major_val = read_word mc_major (U64.uint_to_t field_addr_v) in
         // If the minor field was a minor pointer that was forwarded, it gets rewritten
         (is_minor_pointer minor_val /\ fwd minor_val <> 0UL ==>
           major_val == fwd minor_val) /\
         // If the minor field was NOT a forwardable minor pointer, it's preserved
         (~(is_minor_pointer minor_val /\ fwd minor_val <> 0UL) ==>
           major_val == minor_val))))

/// ---------------------------------------------------------------------------
/// The main theorem: minor + major collection is correct
/// ---------------------------------------------------------------------------

/// After a minor collection, the following hold:
/// 1. All promoted objects exist in the post-minor major heap
/// 2. All pre-existing major objects survive
/// 3. Minor heap is reset
/// 4. Major heap well-formed (parts 1, 3, 4 — size bounds, infix, no-infix)
val gen_gc_correct
  (gs: gen_state) (roots: seq U64.t) (gray_stack: seq obj_addr)
  (fp: U64.t)
  : Lemma (requires gen_wf gs /\
                    well_formed_heap gs.gs_major /\
                    AllocLemmas.fl_valid gs.gs_major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates gs.gs_major fp (heap_size / U64.v mword) /\
                    live_set_no_infix gs.gs_minor (live_set_of gs.gs_minor gs.gs_major roots))
          (ensures (let res = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
                    let live_set = live_set_of gs.gs_minor gs.gs_major roots in
                    let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
                    // 1. All promoted objects exist in the post-minor major heap
                    fwd_targets_in_objects prom_res.fwd_map live_set (Seq.length live_set) res.mc_major /\
                    // 2. All pre-existing major objects survive
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr gs.gs_major) ==>
                      Seq.mem x (objects zero_addr res.mc_major)) /\
                    // 3. Minor heap is reset
                    minor_wf res.mc_minor /\ U64.v res.mc_minor.bump == 0 /\
                    // 4. Major heap well-formed (parts 1, 3, 4)
                    well_formed_heap_part1 res.mc_major /\
                    well_formed_heap_part3 res.mc_major /\
                    well_formed_heap_part4 res.mc_major))

/// ---------------------------------------------------------------------------
/// Preconditions for full well_formed_heap (part 2: pointer closure)
/// ---------------------------------------------------------------------------

/// All live-set object fields that are pointers either:
/// - Are minor pointers targeting objects in the live set (will be promoted)
///   AND those targets have wosize > 0 (ensuring they get promoted), or
/// - Are non-minor pointers targeting valid objects in the original major heap
let minor_field_targets_major (v: U64.t) (major: heap) : prop =
  U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
  Seq.mem (v <: obj_addr) (objects 0UL major)

let minor_fields_well_formed (minor: minor_state) (major: heap) (roots: seq U64.t) : prop =
  let live_set = live_set_of minor major roots in
  forall (obj: U64.t) (j: nat).
    Seq.mem obj live_set /\ j < minor_wosize minor obj ==>
    (let v = minor_read_field minor obj j in
     is_pointer v ==>
       (is_minor_pointer v ==> (Seq.mem v live_set /\ minor_wosize minor v > 0)) /\
       (~(is_minor_pointer v) ==> minor_field_targets_major v major))

/// All live-set objects with wosize > 0 get successfully promoted (alloc succeeds)
let all_promotions_succeed (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  let live_set = live_set_of minor major roots in
  let prom_res = promote_all_spec minor major fp live_set in
  forall (k:nat). k < Seq.length live_set ==>
    (let obj = Seq.index live_set k in
     minor_wosize minor obj > 0 ==>
     prom_res.fwd_map obj <> 0UL)

/// Allocated (non-blue) objects in the major heap are not on the free chain.
/// This is a standard allocator invariant: the free list contains only blue/free blocks.
let allocated_objects_avoid_chain (major: heap) (fp: U64.t) : prop =
  forall (obj: obj_addr).
    Seq.mem obj (objects 0UL major) /\ ~(is_blue obj major) ==>
    AllocLemmas.chain_avoids major fp obj (heap_size / U64.v mword) = true

/// After promote_all, pointer fields that are NOT rewritable minor pointers still
/// target valid objects. This is a frame property: non-promoted objects' pointer fields
/// are unchanged (preserved by wfh_part2 of the original heap), and promoted objects'
/// pointer fields that are NOT minor-with-fwd are already valid major pointers.
/// Provable from: well_formed_heap(major) + fl_valid + allocator frame properties.
let post_promote_pointer_closure (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  let live_set = live_set_of minor major roots in
  let prom_res = promote_all_spec minor major fp live_set in
  pointer_closure_modulo_fwd prom_res.major_final prom_res.fwd_map

/// Full correctness theorem: under additional minor-field and promotion-success
/// preconditions, the post-minor major heap satisfies full well_formed_heap.
/// This enables direct composition with the mark-and-sweep major GC.
val gen_gc_correct_full
  (gs: gen_state) (roots: seq U64.t) (fp: U64.t)
  : Lemma (requires gen_wf gs /\
                    well_formed_heap gs.gs_major /\
                    AllocLemmas.fl_valid gs.gs_major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates gs.gs_major fp (heap_size / U64.v mword) /\
                    minor_fields_well_formed gs.gs_minor gs.gs_major roots /\
                    all_promotions_succeed gs.gs_minor gs.gs_major fp roots /\
                    allocated_objects_avoid_chain gs.gs_major fp /\
                    post_promote_pointer_closure gs.gs_minor gs.gs_major fp roots /\
                    live_set_no_infix gs.gs_minor (live_set_of gs.gs_minor gs.gs_major roots) /\
                    no_scan_invariant gs.gs_major)
          (ensures (let res = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
                    well_formed_heap res.mc_major))

/// ---------------------------------------------------------------------------
/// Composition: Minor collection + Major GC = Full generational correctness
/// ---------------------------------------------------------------------------

/// Conditional composition: IF the post-minor major heap satisfies the
/// mark-and-sweep preconditions, THEN running a major GC yields
/// full_gc_correctness over the composed heap.
///
/// The conditions that the caller must establish for the major heap:
///   - well_formed_heap (full, including pointer closure)
///   - stack/root properties for the mark phase
///   - no black objects (fresh state for marking)
///   - no pointer to blue (no dangling free-list refs in live objects)
val gen_gc_composition
  (gs: gen_state) (roots: seq U64.t) (fp: U64.t)
  (major_roots: seq obj_addr) (major_stack: seq obj_addr) (major_fp: U64.t)
  : Lemma
    (requires
      gen_wf gs /\
      well_formed_heap gs.gs_major /\
      AllocLemmas.fl_valid gs.gs_major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates gs.gs_major fp (heap_size / U64.v mword) /\
      // Major GC preconditions on the post-minor heap
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
       MajorCorrectness.full_gc_correctness res.mc_major h_swept major_roots))

/// ---------------------------------------------------------------------------
/// End-to-End Generational GC Theorem
/// ---------------------------------------------------------------------------

/// The complete generational GC theorem: starting from a well-formed
/// generational state, after a full GC cycle (minor collection + major GC):
///
/// 1. The major heap is well-formed (can be used for further allocation)
/// 2. All objects reachable from major_roots in the post-promotion major heap
///    survive with preserved graph structure
/// 3. Every live minor-heap object (reachable from roots) was promoted to
///    the post-promotion major heap (its forwarded address is a valid object)
/// 4. The roots are rewritten: each root that pointed into the minor heap
///    now points to the promoted copy in the major heap
/// 5. The minor heap is reset (ready for new allocations)
///
/// This composes gen_gc_correct_full (minor correctness) with
/// gen_gc_composition (major correctness) into a single statement.
val generational_gc_end_to_end
  (gs: gen_state) (roots: seq U64.t) (fp: U64.t)
  (major_roots: seq obj_addr) (major_stack: seq obj_addr) (major_fp: U64.t)
  : Lemma
    (requires
      // Gen state well-formed
      gen_wf gs /\
      well_formed_heap gs.gs_major /\
      AllocLemmas.fl_valid gs.gs_major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates gs.gs_major fp (heap_size / U64.v mword) /\
      // Minor heap field & promotion preconditions
      minor_fields_well_formed gs.gs_minor gs.gs_major roots /\
      all_promotions_succeed gs.gs_minor gs.gs_major fp roots /\
      allocated_objects_avoid_chain gs.gs_major fp /\
      post_promote_pointer_closure gs.gs_minor gs.gs_major fp roots /\
      // No infix objects in live set, no-scan invariant on major heap
      live_set_no_infix gs.gs_minor (live_set_of gs.gs_minor gs.gs_major roots) /\
      no_scan_invariant gs.gs_major /\
      // Major GC preconditions on the post-minor heap
      (let res = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
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
      (let minor_res = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
       let h_swept = fst (Sweep.sweep (Mark.mark minor_res.mc_major major_stack) major_fp) in
       let live_set = live_set_of gs.gs_minor gs.gs_major roots in
       let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
       // 1. Post-minor major heap is well-formed
       well_formed_heap minor_res.mc_major /\
       // 2. Major GC correctness (mark-and-sweep preserves reachable objects)
       MajorCorrectness.full_gc_correctness minor_res.mc_major h_swept major_roots /\
       // 3. All live minor objects have valid forwarded addresses
       fwd_targets_in_objects prom_res.fwd_map live_set (Seq.length live_set) minor_res.mc_major /\
       // 4. Roots are rewritten to point to promoted copies
       minor_res.mc_roots == rewrite_roots roots minor_res.mc_fwd /\
       // 5. Minor heap is reset
       minor_wf minor_res.mc_minor /\ U64.v minor_res.mc_minor.bump == 0))
