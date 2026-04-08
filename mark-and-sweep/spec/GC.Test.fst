(*
   GC.Test — Round-trip compatibility test: allocator ↔ collector

   Demonstrates that the allocator and GC specs compose correctly:
     init_heap → collect → allocate → collect → ...

   Init → collect: FULLY VERIFIED
     All init-time properties proven in GC.Test.Bridge (including density).

   Collect → allocate: FULLY VERIFIED
     gc_postcondition gives well_formed_heap, exactly what allocate needs.

   Allocate → collect: VERIFIED for well_formed_heap, fl_valid, no_black
     See alloc_enables_collect for the current state.
     General density, no_pointer_to_blue, and graph_wf preservation across
     allocation are future work (see comments below).
     are documented proof obligations.
*)
module GC.Test

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
open GC.Spec.Allocator.Lemmas
open GC.Spec.Mark
open GC.Spec.Sweep
open GC.Spec.Correctness
open GC.Spec.MarkInv
open GC.Spec.SweepInv
module SpecSweep = GC.Spec.Sweep
open GC.Spec.HeapModel
open GC.Spec.HeapGraph
open GC.Spec.Graph
open GC.Test.Bridge
module U64 = FStar.UInt64
module Seq = FStar.Seq

/// =========================================================================
/// Direction 1: collect → allocate (FULLY VERIFIED)
/// =========================================================================

/// After collection, the heap is well-formed, so we can allocate.
let collect_enables_allocate (h_final: heap) (fp: U64.t) (wz: nat)
  : Lemma (requires gc_postcondition h_final /\
                    fl_valid h_final fp (heap_size / U64.v mword))
          (ensures (let r = alloc_spec h_final fp wz in
                    well_formed_heap r.heap_out))
  = gc_postcondition_elim h_final;
    alloc_spec_preserves_wf h_final fp wz

/// =========================================================================
/// Remaining assumptions
/// =========================================================================

/// -------------------------------------------------------------------------
/// Init-time: FULLY PROVEN in GC.Test.Bridge
///   init_wf, init_fl_valid, init_no_black, init_no_gray,
///   init_no_pointer_to_blue, init_objects_eq, init_objects_nonempty,
///   init_graph_wf
/// -------------------------------------------------------------------------

/// heap_objects_dense holds after init_heap_spec with weakened predicate.
/// Proven in GC.Test.Bridge.init_dense.
let init_dense_lemma (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy)
          (ensures (let (g', _) = init_heap_spec g in
                    heap_objects_dense g'))
  = GC.Test.Bridge.init_dense g

/// -------------------------------------------------------------------------
/// Alloc-time preservation theorems (VERIFIED)
/// -------------------------------------------------------------------------

/// Proven in GC.Spec.Allocator.Lemmas
let alloc_preserves_no_black (g: heap) (fp: U64.t) (wz: nat)
  : Lemma (requires no_black_objects g /\
                    well_formed_heap g /\
                    fl_valid g fp (heap_size / U64.v mword))
          (ensures (let r = alloc_spec g fp wz in
                    no_black_objects r.heap_out))
  = alloc_spec_preserves_no_black g fp wz

/// -------------------------------------------------------------------------
/// Alloc-time proof obligations (future work, documented)
/// -------------------------------------------------------------------------
///
/// The following properties are needed for alloc → collect in general:
///
/// 1. alloc_preserves_dense: heap_objects_dense preserved by alloc_spec.
///    Structural property: exact-fit preserves objects/wosize (use transfer);
///    split creates adjacent tiling blocks (use intro). Purely about headers.
///
/// 2. alloc_preserves_no_ptr_to_blue: no_pointer_to_blue preserved by alloc_spec.
///    Requires zeroing allocated block's fields (stale free-list links may
///    point to blue objects). For the first cycle from init (zeroed heap),
///    trivially holds. For subsequent cycles, compose alloc_spec with
///    zero_fields. Handled at the Pulse implementation level.
///
/// 3. alloc_preserves_graph_wf: graph_wf preserved by alloc_spec.
///    Follows from well_formed_heap preservation + field consistency.
///    Similarly benefits from field zeroing for subsequent cycles.

let alloc_preserves_fl_valid (g: heap) (fp: U64.t) (wz: nat)
  : Lemma (requires well_formed_heap g /\
                    fl_valid g fp (heap_size / U64.v mword) /\
                    fl_chain_terminates g fp (heap_size / U64.v mword))
          (ensures (let r = alloc_spec g fp wz in
                    fl_valid r.heap_out r.fp_out (heap_size / U64.v mword)))
  = alloc_spec_preserves_fl_valid g fp wz

/// =========================================================================
/// Empty-stack properties (FULLY VERIFIED)
/// =========================================================================

/// With an empty stack, stack_props holds iff there are no gray objects.
let empty_stack_props (g: heap)
  : Lemma (requires forall (obj: obj_addr). Seq.mem obj (objects zero_addr g) ==> ~(is_gray obj g))
          (ensures stack_props g Seq.empty)
  = ()

/// With an empty stack, root_props holds vacuously.
let empty_root_props (g: heap)
  : Lemma (root_props g Seq.empty)
  = ()

/// Coercing an empty stack gives an empty vertex list.
let empty_coerce ()
  : Lemma (coerce_to_vertex_list (Seq.empty #obj_addr) == Seq.empty)
  = ()

/// An empty vertex list is trivially a vertex set and subset of any vertices.
let empty_is_vertex_set ()
  : Lemma (is_vertex_set (Seq.empty #vertex_id) /\
           (forall vs. subset_vertices (Seq.empty #vertex_id) vs))
  = ()

/// =========================================================================
/// Init → Collect: the first GC cycle (uses Bridge lemmas)
/// =========================================================================

/// Helper: extract ~(is_gray) for all objects from no_gray_objects
private let no_gray_elim_all (g: heap)
  : Lemma (requires no_gray_objects g)
          (ensures forall (obj: obj_addr). Seq.mem obj (objects zero_addr g) ==> ~(is_gray obj g))
  = let aux (obj: obj_addr) : Lemma
      (requires Seq.mem obj (objects zero_addr g))
      (ensures ~(is_gray obj g))
    = no_gray_elim obj g
    in
    Classical.forall_intro (Classical.move_requires aux)

/// After init, we can establish gc_precondition for the first collection.
/// All init-time properties are now fully proven (including density).
#push-options "--z3rlimit 30"
let init_enables_collect (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy)
          (ensures (let (g', fp) = init_heap_spec g in
                    let st = Seq.empty #obj_addr in
                    mark_inv g' st /\
                    fp_valid fp g' /\
                    root_props g' st /\
                    no_black_objects g' /\
                    no_pointer_to_blue g' /\
                    graph_wf (create_graph g') /\
                    heap_objects_dense g'))
  = let (g', fp) = init_heap_spec g in
    // Bridge lemmas (including init_dense)
    init_dense_lemma g;
    init_wf g;
    init_fl_valid g;
    init_no_black g;
    init_no_gray g;
    init_no_pointer_to_blue g;
    init_objects_nonempty g;
    init_graph_wf g;
    // Empty stack
    let st = Seq.empty #obj_addr in
    no_gray_elim_all g';
    empty_stack_props g';
    empty_root_props g';
    mark_inv_intro g' st;
    // fp = mword, which is in the heap
    init_objects_eq g;
    assert (fp == mword);
    fp_valid_intro (mword <: obj_addr) g'
#pop-options

/// =========================================================================
/// Composing the round-trip at spec level
/// =========================================================================

/// After gc_postcondition + density + graph_wf, we can do another GC with empty roots.
/// This is the key bridge: collect's output satisfies collect's input (with empty stack).
#push-options "--z3rlimit 30"
let gc_postcondition_enables_gc
  (h: heap) (fp: U64.t)
  : Lemma (requires gc_postcondition h /\
                    heap_objects_dense h /\
                    Seq.length (objects zero_addr h) > 0 /\
                    graph_wf (create_graph h) /\
                    fp_in_heap fp h /\
                    no_pointer_to_blue h)
          (ensures (let st = Seq.empty #obj_addr in
                    mark_inv h st /\
                    fp_valid fp h /\
                    root_props h st /\
                    no_black_objects h))
  = gc_postcondition_elim h;
    let aux (x: obj_addr) : Lemma
      (requires Seq.mem x (objects zero_addr h))
      (ensures ~(is_gray x h) /\ ~(is_black x h))
    = is_white_iff x h; is_blue_iff x h; is_gray_iff x h; is_black_iff x h
    in
    Classical.forall_intro (Classical.move_requires aux);
    let st = Seq.empty #obj_addr in
    empty_stack_props h;
    empty_root_props h;
    mark_inv_intro h st;
    // fp_valid: either fp is null (not a pointer field) or fp_in_heap gives membership
    if fp = 0UL then fp_valid_not_pointer fp h
    else begin
      SpecSweep.fp_in_heap_elim fp h;
      fp_valid_intro (fp <: obj_addr) h
    end
#pop-options

/// Full alloc → collect bridge: after allocation, we can collect.
/// Proves the core properties (well_formed_heap, no_black_objects).
/// Density, no_pointer_to_blue, and graph_wf preservation is future work.
let alloc_enables_collect
  (g: heap) (fp: U64.t) (wz: nat)
  : Lemma (requires well_formed_heap g /\
                    fl_valid g fp (heap_size / U64.v mword) /\
                    no_black_objects g)
          (ensures (let r = alloc_spec g fp wz in
                    let g' = r.heap_out in
                    well_formed_heap g' /\
                    no_black_objects g'))
  = alloc_spec_preserves_wf g fp wz;
    alloc_preserves_no_black g fp wz

/// =========================================================================
/// The main round-trip theorem (spec level)
/// =========================================================================

/// Starting from a well-formed heap with a valid free list,
/// successive allocations preserve well_formed_heap.
///
/// Verified properties:
///   1. alloc_spec preserves well_formed_heap (verified)
///   2. alloc_spec preserves fl_valid (verified)
///   3. alloc_spec preserves no_black_objects (verified)
///   4. gc_postcondition implies well_formed_heap (verified)
let round_trip_spec
  (g0: heap) (fp0: U64.t) (wz1 wz2: nat)
  : Lemma (requires well_formed_heap g0 /\
                    fl_valid g0 fp0 (heap_size / U64.v mword) /\
                    fl_chain_terminates g0 fp0 (heap_size / U64.v mword) /\
                    no_black_objects g0)
          (ensures (// Step 1: allocate
                    let r1 = alloc_spec g0 fp0 wz1 in
                    well_formed_heap r1.heap_out /\
                    no_black_objects r1.heap_out /\
                    fl_valid r1.heap_out r1.fp_out (heap_size / U64.v mword) /\
                    // Step 2: the output supports another allocation
                    (let r2 = alloc_spec r1.heap_out r1.fp_out wz2 in
                     well_formed_heap r2.heap_out /\
                     no_black_objects r2.heap_out)))
  = // Step 1: first allocation preserves all properties
    alloc_spec_preserves_wf g0 fp0 wz1;
    alloc_preserves_no_black g0 fp0 wz1;
    alloc_preserves_fl_valid g0 fp0 wz1;
    let r1 = alloc_spec g0 fp0 wz1 in
    // Step 2: second allocation preserves wf and no_black
    alloc_spec_preserves_wf r1.heap_out r1.fp_out wz2;
    alloc_preserves_no_black r1.heap_out r1.fp_out wz2

/// =========================================================================
/// End-to-end test: init → alloc → alloc (from a concrete initial state)
/// =========================================================================

/// Starting from a freshly initialized heap, two successive allocations
/// produce well-formed heaps. All properties are fully verified.
let init_alloc_alloc
  (g: heap) (wz1 wz2: nat)
  : Lemma (requires g == Seq.create heap_size 0uy)
          (ensures (let (g', fp) = init_heap_spec g in
                    let r1 = alloc_spec g' fp wz1 in
                    well_formed_heap r1.heap_out /\
                    no_black_objects r1.heap_out /\
                    fl_valid r1.heap_out r1.fp_out (heap_size / U64.v mword) /\
                    (let r2 = alloc_spec r1.heap_out r1.fp_out wz2 in
                     well_formed_heap r2.heap_out /\
                     no_black_objects r2.heap_out)))
  = let (g', fp) = init_heap_spec g in
    init_enables_collect g;
    init_fl_valid g;
    init_fl_chain_terminates g;
    init_no_black g;
    init_wf g;
    round_trip_spec g' fp wz1 wz2

/// =========================================================================
/// End-to-end test: init → collect (GC with empty roots)
/// =========================================================================

/// From init, we can immediately run a GC pass (with no roots).
/// This tests init_enables_collect + gc_precondition assembly.
let init_collect
  (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy)
          (ensures (let (g', fp) = init_heap_spec g in
                    let st = Seq.empty #obj_addr in
                    mark_inv g' st /\
                    fp_valid fp g' /\
                    root_props g' st /\
                    no_black_objects g' /\
                    no_pointer_to_blue g' /\
                    graph_wf (create_graph g') /\
                    heap_objects_dense g'))
  = init_enables_collect g

/// =========================================================================
/// End-to-end test: init → collect → alloc (full GC cycle)
/// =========================================================================

/// From a zeroed heap: init, then mark+sweep (with empty roots),
/// then allocate. This exercises the sweep_produces_fl_valid bridge.
/// All properties are fully verified — zero admits.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let init_collect_alloc
  (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy)
          (ensures (let (g0, fp0) = init_heap_spec g in
                    // mark with empty stack is identity
                    let g_mark = mark g0 Seq.empty in
                    // sweep produces fl_valid
                    let (g_sweep, fp_sweep) = sweep g_mark fp0 in
                    fl_valid g_sweep fp_sweep (heap_size / U64.v mword) /\
                    well_formed_heap g_sweep /\
                    // allocate on post-sweep heap works
                    (let r = alloc_spec g_sweep fp_sweep wz in
                     well_formed_heap r.heap_out)))
  = let (g0, fp0) = init_heap_spec g in
    // Init properties
    init_wf g;
    init_fl_valid g;
    init_objects_eq g;
    init_all_blue g;
    // mark with empty stack = identity
    mark_empty_identity g0;
    assert (mark g0 Seq.empty == g0);
    let g_mark = g0 in
    // fp_in_heap: fp0 = mword, which is in objects
    Seq.lemma_mem_snoc (Seq.empty #hp_addr) (mword <: hp_addr);
    assert (Seq.mem (mword <: obj_addr) (objects 0UL g0));
    assert (fp_in_heap fp0 g0);
    // All objects are blue → vacuous white/non-blue preconditions
    let blue_implies_not_white (o: obj_addr)
      : Lemma (requires Seq.mem o (objects 0UL g0) /\ is_white o g0)
              (ensures U64.v (wosize_of_object o g0) >= 1)
      = is_white_iff o g0; is_blue_iff o g0
    in
    Classical.forall_intro (Classical.move_requires blue_implies_not_white);
    let blue_implies_no_chain (o: obj_addr)
      : Lemma (requires Seq.mem o (objects 0UL g0) /\ ~(is_blue o g0))
              (ensures chain_not_visits g0 fp0 o (heap_size / U64.v mword))
      = ()  // vacuously true — all objects are blue
    in
    Classical.forall_intro (Classical.move_requires blue_implies_no_chain);
    // sweep_produces_fl_valid
    sweep_produces_fl_valid g_mark fp0;
    let (g_sweep, fp_sweep) = SpecSweep.sweep g_mark fp0 in
    // Establish noGreyObjects for sweep_preserves_wf
    // All objects are blue after init → not gray
    let no_grey (obj: obj_addr)
      : Lemma (requires Seq.mem obj (objects 0UL g0))
              (ensures not (is_gray obj g0))
      = is_blue_iff obj g0; is_gray_iff obj g0
    in
    Classical.forall_intro (Classical.move_requires no_grey);
    sweep_preserves_wf g_mark fp0;
    // allocate
    alloc_spec_preserves_wf g_sweep fp_sweep wz
#pop-options

/// =========================================================================
/// Init → fp_in_heap + vertex set properties (for Pulse test)
/// =========================================================================

/// After init, fp_in_heap holds (fp = mword, which is in objects).
let init_fp_in_heap (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy)
          (ensures (let (g', fp) = init_heap_spec g in
                    fp_in_heap fp g'))
  = let (g', fp) = init_heap_spec g in
    init_objects_eq g;
    Seq.lemma_mem_snoc (Seq.empty #hp_addr) (mword <: hp_addr);
    assert (Seq.mem (mword <: obj_addr) (objects 0UL g'))
