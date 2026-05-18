(*
   Pulse GC (Generational) - Top-Level Entry Point Interface

   Provides:
   - gen_alloc: Allocate an object (routes to minor or major by size)
   - minor_collect: Cheney-style BFS collection of minor heap
   - gen_gc: Full generational GC (minor + major collection)
*)

module GC.Gen.Impl

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Impl.MinorHeap
open GC.Impl.Heap
open GC.Impl.Stack
module SpecFields = GC.Spec.Fields
module AllocLemmas = GC.Spec.Allocator.Lemmas
module CheneySpec = GC.Gen.Cheney
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module PromoteSpec = GC.Gen.Promote
module MajorGC = GC.Impl
module SpecGCPost = GC.Spec.Correctness
module Mark = GC.Spec.Mark
module TopLevel = GC.Gen.CombinedGraph.Isomorphism.TopLevel
module CombinedGraph = GC.Gen.CombinedGraph
module GenCorrectness = GC.Gen.Correctness

/// ---------------------------------------------------------------------------
/// Combined generational heap state
/// ---------------------------------------------------------------------------

noeq
type gen_heap_t = {
  minor : minor_heap_t;
  major : heap_t;
  fp_ref : R.ref U64.t;    // major heap free-list head
}

/// Combined slprop for the generational heap:
///   is_minor — ownership of minor heap array + bump pointer
///   is_heap  — ownership of major heap array
///   R.pts_to — ownership of the free-list head reference
let is_gen_heap (gh: gen_heap_t) (d: minor_heap) (b: U64.t)
                (s: heap_state) (fp: U64.t) : slprop =
  is_minor gh.minor d b **
  is_heap gh.major s **
  R.pts_to gh.fp_ref fp

/// ---------------------------------------------------------------------------
/// Allocation
/// ---------------------------------------------------------------------------

/// Allocate an object. Small objects go to minor heap, large ones to major.
/// Returns 0UL on failure (both heaps full).
fn gen_alloc (gh: gen_heap_t) (wosize: U64.t) (tag: U64.t)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pure (
             // Object body size is at least 1 word (no zero-length objects)
             U64.v wosize > 0 /\
             // Tag fits in the 8-bit OCaml header field (0..255)
             U64.v tag < 256 /\
             // Major heap has valid OCaml object layout: headers have valid
             // wosize/color/tag, objects don't overlap, sizes fit within
             // heap bounds, pointer fields target valid objects, and infix
             // structure is correct
             SpecFields.well_formed_heap 's)
  returns obj: U64.t
  // Heap ownership is returned; internal state may change (bump pointer
  // advanced, or a free-list node consumed)
  ensures exists* d2 b2 s2 fp2. is_gen_heap gh d2 b2 s2 fp2

/// ---------------------------------------------------------------------------
/// Minor collection (Cheney BFS: promote reachable + update pointers + reset)
/// ---------------------------------------------------------------------------

/// Trigger a minor collection using Cheney-style BFS:
/// 1. Forward roots (promote reachable minor objects on discovery)
/// 2. BFS scan: for each promoted object, forward its children
/// 3. Update major-heap pointer fields (rewrite minor refs via fwd map)
/// 4. Rewrite program roots
/// 5. Reset minor heap (bump = 0)
///
/// Postcondition: result matches cheney_collect_spec (promotes only reachable
/// objects, not all objects — sound and precise).
///
/// Correctness properties (proven in GC.Gen.CheneyCorrectness):
/// - All pre-existing major objects survive
/// - Heap well-formedness (part 1) preserved
/// - Minor heap reset
/// - Roots rewritten via forwarding map
fn minor_collect (gh: gen_heap_t)
                 (roots: array U64.t) (nroots: SZ.t)
                 (fwd_arr: array U64.t)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pure (
             // Major heap has valid OCaml object layout: every object's
             // header+body fits in the byte array, pointer fields target
             // valid objects, infix headers are well-formed, and no
             // spurious infix tags appear inside object bodies
             SpecFields.well_formed_heap 's /\

             // Free-list from 'fp consists of valid objects: each node is
             // a member of objects(0, major), has wosize >= 1, blue color,
             // and its first field (next pointer) links to another valid
             // node or terminates
             AllocLemmas.fl_valid 's 'fp (heap_size / U64.v mword) /\

             // Free-list traversal from 'fp terminates within
             // heap_size/mword steps (no cycles; the chain is finite)
             AllocLemmas.fl_chain_terminates 's 'fp (heap_size / U64.v mword) /\

             // Object walk is well-formed: stepping from any object's header
             // (at header + (1 + wosize) * 8 bytes) lands on another valid
             // object header. Both allocated and free-list nodes are objects,
             // so the heap is fully partitioned with no unaccounted bytes
             PromoteSpec.heap_objects_dense 's /\

             // Every allocated (non-blue) object is NOT on the free chain;
             // equivalently, the free chain only visits blue objects
             PromoteSpec.chain_objects_blue 's 'fp /\

             // nroots matches the actual root array length
             SZ.v nroots == Seq.length 'rs /\

             // Forwarding array has exactly fwd_array_size entries
             // (sized for the minor heap address range)
             Seq.length 'farr == UpdatePtrs.fwd_array_size /\

             // Forwarding array is zeroed: no stale forwarding entries
             // from a previous collection cycle
             (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\

             // Minor heap bump pointer is word-aligned, within
             // minor_heap_size, and the allocated prefix [0..bump)
             // forms a valid chain of OCaml objects
             minor_wf ({ data = 'd; bump = 'b }) /\

             // Guard completeness: any minor-heap address that passes
             // the runtime object-recognition checks (aligned, positive
             // wosize, fits before bump) is genuinely in the minor
             // object list — no false negatives when scanning
             minor_guards_complete ({ data = 'd; bump = 'b }) /\

             // Major heap contains at least one object (the initial
             // free-list sentinel; needed for free-list operations)
             Seq.length (SpecFields.objects zero_addr 's) > 0)
  ensures exists* d2 b2 s2 fp2 rs2 farr2.
    is_gen_heap gh d2 b2 s2 fp2 **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pure (
      let minor_st : minor_state = { data = 'd; bump = 'b } in
      let res = CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs in
      let prom = CheneySpec.cheney_promote minor_st 's 'fp 'rs in

      // --- Spec refinement ---
      // Post-collection major heap is exactly the Cheney BFS spec output:
      // BFS-promoted reachable minor objects, then pointer fields updated
      // to reflect forwarding
      s2 == res.mc_major /\

      // Post-collection free pointer matches spec (free-list head
      // advanced past all newly promoted objects)
      fp2 == res.mc_fp /\

      // Post-collection roots match spec output
      rs2 == res.mc_roots /\

      // Minor heap has been fully reset (bump pointer = 0, ready for
      // new allocations)
      U64.v b2 == 0 /\

      // --- Object survival ---
      // Every object that existed in the major heap before collection
      // still exists afterward; promotion only adds objects, never
      // removes existing ones
      (forall (x: obj_addr). Seq.mem x (SpecFields.objects zero_addr 's) ==>
        Seq.mem x (SpecFields.objects zero_addr s2)) /\

      // --- Root rewriting ---
      // Each root has been pointwise rewritten through the forwarding
      // map: roots pointing into the minor heap now point to the
      // promoted copy in the major heap; other roots are unchanged
      rs2 == PromoteSpec.rewrite_roots 'rs prom.fwd_map /\

      // --- Structural invariants preserved ---
      // Post-collection heap satisfies size-bounds invariant: every
      // object's header+body fits within the heap byte array
      SpecFields.well_formed_heap_part1 s2 /\

      // Post-collection free-list is valid (each node is a blue object
      // with wosize >= 1 and a valid next link)
      AllocLemmas.fl_valid s2 fp2 (heap_size / U64.v mword) /\

      // Post-collection free-list terminates (no cycles introduced
      // by promotion)
      AllocLemmas.fl_chain_terminates s2 fp2 (heap_size / U64.v mword))

/// ---------------------------------------------------------------------------
/// Full generational GC (minor collection + major collection)
/// ---------------------------------------------------------------------------

/// Full generational GC cycle:
/// 1. Minor collection (Cheney BFS): promote reachable minor objects to major
/// 2. Major collection (mark-and-sweep): reclaim unreachable major objects
///
/// Postcondition provides:
/// - Major GC correctness (5 pillars of mark-and-sweep) on post-minor heap
/// - Minor collection properties (roots rewritten, minor heap reset)
///
/// The caller must provide gc_precondition on the post-minor heap.
/// no_black_objects on the post-minor heap is derived internally from
/// no_black_objects on the pre-minor heap via cheney_collect_no_black.
fn gen_gc (gh: gen_heap_t)
          (roots: array U64.t) (nroots: SZ.t)
          (fwd_arr: array U64.t)
          (st: gray_stack)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           is_gray_stack st 'st **
           pure (
             // ============================
             // Minor collection preconditions
             // ============================

             // Major heap has valid OCaml object layout (see minor_collect)
             SpecFields.well_formed_heap 's /\

             // Free-list from 'fp is valid: each node is a blue object
             // with wosize >= 1 and a valid next link
             AllocLemmas.fl_valid 's 'fp (heap_size / U64.v mword) /\

             // Free-list from 'fp terminates within bounded steps
             AllocLemmas.fl_chain_terminates 's 'fp (heap_size / U64.v mword) /\

             // Object walk is well-formed: stepping header-to-header covers
             // the entire heap with no unaccounted bytes (both allocated
             // and free-list nodes are valid objects)
             PromoteSpec.heap_objects_dense 's /\

             // Free chain visits only blue objects (allocated objects
             // are not on the free list)
             PromoteSpec.chain_objects_blue 's 'fp /\

             // nroots matches root array length
             SZ.v nroots == Seq.length 'rs /\

             // Forwarding array is correctly sized for the minor
             // heap address range
             Seq.length 'farr == UpdatePtrs.fwd_array_size /\

             // Forwarding array is zeroed (clean slate for this cycle)
             (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\

             // Minor heap is well-formed: bump pointer aligned,
             // within bounds, allocated prefix is a valid object chain
             minor_wf ({ data = 'd; bump = 'b }) /\

             // Guard completeness for minor heap object recognition
             // (see minor_collect for details)
             minor_guards_complete ({ data = 'd; bump = 'b }) /\

             // Major heap has at least one object (free-list sentinel)
             Seq.length (SpecFields.objects zero_addr 's) > 0 /\

             // No major-heap object is black: the tri-color starting
             // state requires all objects to be white (allocated) or
             // blue (free) before any GC cycle begins
             Mark.no_black_objects 's /\

             // ============================
             // Major GC preconditions on the POST-minor-collection heap
             // ============================
             // These must hold on the heap state AFTER Cheney promotion,
             // since mark-and-sweep runs on that heap. The caller states
             // them in terms of cheney_collect_spec's output.
             // Includes: bounded_mark_inv (gray stack capacity sufficient),
             // fp_valid, root_props (roots are valid object addresses),
             // fp_in_heap, no_black_objects on post-minor heap,
             // no_pointer_to_blue (live objects don't point to free-list
             // nodes), no_scan_invariant (objects with tag >= 251 have
             // no pointer fields), gray/black objects are in the stack,
             // and graph well-formedness
             (let res = CheneySpec.cheney_collect_spec
                          ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs in
              MajorGC.gc_precondition res.mc_major 'st res.mc_fp (stack_capacity st)))
  returns final_fp: U64.t
  ensures exists* d2 b2 s2 rs2 farr2 st2.
    is_gen_heap gh d2 b2 s2 final_fp **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    is_gray_stack st st2 **
    pure (
      let minor_st : minor_state = { data = 'd; bump = 'b } in
      let res = CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs in
      let prom = CheneySpec.cheney_promote minor_st 's 'fp 'rs in

      // --- Major GC correctness (applied to the post-minor heap) ---

      // Post-GC heap is well-formed AND every object is white or blue
      // (no gray or black objects remain — marking is complete and
      // colors have been reset by sweep)
      SpecGCPost.gc_postcondition s2 /\

      // Full mark-and-sweep correctness theorem (5 pillars):
      //   1. well_formed_heap preserved through mark+sweep
      //   2. Reachability-based survival: objects reachable from roots
      //      in the post-minor heap survive sweep
      //   3. Successor preservation: surviving objects' pointer fields
      //      still point to surviving objects
      //   4. Color reset: all objects are white or blue after sweep
      //   5. Field data preservation: non-color header bits and object
      //      body data are unchanged by mark+sweep
      // Here res.mc_major is the post-minor heap (input to mark-sweep),
      // s2 is the final post-sweep heap, and 'st is the gray stack
      // contents (roots for the major GC)
      SpecGCPost.full_gc_correctness res.mc_major s2 'st /\

      // --- Minor collection properties ---

      // Roots match the Cheney spec's output
      rs2 == res.mc_roots /\

      // Roots have been pointwise rewritten through the forwarding map:
      // minor-heap pointers now point to promoted copies in major heap
      rs2 == PromoteSpec.rewrite_roots 'rs prom.fwd_map /\

      // Minor heap has been fully reset (bump = 0)
      U64.v b2 == 0 /\

      // --- Post-minor heap properties (proven by minor_collect) ---

      // Pre-existing major-heap objects survive minor collection
      // (promotion only adds, never removes)
      (forall (x: obj_addr). Seq.mem x (SpecFields.objects zero_addr 's) ==>
        Seq.mem x (SpecFields.objects zero_addr res.mc_major)) /\

      // Post-minor heap satisfies size-bounds invariant
      SpecFields.well_formed_heap_part1 res.mc_major /\

      // Post-minor free-list is valid
      AllocLemmas.fl_valid res.mc_major res.mc_fp (heap_size / U64.v mword) /\

      // Post-minor free-list terminates
      AllocLemmas.fl_chain_terminates res.mc_major res.mc_fp (heap_size / U64.v mword))

/// ---------------------------------------------------------------------------
/// gen_gc with isomorphism postcondition
/// ---------------------------------------------------------------------------
///
/// Strengthened variant of gen_gc that additionally proves:
///   The pre-GC combined graph (minor + major) is isomorphic to
///   the post-GC major graph, restricted to reachable vertices.
///
/// The isomorphism is witnessed by fwd_morphism:
///   MinorV v → fwd(v)  (promoted copy in major heap)
///   MajorV v → v       (identity on major objects)
///
/// The 4 iso_* preconditions are explicit, auditable assumptions about the
/// forwarding map's structural properties. They are individually dischargeable
/// from the Cheney BFS algorithm's correctness properties.
///
/// NOTE: The isomorphism is stated about the spec-level sweep heap
/// (fst (Sweep.sweep (Mark.mark mc_major stack) fp)), not the coalesced
/// runtime heap. Since coalescing only merges free (blue) blocks without
/// affecting surviving objects' fields, the reachable subgraph is identical.
///
/// PARAMETERS:
///   gh            — The gen_heap_t record: {major, minor_data, bump_ref, fp_ref}
///   roots         — Array of root pointers (mutator roots + remembered set)
///   nroots        — Length of roots array (SizeT.t for bounds safety)
///   fwd_arr       — Forwarding array (maps minor addr/8 → new major addr)
///   st            — Gray stack for mark phase (bounded-depth DFS)
///   combined_roots — (Ghost) Abstract vertices designating the combined graph's roots
///
fn gen_gc_iso (gh: gen_heap_t)
              (roots: array U64.t) (nroots: SZ.t)
              (fwd_arr: array U64.t)
              (st: gray_stack)
              (#combined_roots: Ghost.erased (Seq.seq CombinedGraph.combined_vertex))
  requires is_gen_heap gh 'd 'b 's 'fp **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           is_gray_stack st 'st **
           pure (
             // ---------------------------------------------------------------
             // (1) Major heap structural well-formedness
             // ---------------------------------------------------------------
             // The major heap is valid: every object fits in bounds, pointers
             // lie within object bodies, infix layout is consistent, and no
             // live object has infix_tag. Callers establish this from the
             // initial heap state or from the previous GC cycle's postcondition.
             SpecFields.well_formed_heap 's /\

             // ---------------------------------------------------------------
             // (2) Free-list validity
             // ---------------------------------------------------------------
             // 'fp starts a well-formed chain of blue (free) objects in 's.
             // Each node's "next" pointer points to another blue object or
             // terminates. The chain has no cycles and stays within heap bounds.
             // Established by the allocator or previous sweep/coalesce phase.
             AllocLemmas.fl_valid 's 'fp (heap_size / U64.v mword) /\

             // ---------------------------------------------------------------
             // (3) Free-list termination
             // ---------------------------------------------------------------
             // Walking the free-list from 'fp terminates within bounded steps
             // (heap_size / mword). Prevents infinite loops during allocation
             // or sweep. Established together with fl_valid.
             AllocLemmas.fl_chain_terminates 's 'fp (heap_size / U64.v mword) /\

             // ---------------------------------------------------------------
             // (4) Object layout density
             // ---------------------------------------------------------------
             // Objects in the major heap are densely packed: if object at addr
             // `a` has wosize `w`, then the next object starts at `a + (w+1)*8`.
             // This ensures linear-scan enumeration finds all objects. Holds by
             // construction from allocation (allocator maintains contiguity).
             PromoteSpec.heap_objects_dense 's /\

             // ---------------------------------------------------------------
             // (5) Free-list nodes are blue
             // ---------------------------------------------------------------
             // Every object on the free-list chain has color = Blue.
             // Ensures promotion never overwrites a free-list node that
             // still appears "live". Maintained by sweep (which colors freed
             // blocks blue) and never changed by the mutator.
             PromoteSpec.chain_objects_blue 's 'fp /\

             // ---------------------------------------------------------------
             // (6) Root array length agreement
             // ---------------------------------------------------------------
             // The SizeT nroots matches the actual sequence length.
             // Trivially established: nroots is the length passed by the caller.
             SZ.v nroots == Seq.length 'rs /\

             // ---------------------------------------------------------------
             // (7) Forwarding array size
             // ---------------------------------------------------------------
             // The forwarding array has exactly `fwd_array_size` entries
             // (= minor_heap_size / 8). One slot per possible minor object
             // address. Established at allocation time.
             Seq.length 'farr == UpdatePtrs.fwd_array_size /\

             // ---------------------------------------------------------------
             // (8) Forwarding array initially zeroed
             // ---------------------------------------------------------------
             // All entries are 0 (no forwarding has occurred yet).
             // The Cheney algorithm writes non-zero entries as it promotes.
             // Caller must zero the array between GC cycles.
             (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\

             // ---------------------------------------------------------------
             // (9) Minor heap well-formedness
             // ---------------------------------------------------------------
             // Bump pointer is 8-byte aligned, within minor_heap_size, and
             // the allocated-object chain from offset 0 to bump is valid
             // (each object header has consistent wosize and the objects
             // tile the region without gaps). Maintained by the minor allocator.
             minor_wf ({ data = 'd; bump = 'b }) /\

             // ---------------------------------------------------------------
             // (10) Minor heap guard completeness
             // ---------------------------------------------------------------
             // Trust assumption: every aligned address below bump with a
             // plausible header appears in the minor_objects enumeration.
             // This ensures live_set_of captures all reachable minor objects.
             // Established by the minor allocator's initialization protocol.
             minor_guards_complete ({ data = 'd; bump = 'b }) /\

             // ---------------------------------------------------------------
             // (11) Major heap has at least one object
             // ---------------------------------------------------------------
             // Required for graph construction (create_graph expects non-empty
             // object list). Trivially holds after initial heap setup (the
             // first free block counts as an object).
             Seq.length (SpecFields.objects zero_addr 's) > 0 /\

             // ---------------------------------------------------------------
             // (12) No black objects before GC
             // ---------------------------------------------------------------
             // All objects start white or blue (not yet marked). This is the
             // initial coloring invariant: black is only used during marking.
             // Guaranteed by the previous cycle's sweep (resets black → white)
             // or by initial heap setup.
             Mark.no_black_objects 's /\

             // ---------------------------------------------------------------
             // (13) Major GC precondition on post-minor heap
             // ---------------------------------------------------------------
             // After Cheney promotion, the resulting major heap (res.mc_major)
             // satisfies all preconditions for the mark-sweep collector:
             //   - bounded_mark_inv: wf heap, stack props, objects > 0, density
             //   - fp_valid: free-list is valid in post-promotion heap
             //   - root_props: all stack entries are valid gray/black objects
             //   - fp_in_heap: free-list pointer is within heap bounds
             //   - no_black_objects: coloring is clean
             //   - no_pointer_to_blue: no live object points into free blocks
             //   - no_scan_invariant: no-scan objects have no pointer fields
             //   - graph_wf, is_vertex_set, subset_vertices: graph is well-formed
             //
             // Established by cheney_collect's correctness proof (the post-
             // promotion heap inherits structural properties from the original
             // plus the allocator's preservation lemmas).
             (let res = CheneySpec.cheney_collect_spec
                          ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs in
              MajorGC.gc_precondition res.mc_major 'st res.mc_fp (stack_capacity st)) /\

             // ---------------------------------------------------------------
             // ISOMORPHISM-SPECIFIC PRECONDITIONS
             // The following are needed ON TOP of the standard gen_gc
             // preconditions to derive the structural isomorphism theorem.
             // ---------------------------------------------------------------
             (let minor_st : minor_state = { data = 'd; bump = 'b } in

              // ---------------------------------------------------------------
              // (14) Minor fields well-formed
              // ---------------------------------------------------------------
              // Every pointer field of a live minor object either:
              //   (a) points to another live minor object, or
              //   (b) points to a valid major-heap object.
              // This ensures the combined graph has no dangling edges from
              // minor vertices. Established from the write barrier + allocator
              // invariants (mutator can only store valid pointers).
              GenCorrectness.minor_fields_well_formed minor_st 's 'rs /\

              // ---------------------------------------------------------------
              // (15) All promotions succeed
              // ---------------------------------------------------------------
              // Every live minor object with positive wosize receives a nonzero
              // forwarding address (the allocator had enough free space).
              // Established from sufficient free-list capacity relative to
              // live_set size. In practice, the GC aborts if OOM occurs.
              GenCorrectness.all_promotions_succeed minor_st 's 'fp 'rs /\

              // ---------------------------------------------------------------
              // (16) Allocated objects avoid the free chain
              // ---------------------------------------------------------------
              // Non-blue (allocated/live) objects are NOT on the free-list.
              // This is the fundamental allocator invariant separating free
              // blocks from live data. Maintained by allocation (removes node
              // from chain) and sweep (adds node back as blue).
              GenCorrectness.allocated_objects_avoid_chain 's 'fp /\

              // ---------------------------------------------------------------
              // (17) Post-promotion pointer closure
              // ---------------------------------------------------------------
              // After promoting all live minor objects, every pointer field in
              // the post-promotion major heap either:
              //   (a) points to a valid major object directly, or
              //   (b) can be resolved through the forwarding map.
              // This ensures the final update_pointers pass produces a closed
              // heap (no dangling references). Follows from minor_fields_wf +
              // promotion correctness.
              GenCorrectness.post_promote_pointer_closure minor_st 's 'fp 'rs /\

              // ---------------------------------------------------------------
              // (18) Live set contains no infix objects
              // ---------------------------------------------------------------
              // Objects in the minor live set do not have infix_tag (249).
              // Infix objects are internal sub-objects (e.g., closures inside
              // closures) that should not be independently promoted. The minor
              // allocator never creates infix objects.
              PromoteSpec.live_set_no_infix minor_st (PromoteSpec.live_set_of minor_st 's 'rs) /\

              // ---------------------------------------------------------------
              // (19) Major heap no-scan invariant
              // ---------------------------------------------------------------
              // Objects with tag >= no_scan_tag (251) contain only raw data
              // (no pointer fields). Ensures the GC never traces into strings,
              // custom blocks, or other opaque payloads. Maintained by the
              // allocator (sets tag correctly) and never mutated after creation.
              SpecFields.no_scan_invariant 's /\

              // ---------------------------------------------------------------
              // (20) Minor heap no-scan invariant
              // ---------------------------------------------------------------
              // Same as (19) but for the minor heap: minor objects with
              // tag >= no_scan_tag have no pointer fields. Maintained by the
              // minor allocator's tag assignment.
              PromoteSpec.minor_no_scan_invariant minor_st /\

              // ---------------------------------------------------------------
              // (21) All live minor objects have positive wosize
              // ---------------------------------------------------------------
              // Every object in the live set has wosize > 0 (at least one word
              // of payload). This ensures the forwarding map can distinguish
              // promoted objects from empty headers and that the allocator
              // actually allocates space. Follows from minor_wf (objects in the
              // chain have valid headers).
              (let live_set = PromoteSpec.live_set_of minor_st 's 'rs in
               forall (v: U64.t). Seq.mem v live_set ==> GC.Gen.MinorHeap.minor_wosize minor_st v > 0) /\

              // ---------------------------------------------------------------
              // (22) Isomorphism structural bridge (OPAQUE BUNDLE)
              // ---------------------------------------------------------------
              // Bundles 4 semantic assumptions about the forwarding map and
              // combined graph, which together enable the isomorphism proof:
              //
              //   iso_structural_preconditions:
              //     Root correspondence (major_stack ↔ combined_roots via fwd),
              //     fwd nonzero on live_set, fwd injective, field correspondence,
              //     reachability bridge, promoted objects disjoint from old major.
              //
              //   iso_edge_bridge_forward:
              //     Combined-graph edges are preserved in post-promotion major.
              //
              //   iso_surjectivity:
              //     Every reachable post-GC object has a pre-image in the
              //     combined graph (no orphans created by GC).
              //
              //   iso_edge_backward:
              //     Post-GC edges correspond to combined-graph edges
              //     (no spurious edges introduced).
              //
              // These are individually dischargeable from the Cheney BFS
              // algorithm's correctness properties. They are opaque to avoid
              // exposing complex quantifiers to Pulse's slprop elaborator.
              // Use TopLevel.iso_preconditions_bundle_intro to construct,
              // and TopLevel.iso_preconditions_bundle_elim to decompose.
              (let res = CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs in
               TopLevel.iso_preconditions_bundle minor_st 's 'fp 'rs combined_roots 'st res.mc_fp)))
  returns final_fp: U64.t
  ensures exists* d2 b2 s2 rs2 farr2 st2.
    is_gen_heap gh d2 b2 s2 final_fp **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    is_gray_stack st st2 **
    pure (
      let minor_st : minor_state = { data = 'd; bump = 'b } in
      let res = CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs in
      let prom = CheneySpec.cheney_promote minor_st 's 'fp 'rs in

      // =================================================================
      // POSTCONDITION (A): Major heap post-GC well-formedness
      // =================================================================
      // The final major heap is structurally valid: all objects fit within
      // bounds, surviving objects are white (color reset), free blocks are
      // blue. The heap is ready for another allocation/GC cycle.
      // Callers can use this to re-establish gen_gc preconditions.
      SpecGCPost.gc_postcondition s2 /\

      // =================================================================
      // POSTCONDITION (B): Full GC correctness (5 pillars)
      // =================================================================
      // Bundles the 5 correctness properties of mark-sweep:
      //   1. Well-formedness preservation (heap structure intact)
      //   2. Reachability survival (reachable objects not freed)
      //   3. Successor preservation (edges between survivors intact)
      //   4. Color reset (all objects white or blue after sweep)
      //   5. Field data preservation (non-color header bits unchanged)
      //
      // This is stated relative to res.mc_major (the POST-CHENEY major
      // heap before mark-sweep) and s2 (the final heap after mark-sweep).
      // Callers use this to reason about what survived the GC.
      SpecGCPost.full_gc_correctness res.mc_major s2 'st /\

      // =================================================================
      // POSTCONDITION (C): Root array updated to post-Cheney roots
      // =================================================================
      // The roots array now contains the rewritten root pointers:
      // each minor pointer has been replaced by its forwarded major address.
      // Major pointers are unchanged. This is the canonical root set for
      // the next mutator phase.
      rs2 == res.mc_roots /\

      // =================================================================
      // POSTCONDITION (D): Root rewriting characterization
      // =================================================================
      // Gives a more explicit characterization of how roots were updated:
      // rs2 == rewrite_roots 'rs fwd_map, where fwd_map is the Cheney
      // forwarding function. For each root r:
      //   - If r is a minor pointer and fwd_map(r) ≠ 0: replaced by fwd_map(r)
      //   - Otherwise: unchanged.
      // Callers can use this to track individual root provenance.
      rs2 == PromoteSpec.rewrite_roots 'rs prom.fwd_map /\

      // =================================================================
      // POSTCONDITION (E): Minor heap reset
      // =================================================================
      // The minor bump pointer is reset to 0 (minor heap is empty).
      // The minor heap is ready for fresh allocations. All previously
      // live minor objects have been promoted to the major heap.
      U64.v b2 == 0 /\

      // =================================================================
      // POSTCONDITION (F): Major object set monotonicity
      // =================================================================
      // Every object that existed in the original major heap 's still
      // exists in the post-Cheney major heap. Promotion only ADDS new
      // objects (from minor → major); it never removes existing ones.
      // This is useful for proving that external references to major
      // objects remain valid after minor collection.
      (forall (x: obj_addr). Seq.mem x (SpecFields.objects zero_addr 's) ==>
        Seq.mem x (SpecFields.objects zero_addr res.mc_major)) /\

      // =================================================================
      // POSTCONDITION (G): Post-Cheney heap partial well-formedness
      // =================================================================
      // The post-promotion major heap satisfies well_formed_heap_part1:
      // all objects fit within heap bounds. (The full well_formed_heap is
      // inside gc_postcondition on s2.) This intermediate fact is useful
      // for callers who need bounds reasoning on the pre-sweep heap.
      SpecFields.well_formed_heap_part1 res.mc_major /\

      // =================================================================
      // POSTCONDITION (H): Post-Cheney free-list valid
      // =================================================================
      // The free-list in the post-promotion heap is still well-formed.
      // Promotion consumed some free blocks but left the remaining chain
      // intact. Useful for callers reasoning about available memory.
      AllocLemmas.fl_valid res.mc_major res.mc_fp (heap_size / U64.v mword) /\

      // =================================================================
      // POSTCONDITION (I): Post-Cheney free-list terminates
      // =================================================================
      // The post-promotion free-list still terminates within bounded steps.
      AllocLemmas.fl_chain_terminates res.mc_major res.mc_fp (heap_size / U64.v mword) /\

      // =================================================================
      // POSTCONDITION (J): ISOMORPHISM — reachable subgraph preserved
      // =================================================================
      // The main theorem: the pre-GC combined graph (minor objects +
      // major objects + inter-generational edges), when restricted to
      // vertices reachable from combined_roots, is graph-isomorphic to
      // the post-GC major graph restricted to vertices reachable from
      // the mark roots.
      //
      // Concretely (via isomorphism_postcondition_elim):
      //
      //   reachable_implies_forwarded:
      //     Every minor vertex reachable in the combined graph has a
      //     nonzero forwarding address (it was promoted successfully).
      //
      //   reachable_subgraph_isomorphism:
      //     The fwd_morphism (MinorV v ↦ fwd(v), MajorV v ↦ v) is a
      //     graph isomorphism between:
      //       - Source: combined_graph restricted to combined_roots-reachable
      //       - Target: post-sweep major graph restricted to mark-reachable
      //     Specifically: edges are bijectively preserved, the morphism is
      //     injective on reachable vertices, and every reachable post-GC
      //     vertex has a pre-image in the combined graph.
      //
      // This guarantees the GC preserves the full object graph structure:
      // no reachable objects are lost, no spurious edges are created, and
      // no edges between reachable objects are destroyed. It is the
      // strongest possible correctness statement for a copying/compacting GC.
      //
      // Callers use TopLevel.isomorphism_postcondition_elim to decompose
      // this into the two constituent properties.
      TopLevel.isomorphism_postcondition minor_st 's 'fp 'rs combined_roots 'st res.mc_fp)
