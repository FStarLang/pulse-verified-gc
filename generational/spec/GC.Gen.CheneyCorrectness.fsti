/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyCorrectness — End-to-end correctness for Cheney minor collector
/// ---------------------------------------------------------------------------
///
/// This module states the main correctness theorem for the Cheney BFS minor
/// collector (cheney_collect_spec from GC.Gen.Cheney). The spec models:
///   1. BFS promotion of reachable minor objects into the major heap
///   2. Updating all major-heap pointer fields via the forwarding map
///   3. Rewriting program roots via the forwarding map
///   4. Resetting the minor heap (bump = 0)
///
/// The result type is minor_collect_result with fields:
///   mc_major  — the post-collection major heap (byte sequence)
///   mc_fp     — the post-collection free-list head
///   mc_minor  — the post-collection minor heap state
///   mc_roots  — the post-collection program roots
///   mc_fwd    — the forwarding map (minor addr → major addr, or 0 if not forwarded)
///
/// Properties proved:
///
/// 1. **Object survival**: all pre-existing major-heap objects survive
///    (promotion only appends into free-list nodes; never removes objects)
/// 2. **Heap well-formedness (part 1)**: every object's header+body fits
///    within the heap byte array after promotion
/// 3. **Minor reset**: minor heap bump pointer reset to 0
/// 4. **Root rewriting**: roots pointwise rewritten through the forwarding map
///    (minor-heap pointers replaced with their promoted major-heap addresses)
///
/// Properties 1-4 are UNCONDITIONAL — they hold even if the major heap
/// runs out of free-list space during promotion (partial promotion is safe).
///
/// 5. **BFS completeness** (CONDITIONAL on sufficient space): all minor objects
///    reachable from roots via minor_successors are forwarded.
///    This requires cheney_no_oom — that no promote_object call failed.

module GC.Gen.CheneyCorrectness

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Cheney

module AllocLemmas = GC.Spec.Allocator.Lemmas
module MH = GC.Spec.MajorHeap
module SpecMajorAlloc = GC.Spec.MajorAllocator
module PromotionDemand = GC.Gen.PromotionDemand
module ChunkedCheney = GC.Gen.ChunkedCheney
module ChunkedUpdate = GC.Gen.ChunkedUpdate
module CheneyPres = GC.Gen.CheneyPreservation
module GenInv = GC.Gen.HeapInvariant
module CG = GC.Gen.CombinedGraph

/// ---------------------------------------------------------------------------
/// Property 1: Object survival — pre-existing major objects survive collection
/// ---------------------------------------------------------------------------

/// Every object address present in objects(0, major) before collection is
/// still present in objects(0, mc_major) after collection. Cheney promotion
/// consumes free-list nodes to hold promoted objects, but never overwrites
/// or removes any existing allocated object.
///
/// Preconditions: the major heap is well-formed, and the free-list from fp
/// is valid and terminates. These ensure promote_object writes only into
/// legitimate free-list nodes.
val cheney_collect_preserves_objects
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      // Major heap has valid OCaml object layout
      well_formed_heap major /\
      // Free-list from fp: each node is a valid blue object with wosize >= 1
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      // Free-list traversal terminates (no cycles)
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
    (ensures (let res = cheney_collect_spec minor major fp roots in
              // Every pre-existing object address is still in the post-collection object list
              forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                Seq.mem x (objects zero_addr res.mc_major)))

/// ---------------------------------------------------------------------------
/// Property 2: Heap size-bounds invariant preserved after collection
/// ---------------------------------------------------------------------------

/// After collection, every object in the post-collection heap still has its
/// header+body fitting within the heap byte array. This is the "part 1"
/// sub-invariant of well_formed_heap (the weakest component, but sufficient
/// for safe object traversal).
///
/// Note: full well_formed_heap (parts 1-4) is NOT preserved unconditionally
/// because promotion may violate pointer-closure (part 2) if the forwarding
/// map introduces dangling minor-heap references. Part 1 alone is always safe.
val cheney_collect_preserves_wfh_part1
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      // Major heap well-formed
      well_formed_heap major /\
      // Free-list valid and terminating
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
    (ensures
      // Every object's header+body fits within the post-collection heap byte array
      well_formed_heap_part1 (cheney_collect_spec minor major fp roots).mc_major)

/// ---------------------------------------------------------------------------
/// Property 3: Minor heap is properly reset
/// ---------------------------------------------------------------------------

/// After collection, the minor heap is well-formed and its bump pointer is 0.
/// This means the entire minor heap is available for new allocations.
/// This property is UNCONDITIONAL — no preconditions required.
val cheney_collect_resets_minor
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (ensures (let res = cheney_collect_spec minor major fp roots in
              // Minor heap satisfies structural well-formedness
              // (bump aligned, within bounds, object chain valid)
              minor_wf res.mc_minor /\
              // Bump pointer is 0: entire minor heap is free
              U64.v res.mc_minor.bump == 0))

/// ---------------------------------------------------------------------------
/// Property 4: Roots are rewritten via forwarding map
/// ---------------------------------------------------------------------------

/// The post-collection roots equal rewrite_roots(original_roots, fwd_map),
/// where fwd_map is the forwarding map produced by cheney_promote.
/// Pointwise: each root r is replaced by fwd_map(r) if fwd_map(r) != 0
/// (i.e., if r pointed into the minor heap and was forwarded), or left
/// unchanged otherwise.
/// This property is UNCONDITIONAL — no preconditions required.
val cheney_collect_rewrites_roots
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (ensures (let res = cheney_collect_spec minor major fp roots in
              let prom = cheney_promote minor major fp roots in
              // Post-collection roots == original roots pointwise-rewritten
              // through the forwarding map (minor addrs → major addrs)
              res.mc_roots == rewrite_roots roots prom.fwd_map))

/// ---------------------------------------------------------------------------
/// Main theorem: composition of properties 1-5 (unconditional)
/// ---------------------------------------------------------------------------

/// The main correctness theorem for Cheney collection. Composes all four
/// unconditional properties plus allocator invariant preservation into a
/// single lemma for convenient use in the Pulse implementation.
///
/// This is what GC.Gen.Impl.fst calls to establish Cheney collection
/// postconditions around the full minor collection path.
val cheney_gc_correct
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      // Major heap has valid OCaml object layout (all 4 well-formedness parts)
      well_formed_heap major /\
      // Free-list from fp: each node is a valid blue object, wosize >= 1,
      // and the next-pointer chain is valid
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      // Free-list terminates within bounded steps (no cycles)
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      // Free chain only visits blue objects: no allocated (non-blue) object
      // appears on the free list (prevents promote_object from clobbering
      // live data)
      chain_objects_blue major fp)
    (ensures (let res = cheney_collect_spec minor major fp roots in
              let prom = cheney_promote minor major fp roots in

              // Property 1 — Object survival: every object address in the
              // pre-collection major heap is still present after collection
              (forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                Seq.mem x (objects zero_addr res.mc_major)) /\

              // Property 2 — Size-bounds invariant: every post-collection
              // object's header+body fits within the heap byte array
              well_formed_heap_part1 res.mc_major /\

              // Property 3a — Post-collection free-list validity: the new
              // free-list head (res.mc_fp) leads through valid blue objects
              AllocLemmas.fl_valid res.mc_major res.mc_fp (heap_size / U64.v mword) /\

              // Property 3b — Post-collection free-list terminates (no
              // cycles introduced by consuming free-list nodes for promotion)
              AllocLemmas.fl_chain_terminates res.mc_major res.mc_fp (heap_size / U64.v mword) /\

              // Property 4a — Minor heap well-formed (bump aligned, in bounds)
              minor_wf res.mc_minor /\

              // Property 4b — Minor heap fully reset: bump = 0, entire
              // minor region available for new allocations
              U64.v res.mc_minor.bump == 0 /\

              // Property 5 — Root rewriting: each root is pointwise rewritten
              // through fwd_map; roots that pointed into the minor heap now
              // point to the promoted copy in the major heap
              res.mc_roots == rewrite_roots roots prom.fwd_map))

/// ---------------------------------------------------------------------------
/// Property 6: BFS completeness (conditional on sufficient space)
/// ---------------------------------------------------------------------------

open GC.Gen.Reachability

/// BFS completeness: every minor-heap object reachable from the program roots
/// (via the minor_reachable transitive closure) is forwarded by cheney_promote,
/// provided no out-of-memory occurred during the BFS.
///
/// minor_reachable(minor, roots) computes the set of minor-heap object
/// addresses reachable from roots via minor_successors (the pointer fields
/// of minor-heap objects that point to other minor-heap objects).
///
/// The precondition cheney_no_oom says: the final forwarding map produced by
/// cheney_promote covers all roots and is closed under minor_successors.
/// This is the structural property the BFS naturally produces when every
/// promote_object call succeeds (i.e., the major-heap free-list had enough
/// space for all reachable objects).
///
/// The conclusion: for every reachable minor address x, either:
///   - fwd_map(x) != 0UL (x was forwarded to a major-heap address), or
///   - minor_wosize(minor, x) == 0 (x has zero body size, a degenerate
///     object that needs no promotion)
///
/// The proof is NON-TRIVIAL: it uses structural induction on the
/// minor_reachable definition to show that root-coverage + successor-closure
/// implies full reachability coverage. See GC.Gen.CheneyBFS for details.
val cheney_promotes_all_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      // The BFS completed without running out of free-list space:
      // the forwarding map covers all roots and is closed under
      // minor_successors (every child of a forwarded object is also forwarded)
      GC.Gen.CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures (let prom = cheney_promote minor major fp roots in
              // Every reachable minor object is forwarded (or has zero wosize)
              forall (x: U64.t). Seq.mem x (minor_reachable minor roots) ==>
                prom.fwd_map x <> 0UL \/ minor_wosize minor x = 0))

/// Chunked/preflight analogue of `cheney_promotes_all_reachable`: after the
/// optional major-heap head-capacity expansion and full chunked minor
/// collection, every minor object reachable from the original roots was
/// forwarded, unless it is zero-sized.
val chunked_cheney_collect_after_preflight_forwards_reachable
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
     minor_wf minor /\
     alloc_fuel > 1 /\
     GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
     SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
     GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
     (SpecMajorAlloc.major_fl_head_wosize major fp <
      PromotionDemand.minor_promotion_demand minor + 1 ==>
      MH.chunk_disjoint_from_all fresh major /\
      fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
      U64.v fresh.base >= U64.v zero_addr /\
      SpecMajorAlloc.fresh_chunk_wosize fresh >=
        PromotionDemand.minor_promotion_demand minor + 1 /\
      CG.chunked_all_major_object_expansion_safe
        major fresh (MH.major_objects major) 0))
    (ensures
     (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
      let r =
        SpecMajorAlloc.ensure_major_head_capacity_spec
          major fp alloc_fuel needed fresh in
      let collect =
        ChunkedCheney.chunked_cheney_collect_spec
          minor r.capacity_major_out r.capacity_fp_out roots
          r.capacity_fuel_out in
      forall (x: U64.t). Seq.mem x (minor_reachable minor roots) ==>
        collect.cmc_fwd x <> 0UL \/ minor_wosize minor x = 0))

/// Chunked/preflight end-to-end minor-collection correctness bundle.  This is
/// the client-facing analogue of `cheney_gc_correct` for the current chunked
/// collection shell: optional head-capacity expansion, chunked Cheney
/// promotion, chunked major-pointer update, root rewrite, and minor reset.
val chunked_cheney_gc_correct_after_preflight
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
     minor_wf minor /\
     alloc_fuel > 1 /\
     GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
     SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
     GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
     (SpecMajorAlloc.major_fl_head_wosize major fp <
      PromotionDemand.minor_promotion_demand minor + 1 ==>
      MH.chunk_disjoint_from_all fresh major /\
      fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
      U64.v fresh.base >= U64.v zero_addr /\
      SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
      CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
     (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
      let r =
       SpecMajorAlloc.ensure_major_head_capacity_spec
         major fp alloc_fuel needed fresh in
      let prom =
       ChunkedCheney.chunked_cheney_promote
         minor r.capacity_major_out r.capacity_fp_out roots
         r.capacity_fuel_out in
      let collect =
       ChunkedCheney.chunked_cheney_collect_spec
         minor r.capacity_major_out r.capacity_fp_out roots
         r.capacity_fuel_out in
      collect.cmc_fp == prom.fp_final /\
      collect.cmc_minor == minor_reset minor /\
      minor_wf collect.cmc_minor /\
      U64.v collect.cmc_minor.bump == 0 /\
      collect.cmc_roots == rewrite_roots roots prom.fwd_map /\
      collect.cmc_fwd == prom.fwd_map /\
      CheneyPres.chunked_fwd_targets_above_minor collect.cmc_fwd /\
      GenInv.chunked_major_alloc_shape
       collect.cmc_major collect.cmc_fp r.capacity_fuel_out /\
      SpecMajorAlloc.major_fl_chain_terminates
       collect.cmc_major collect.cmc_fp r.capacity_fuel_out = true /\
      GenInv.chunked_chain_objects_blue
       collect.cmc_major collect.cmc_fp r.capacity_fuel_out /\
      (forall (src: obj_addr).
       Seq.mem src (MH.major_objects major) ==>
       Seq.mem src (MH.major_objects collect.cmc_major)) /\
      (forall (src: obj_addr). forall (hdr: U64.t).
       Seq.mem src (MH.major_objects major) /\
       MH.read_word_in_major major (GC.Spec.Heap.hd_address src) == Some hdr /\
       GC.Spec.Object.getColor hdr <> GC.Lib.Header.Blue /\
       U64.v (GC.Spec.Object.getWosize hdr) >= 1 ==>
       MH.read_word_in_major collect.cmc_major (GC.Spec.Heap.hd_address src) ==
         Some hdr) /\
      (forall (src: obj_addr). forall (hdr: U64.t).
       forall (j:nat). forall (field_addr: hp_addr).
       forall (old: U64.t).
       Seq.mem src (MH.major_objects major) /\
       MH.read_word_in_major major (GC.Spec.Heap.hd_address src) == Some hdr /\
       GC.Spec.Object.getColor hdr <> GC.Lib.Header.Blue /\
       j < U64.v (GC.Spec.Object.getWosize hdr) /\
       U64.v field_addr == U64.v src + j * U64.v mword /\
       MH.read_word_in_major major field_addr == Some old /\
       (U64.v (GC.Spec.Object.getTag hdr) >= U64.v GC.Spec.Object.no_scan_tag \/
        ~(is_minor_pointer (to_minor_offset old) /\
          collect.cmc_fwd (to_minor_offset old) <> 0UL)) ==>
       MH.read_word_in_major collect.cmc_major field_addr == Some old) /\
      (forall (src: obj_addr). forall (hdr: U64.t).
       forall (j:nat). forall (field_addr: hp_addr).
       forall (old: U64.t).
       Seq.mem src (MH.major_objects major) /\
       MH.read_word_in_major major (GC.Spec.Heap.hd_address src) == Some hdr /\
       GC.Spec.Object.getColor hdr <> GC.Lib.Header.Blue /\
       U64.v (GC.Spec.Object.getTag hdr) <
         U64.v GC.Spec.Object.no_scan_tag /\
       j < U64.v (GC.Spec.Object.getWosize hdr) /\
       U64.v field_addr == U64.v src + j * U64.v mword /\
       MH.read_word_in_major major field_addr == Some old ==>
       MH.read_word_in_major collect.cmc_major field_addr ==
         Some (ChunkedUpdate.chunked_update_expected_value
           collect.cmc_fwd old)) /\
      (forall (x: U64.t). Seq.mem x (minor_reachable minor roots) ==>
       collect.cmc_fwd x <> 0UL \/ minor_wosize minor x = 0)))

/// Edge-level consequence of the chunked correctness bundle for old scanned
/// major fields.  The theorem is intentionally phrased with an explicit
/// `expected` post-major object: target-membership can come either from an old
/// major target or from a forwarded minor target, while this lemma packages the
/// common field-update/header-framing/graph-introduction reasoning.
val chunked_cheney_gc_correct_after_preflight_old_major_field_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (src expected: obj_addr) (hdr: U64.t) (j: nat)
  (field_addr: hp_addr) (old: U64.t)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
      PromotionDemand.minor_promotion_demand minor + 1 ==>
      MH.chunk_disjoint_from_all fresh major /\
      fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
      U64.v fresh.base >= U64.v zero_addr /\
      SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
      CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0) /\
      (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
      let r =
       SpecMajorAlloc.ensure_major_head_capacity_spec
         major fp alloc_fuel needed fresh in
      let collect =
       ChunkedCheney.chunked_cheney_collect_spec
         minor r.capacity_major_out r.capacity_fp_out roots
         r.capacity_fuel_out in
      Seq.mem src (MH.major_objects major) /\
      MH.read_word_in_major major (GC.Spec.Heap.hd_address src) == Some hdr /\
      GC.Spec.Object.getColor hdr <> GC.Lib.Header.Blue /\
      U64.v (GC.Spec.Object.getTag hdr) <
       U64.v GC.Spec.Object.no_scan_tag /\
      j < U64.v (GC.Spec.Object.getWosize hdr) /\
      U64.v field_addr == U64.v src + j * U64.v mword /\
      CG.chunked_major_field_slot src j == Some field_addr /\
      MH.read_word_in_major major field_addr == Some old /\
      ChunkedUpdate.chunked_update_expected_value collect.cmc_fwd old ==
       expected /\
      Seq.mem expected (MH.major_objects collect.cmc_major)))
    (ensures
      (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
      let r =
       SpecMajorAlloc.ensure_major_head_capacity_spec
         major fp alloc_fuel needed fresh in
      let collect =
       ChunkedCheney.chunked_cheney_collect_spec
         minor r.capacity_major_out r.capacity_fp_out roots
         r.capacity_fuel_out in
      CG.mem_ce (CG.MajorV src, CG.MajorV expected)
       (CG.build_chunked_combined_graph
         collect.cmc_minor collect.cmc_major)))

/// Common old-major edge corollary: if an old scanned major field contained an
/// old active major object and the update guard does not rewrite that raw value,
/// then the same concrete MajorV->MajorV edge is present after the chunked
/// collection.
val chunked_cheney_gc_correct_after_preflight_old_major_nonforwarded_field_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (src dst: obj_addr) (hdr: U64.t) (j: nat)
  (field_addr: hp_addr) (old: U64.t)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
      PromotionDemand.minor_promotion_demand minor + 1 ==>
      MH.chunk_disjoint_from_all fresh major /\
      fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
      U64.v fresh.base >= U64.v zero_addr /\
      SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
      CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0) /\
      (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
      let r =
       SpecMajorAlloc.ensure_major_head_capacity_spec
         major fp alloc_fuel needed fresh in
      let collect =
       ChunkedCheney.chunked_cheney_collect_spec
         minor r.capacity_major_out r.capacity_fp_out roots
         r.capacity_fuel_out in
      Seq.mem src (MH.major_objects major) /\
      Seq.mem dst (MH.major_objects major) /\
      MH.read_word_in_major major (GC.Spec.Heap.hd_address src) == Some hdr /\
      GC.Spec.Object.getColor hdr <> GC.Lib.Header.Blue /\
      U64.v (GC.Spec.Object.getTag hdr) <
       U64.v GC.Spec.Object.no_scan_tag /\
      j < U64.v (GC.Spec.Object.getWosize hdr) /\
      U64.v field_addr == U64.v src + j * U64.v mword /\
      CG.chunked_major_field_slot src j == Some field_addr /\
      MH.read_word_in_major major field_addr == Some old /\
      old == dst /\
      ~(is_minor_pointer (to_minor_offset old) /\
        collect.cmc_fwd (to_minor_offset old) <> 0UL)))
    (ensures
      (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
      let r =
       SpecMajorAlloc.ensure_major_head_capacity_spec
         major fp alloc_fuel needed fresh in
      let collect =
       ChunkedCheney.chunked_cheney_collect_spec
         minor r.capacity_major_out r.capacity_fp_out roots
         r.capacity_fuel_out in
      CG.mem_ce (CG.MajorV src, CG.MajorV dst)
       (CG.build_chunked_combined_graph
         collect.cmc_minor collect.cmc_major)))

/// Forwarded-minor old-major edge corollary: if an old scanned major field
/// contained a minor pointer and chunked collection rewrites that minor pointer
/// to an active post-major object, then the rewritten MajorV->MajorV edge is
/// present in the post chunked combined graph.  The active-target premise is
/// explicit so clients can discharge it with normal-forwarding facts while
/// excluding infix interior forwarding targets.
val chunked_cheney_gc_correct_after_preflight_old_major_forwarded_minor_field_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (src expected: obj_addr) (hdr: U64.t) (j: nat)
  (field_addr: hp_addr) (old: U64.t)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
      PromotionDemand.minor_promotion_demand minor + 1 ==>
      MH.chunk_disjoint_from_all fresh major /\
      fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
      U64.v fresh.base >= U64.v zero_addr /\
      SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
      CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0) /\
      (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
      let r =
       SpecMajorAlloc.ensure_major_head_capacity_spec
         major fp alloc_fuel needed fresh in
      let collect =
       ChunkedCheney.chunked_cheney_collect_spec
         minor r.capacity_major_out r.capacity_fp_out roots
         r.capacity_fuel_out in
      let x = to_minor_offset old in
      Seq.mem src (MH.major_objects major) /\
      MH.read_word_in_major major (GC.Spec.Heap.hd_address src) == Some hdr /\
      GC.Spec.Object.getColor hdr <> GC.Lib.Header.Blue /\
      U64.v (GC.Spec.Object.getTag hdr) <
       U64.v GC.Spec.Object.no_scan_tag /\
      j < U64.v (GC.Spec.Object.getWosize hdr) /\
      U64.v field_addr == U64.v src + j * U64.v mword /\
      CG.chunked_major_field_slot src j == Some field_addr /\
      MH.read_word_in_major major field_addr == Some old /\
      is_minor_pointer x /\
      collect.cmc_fwd x <> 0UL /\
      collect.cmc_fwd x == expected /\
      Seq.mem expected (MH.major_objects collect.cmc_major)))
    (ensures
      (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
      let r =
       SpecMajorAlloc.ensure_major_head_capacity_spec
         major fp alloc_fuel needed fresh in
      let collect =
       ChunkedCheney.chunked_cheney_collect_spec
         minor r.capacity_major_out r.capacity_fp_out roots
         r.capacity_fuel_out in
      let x = to_minor_offset old in
      CG.mem_ce (CG.MajorV src, CG.MajorV expected)
       (CG.build_chunked_combined_graph
         collect.cmc_minor collect.cmc_major)))
