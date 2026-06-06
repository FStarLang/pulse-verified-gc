/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyCorrectness — Proofs of Cheney collector correctness
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyCorrectness

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.PromoteUpdate
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
/// Property 1: Object survival
/// ---------------------------------------------------------------------------

let cheney_collect_preserves_objects
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = cheney_collect_spec minor major fp roots in
                    forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                      Seq.mem x (objects zero_addr res.mc_major)))
  =
  cheney_promote_preserves_objects minor major fp roots;
  let prom = cheney_promote minor major fp roots in
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  update_major_pointers_preserves_objects prom.major_final prom.fwd_map

/// ---------------------------------------------------------------------------
/// Property 2: well_formed_heap_part1
/// ---------------------------------------------------------------------------

let cheney_collect_preserves_wfh_part1
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures well_formed_heap_part1 (cheney_collect_spec minor major fp roots).mc_major)
  =
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  let prom = cheney_promote minor major fp roots in
  update_major_pointers_preserves_wfh_part1 prom.major_final prom.fwd_map

/// ---------------------------------------------------------------------------
/// Property 3: Minor reset
/// ---------------------------------------------------------------------------

let cheney_collect_resets_minor
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (ensures (let res = cheney_collect_spec minor major fp roots in
                    minor_wf res.mc_minor /\
                    U64.v res.mc_minor.bump == 0))
  = ()

/// ---------------------------------------------------------------------------
/// Property 4: Root rewriting
/// ---------------------------------------------------------------------------

let cheney_collect_rewrites_roots
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (ensures (let res = cheney_collect_spec minor major fp roots in
                    let prom = cheney_promote minor major fp roots in
                    res.mc_roots == rewrite_roots roots prom.fwd_map))
  = ()

/// ---------------------------------------------------------------------------
/// Main theorem (properties 1-4, unconditional)
/// ---------------------------------------------------------------------------

let cheney_gc_correct
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp)
          (ensures (let res = cheney_collect_spec minor major fp roots in
                    let prom = cheney_promote minor major fp roots in
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                      Seq.mem x (objects zero_addr res.mc_major)) /\
                    well_formed_heap_part1 res.mc_major /\
                    AllocLemmas.fl_valid res.mc_major res.mc_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates res.mc_major res.mc_fp (heap_size / U64.v mword) /\
                    minor_wf res.mc_minor /\
                    U64.v res.mc_minor.bump == 0 /\
                    res.mc_roots == rewrite_roots roots prom.fwd_map))
  =
  cheney_collect_preserves_objects minor major fp roots;
  cheney_collect_preserves_wfh_part1 minor major fp roots;
  cheney_collect_resets_minor minor major fp roots;
  cheney_collect_rewrites_roots minor major fp roots;
  cheney_collect_preserves_fl_valid minor major fp roots

/// ---------------------------------------------------------------------------
/// Property 6: BFS completeness (conditional)
/// ---------------------------------------------------------------------------

open GC.Gen.Reachability
module BFS = GC.Gen.CheneyBFS

/// BFS completeness: delegates to CheneyBFS.cheney_promotes_all_reachable
/// which uses the reachability induction principle.
let cheney_promotes_all_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires BFS.cheney_no_oom minor major fp roots)
          (ensures (let prom = cheney_promote minor major fp roots in
                    forall (x: U64.t). Seq.mem x (minor_reachable minor roots) ==>
                      prom.fwd_map x <> 0UL \/ minor_wosize minor x = 0))
  =
  BFS.cheney_promotes_all_reachable minor major fp roots;
  // BFS ensures: reachable /\ wosize > 0 ==> fwd <> 0
  // Goal: reachable ==> fwd <> 0 \/ wosize = 0
  // These are equivalent: (wosize > 0 ==> fwd <> 0) ↔ (fwd <> 0 \/ wosize = 0)
  // when wosize is nat (>= 0)
  let prom = cheney_promote minor major fp roots in
  let aux (x: U64.t)
    : Lemma (requires Seq.mem x (minor_reachable minor roots))
            (ensures prom.fwd_map x <> 0UL \/ minor_wosize minor x = 0)
    = ()
  in
  Classical.forall_intro (Classical.move_requires aux)

#push-options "--split_queries always"
let chunked_cheney_collect_after_preflight_forwards_reachable
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
  =
  CheneyPres.chunked_cheney_collect_after_minor_promotion_head_preflight
    minor major fp roots alloc_fuel fresh;
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      major fp alloc_fuel needed fresh in
  let collect =
    ChunkedCheney.chunked_cheney_collect_spec
      minor r.capacity_major_out r.capacity_fp_out roots
      r.capacity_fuel_out in
  let aux (x: U64.t)
    : Lemma
        (requires Seq.mem x (minor_reachable minor roots))
        (ensures collect.cmc_fwd x <> 0UL \/ minor_wosize minor x = 0)
    =
    if minor_wosize minor x > 0 then
      assert (collect.cmc_fwd x <> 0UL)
    else
      assert (minor_wosize minor x = 0)
  in
  Classical.forall_intro (Classical.move_requires aux)
#pop-options

#push-options "--split_queries always"
let chunked_cheney_gc_correct_after_preflight
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
  =
  CheneyPres.chunked_cheney_collect_after_minor_promotion_head_preflight
    minor major fp roots alloc_fuel fresh;
  chunked_cheney_collect_after_preflight_forwards_reachable
    minor major fp roots alloc_fuel fresh
#pop-options

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 0"
let chunked_cheney_gc_correct_after_preflight_old_major_field_edge
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
  =
  chunked_cheney_gc_correct_after_preflight
    minor major fp roots alloc_fuel fresh;
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      major fp alloc_fuel needed fresh in
  let collect =
    ChunkedCheney.chunked_cheney_collect_spec
      minor r.capacity_major_out r.capacity_fp_out roots
      r.capacity_fuel_out in
  assert (collect.cmc_minor == minor_reset minor);
  assert (Seq.mem src (MH.major_objects collect.cmc_major));
  assert (MH.read_word_in_major collect.cmc_major
            (GC.Spec.Heap.hd_address src) == Some hdr);
  assert (MH.read_word_in_major collect.cmc_major field_addr ==
          Some expected);
  CG.chunked_wosize_nat_header collect.cmc_major src hdr;
  CG.chunked_is_no_scan_header collect.cmc_major src hdr;
  assert (j < CG.chunked_wosize_nat_of_object collect.cmc_major src);
  assert (CG.chunked_is_no_scan collect.cmc_major src == false);
  assert (CG.chunked_major_field_slot src j == Some field_addr);
  minor_reset_objects_not_mem minor (to_minor_offset expected);
  assert (~(Seq.mem (to_minor_offset expected)
              (minor_objects collect.cmc_minor)));
  assert (~(is_minor_pointer (to_minor_offset expected) /\
            Seq.mem (to_minor_offset expected)
              (minor_objects collect.cmc_minor)));
  CG.chunked_classify_major_field_major
    collect.cmc_minor collect.cmc_major expected;
  assert (CG.chunked_classify_major_field
            collect.cmc_minor collect.cmc_major expected ==
          Some (CG.MajorV expected));
  assert (Seq.mem src (MH.major_objects collect.cmc_major));
  assert (CG.chunked_is_no_scan collect.cmc_major src == false);
  assert (j < CG.chunked_wosize_nat_of_object collect.cmc_major src);
  assert (CG.chunked_major_field_slot src j == Some field_addr);
  assert (MH.read_word_in_major collect.cmc_major field_addr == Some expected);
  CG.chunked_major_field_edge_intro_full
    collect.cmc_minor collect.cmc_major
    src j field_addr expected (CG.MajorV expected)
#pop-options
