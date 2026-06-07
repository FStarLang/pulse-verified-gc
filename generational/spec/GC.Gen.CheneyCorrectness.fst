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
module ChunkedPromote = GC.Gen.ChunkedPromote
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

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 0"
let chunked_cheney_gc_correct_after_preflight_minor_successor_forwarded
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (src dst: U64.t) (j: nat)
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
      Seq.mem src (minor_reachable minor roots) /\
      j < minor_wosize minor src /\
      to_minor_offset (minor_read_field minor src j) == dst /\
      is_minor_addr dst /\
      Seq.mem dst (minor_objects minor) /\
      minor_wosize minor dst > 0)
    (ensures
      (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
       let r =
         SpecMajorAlloc.ensure_major_head_capacity_spec
           major fp alloc_fuel needed fresh in
       let collect =
         ChunkedCheney.chunked_cheney_collect_spec
           minor r.capacity_major_out r.capacity_fp_out roots
           r.capacity_fuel_out in
       CG.mem_ce (CG.MinorV src, CG.MinorV dst)
         (CG.build_chunked_combined_graph minor major) /\
       collect.cmc_fwd src <> 0UL /\
       collect.cmc_fwd dst <> 0UL))
  =
  minor_reachable_subset minor roots;
  assert (Seq.mem src (minor_objects minor));
  let raw = minor_read_field minor src j in
  CG.chunked_classify_minor_field_minor minor major raw;
  assert (CG.chunked_classify_minor_field minor major raw ==
          Some (CG.MinorV dst));
  CG.chunked_minor_field_edge_intro_full
    minor major src j (CG.MinorV dst);
  FStar.Classical.exists_intro
    (fun (i:nat) ->
      i < minor_wosize minor src /\
      to_minor_offset (minor_read_field minor src i) == dst /\
      is_minor_addr dst /\
      Seq.mem dst (minor_objects minor))
    j;
  minor_successors_char minor src dst;
  assert (Seq.mem dst (minor_successors minor src));
  minor_reachable_closed minor roots src dst;
  assert (Seq.mem dst (minor_reachable minor roots));
  chunked_cheney_collect_after_preflight_forwards_reachable
    minor major fp roots alloc_fuel fresh;
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      major fp alloc_fuel needed fresh in
  let collect =
    ChunkedCheney.chunked_cheney_collect_spec
      minor r.capacity_major_out r.capacity_fp_out roots
      r.capacity_fuel_out in
  assert (minor_wosize minor src > 0);
  assert (collect.cmc_fwd src <> 0UL);
  assert (collect.cmc_fwd dst <> 0UL)
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
       CheneyPres.chunked_fwd_targets_valid_addr collect.cmc_fwd /\
       CheneyPres.chunked_fwd_noninfix_targets_in_major
         minor collect.cmc_fwd collect.cmc_major /\
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
let chunked_cheney_gc_correct_after_preflight_forwarded_minor_object_in_major
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (x: U64.t)
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
      Seq.mem x (minor_objects minor) /\
      (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
       let r =
        SpecMajorAlloc.ensure_major_head_capacity_spec
          major fp alloc_fuel needed fresh in
       let collect =
        ChunkedCheney.chunked_cheney_collect_spec
          minor r.capacity_major_out r.capacity_fp_out roots
          r.capacity_fuel_out in
       collect.cmc_fwd x <> 0UL))
    (ensures
      (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
       let r =
        SpecMajorAlloc.ensure_major_head_capacity_spec
          major fp alloc_fuel needed fresh in
       let collect =
        ChunkedCheney.chunked_cheney_collect_spec
          minor r.capacity_major_out r.capacity_fp_out roots
          r.capacity_fuel_out in
       is_val_addr (collect.cmc_fwd x) /\
       Seq.mem ((collect.cmc_fwd x) <: obj_addr)
        (MH.major_objects collect.cmc_major)))
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
  minor_objects_not_infix minor x;
  assert (~(is_infix_in_minor minor x));
  CheneyPres.chunked_fwd_noninfix_targets_in_major_elim
    minor collect.cmc_fwd collect.cmc_major x
#pop-options

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 0"
let chunked_cheney_gc_correct_after_preflight_reachable_forwarding_target_in_major
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (x: U64.t)
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
      Seq.mem x (minor_reachable minor roots) /\
      minor_wosize minor x > 0)
    (ensures
      (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
       let r =
        SpecMajorAlloc.ensure_major_head_capacity_spec
          major fp alloc_fuel needed fresh in
       let collect =
        ChunkedCheney.chunked_cheney_collect_spec
          minor r.capacity_major_out r.capacity_fp_out roots
          r.capacity_fuel_out in
       is_val_addr (collect.cmc_fwd x) /\
       Seq.mem ((collect.cmc_fwd x) <: obj_addr)
        (MH.major_objects collect.cmc_major)))
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
  minor_reachable_subset minor roots;
  assert (Seq.mem x (minor_objects minor));
  assert (collect.cmc_fwd x <> 0UL);
  chunked_cheney_gc_correct_after_preflight_forwarded_minor_object_in_major
    minor major fp roots alloc_fuel fresh x
#pop-options

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 0"
let chunked_update_forwarded_minor_field_edge
  (minor: minor_state) (mh: MH.major_heap) (fwd: forwarding_map)
  (src expected: obj_addr) (hdr: U64.t) (j: nat)
  (field_addr: hp_addr) (old: U64.t)
  : Lemma
    (requires
      MH.well_formed_major_heap mh /\
      CheneyPres.chunked_fwd_targets_above_minor fwd /\
      Seq.mem src (MH.major_objects mh) /\
      Seq.mem expected (MH.major_objects mh) /\
      MH.read_word_in_major mh (GC.Spec.Heap.hd_address src) == Some hdr /\
      GC.Spec.Object.getColor hdr <> GC.Lib.Header.Blue /\
      U64.v (GC.Spec.Object.getTag hdr) <
        U64.v GC.Spec.Object.no_scan_tag /\
      j < U64.v (GC.Spec.Object.getWosize hdr) /\
      U64.v field_addr == U64.v src + j * U64.v mword /\
      CG.chunked_major_field_slot src j == Some field_addr /\
      MH.read_word_in_major mh field_addr == Some old /\
      (let x = to_minor_offset old in
       is_minor_pointer x /\ fwd x <> 0UL /\ fwd x == expected))
    (ensures
      CG.mem_ce (CG.MajorV src, CG.MajorV expected)
        (CG.build_chunked_combined_graph
          (minor_reset minor)
          (ChunkedUpdate.chunked_update_major_pointers mh fwd)))
  =
  let updated = ChunkedUpdate.chunked_update_major_pointers mh fwd in
  let x = to_minor_offset old in
  ChunkedUpdate.chunked_update_expected_value_effect fwd old;
  assert (ChunkedUpdate.chunked_update_expected_value fwd old == expected);
  CheneyPres.chunked_fwd_targets_above_minor_expected_stable fwd old;
  ChunkedUpdate.chunked_update_major_pointers_field_effect_stable
    mh fwd src hdr j field_addr old;
  assert (MH.read_word_in_major updated field_addr == Some expected);
  ChunkedUpdate.chunked_update_major_pointers_preserves_wf_and_major_objects
    mh fwd;
  assert (MH.major_objects updated == MH.major_objects mh);
  assert (Seq.mem src (MH.major_objects updated));
  assert (Seq.mem expected (MH.major_objects updated));
  ChunkedUpdate.chunked_update_major_pointers_preserves_header
    mh fwd src hdr;
  assert (MH.read_word_in_major updated (GC.Spec.Heap.hd_address src) ==
          Some hdr);
  CG.chunked_wosize_nat_header updated src hdr;
  CG.chunked_is_no_scan_header updated src hdr;
  assert (j < CG.chunked_wosize_nat_of_object updated src);
  assert (CG.chunked_is_no_scan updated src == false);
  assert (CG.chunked_major_field_slot src j == Some field_addr);
  minor_reset_objects_not_mem minor (to_minor_offset expected);
  assert (~(Seq.mem (to_minor_offset expected)
              (minor_objects (minor_reset minor))));
  assert (~(is_minor_pointer (to_minor_offset expected) /\
            Seq.mem (to_minor_offset expected)
              (minor_objects (minor_reset minor))));
  is_val_addr_spec expected;
  assert (is_val_addr expected);
  CG.chunked_classify_major_field_major
    (minor_reset minor) updated expected;
  assert (CG.chunked_classify_major_field
            (minor_reset minor) updated expected ==
          Some (CG.MajorV expected));
  CG.chunked_major_field_edge_intro_full
    (minor_reset minor) updated
    src j field_addr expected (CG.MajorV expected)
#pop-options

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 0"
let chunked_forward_one_normal_updated_field_edge
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat) (j: nat)
  (promoted expected: obj_addr) (hdr: U64.t) (field_addr: hp_addr)
  : Lemma
    (requires
      fuel > 1 /\
      Seq.mem addr (minor_objects minor) /\
      cs.ccs_fwd addr = 0UL /\
      ~(is_infix_in_minor minor addr) /\
      minor_wosize minor addr > 0 /\
      minor_wosize minor addr < pow2 54 /\
      FStar.UInt.size (minor_wosize minor addr) 64 /\
      j < minor_wosize minor addr /\
      promoted == cs.ccs_fp /\
      GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
      cs.ccs_fp <> 0UL /\
      SpecMajorAlloc.major_fl_head_wosize
        cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2 /\
      U64.v field_addr == U64.v promoted + j * U64.v mword /\
      (let cs' = ChunkedCheney.chunked_cheney_forward_one
          minor cs addr fuel in
       let old = minor_read_field minor addr j in
       let x = to_minor_offset old in
       MH.well_formed_major_heap cs'.ccs_major /\
       CheneyPres.chunked_fwd_targets_above_minor cs'.ccs_fwd /\
       Seq.mem promoted (MH.major_objects cs'.ccs_major) /\
       Seq.mem expected (MH.major_objects cs'.ccs_major) /\
       MH.read_word_in_major cs'.ccs_major
        (GC.Spec.Heap.hd_address promoted) == Some hdr /\
       GC.Spec.Object.getColor hdr <> GC.Lib.Header.Blue /\
       U64.v (GC.Spec.Object.getTag hdr) <
        U64.v GC.Spec.Object.no_scan_tag /\
       j < U64.v (GC.Spec.Object.getWosize hdr) /\
       CG.chunked_major_field_slot promoted j == Some field_addr /\
       is_minor_pointer x /\
       cs'.ccs_fwd x <> 0UL /\
       cs'.ccs_fwd x == expected))
    (ensures
      (let cs' = ChunkedCheney.chunked_cheney_forward_one
        minor cs addr fuel in
       CG.mem_ce (CG.MajorV promoted, CG.MajorV expected)
        (CG.build_chunked_combined_graph
          (minor_reset minor)
          (ChunkedUpdate.chunked_update_major_pointers
            cs'.ccs_major cs'.ccs_fwd))))
  =
  let cs' = ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel in
  let old = minor_read_field minor addr j in
  let x = to_minor_offset old in
  assert (U64.v field_addr == U64.v cs.ccs_fp + j * U64.v mword);
  ChunkedCheney.chunked_cheney_forward_one_normal_head_split_field_effect
    minor cs addr fuel j field_addr;
  assert (MH.read_word_in_major cs'.ccs_major field_addr == Some old);
  chunked_update_forwarded_minor_field_edge
    minor cs'.ccs_major cs'.ccs_fwd
    promoted expected hdr j field_addr old
#pop-options

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 0"
let chunked_forward_one_normal_head_split_updated_field_edge
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat) (j: nat)
  (promoted expected: obj_addr) (field_addr: hp_addr)
  : Lemma
    (requires
      fuel > 1 /\
      Seq.mem addr (minor_objects minor) /\
      cs.ccs_fwd addr = 0UL /\
      ~(is_infix_in_minor minor addr) /\
      minor_wosize minor addr > 0 /\
      minor_wosize minor addr < pow2 54 /\
      FStar.UInt.size (minor_wosize minor addr) 64 /\
      minor_tag minor addr < U64.v GC.Spec.Object.no_scan_tag /\
      j < minor_wosize minor addr /\
      promoted == cs.ccs_fp /\
      GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
      cs.ccs_fp <> 0UL /\
      SpecMajorAlloc.major_fl_head_wosize
        cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2 /\
      U64.v field_addr == U64.v promoted + j * U64.v mword /\
      CG.chunked_major_field_slot promoted j == Some field_addr /\
      (let cs' = ChunkedCheney.chunked_cheney_forward_one
          minor cs addr fuel in
       let old = minor_read_field minor addr j in
       let x = to_minor_offset old in
       CheneyPres.chunked_fwd_targets_above_minor cs'.ccs_fwd /\
       Seq.mem expected (MH.major_objects cs'.ccs_major) /\
       is_minor_pointer x /\
       cs'.ccs_fwd x <> 0UL /\
       cs'.ccs_fwd x == expected))
    (ensures
      (let cs' = ChunkedCheney.chunked_cheney_forward_one
        minor cs addr fuel in
       CG.mem_ce (CG.MajorV promoted, CG.MajorV expected)
        (CG.build_chunked_combined_graph
          (minor_reset minor)
          (ChunkedUpdate.chunked_update_major_pointers
            cs'.ccs_major cs'.ccs_fwd))))
  =
  let cs' = ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel in
  let old = minor_read_field minor addr j in
  let x = to_minor_offset old in
  assert (U64.v cs.ccs_fp == U64.v promoted);
  assert (U64.v cs.ccs_fp >= U64.v mword);
  let promoted_fp : obj_addr = cs.ccs_fp in
  assert (promoted_fp == promoted);
  assert (U64.v field_addr == U64.v cs.ccs_fp + j * U64.v mword);
  ChunkedCheney.chunked_cheney_forward_one_normal_head_split_field_effect
    minor cs addr fuel j field_addr;
  assert (MH.read_word_in_major cs'.ccs_major field_addr == Some old);
  ChunkedCheney.chunked_cheney_forward_one_normal_head_split_header_effect
    minor cs addr fuel;
  assert (MH.well_formed_major_heap cs'.ccs_major);
  assert (Seq.mem promoted (MH.major_objects cs'.ccs_major));
  match MH.read_word_in_major
          cs'.ccs_major (GC.Spec.Heap.hd_address promoted) with
  | None -> assert False
  | Some hdr ->
    assert (GC.Spec.Object.getColor hdr == GC.Lib.Header.White);
    assert (GC.Spec.Object.getColor hdr <> GC.Lib.Header.Blue);
    assert (U64.v (GC.Spec.Object.getTag hdr) == minor_tag minor addr);
    assert (U64.v (GC.Spec.Object.getTag hdr) <
            U64.v GC.Spec.Object.no_scan_tag);
    assert (U64.v (GC.Spec.Object.getWosize hdr) ==
            minor_wosize minor addr);
    assert (j < U64.v (GC.Spec.Object.getWosize hdr));
    chunked_update_forwarded_minor_field_edge
      minor cs'.ccs_major cs'.ccs_fwd
      promoted expected hdr j field_addr old
#pop-options

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 0"
let chunked_forward_one_normal_existing_forwarded_updated_field_edge
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat) (j: nat)
  (promoted expected: obj_addr) (field_addr: hp_addr)
  : Lemma
    (requires
      fuel > 1 /\
      Seq.mem addr (minor_objects minor) /\
      cs.ccs_fwd addr = 0UL /\
      ~(is_infix_in_minor minor addr) /\
      minor_wosize minor addr > 0 /\
      minor_wosize minor addr < pow2 54 /\
      FStar.UInt.size (minor_wosize minor addr) 64 /\
      minor_tag minor addr < U64.v GC.Spec.Object.no_scan_tag /\
      j < minor_wosize minor addr /\
      promoted == cs.ccs_fp /\
      GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
      SpecMajorAlloc.major_fl_chain_terminates
        cs.ccs_major cs.ccs_fp fuel = true /\
      CheneyPres.chunked_fwd_targets_above_minor cs.ccs_fwd /\
      CheneyPres.chunked_cheney_forward_one_budget_ready minor cs addr 1 /\
      cs.ccs_fp <> 0UL /\
      SpecMajorAlloc.major_fl_head_wosize
        cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2 /\
      U64.v field_addr == U64.v promoted + j * U64.v mword /\
      CG.chunked_major_field_slot promoted j == Some field_addr /\
      (let old = minor_read_field minor addr j in
       let x = to_minor_offset old in
       is_minor_pointer x /\
       cs.ccs_fwd x <> 0UL /\
       cs.ccs_fwd x == expected /\
       Seq.mem expected (MH.major_objects cs.ccs_major)))
    (ensures
      (let cs' = ChunkedCheney.chunked_cheney_forward_one
        minor cs addr fuel in
       CG.mem_ce (CG.MajorV promoted, CG.MajorV expected)
        (CG.build_chunked_combined_graph
          (minor_reset minor)
          (ChunkedUpdate.chunked_update_major_pointers
            cs'.ccs_major cs'.ccs_fwd))))
  =
  let wz = minor_wosize minor addr in
  let old = minor_read_field minor addr j in
  let x = to_minor_offset old in
  let cs' = ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel in
  assert (wz > 0);
  assert (SpecMajorAlloc.major_fl_head_wosize
            cs.ccs_major cs.ccs_fp >= wz + 1 + 1);
  CheneyPres.chunked_cheney_forward_one_preserves_fwd_targets_above_minor
    minor cs addr fuel 1;
  assert (CheneyPres.chunked_fwd_targets_above_minor cs'.ccs_fwd);
  assert (x <> addr);
  ChunkedCheney.chunked_cheney_forward_one_normal minor cs addr fuel;
  ChunkedCheney.chunked_cheney_forward_normal_other_fwd
    minor cs addr x fuel;
  assert (cs'.ccs_fwd x == expected);
  CheneyPres.chunked_promote_object_head_split_preserves_chunked_alloc_shape
    minor cs.ccs_major addr cs.ccs_fp wz fuel;
  let res =
    ChunkedPromote.chunked_promote_object_with_fuel
      minor cs.ccs_major addr cs.ccs_fp wz fuel in
  assert (res.new_addr == cs.ccs_fp);
  assert (res.new_addr <> 0UL);
  ChunkedCheney.chunked_cheney_forward_normal_success minor cs addr fuel;
  assert (cs'.ccs_major == res.major_out);
  assert (Seq.mem expected (MH.major_objects res.major_out));
  assert (Seq.mem expected (MH.major_objects cs'.ccs_major));
  chunked_forward_one_normal_head_split_updated_field_edge
    minor cs addr fuel j promoted expected field_addr
#pop-options

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 0"
let chunked_forward_fields_preserved_forwarded_minor_field_edge
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (idx wosize alloc_fuel: nat)
  (src expected: obj_addr) (hdr: U64.t) (j: nat)
  (field_addr: hp_addr) (old: U64.t)
  : Lemma
    (requires
      alloc_fuel > 1 /\
      GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates
        cs.ccs_major cs.ccs_fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue cs.ccs_major cs.ccs_fp alloc_fuel /\
      CheneyPres.chunked_cheney_forward_fields_split_ready
        minor cs parent idx wosize alloc_fuel /\
      Seq.mem src (MH.major_objects cs.ccs_major) /\
      MH.read_word_in_major cs.ccs_major
        (GC.Spec.Heap.hd_address src) == Some hdr /\
      GC.Spec.Object.getColor hdr <> GC.Lib.Header.Blue /\
      U64.v (GC.Spec.Object.getTag hdr) <
        U64.v GC.Spec.Object.no_scan_tag /\
      j < U64.v (GC.Spec.Object.getWosize hdr) /\
      U64.v field_addr == U64.v src + j * U64.v mword /\
      CG.chunked_major_field_slot src j == Some field_addr /\
      MH.read_word_in_major cs.ccs_major field_addr == Some old /\
      (let cs' =
        ChunkedCheney.chunked_cheney_forward_fields
          minor cs parent idx wosize alloc_fuel in
       let x = to_minor_offset old in
       CheneyPres.chunked_fwd_targets_above_minor cs'.ccs_fwd /\
       Seq.mem expected (MH.major_objects cs'.ccs_major) /\
       is_minor_pointer x /\
       cs'.ccs_fwd x <> 0UL /\
       cs'.ccs_fwd x == expected))
    (ensures
      (let cs' =
        ChunkedCheney.chunked_cheney_forward_fields
          minor cs parent idx wosize alloc_fuel in
       CG.mem_ce (CG.MajorV src, CG.MajorV expected)
        (CG.build_chunked_combined_graph
          (minor_reset minor)
          (ChunkedUpdate.chunked_update_major_pointers
            cs'.ccs_major cs'.ccs_fwd))))
  =
  let cs' =
    ChunkedCheney.chunked_cheney_forward_fields
      minor cs parent idx wosize alloc_fuel in
  CheneyPres.chunked_cheney_forward_fields_head_split_preserves_old_non_blue_object_field
    minor cs parent idx wosize alloc_fuel src hdr j field_addr old;
  GenInv.chunked_major_alloc_shape_elim
    cs'.ccs_major cs'.ccs_fp alloc_fuel;
  assert (MH.well_formed_major_heap cs'.ccs_major);
  assert (Seq.mem src (MH.major_objects cs'.ccs_major));
  assert (MH.read_word_in_major cs'.ccs_major
            (GC.Spec.Heap.hd_address src) == Some hdr);
  assert (MH.read_word_in_major cs'.ccs_major field_addr == Some old);
  let x = to_minor_offset old in
  chunked_update_forwarded_minor_field_edge
    minor cs'.ccs_major cs'.ccs_fwd
    src expected hdr j field_addr old
#pop-options

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 0"
let chunked_forward_fields_preserved_minor_object_field_edge
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (idx wosize alloc_fuel: nat)
  (src: obj_addr) (hdr: U64.t) (j: nat)
  (field_addr: hp_addr) (old: U64.t)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates
        cs.ccs_major cs.ccs_fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue cs.ccs_major cs.ccs_fp alloc_fuel /\
      CheneyPres.chunked_cheney_forward_fields_split_ready
        minor cs parent idx wosize alloc_fuel /\
      Seq.mem src (MH.major_objects cs.ccs_major) /\
      MH.read_word_in_major cs.ccs_major
        (GC.Spec.Heap.hd_address src) == Some hdr /\
      GC.Spec.Object.getColor hdr <> GC.Lib.Header.Blue /\
      U64.v (GC.Spec.Object.getTag hdr) <
        U64.v GC.Spec.Object.no_scan_tag /\
      j < U64.v (GC.Spec.Object.getWosize hdr) /\
      U64.v field_addr == U64.v src + j * U64.v mword /\
      CG.chunked_major_field_slot src j == Some field_addr /\
      MH.read_word_in_major cs.ccs_major field_addr == Some old /\
      (let cs' =
        ChunkedCheney.chunked_cheney_forward_fields
          minor cs parent idx wosize alloc_fuel in
       let x = to_minor_offset old in
       CheneyPres.chunked_fwd_targets_above_minor cs'.ccs_fwd /\
       CheneyPres.chunked_fwd_noninfix_targets_in_major
        minor cs'.ccs_fwd cs'.ccs_major /\
       is_minor_pointer x /\
       Seq.mem x (minor_objects minor) /\
       cs'.ccs_fwd x <> 0UL))
    (ensures
      (let cs' =
        ChunkedCheney.chunked_cheney_forward_fields
          minor cs parent idx wosize alloc_fuel in
       let x = to_minor_offset old in
       CG.mem_ce (CG.MajorV src, CG.MajorV (cs'.ccs_fwd x))
        (CG.build_chunked_combined_graph
          (minor_reset minor)
          (ChunkedUpdate.chunked_update_major_pointers
            cs'.ccs_major cs'.ccs_fwd))))
  =
  let cs' =
    ChunkedCheney.chunked_cheney_forward_fields
      minor cs parent idx wosize alloc_fuel in
  let x = to_minor_offset old in
  minor_objects_not_infix minor x;
  assert (~(is_infix_in_minor minor x));
  CheneyPres.chunked_fwd_noninfix_targets_in_major_elim
    minor cs'.ccs_fwd cs'.ccs_major x;
  let expected = (cs'.ccs_fwd x <: obj_addr) in
  assert (cs'.ccs_fwd x == expected);
  chunked_forward_fields_preserved_forwarded_minor_field_edge
    minor cs parent idx wosize alloc_fuel
    src expected hdr j field_addr old
#pop-options

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 0"
let chunked_forward_one_normal_then_fields_minor_successor_edge
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat) (j: nat)
  (promoted: obj_addr) (field_addr: hp_addr)
  : Lemma
    (requires
      minor_wf minor /\
      fuel > 1 /\
      Seq.mem addr (minor_objects minor) /\
      cs.ccs_fwd addr = 0UL /\
      ~(is_infix_in_minor minor addr) /\
      minor_wosize minor addr > 0 /\
      minor_wosize minor addr < pow2 54 /\
      FStar.UInt.size (minor_wosize minor addr) 64 /\
      minor_tag minor addr < U64.v GC.Spec.Object.no_scan_tag /\
      j < minor_wosize minor addr /\
      promoted == cs.ccs_fp /\
      GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
      SpecMajorAlloc.major_fl_chain_terminates
        cs.ccs_major cs.ccs_fp fuel = true /\
      GenInv.chunked_chain_objects_blue cs.ccs_major cs.ccs_fp fuel /\
      cs.ccs_fp <> 0UL /\
      SpecMajorAlloc.major_fl_head_wosize
        cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2 /\
      U64.v field_addr == U64.v promoted + j * U64.v mword /\
      CG.chunked_major_field_slot promoted j == Some field_addr /\
      (let cs1 =
        ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel in
       let cs2 =
        ChunkedCheney.chunked_cheney_forward_fields
          minor cs1 addr 0 (minor_wosize minor addr) fuel in
       let old = minor_read_field minor addr j in
       let x = to_minor_offset old in
       CheneyPres.chunked_cheney_forward_fields_split_ready
        minor cs1 addr 0 (minor_wosize minor addr) fuel /\
       CheneyPres.chunked_cheney_forward_fields_budget_ready
        minor cs1 addr 0 (minor_wosize minor addr) fuel 1 /\
       CheneyPres.chunked_fwd_targets_above_minor cs2.ccs_fwd /\
       CheneyPres.chunked_fwd_noninfix_targets_in_major
        minor cs2.ccs_fwd cs2.ccs_major /\
       is_minor_pointer x /\
       Seq.mem x (minor_objects minor) /\
       minor_wosize minor x > 0))
    (ensures
      (let cs1 =
        ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel in
       let cs2 =
        ChunkedCheney.chunked_cheney_forward_fields
          minor cs1 addr 0 (minor_wosize minor addr) fuel in
       let x = to_minor_offset (minor_read_field minor addr j) in
       CG.mem_ce (CG.MajorV promoted, CG.MajorV (cs2.ccs_fwd x))
        (CG.build_chunked_combined_graph
          (minor_reset minor)
          (ChunkedUpdate.chunked_update_major_pointers
            cs2.ccs_major cs2.ccs_fwd))))
  =
  let wz = minor_wosize minor addr in
  let old = minor_read_field minor addr j in
  let x = to_minor_offset old in
  let cs1 = ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel in
  let cs2 =
    ChunkedCheney.chunked_cheney_forward_fields minor cs1 addr 0 wz fuel in
  ChunkedCheney.chunked_cheney_forward_one_normal_head_split_field_effect
    minor cs addr fuel j field_addr;
  ChunkedCheney.chunked_cheney_forward_one_normal_head_split_header_effect
    minor cs addr fuel;
  CheneyPres.chunked_cheney_forward_one_head_split_preserves_chain_objects_blue
    minor cs addr fuel;
  assert (GenInv.chunked_major_alloc_shape cs1.ccs_major cs1.ccs_fp fuel);
  assert (SpecMajorAlloc.major_fl_chain_terminates
            cs1.ccs_major cs1.ccs_fp fuel = true);
  assert (GenInv.chunked_chain_objects_blue cs1.ccs_major cs1.ccs_fp fuel);
  is_minor_addr_from_bounds x;
  FStar.Classical.exists_intro
    (fun (i:nat) ->
      i < minor_wosize minor addr /\
      to_minor_offset (minor_read_field minor addr i) == x /\
      is_minor_addr x /\
      Seq.mem x (minor_objects minor))
    j;
  minor_successors_char minor addr x;
  assert (Seq.mem x (minor_successors minor addr));
  CheneyPres.chunked_cheney_forward_fields_covers_successors_from_budget
    minor cs1 addr fuel 1;
  assert (cs2.ccs_fwd x <> 0UL);
  assert (MH.read_word_in_major cs1.ccs_major field_addr == Some old);
  match MH.read_word_in_major cs1.ccs_major (GC.Spec.Heap.hd_address promoted) with
  | Some hdr ->
    assert (Seq.mem promoted (MH.major_objects cs1.ccs_major));
    assert (GC.Spec.Object.getColor hdr == GC.Lib.Header.White);
    assert (GC.Spec.Object.getColor hdr <> GC.Lib.Header.Blue);
    assert (U64.v (GC.Spec.Object.getTag hdr) == minor_tag minor addr);
    assert (U64.v (GC.Spec.Object.getTag hdr) <
            U64.v GC.Spec.Object.no_scan_tag);
    assert (U64.v (GC.Spec.Object.getWosize hdr) == wz);
    chunked_forward_fields_preserved_minor_object_field_edge
      minor cs1 addr 0 wz fuel promoted hdr j field_addr old
  | None ->
    assert False
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

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 0"
let chunked_cheney_gc_correct_after_preflight_old_major_nonforwarded_field_edge
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
  assert (Seq.mem dst (MH.major_objects collect.cmc_major));
  ChunkedUpdate.chunked_update_expected_value_effect collect.cmc_fwd old;
  assert (ChunkedUpdate.chunked_update_expected_value collect.cmc_fwd old ==
          old);
  assert (ChunkedUpdate.chunked_update_expected_value collect.cmc_fwd old ==
          dst);
  chunked_cheney_gc_correct_after_preflight_old_major_field_edge
    minor major fp roots alloc_fuel fresh src dst hdr j field_addr old
#pop-options

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 0"
let chunked_cheney_gc_correct_after_preflight_old_major_forwarded_minor_field_edge
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
  let x = to_minor_offset old in
  ChunkedUpdate.chunked_update_expected_value_effect collect.cmc_fwd old;
  assert (ChunkedUpdate.chunked_update_expected_value collect.cmc_fwd old ==
          collect.cmc_fwd x);
  assert (ChunkedUpdate.chunked_update_expected_value collect.cmc_fwd old ==
          expected);
  chunked_cheney_gc_correct_after_preflight_old_major_field_edge
    minor major fp roots alloc_fuel fresh src expected hdr j field_addr old
#pop-options
