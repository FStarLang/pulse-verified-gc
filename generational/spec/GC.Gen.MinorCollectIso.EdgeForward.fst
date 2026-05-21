/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectIso.EdgeForward — Implementation
/// ---------------------------------------------------------------------------

module GC.Gen.MinorCollectIso.EdgeForward

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
open GC.Gen.Remembered
open GC.Gen.CombinedGraph
open GC.Gen.Cheney
open GC.Gen.Correctness
open GC.Gen.MinorCollectIso

module Iso = GC.Gen.CombinedGraph.Isomorphism
module CheneyCorr = GC.Gen.CheneyCorrectness
module CheneyDisch = GC.Gen.CheneyDischarge
module CheneyDisj = GC.Gen.CheneyDisjoint
module Reach = GC.Gen.Reachability
module RBridge = GC.Gen.ReachabilityBridge
module HeaderPres = GC.Gen.MinorCollectIso.HeaderPres
module HeapGraph = GC.Spec.HeapGraph
module EdgeBridge = GC.Gen.CombinedGraph.EdgeBridge
module EdgePres = GC.Gen.CombinedGraph.EdgePreservation
module MajorBridge = GC.Gen.CombinedGraph.MajorBridge
module Helpers = GC.Gen.MinorCollectIso.Helpers

/// ---------------------------------------------------------------------------
/// Edge forward: Major→Major case
/// ---------------------------------------------------------------------------

private
#push-options "--z3rlimit 50 --fuel 0 --ifuel 1 --split_queries always"
let prove_edge_forward_major_major
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src dst: obj_addr)
  : Lemma
    (requires
      minor_collect_iso_preconditions minor major fp roots /\
      (let cg = build_combined_graph minor major in
       let combined_roots = pre_gc_roots roots in
       combined_reachable cg combined_roots (MajorV src) /\
       combined_reachable cg combined_roots (MajorV dst) /\
       mem_ce (MajorV src, MajorV dst) cg))
    (ensures (
      let res = cheney_collect_spec minor major fp roots in
      let g_mc = create_graph res.mc_major in
      Seq.mem ((src <: hp_addr), (dst <: hp_addr)) g_mc.edges))
  = RBridge.reachable_major_valid_nonblue minor major roots;
    major_edge_elim minor major src (MajorV dst);
    let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun i -> i < U64.v (wosize_of_object src major) /\
                ~(is_no_scan src major) /\
                U64.v src + i * 8 + 8 <= heap_size /\
                (U64.v src + i * 8) % 8 == 0 /\
                classify_major_field minor major (read_word major (U64.uint_to_t (U64.v src + i * 8))) == Some (MajorV dst)) in
    classify_major_field_inv_major minor major (read_word major (U64.uint_to_t (U64.v src + i * 8))) dst;
    let field_addr = U64.uint_to_t (U64.v src + i * 8) in
    MajorBridge.major_object_not_minor_pointer major dst;
    Helpers.derive_mc_major_field_value minor major fp roots src i;
    let res = cheney_collect_spec minor major fp roots in
    CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
    HeaderPres.minor_collect_preserves_wosize minor major fp roots src;
    HeaderPres.minor_collect_preserves_is_no_scan minor major fp roots src;
    wf_object_bound res.mc_major src;
    HeapGraph.object_fits_from_bound src res.mc_major;
    let j = U64.uint_to_t (i + 1) in
    wosize_of_object_bound src res.mc_major;
    EdgeBridge.field_index_bridge res.mc_major src i;
    EdgePres.major_object_is_pointer_field major dst;
    objects_is_vertex_set res.mc_major;
    HeapGraph.pointer_field_is_graph_edge res.mc_major (objects zero_addr res.mc_major) src j
#pop-options

/// ---------------------------------------------------------------------------
/// Edge forward: Major→Minor case
/// ---------------------------------------------------------------------------

private
#push-options "--z3rlimit 50 --fuel 0 --ifuel 1 --split_queries always"
let prove_edge_forward_major_minor
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: obj_addr) (dst: U64.t)
  : Lemma
    (requires
      minor_collect_iso_preconditions minor major fp roots /\
      (let cg = build_combined_graph minor major in
       let combined_roots = pre_gc_roots roots in
       combined_reachable cg combined_roots (MajorV src) /\
       combined_reachable cg combined_roots (MinorV dst) /\
       mem_ce (MajorV src, MinorV dst) cg))
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let fwd = prom.fwd_map in
      let res = cheney_collect_spec minor major fp roots in
      let g_mc = create_graph res.mc_major in
      let fwd_dst = fwd dst in
      U64.v fwd_dst >= 0 /\ U64.v fwd_dst < heap_size /\ U64.v fwd_dst % U64.v mword == 0 /\
      Seq.mem ((src <: hp_addr), (fwd_dst <: hp_addr)) g_mc.edges))
  = RBridge.reachable_major_valid_nonblue minor major roots;
    major_edge_elim minor major src (MinorV dst);
    let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun i -> i < U64.v (wosize_of_object src major) /\
                ~(is_no_scan src major) /\
                U64.v src + i * 8 + 8 <= heap_size /\
                (U64.v src + i * 8) % 8 == 0 /\
                classify_major_field minor major (read_word major (U64.uint_to_t (U64.v src + i * 8))) == Some (MinorV dst)) in
    classify_major_field_inv_minor minor major (read_word major (U64.uint_to_t (U64.v src + i * 8))) dst;
    let field_addr = U64.uint_to_t (U64.v src + i * 8) in
    RBridge.reachability_bridge minor major roots;
    let remembered = minor_roots_from_major major in
    FStar.Seq.Properties.lemma_mem_append roots remembered;
    let aux_mono (v: U64.t) : Lemma
      (requires Seq.mem v (live_set_of minor major roots))
      (ensures Seq.mem v (Reach.minor_reachable minor roots))
    = Reach.minor_reachable_mono minor (Seq.append roots remembered) roots v
    in
    Classical.forall_intro (Classical.move_requires aux_mono);
    CheneyCorr.cheney_promotes_all_reachable minor major fp roots;
    let prom = cheney_promote minor major fp roots in
    Helpers.derive_mc_major_field_value minor major fp roots src i;
    let res = cheney_collect_spec minor major fp roots in
    let fwd_dst : U64.t = prom.fwd_map dst in
    CheneyDisch.cheney_fwd_targets_in_mc_major minor major fp roots;
    CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
    HeaderPres.minor_collect_preserves_wosize minor major fp roots src;
    HeaderPres.minor_collect_preserves_is_no_scan minor major fp roots src;
    wf_object_bound res.mc_major src;
    HeapGraph.object_fits_from_bound src res.mc_major;
    let j = U64.uint_to_t (i + 1) in
    wosize_of_object_bound src res.mc_major;
    EdgeBridge.field_index_bridge res.mc_major src i;
    EdgePres.major_object_is_pointer_field res.mc_major (fwd_dst <: obj_addr);
    objects_is_vertex_set res.mc_major;
    HeapGraph.pointer_field_is_graph_edge res.mc_major (objects zero_addr res.mc_major) src j
#pop-options

/// ---------------------------------------------------------------------------
/// Edge forward: Minor→* helper lemmas
/// ---------------------------------------------------------------------------

private
#push-options "--z3rlimit 50 --fuel 0 --ifuel 1"
let minor_edge_src_scannable
  (minor: minor_state) (major: heap) (src: U64.t) (dst: combined_vertex)
  (i: nat)
  : Lemma
    (requires
      minor_no_scan_no_classify minor major /\
      Seq.mem src (minor_objects minor) /\
      i < minor_wosize minor src /\
      classify_minor_field minor major (minor_read_field minor src i) == Some dst)
    (ensures minor_tag minor src < 251)
  = ()
#pop-options

private
#push-options "--z3rlimit 50 --fuel 0 --ifuel 1 --split_queries always"
let prove_minor_to_graph_edge
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: U64.t) (dst: combined_vertex)
  (i: nat) (fwd_dst: U64.t) (fwd_src: obj_addr) (fwd: forwarding_map)
  (res: minor_collect_result)
  : Lemma
    (requires
      well_formed_heap res.mc_major /\
      res == cheney_collect_spec minor major fp roots /\
      Seq.mem fwd_src (objects zero_addr res.mc_major) /\
      is_no_scan fwd_src res.mc_major = false /\
      U64.v (wosize_of_object fwd_src res.mc_major) >= minor_wosize minor src /\
      U64.v fwd_dst >= U64.v mword /\ U64.v fwd_dst < heap_size /\ U64.v fwd_dst % U64.v mword == 0 /\
      Seq.mem (fwd_dst <: obj_addr) (objects zero_addr res.mc_major) /\
      i < minor_wosize minor src /\
      (let field_addr_v = U64.v fwd_src + i * 8 in
       field_addr_v + 8 <= heap_size /\
       field_addr_v % 8 == 0 /\
       read_word res.mc_major (U64.uint_to_t field_addr_v) == fwd_dst))
    (ensures
      U64.v fwd_src >= 0 /\ U64.v fwd_src < heap_size /\ U64.v fwd_src % U64.v mword == 0 /\
      U64.v fwd_dst >= 0 /\ U64.v fwd_dst < heap_size /\ U64.v fwd_dst % U64.v mword == 0 /\
      Seq.mem ((fwd_src <: hp_addr), (fwd_dst <: hp_addr)) (create_graph res.mc_major).edges)
  = wf_object_bound res.mc_major fwd_src;
    HeapGraph.object_fits_from_bound fwd_src res.mc_major;
    GC.Spec.Object.wosize_of_object_bound fwd_src res.mc_major;
    assert (i < U64.v (wosize_of_object fwd_src res.mc_major));
    assert (HeapGraph.object_fits_in_heap fwd_src res.mc_major);
    assert (i + 1 < pow2 54);
    let j = U64.uint_to_t (i + 1) in
    EdgeBridge.field_index_bridge res.mc_major fwd_src i;
    EdgePres.major_object_is_pointer_field res.mc_major (fwd_dst <: obj_addr);
    objects_is_vertex_set res.mc_major;
    HeapGraph.pointer_field_is_graph_edge res.mc_major (objects zero_addr res.mc_major) fwd_src j
#pop-options

private
#push-options "--z3rlimit 50 --fuel 0 --ifuel 1 --split_queries always"
let prove_edge_forward_minor_case
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: U64.t) (dst: combined_vertex)
  (i: nat) (fwd: forwarding_map)
  (res: minor_collect_result)
  : Lemma
    (requires
      minor_collect_iso_preconditions minor major fp roots /\
      (let prom = cheney_promote minor major fp roots in
       let cg = build_combined_graph minor major in
       let combined_roots = pre_gc_roots roots in
       fwd == prom.fwd_map /\
       res == cheney_collect_spec minor major fp roots /\
       combined_reachable cg combined_roots (MinorV src) /\
       combined_reachable cg combined_roots dst /\
       mem_ce (MinorV src, dst) cg /\
       i < minor_wosize minor src /\
       classify_minor_field minor major (minor_read_field minor src i) == Some dst /\
       Seq.mem src (live_set_of minor major roots) /\
       Seq.mem src (minor_objects minor) /\
       fwd src <> 0UL /\
       Seq.mem (fwd src <: obj_addr) (objects zero_addr res.mc_major) /\
       (match dst with MinorV d -> fwd d <> 0UL | MajorV _ -> true)))
    (ensures (
      let fwd_src = fwd src in
      let fwd_dst = Iso.fwd_morphism fwd dst in
      U64.v fwd_src >= 0 /\ U64.v fwd_src < heap_size /\ U64.v fwd_src % U64.v mword == 0 /\
      U64.v fwd_dst >= 0 /\ U64.v fwd_dst < heap_size /\ U64.v fwd_dst % U64.v mword == 0 /\
      Seq.mem ((fwd_src <: hp_addr), (fwd_dst <: hp_addr)) (create_graph res.mc_major).edges))
  = let fwd_src : obj_addr = fwd src in
    let minor_val = minor_read_field minor src i in
    let fwd_dst = Iso.fwd_morphism fwd dst in
    minor_edge_src_scannable minor major src dst i;
    Helpers.promoted_copy_properties_instance minor major fp roots src;
    wf_object_bound res.mc_major fwd_src;
    let bound = U64.v (wosize_of_object fwd_src res.mc_major) in
    Helpers.field_addr_arithmetic (U64.v fwd_src) i bound;
    let field_addr_v = U64.v fwd_src + i * 8 in
    let mc_val = read_word res.mc_major (U64.uint_to_t field_addr_v) in
    Helpers.field_correspondence_instance minor major res.mc_major fwd roots src i;
    (match dst with
     | MinorV d ->
       classify_minor_field_inv_minor minor major minor_val d;
       GC.Gen.MinorHeap.minor_objects_valid minor d;
       assert (minor_val == d);
       assert (is_minor_pointer minor_val);
       assert (fwd d <> 0UL);
       assert (mc_val == fwd minor_val)
     | MajorV d ->
       classify_minor_field_inv_major minor major minor_val d;
       MajorBridge.major_object_not_minor_pointer major d;
       assert (~(is_minor_pointer minor_val));
       assert (mc_val == minor_val));
    assert (mc_val == fwd_dst);
    (match dst with
     | MinorV d ->
       CheneyDisch.cheney_fwd_targets_in_mc_major minor major fp roots
     | MajorV d ->
       CheneyCorr.cheney_collect_preserves_objects minor major fp roots);
    prove_minor_to_graph_edge minor major fp roots src dst i fwd_dst fwd_src fwd res
#pop-options

/// ---------------------------------------------------------------------------
/// Edge forward: Minor→* main
/// ---------------------------------------------------------------------------

private
#push-options "--z3rlimit 50 --fuel 0 --ifuel 1 --split_queries always"
let prove_edge_forward_minor
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: U64.t) (dst: combined_vertex)
  : Lemma
    (requires
      minor_collect_iso_preconditions minor major fp roots /\
      (let cg = build_combined_graph minor major in
       let combined_roots = pre_gc_roots roots in
       combined_reachable cg combined_roots (MinorV src) /\
       combined_reachable cg combined_roots dst /\
       mem_ce (MinorV src, dst) cg))
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let fwd = prom.fwd_map in
      let res = cheney_collect_spec minor major fp roots in
      let g_mc = create_graph res.mc_major in
      let fwd_src = fwd src in
      let fwd_dst = Iso.fwd_morphism fwd dst in
      U64.v fwd_src >= 0 /\ U64.v fwd_src < heap_size /\ U64.v fwd_src % U64.v mword == 0 /\
      U64.v fwd_dst >= 0 /\ U64.v fwd_dst < heap_size /\ U64.v fwd_dst % U64.v mword == 0 /\
      Seq.mem ((fwd_src <: hp_addr), (fwd_dst <: hp_addr)) g_mc.edges))
  = RBridge.reachability_bridge minor major roots;
    let remembered = minor_roots_from_major major in
    FStar.Seq.Properties.lemma_mem_append roots remembered;
    let aux_mono (v: U64.t) : Lemma
      (requires Seq.mem v (live_set_of minor major roots))
      (ensures Seq.mem v (Reach.minor_reachable minor roots))
    = Reach.minor_reachable_mono minor (Seq.append roots remembered) roots v
    in
    Classical.forall_intro (Classical.move_requires aux_mono);
    CheneyCorr.cheney_promotes_all_reachable minor major fp roots;
    let prom = cheney_promote minor major fp roots in
    let fwd = prom.fwd_map in
    let res = cheney_collect_spec minor major fp roots in
    CheneyDisch.cheney_fwd_targets_in_mc_major minor major fp roots;
    let fwd_src : obj_addr = fwd src in
    minor_edge_elim minor major src dst;
    let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun i -> i < minor_wosize minor src /\
                classify_minor_field minor major (minor_read_field minor src i) == Some dst) in
    assert (match dst with MinorV d -> fwd d <> 0UL | MajorV _ -> true);
    prove_edge_forward_minor_case minor major fp roots src dst i fwd res
#pop-options

/// ---------------------------------------------------------------------------
/// Wrappers for dispatch from forward reachability
/// ---------------------------------------------------------------------------

private
#restart-solver
#push-options "--z3rlimit 50 --split_queries always"
let prove_edge_forward_major_major_u
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src dst: U64.t)
  : Lemma
    (requires
      minor_collect_iso_preconditions minor major fp roots /\
      (let cg = build_combined_graph minor major in
       let combined_roots = pre_gc_roots roots in
       combined_reachable cg combined_roots (MajorV src) /\
       combined_reachable cg combined_roots (MajorV dst) /\
       mem_ce (MajorV src, MajorV dst) cg))
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let fwd = prom.fwd_map in
      let res = cheney_collect_spec minor major fp roots in
      let g_mc = create_graph res.mc_major in
      U64.v src >= 0 /\ U64.v src < heap_size /\ U64.v src % U64.v mword == 0 /\
      U64.v dst >= 0 /\ U64.v dst < heap_size /\ U64.v dst % U64.v mword == 0 /\
      Seq.mem ((src <: hp_addr), (dst <: hp_addr)) g_mc.edges))
  = RBridge.reachable_major_valid_nonblue minor major roots;
    prove_edge_forward_major_major minor major fp roots src dst
#pop-options

private
#restart-solver
#push-options "--z3rlimit 50 --split_queries always"
let prove_edge_forward_major_minor_u
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src dst: U64.t)
  : Lemma
    (requires
      minor_collect_iso_preconditions minor major fp roots /\
      (let cg = build_combined_graph minor major in
       let combined_roots = pre_gc_roots roots in
       combined_reachable cg combined_roots (MajorV src) /\
       combined_reachable cg combined_roots (MinorV dst) /\
       mem_ce (MajorV src, MinorV dst) cg))
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let fwd = prom.fwd_map in
      let res = cheney_collect_spec minor major fp roots in
      let g_mc = create_graph res.mc_major in
      let fwd_dst = fwd dst in
      U64.v src >= 0 /\ U64.v src < heap_size /\ U64.v src % U64.v mword == 0 /\
      U64.v fwd_dst >= 0 /\ U64.v fwd_dst < heap_size /\ U64.v fwd_dst % U64.v mword == 0 /\
      Seq.mem ((src <: hp_addr), (fwd_dst <: hp_addr)) g_mc.edges))
  = RBridge.reachable_major_valid_nonblue minor major roots;
    prove_edge_forward_major_minor minor major fp roots src dst
#pop-options

/// ---------------------------------------------------------------------------
/// (C) prove_edge_forward: universal quantifier lift
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 50 --fuel 0 --ifuel 1"
let prove_edge_forward
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires minor_collect_iso_preconditions minor major fp roots)
    (ensures (
      let combined_roots = pre_gc_roots roots in
      let cg = build_combined_graph minor major in
      let prom = cheney_promote minor major fp roots in
      let fwd = prom.fwd_map in
      let res = cheney_collect_spec minor major fp roots in
      let g_mc = create_graph res.mc_major in
      forall (u v: combined_vertex).
        combined_reachable cg combined_roots u /\
        combined_reachable cg combined_roots v /\
        mem_ce (u, v) cg ==>
        (let fu = Iso.fwd_morphism fwd u in
         let fv = Iso.fwd_morphism fwd v in
         U64.v fu >= 0 /\ U64.v fu < heap_size /\ U64.v fu % U64.v mword == 0 /\
         U64.v fv >= 0 /\ U64.v fv < heap_size /\ U64.v fv % U64.v mword == 0 /\
         Seq.mem ((fu <: hp_addr), (fv <: hp_addr)) g_mc.edges)))
  = let aux_inner (u: combined_vertex) (v: combined_vertex) : Lemma
      (requires (let cg = build_combined_graph minor major in
                 let combined_roots = pre_gc_roots roots in
                 combined_reachable cg combined_roots u /\
                 combined_reachable cg combined_roots v /\
                 mem_ce (u, v) cg))
      (ensures (let prom = cheney_promote minor major fp roots in
                let fwd = prom.fwd_map in
                let res = cheney_collect_spec minor major fp roots in
                let g_mc = create_graph res.mc_major in
                let fu = Iso.fwd_morphism fwd u in
                let fv = Iso.fwd_morphism fwd v in
                U64.v fu >= 0 /\ U64.v fu < heap_size /\ U64.v fu % U64.v mword == 0 /\
                U64.v fv >= 0 /\ U64.v fv < heap_size /\ U64.v fv % U64.v mword == 0 /\
                Seq.mem ((fu <: hp_addr), (fv <: hp_addr)) g_mc.edges))
    = match u, v with
      | MajorV src, MajorV dst ->
        prove_edge_forward_major_major_u minor major fp roots src dst
      | MajorV src, MinorV dst ->
        prove_edge_forward_major_minor_u minor major fp roots src dst
      | MinorV src, _ ->
        prove_edge_forward_minor minor major fp roots src v
    in
    let aux_outer (u: combined_vertex) : Lemma
      (ensures (let cg = build_combined_graph minor major in
                let combined_roots = pre_gc_roots roots in
                let prom = cheney_promote minor major fp roots in
                let fwd = prom.fwd_map in
                let res = cheney_collect_spec minor major fp roots in
                let g_mc = create_graph res.mc_major in
                forall (v: combined_vertex).
                  combined_reachable cg combined_roots u /\
                  combined_reachable cg combined_roots v /\
                  mem_ce (u, v) cg ==>
                  (let fu = Iso.fwd_morphism fwd u in
                   let fv = Iso.fwd_morphism fwd v in
                   U64.v fu >= 0 /\ U64.v fu < heap_size /\ U64.v fu % U64.v mword == 0 /\
                   U64.v fv >= 0 /\ U64.v fv < heap_size /\ U64.v fv % U64.v mword == 0 /\
                   Seq.mem ((fu <: hp_addr), (fv <: hp_addr)) g_mc.edges)))
    = Classical.forall_intro (Classical.move_requires (aux_inner u))
    in
    Classical.forall_intro aux_outer
#pop-options

/// ---------------------------------------------------------------------------
/// (G) Forward reachability via induction
/// ---------------------------------------------------------------------------

private
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
let root_morphism_in_mc_roots
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (v: combined_vertex)
  : Lemma
    (requires minor_collect_iso_preconditions minor major fp roots /\
             (let cg = build_combined_graph minor major in
              let combined_roots = pre_gc_roots roots in
              Seq.mem v combined_roots /\ mem_cv v cg /\
              combined_reachable cg combined_roots v))
    (ensures (let prom = cheney_promote minor major fp roots in
              let fwd = prom.fwd_map in
              let res = cheney_collect_spec minor major fp roots in
              let mc_roots = res.mc_roots in
              Seq.mem (Iso.fwd_morphism fwd v) mc_roots))
  = let prom = cheney_promote minor major fp roots in
    let fwd = prom.fwd_map in
    let res = cheney_collect_spec minor major fp roots in
    let mc_roots = res.mc_roots in
    match v with
    | MinorV a ->
      classify_roots_inv_minor roots a;
      Helpers.reachable_minor_gives_fwd_nonzero minor major fp roots a;
      assert (rewrite_root a fwd == fwd a);
      let i = FStar.Seq.Properties.index_mem a roots in
      rewrite_roots_length roots fwd;
      rewrite_roots_index roots fwd i;
      assert (Seq.mem (fwd a) mc_roots)
    | MajorV a ->
      classify_roots_inv_major roots a;
      assert (rewrite_root a fwd == a);
      let i = FStar.Seq.Properties.index_mem a roots in
      rewrite_roots_length roots fwd;
      rewrite_roots_index roots fwd i;
      assert (Seq.mem a mc_roots)
#pop-options

#restart-solver
#push-options "--z3rlimit 50 --fuel 0 --ifuel 1 --split_queries always"
let prove_forward_reachability
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires minor_collect_iso_preconditions minor major fp roots)
    (ensures (
      let combined_roots = pre_gc_roots roots in
      let cg = build_combined_graph minor major in
      let prom = cheney_promote minor major fp roots in
      let fwd = prom.fwd_map in
      let res = cheney_collect_spec minor major fp roots in
      let g_mc = create_graph res.mc_major in
      let mc_roots = res.mc_roots in
      forall (v: combined_vertex).
        combined_reachable cg combined_roots v ==>
        (let w = Iso.fwd_morphism fwd v in
         U64.v w >= U64.v mword /\ U64.v w < heap_size /\ U64.v w % U64.v mword == 0 /\
         Seq.mem (w <: hp_addr) g_mc.vertices /\
         (exists (r: U64.t).
           Seq.mem r mc_roots /\
           U64.v r >= U64.v mword /\ U64.v r < heap_size /\ U64.v r % U64.v mword == 0 /\
           Seq.mem (r <: hp_addr) g_mc.vertices /\
           reachable g_mc (r <: hp_addr) (w <: hp_addr)))))
  = let cg = build_combined_graph minor major in
    let combined_roots = pre_gc_roots roots in
    let prom = cheney_promote minor major fp roots in
    let fwd = prom.fwd_map in
    let res = cheney_collect_spec minor major fp roots in
    let g_mc = create_graph res.mc_major in
    let mc_roots = res.mc_roots in
    let p (v: combined_vertex) : prop =
      combined_reachable cg combined_roots v /\
      (let w = Iso.fwd_morphism fwd v in
       U64.v w >= U64.v mword /\ U64.v w < heap_size /\ U64.v w % U64.v mword == 0 /\
       Seq.mem (w <: hp_addr) g_mc.vertices /\
       (exists (r: U64.t).
         Seq.mem r mc_roots /\
         U64.v r >= U64.v mword /\ U64.v r < heap_size /\ U64.v r % U64.v mword == 0 /\
         Seq.mem (r <: hp_addr) g_mc.vertices /\
         reachable g_mc (r <: hp_addr) (w <: hp_addr)))
    in
    let base_lemma (v: combined_vertex) : Lemma
      (requires Seq.mem v combined_roots /\ mem_cv v cg)
      (ensures p v)
    = combined_reachable_root cg combined_roots v;
      (match v with
       | MinorV a -> Helpers.prove_image_validity_minor minor major fp roots a
       | MajorV a -> Helpers.prove_image_validity_major minor major fp roots a);
      root_morphism_in_mc_roots minor major fp roots v;
      let w = Iso.fwd_morphism fwd v in
      reach_refl g_mc (w <: hp_addr)
    in
    let step_lemma (u: combined_vertex) (w: combined_vertex) : Lemma
      (requires p u /\ mem_ce (u, w) cg)
      (ensures p w)
    = combined_reachable_step cg combined_roots u w;
      (match w with
       | MinorV a -> Helpers.prove_image_validity_minor minor major fp roots a
       | MajorV a -> Helpers.prove_image_validity_major minor major fp roots a);
      let fu = Iso.fwd_morphism fwd u in
      let fw = Iso.fwd_morphism fwd w in
      (match u, w with
       | MajorV s, MajorV d -> prove_edge_forward_major_major_u minor major fp roots s d
       | MajorV s, MinorV d -> prove_edge_forward_major_minor_u minor major fp roots s d
       | MinorV s, _ -> prove_edge_forward_minor minor major fp roots s w);
      assert (Seq.mem ((fu <: hp_addr), (fw <: hp_addr)) g_mc.edges);
      edge_reach g_mc (fu <: hp_addr) (fw <: hp_addr);
      let r = FStar.IndefiniteDescription.indefinite_description_ghost U64.t
        (fun r -> Seq.mem r mc_roots /\
                  U64.v r >= U64.v mword /\ U64.v r < heap_size /\ U64.v r % U64.v mword == 0 /\
                  Seq.mem (r <: hp_addr) g_mc.vertices /\
                  reachable g_mc (r <: hp_addr) (fu <: hp_addr)) in
      reach_trans g_mc (r <: hp_addr) (fu <: hp_addr) (fw <: hp_addr)
    in
    let aux (v: combined_vertex) : Lemma
      (requires combined_reachable cg combined_roots v)
      (ensures (let w = Iso.fwd_morphism fwd v in
                U64.v w >= U64.v mword /\ U64.v w < heap_size /\ U64.v w % U64.v mword == 0 /\
                Seq.mem (w <: hp_addr) g_mc.vertices /\
                (exists (r: U64.t).
                  Seq.mem r mc_roots /\
                  U64.v r >= U64.v mword /\ U64.v r < heap_size /\ U64.v r % U64.v mword == 0 /\
                  Seq.mem (r <: hp_addr) g_mc.vertices /\
                  reachable g_mc (r <: hp_addr) (w <: hp_addr))))
    = Classical.forall_intro (Classical.move_requires base_lemma);
      let step_outer (u': combined_vertex) : Lemma
        (ensures forall (w': combined_vertex). p u' /\ mem_ce (u', w') cg ==> p w')
      = Classical.forall_intro (Classical.move_requires (step_lemma u'))
      in
      Classical.forall_intro step_outer;
      combined_reachable_ind cg combined_roots p v
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options
