/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectIso.EdgeBackward — Strong edge backward lemmas
/// ---------------------------------------------------------------------------
///
/// Provides edge-backward reasoning for the surjectivity proof (H).
/// Given an edge (mid, target) in mc_major where mid is the image of a
/// combined-reachable vertex under fwd_morphism, establishes the corresponding
/// combined edge.

module GC.Gen.IsoEdgeBackward

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

/// Graph edge implies points_to predicate.
/// Bridges from mem_graph_edge to the points_to predicate needed by no_pointer_to_blue.
val graph_edge_implies_points_to (g: heap) (src dst: obj_addr)
  : Lemma
    (requires well_formed_heap g /\
             Seq.mem src (objects zero_addr g) /\
             ~(is_no_scan src g) /\
             Seq.mem ((src <: hp_addr), (dst <: hp_addr)) (create_graph g).edges)
    (ensures GC.Spec.Fields.points_to g src dst)

/// Graph edge target is non-blue when source is non-blue.
/// Uses: edge → points_to → no_pointer_to_blue conclusion.
val mc_edge_target_nonblue
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: obj_addr) (dst: obj_addr)
  : Lemma
    (requires minor_collect_iso_preconditions minor major fp roots /\
             (let res = cheney_collect_spec minor major fp roots in
              let g_mc = create_graph res.mc_major in
              Seq.mem src (objects zero_addr res.mc_major) /\
              ~(is_blue src res.mc_major) /\
              Seq.mem ((src <: hp_addr), (dst <: hp_addr)) g_mc.edges))
    (ensures (let res = cheney_collect_spec minor major fp roots in
              ~(is_blue dst res.mc_major)))

/// Strong edge backward: target is pre-existing non-blue major object.
/// Given an mc_major edge from fwd_morphism(cv_mid) to dst, and dst is a
/// pre-existing non-blue major object, establishes the combined edge
/// (cv_mid, MajorV dst).
val strong_edge_backward_to_major
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (cv_mid: combined_vertex) (dst: U64.t)
  : Lemma
    (requires minor_collect_iso_preconditions minor major fp roots /\
             (let cg = build_combined_graph minor major in
              let combined_roots = pre_gc_roots roots in
              let prom = cheney_promote minor major fp roots in
              let fwd = prom.fwd_map in
              let res = cheney_collect_spec minor major fp roots in
              let g_mc = create_graph res.mc_major in
              let mid = Iso.fwd_morphism fwd cv_mid in
              combined_reachable cg combined_roots cv_mid /\
              U64.v mid >= U64.v mword /\ U64.v mid < heap_size /\ U64.v mid % U64.v mword == 0 /\
              U64.v dst >= U64.v mword /\ U64.v dst < heap_size /\ U64.v dst % U64.v mword == 0 /\
              Seq.mem (dst <: obj_addr) (objects zero_addr major) /\
              ~(is_blue (dst <: obj_addr) major) /\
              mem_graph_edge g_mc (mid <: hp_addr) (dst <: hp_addr)))
    (ensures mem_ce (cv_mid, MajorV dst) (build_combined_graph minor major))

/// Strong edge backward: target is a forwarding target (promoted copy).
/// Given an mc_major edge from fwd_morphism(cv_mid) to fwd(a), and a is
/// a live minor object, establishes the combined edge (cv_mid, MinorV a).
val strong_edge_backward_to_minor
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (cv_mid: combined_vertex) (a: U64.t)
  : Lemma
    (requires minor_collect_iso_preconditions minor major fp roots /\
             (let cg = build_combined_graph minor major in
              let combined_roots = pre_gc_roots roots in
              let prom = cheney_promote minor major fp roots in
              let fwd = prom.fwd_map in
              let res = cheney_collect_spec minor major fp roots in
              let g_mc = create_graph res.mc_major in
              let mid = Iso.fwd_morphism fwd cv_mid in
              let live_set = live_set_of minor major roots in
              combined_reachable cg combined_roots cv_mid /\
              U64.v mid >= U64.v mword /\ U64.v mid < heap_size /\ U64.v mid % U64.v mword == 0 /\
              Seq.mem a live_set /\ fwd a <> 0UL /\ Seq.mem a (minor_objects minor) /\
              U64.v (fwd a) >= U64.v mword /\ U64.v (fwd a) < heap_size /\ U64.v (fwd a) % U64.v mword == 0 /\
              mem_graph_edge g_mc (mid <: hp_addr) (fwd a <: hp_addr)))
    (ensures mem_ce (cv_mid, MinorV a) (build_combined_graph minor major))
