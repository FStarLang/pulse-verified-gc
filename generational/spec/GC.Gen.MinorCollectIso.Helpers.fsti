/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectIso.Helpers — Shared helper lemmas for isomorphism proofs
/// ---------------------------------------------------------------------------
///
/// Provides helper lemmas used by both EdgeForward and Surjectivity modules.
/// Isolated behind an .fsti to prevent SMT context pollution.

module GC.Gen.MinorCollectIso.Helpers

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

module Iso = GC.Gen.CombinedGraph.Isomorphism
module Reach = GC.Gen.Reachability
module RBridge = GC.Gen.ReachabilityBridge

open GC.Gen.MinorCollectIso

/// Derive mc_major field value for Major source.
/// After cheney_promote (field unchanged) + update_major_pointers (conditional rewrite).
val derive_mc_major_field_value
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: obj_addr) (i: nat)
  : Lemma
    (requires
      minor_collect_iso_preconditions minor major fp roots /\
      Seq.mem src (objects zero_addr major) /\ ~(is_blue src major) /\
      ~(is_no_scan src major) /\
      U64.v (wosize_of_object src major) >= 1 /\
      i < U64.v (wosize_of_object src major) /\
      U64.v src + i * 8 + 8 <= heap_size /\
      (U64.v src + i * 8) % 8 == 0)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec minor major fp roots in
      let field_addr = U64.uint_to_t (U64.v src + i * 8) in
      let old_val = read_word major field_addr in
      let mc_val = read_word res.mc_major field_addr in
      (is_minor_pointer old_val /\ prom.fwd_map old_val <> 0UL ==>
        mc_val == prom.fwd_map old_val) /\
      (~(is_minor_pointer old_val /\ prom.fwd_map old_val <> 0UL) ==>
        mc_val == old_val)))

/// Pure arithmetic helper: field_addr alignment and bounds.
val field_addr_arithmetic
  (fwd_src_v: nat) (i: nat) (bound: nat)
  : Lemma
    (requires
      fwd_src_v >= 8 /\
      fwd_src_v % 8 == 0 /\
      i < bound /\
      fwd_src_v + bound * 8 <= heap_size)
    (ensures (
      let field_addr_v = fwd_src_v + i * 8 in
      field_addr_v + 8 <= heap_size /\
      field_addr_v % 8 == 0 /\
      field_addr_v >= 0))

/// For src with edge in mc_major, src is not no_scan in mc_major.
val mc_edge_source_not_no_scan
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: obj_addr) (dst: U64.t)
  : Lemma
    (requires minor_collect_iso_preconditions minor major fp roots /\
             U64.v dst < heap_size /\ U64.v dst % U64.v mword == 0 /\
             (let res = cheney_collect_spec minor major fp roots in
              let g_mc = create_graph res.mc_major in
              Seq.mem src (objects zero_addr res.mc_major) /\
              Seq.mem ((src <: hp_addr), (dst <: hp_addr)) g_mc.edges))
    (ensures (let res = cheney_collect_spec minor major fp roots in
              ~(is_no_scan src res.mc_major)))

/// From reachability of MinorV v, derive v ∈ live_set, fwd(v) ≠ 0, and v ∈ minor_objects.
val reachable_minor_gives_fwd_nonzero
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (a: U64.t)
  : Lemma
    (requires minor_collect_iso_preconditions minor major fp roots /\
             (let cg = build_combined_graph minor major in
              let combined_roots = pre_gc_roots roots in
              combined_reachable cg combined_roots (MinorV a)))
    (ensures (let prom = cheney_promote minor major fp roots in
              Seq.mem a (live_set_of minor major roots) /\
              prom.fwd_map a <> 0UL /\
              Seq.mem a (minor_objects minor)))

/// Explicit instantiation of field_correspondence.
val field_correspondence_instance
  (minor: minor_state) (major mc_major: heap) (fwd: forwarding_map) (roots: seq U64.t)
  (obj: U64.t) (j: nat)
  : Lemma
    (requires
      field_correspondence minor major mc_major fwd roots /\
      Seq.mem obj (live_set_of minor major roots) /\
      fwd obj <> 0UL /\
      j < minor_wosize minor obj /\
      (let field_addr_v = U64.v (fwd obj) + j * 8 in
       field_addr_v + 8 <= heap_size /\
       field_addr_v % 8 == 0))
    (ensures (
      let minor_val = minor_read_field minor obj j in
      let field_addr_v = U64.v (fwd obj) + j * 8 in
      let mc_val = read_word mc_major (U64.uint_to_t field_addr_v) in
      (is_minor_pointer minor_val /\ fwd minor_val <> 0UL ==>
        mc_val == fwd minor_val) /\
      (~(is_minor_pointer minor_val /\ fwd minor_val <> 0UL) ==>
        mc_val == minor_val)))

/// Explicit instantiation of promoted_copy_properties.
val promoted_copy_properties_instance
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (v: U64.t)
  : Lemma
    (requires
      promoted_copy_properties minor major fp roots /\
      Seq.mem v (live_set_of minor major roots) /\
      (cheney_promote minor major fp roots).fwd_map v <> 0UL)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec minor major fp roots in
      let fwd_v = prom.fwd_map v in
      U64.v fwd_v >= U64.v mword /\ U64.v fwd_v < heap_size /\ U64.v fwd_v % U64.v mword == 0 /\
      Seq.mem (fwd_v <: obj_addr) (objects zero_addr res.mc_major) /\
      U64.v (wosize_of_object (fwd_v <: obj_addr) res.mc_major) >= minor_wosize minor v /\
      (minor_tag minor v < 251 ==> is_no_scan (fwd_v <: obj_addr) res.mc_major = false)))

/// Image validity for minor vertices.
val prove_image_validity_minor
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (a: U64.t)
  : Lemma
    (requires minor_collect_iso_preconditions minor major fp roots /\
             (let cg = build_combined_graph minor major in
              let combined_roots = pre_gc_roots roots in
              combined_reachable cg combined_roots (MinorV a)))
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let fwd = prom.fwd_map in
      let res = cheney_collect_spec minor major fp roots in
      let g_mc = create_graph res.mc_major in
      let w = fwd a in
      U64.v w >= U64.v mword /\ U64.v w < heap_size /\ U64.v w % U64.v mword == 0 /\
      Seq.mem (w <: hp_addr) g_mc.vertices))

/// Image validity for major vertices.
val prove_image_validity_major
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (a: U64.t)
  : Lemma
    (requires minor_collect_iso_preconditions minor major fp roots /\
             (let cg = build_combined_graph minor major in
              let combined_roots = pre_gc_roots roots in
              combined_reachable cg combined_roots (MajorV a)))
    (ensures (
      let res = cheney_collect_spec minor major fp roots in
      let g_mc = create_graph res.mc_major in
      U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword == 0 /\
      Seq.mem (a <: hp_addr) g_mc.vertices))

/// Blue elimination: in a well-formed heap with no_pointer_to_blue,
/// a non-blue object's field value cannot equal a blue target address.
/// Used to eliminate the "field not rewritten" case in edge backward proofs.
val major_field_not_equal_blue
  (major: heap) (src: obj_addr) (i: nat) (target: obj_addr)
  : Lemma
    (requires
      well_formed_heap major /\
      GC.Spec.Mark.no_pointer_to_blue major /\
      Seq.mem src (objects zero_addr major) /\ ~(is_blue src major) /\
      Seq.mem target (objects zero_addr major) /\ is_blue target major /\
      i < U64.v (wosize_of_object src major) /\
      U64.v src + i * 8 + 8 <= heap_size /\ (U64.v src + i * 8) % 8 == 0)
    (ensures read_word major (U64.uint_to_t (U64.v src + i * 8)) <> (target <: U64.t))

/// Graph vertex implies obj_addr bound: any vertex in create_graph mc
/// has address >= mword. This bridges the vertex_id → obj_addr gap.
val graph_vertex_ge_mword (mc: heap) (v: vertex_id)
  : Lemma (requires mem_graph_vertex (create_graph mc) v)
          (ensures U64.v v >= U64.v mword)

/// Any object in a major heap (objects starting at zero_addr) cannot be
/// a minor pointer: its address >= zero_addr + mword >= minor_heap_size + 8.
val major_object_not_minor (mc: heap) (root: obj_addr)
  : Lemma (requires Seq.mem root (objects zero_addr mc))
          (ensures ~(is_minor_pointer root))
