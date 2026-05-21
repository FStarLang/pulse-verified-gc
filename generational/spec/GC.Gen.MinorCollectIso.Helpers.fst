/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectIso.Helpers — Implementation
/// ---------------------------------------------------------------------------

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

module AllocLemmas = GC.Spec.Allocator.Lemmas
module Iso = GC.Gen.CombinedGraph.Isomorphism
module CheneyCorr = GC.Gen.CheneyCorrectness
module CheneyDisch = GC.Gen.CheneyDischarge
module Reach = GC.Gen.Reachability
module RBridge = GC.Gen.ReachabilityBridge
module HeaderPres = GC.Gen.MinorCollectIso.HeaderPres
module HeapGraph = GC.Spec.HeapGraph
module PromUpdate = GC.Gen.PromoteUpdate

open GC.Gen.MinorCollectIso

/// Helper: derive chain_avoids from chain_objects_blue + ~is_blue
private
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let derive_chain_avoids
  (major: heap) (fp: U64.t) (src: obj_addr)
  : Lemma
    (requires chain_objects_blue major fp /\ Seq.mem src (objects zero_addr major) /\ ~(is_blue src major))
    (ensures AllocLemmas.chain_avoids major fp (src <: U64.t) (heap_size / U64.v mword) = true)
  = CheneyDisch.chain_blue_implies_alloc_avoids major fp
#pop-options

/// Helper: derive is_no_scan/is_blue preservation on prom.major_final
private
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let derive_prom_header_preserved
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: obj_addr)
  : Lemma
    (requires
      minor_collect_iso_preconditions minor major fp roots /\
      Seq.mem src (objects zero_addr major) /\ ~(is_blue src major) /\
      U64.v (wosize_of_object src major) >= 1)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      Seq.mem src (objects zero_addr prom.major_final) /\
      wosize_of_object src prom.major_final == wosize_of_object src major /\
      is_blue src prom.major_final = is_blue src major /\
      is_no_scan src prom.major_final = is_no_scan src major))
  = let prom = cheney_promote minor major fp roots in
    GC.Gen.Cheney.cheney_promote_preserves_objects minor major fp roots;
    HeaderPres.cheney_promote_preserves_wosize minor major fp roots src;
    CheneyDisch.chain_blue_implies_alloc_avoids major fp;
    GC.Gen.Cheney.cheney_promote_preserves_read_header minor major fp roots src;
    GC.Spec.Object.color_of_header_eq src major prom.major_final;
    GC.Spec.Object.tag_of_object_spec src major;
    GC.Spec.Object.tag_of_object_spec src prom.major_final;
    GC.Spec.Object.is_no_scan_spec src major;
    GC.Spec.Object.is_no_scan_spec src prom.major_final
#pop-options

/// Helper: body field value preserved through cheney_promote for non-blue src
private
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let derive_prom_field_preserved
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: obj_addr) (i: nat)
  : Lemma
    (requires
      minor_collect_iso_preconditions minor major fp roots /\
      Seq.mem src (objects zero_addr major) /\ ~(is_blue src major) /\
      U64.v (wosize_of_object src major) >= 1 /\
      i < U64.v (wosize_of_object src major) /\
      U64.v src + i * 8 + 8 <= heap_size /\
      (U64.v src + i * 8) % 8 == 0)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let field_addr : hp_addr = U64.uint_to_t (U64.v src + i * 8) in
      read_word prom.major_final field_addr == read_word major field_addr))
  = let field_addr : hp_addr = U64.uint_to_t (U64.v src + i * 8) in
    CheneyDisch.chain_blue_implies_alloc_avoids major fp;
    GC.Gen.Cheney.cheney_promote_preserves_read_body minor major fp roots src field_addr
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let derive_mc_major_field_value
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
  = let prom = cheney_promote minor major fp roots in
    let field_addr : hp_addr = U64.uint_to_t (U64.v src + i * 8) in
    derive_prom_field_preserved minor major fp roots src i;
    assert (read_word prom.major_final field_addr == read_word major field_addr);
    GC.Gen.Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
    GC.Gen.Cheney.cheney_promote_preserves_objects minor major fp roots;
    derive_prom_header_preserved minor major fp roots src;
    PromUpdate.update_major_pointers_field_effect prom.major_final prom.fwd_map src i
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let field_addr_arithmetic
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
  = FStar.Math.Lemmas.modulo_addition_lemma fwd_src_v 8 i;
    FStar.Math.Lemmas.lemma_mult_le_right 8 (i + 1) bound
#pop-options

#restart-solver
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let mc_edge_source_not_no_scan
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
  = let res = cheney_collect_spec minor major fp roots in
    let mc = res.mc_major in
    let dst_hp : hp_addr = dst in
    HeapGraph.all_edges_source_membership mc (objects zero_addr mc) src dst_hp;
    ()
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let reachable_minor_gives_fwd_nonzero
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
  = RBridge.reachability_bridge minor major roots;
    let remembered = minor_roots_from_major major in
    FStar.Seq.Properties.lemma_mem_append roots remembered;
    Reach.minor_reachable_mono minor (Seq.append roots remembered) roots a;
    CheneyCorr.cheney_promotes_all_reachable minor major fp roots;
    Reach.minor_reachable_subset minor (Seq.append roots remembered)
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let field_correspondence_instance
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
  = ()
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let promoted_copy_properties_instance
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
  = ()
#pop-options

#push-options "--z3rlimit 50"
let prove_image_validity_minor
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
  = let prom = cheney_promote minor major fp roots in
    let fwd = prom.fwd_map in
    let res = cheney_collect_spec minor major fp roots in
    RBridge.reachability_bridge minor major roots;
    let remembered = minor_roots_from_major major in
    FStar.Seq.Properties.lemma_mem_append roots remembered;
    Reach.minor_reachable_mono minor (Seq.append roots remembered) roots a;
    CheneyCorr.cheney_promotes_all_reachable minor major fp roots;
    CheneyDisch.cheney_fwd_targets_in_mc_major minor major fp roots;
    graph_vertices_mem res.mc_major (fwd a <: obj_addr)
#pop-options

#push-options "--z3rlimit 50"
let prove_image_validity_major
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
  = let res = cheney_collect_spec minor major fp roots in
    RBridge.reachable_major_valid_nonblue minor major roots;
    CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
    graph_vertices_mem res.mc_major (a <: obj_addr)
#pop-options

module Mark = GC.Spec.Mark

/// Blue elimination: field of non-blue object cannot point to blue target.
/// Proof: if field == target (blue, valid obj_addr), then field_read_implies_exists_pointing
/// establishes points_to, contradicting no_pointer_to_blue.
#push-options "--z3rlimit 80 --fuel 2 --ifuel 0"
let major_field_not_equal_blue
  (major: heap) (src: obj_addr) (i: nat) (target: obj_addr)
  : Lemma
    (requires
      well_formed_heap major /\
      Mark.no_pointer_to_blue major /\
      Seq.mem src (objects zero_addr major) /\ ~(is_blue src major) /\
      Seq.mem target (objects zero_addr major) /\ is_blue target major /\
      i < U64.v (wosize_of_object src major) /\
      U64.v src + i * 8 + 8 <= heap_size /\ (U64.v src + i * 8) % 8 == 0)
    (ensures read_word major (U64.uint_to_t (U64.v src + i * 8)) <> (target <: U64.t))
  = let field_addr : hp_addr = U64.uint_to_t (U64.v src + i * 8) in
    let fv = read_word major field_addr in
    if fv = (target <: U64.t) then begin
      // target ∈ objects → U64.v target > U64.v zero_addr
      // Combined with alignment: target >= zero_addr + mword → is_pointer target
      objects_addresses_gt_start zero_addr major target;
      assert (is_pointer_field fv);
      assert (is_pointer_to fv target);
      // Establish points_to via field_read_implies_exists_pointing
      let k = U64.uint_to_t i in
      let wz = wosize_of_object src major in
      wf_object_size_bound major src;
      wosize_of_object_bound src major;
      FStar.Math.Lemmas.pow2_lt_compat 61 54;
      field_read_implies_exists_pointing major src wz k target;
      assert (points_to major src target)
      // no_pointer_to_blue: src non-blue, points_to → ~(is_blue target major). Contradiction!
    end
#pop-options

/// Graph vertex → obj_addr bound.
/// Any vertex in create_graph mc has address >= mword because vertices
/// come from `objects zero_addr mc` (all obj_addr values).
private
#push-options "--z3rlimit 50 --fuel 2 --ifuel 0"
let rec coerce_vertex_ge_mword (s: seq obj_addr) (x: vertex_id)
  : Lemma (requires Seq.mem x (HeapGraph.coerce_to_vertex_list s))
          (ensures U64.v x >= U64.v mword)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      let hd : obj_addr = Seq.head s in
      let tl = Seq.tail s in
      let coerced_tl = HeapGraph.coerce_to_vertex_list tl in
      // coerce_to_vertex_list s = cons hd (coerce_to_vertex_list tl)
      // So mem x → x = hd \/ mem x coerced_tl
      FStar.Seq.Properties.mem_cons (hd <: vertex_id) coerced_tl;
      if x = (hd <: vertex_id) then ()
      else coerce_vertex_ge_mword tl x
    end
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let graph_vertex_ge_mword (mc: heap) (v: vertex_id)
  : Lemma (requires mem_graph_vertex (create_graph mc) v)
          (ensures U64.v v >= U64.v mword)
  = objects_is_vertex_set mc;
    coerce_vertex_ge_mword (objects zero_addr mc) v
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let major_object_not_minor (mc: heap) (root: obj_addr)
  : Lemma (requires Seq.mem root (objects zero_addr mc))
          (ensures ~(is_minor_pointer root))
  = GC.Spec.Fields.objects_addresses_gt_start zero_addr mc root;
    GC.Gen.Base.major_starts_after_minor()
#pop-options
