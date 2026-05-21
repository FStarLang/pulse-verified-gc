/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectIso.EdgeBackward — Implementation
/// ---------------------------------------------------------------------------
///
/// Proves strong edge backward lemmas for the surjectivity proof.
/// Isolated in its own module to prevent SMT context pollution.

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
module HeapGraph = GC.Spec.HeapGraph
module HeaderPres = GC.Gen.MinorCollectIso.HeaderPres
module Helpers = GC.Gen.MinorCollectIso.Helpers
module RBridge = GC.Gen.ReachabilityBridge
module CheneyCorr = GC.Gen.CheneyCorrectness
module CheneyDisj = GC.Gen.CheneyDisjoint
module CheneyDisch = GC.Gen.CheneyDischarge
module CheneyInj = GC.Gen.CheneyInjectivity
module MajorBridge = GC.Gen.CombinedGraph.MajorBridge

/// ---------------------------------------------------------------------------
/// graph_edge_implies_points_to
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let graph_edge_implies_points_to (g: heap) (src dst: obj_addr)
  : Lemma
    (requires well_formed_heap g /\
             Seq.mem src (objects zero_addr g) /\
             ~(is_no_scan src g) /\
             Seq.mem ((src <: hp_addr), (dst <: hp_addr)) (create_graph g).edges)
    (ensures GC.Spec.Fields.points_to g src dst)
  = objects_is_vertex_set g;
    GC.Spec.Fields.wf_object_bound g src;
    HeapGraph.object_fits_from_bound src g;
    HeapGraph.graph_edge_has_field_index g (objects zero_addr g) src (dst <: hp_addr);
    let j = FStar.IndefiniteDescription.indefinite_description_ghost
      (j:U64.t{U64.v j >= 1})
      (fun j -> U64.v j <= U64.v (wosize_of_object src g) /\
                HeapGraph.get_field g src j == (dst <: hp_addr) /\
                HeapGraph.is_pointer_field (dst <: hp_addr)) in
    let k = U64.sub j 1UL in
    let wz = wosize_of_object src g in
    assert (U64.v k < U64.v wz);
    GC.Spec.Fields.wf_object_bound g src;
    hd_address_spec src;
    wosize_of_object_bound src g;
    assert (U64.v wz < pow2 54);
    FStar.Math.Lemmas.pow2_lt_compat 61 54;
    assert (U64.v k < pow2 61);
    Helpers.field_addr_arithmetic (U64.v src) (U64.v k) (U64.v (wosize_of_object src g));
    HeapGraph.get_field_addr_eq g src j;
    assert (GC.Spec.Fields.is_pointer_to (dst <: U64.t) dst);
    GC.Spec.Fields.field_read_implies_exists_pointing g src wz k dst
#pop-options

/// ---------------------------------------------------------------------------
/// mc_edge_target_nonblue
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let mc_edge_target_nonblue
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
  = let res = cheney_collect_spec minor major fp roots in
    let mc = res.mc_major in
    Helpers.mc_edge_source_not_no_scan minor major fp roots src dst;
    graph_edge_implies_points_to mc src dst
#pop-options

/// ---------------------------------------------------------------------------
/// strong_edge_backward_to_major
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1 --split_queries always"
let strong_edge_backward_to_major
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
  = let prom = cheney_promote minor major fp roots in
    let fwd = prom.fwd_map in
    let res = cheney_collect_spec minor major fp roots in
    let mc = res.mc_major in
    let g_mc = create_graph mc in
    let mid : hp_addr = Iso.fwd_morphism fwd cv_mid in
    match cv_mid with
    | MajorV s ->
      RBridge.reachable_major_valid_nonblue minor major roots;
      CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
      CheneyDisj.cheney_promote_fwd_disjoint_nonblue minor major fp roots;
      Helpers.mc_edge_source_not_no_scan minor major fp roots (s <: obj_addr) dst;
      HeaderPres.minor_collect_preserves_wosize minor major fp roots (s <: obj_addr);
      HeaderPres.minor_collect_preserves_is_no_scan minor major fp roots (s <: obj_addr);
      assert (Seq.mem (s <: obj_addr) (objects zero_addr major));
      assert (Seq.mem (s <: obj_addr) (objects zero_addr mc));
      GC.Spec.Fields.wf_object_bound mc (s <: obj_addr);
      HeapGraph.object_fits_from_bound (s <: obj_addr) mc;
      objects_is_vertex_set mc;
      HeapGraph.graph_edge_has_field_index mc (objects zero_addr mc) (s <: obj_addr) dst;
      let j = FStar.IndefiniteDescription.indefinite_description_ghost
        (j:U64.t{U64.v j >= 1})
        (fun j -> U64.v j <= U64.v (wosize_of_object (s <: obj_addr) mc) /\
                  HeapGraph.get_field mc (s <: obj_addr) j == dst /\
                  HeapGraph.is_pointer_field dst) in
      let i : nat = U64.v j - 1 in
      assert (U64.v j <= U64.v (wosize_of_object (s <: obj_addr) major));
      wosize_of_object_bound (s <: obj_addr) mc;
      Helpers.field_addr_arithmetic (U64.v s) i (U64.v (wosize_of_object (s <: obj_addr) mc));
      HeapGraph.get_field_addr_eq mc (s <: obj_addr) j;
      Helpers.derive_mc_major_field_value minor major fp roots (s <: obj_addr) i;
      let field_addr : hp_addr = U64.uint_to_t (U64.v s + i * 8) in
      let old_val = read_word major field_addr in
      let mc_val = read_word mc field_addr in
      assert (mc_val == dst);
      // dst is non-blue → fwd(a) ≠ dst for all a → field wasn't rewritten → old_val = dst
      assert (old_val == dst);
      GC.Spec.Fields.wf_object_bound major (s <: obj_addr);
      HeapGraph.get_field_addr_eq major (s <: obj_addr) j;
      objects_is_vertex_set major;
      HeapGraph.object_fits_from_bound (s <: obj_addr) major;
      HeapGraph.pointer_field_is_graph_edge major (objects zero_addr major) (s <: obj_addr) j;
      MajorBridge.heapgraph_edge_implies_combined minor major (s <: obj_addr) (dst <: obj_addr)
    | MinorV s ->
      Helpers.reachable_minor_gives_fwd_nonzero minor major fp roots s;
      assert (Seq.mem s (live_set_of minor major roots));
      assert (Seq.mem s (minor_objects minor));
      let fwd_s : obj_addr = fwd s in
      CheneyDisch.cheney_fwd_targets_in_mc_major minor major fp roots;
      CheneyDisj.cheney_promote_fwd_disjoint_nonblue minor major fp roots;
      CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
      Helpers.mc_edge_source_not_no_scan minor major fp roots fwd_s dst;
      assert (Seq.mem fwd_s (objects zero_addr mc));
      GC.Spec.Fields.wf_object_bound mc fwd_s;
      HeapGraph.object_fits_from_bound fwd_s mc;
      objects_is_vertex_set mc;
      HeapGraph.graph_edge_has_field_index mc (objects zero_addr mc) fwd_s dst;
      let j = FStar.IndefiniteDescription.indefinite_description_ghost
        (j:U64.t{U64.v j >= 1})
        (fun j -> U64.v j <= U64.v (wosize_of_object fwd_s mc) /\
                  HeapGraph.get_field mc fwd_s j == dst /\
                  HeapGraph.is_pointer_field dst) in
      let i : nat = U64.v j - 1 in
      assert (i < minor_wosize minor s);
      wosize_of_object_bound fwd_s mc;
      Helpers.field_addr_arithmetic (U64.v fwd_s) i (U64.v (wosize_of_object fwd_s mc));
      HeapGraph.get_field_addr_eq mc fwd_s j;
      let field_addr_v = U64.v fwd_s + i * 8 in
      assert (read_word mc (U64.uint_to_t field_addr_v) == dst);
      assert (U64.v fwd_s + i * 8 + 8 <= heap_size);
      assert (U64.v fwd_s % 8 == 0);
      Helpers.field_correspondence_instance minor major mc fwd roots s i;
      let minor_val = minor_read_field minor s i in
      // dst is non-blue and fwd targets are blue → minor_val can't satisfy Case 1 (fwd(minor_val)=dst)
      // So Case 2: minor_val = dst. dst is major obj, not minor pointer.
      assert (minor_val == dst);
      MajorBridge.major_object_not_minor_pointer major (dst <: obj_addr);
      classify_minor_field_major minor major dst;
      minor_field_edge_intro minor major s i (MajorV dst)
#pop-options

/// ---------------------------------------------------------------------------
/// strong_edge_backward_to_minor
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1 --split_queries always"
let strong_edge_backward_to_minor
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
  = let prom = cheney_promote minor major fp roots in
    let fwd = prom.fwd_map in
    let res = cheney_collect_spec minor major fp roots in
    let mc = res.mc_major in
    let g_mc = create_graph mc in
    let mid : hp_addr = Iso.fwd_morphism fwd cv_mid in
    let fwd_a : U64.t = fwd a in
    match cv_mid with
    | MajorV s ->
      RBridge.reachable_major_valid_nonblue minor major roots;
      CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
      CheneyDisj.cheney_promote_fwd_disjoint_nonblue minor major fp roots;
      CheneyInj.cheney_promote_fwd_injective minor major fp roots;
      Helpers.mc_edge_source_not_no_scan minor major fp roots (s <: obj_addr) fwd_a;
      HeaderPres.minor_collect_preserves_wosize minor major fp roots (s <: obj_addr);
      HeaderPres.minor_collect_preserves_is_no_scan minor major fp roots (s <: obj_addr);
      assert (Seq.mem (s <: obj_addr) (objects zero_addr major));
      assert (Seq.mem (s <: obj_addr) (objects zero_addr mc));
      GC.Spec.Fields.wf_object_bound mc (s <: obj_addr);
      HeapGraph.object_fits_from_bound (s <: obj_addr) mc;
      objects_is_vertex_set mc;
      HeapGraph.graph_edge_has_field_index mc (objects zero_addr mc) (s <: obj_addr) fwd_a;
      let j = FStar.IndefiniteDescription.indefinite_description_ghost
        (j:U64.t{U64.v j >= 1})
        (fun j -> U64.v j <= U64.v (wosize_of_object (s <: obj_addr) mc) /\
                  HeapGraph.get_field mc (s <: obj_addr) j == fwd_a /\
                  HeapGraph.is_pointer_field fwd_a) in
      let i : nat = U64.v j - 1 in
      assert (U64.v j <= U64.v (wosize_of_object (s <: obj_addr) major));
      wosize_of_object_bound (s <: obj_addr) mc;
      Helpers.field_addr_arithmetic (U64.v s) i (U64.v (wosize_of_object (s <: obj_addr) mc));
      HeapGraph.get_field_addr_eq mc (s <: obj_addr) j;
      Helpers.derive_mc_major_field_value minor major fp roots (s <: obj_addr) i;
      let field_addr : hp_addr = U64.uint_to_t (U64.v s + i * 8) in
      let old_val = read_word major field_addr in
      let mc_val = read_word mc field_addr in
      assert (mc_val == fwd_a);
      // fwd(a) was blue in original major (from fwd_targets_originally_blue precondition)
      assert (is_blue (fwd_a <: obj_addr) major);
      // s is non-blue → no_pointer_to_blue → old_val can't be fwd_a directly
      Helpers.major_field_not_equal_blue major (s <: obj_addr) i (fwd_a <: obj_addr);
      // derive_mc_major_field_value: Case 2 impossible → Case 1 holds
      assert (is_minor_pointer old_val /\ fwd old_val == fwd_a);
      // By injectivity fwd(old_val) = fwd(a) → old_val = a
      assert (old_val == (a <: U64.t));
      assert (is_minor_pointer (a <: U64.t));
      GC.Gen.MinorHeap.minor_objects_valid minor a;
      is_minor_addr_intro a;
      classify_major_field_is_minor minor major a;
      major_field_edge_intro minor major (s <: obj_addr) i (MinorV a)
    | MinorV s ->
      Helpers.reachable_minor_gives_fwd_nonzero minor major fp roots s;
      assert (Seq.mem s (live_set_of minor major roots));
      assert (Seq.mem s (minor_objects minor));
      let fwd_s : obj_addr = fwd s in
      CheneyDisch.cheney_fwd_targets_in_mc_major minor major fp roots;
      CheneyInj.cheney_promote_fwd_injective minor major fp roots;
      Helpers.mc_edge_source_not_no_scan minor major fp roots fwd_s fwd_a;
      assert (Seq.mem fwd_s (objects zero_addr mc));
      GC.Spec.Fields.wf_object_bound mc fwd_s;
      HeapGraph.object_fits_from_bound fwd_s mc;
      objects_is_vertex_set mc;
      HeapGraph.graph_edge_has_field_index mc (objects zero_addr mc) fwd_s fwd_a;
      let j = FStar.IndefiniteDescription.indefinite_description_ghost
        (j:U64.t{U64.v j >= 1})
        (fun j -> U64.v j <= U64.v (wosize_of_object fwd_s mc) /\
                  HeapGraph.get_field mc fwd_s j == fwd_a /\
                  HeapGraph.is_pointer_field fwd_a) in
      let i : nat = U64.v j - 1 in
      assert (i < minor_wosize minor s);
      wosize_of_object_bound fwd_s mc;
      Helpers.field_addr_arithmetic (U64.v fwd_s) i (U64.v (wosize_of_object fwd_s mc));
      HeapGraph.get_field_addr_eq mc fwd_s j;
      let field_addr_v = U64.v fwd_s + i * 8 in
      assert (read_word mc (U64.uint_to_t field_addr_v) == fwd_a);
      assert (U64.v fwd_s + i * 8 + 8 <= heap_size);
      assert (U64.v fwd_s % 8 == 0);
      Helpers.field_correspondence_instance minor major mc fwd roots s i;
      let minor_val = minor_read_field minor s i in
      // fwd(a) was blue in original. minor can't point to blue major object.
      // Case 1 (fwd(minor_val) = fwd_a): injectivity → minor_val = a
      // Case 2 (minor_val = fwd_a): fwd_a blue in major → impossible
      assert (minor_val == (a <: U64.t));
      GC.Gen.MinorHeap.minor_objects_valid minor a;
      is_minor_addr_intro a;
      classify_minor_field_minor minor major a;
      minor_field_edge_intro minor major s i (MinorV a)
#pop-options
