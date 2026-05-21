/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectIso.Surjectivity — Implementation
/// ---------------------------------------------------------------------------

module GC.Gen.MinorCollectIso.Surjectivity

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
module CheneyInj = GC.Gen.CheneyInjectivity
module CheneyCorr = GC.Gen.CheneyCorrectness
module CheneyDisch = GC.Gen.CheneyDischarge
module CheneyDisj = GC.Gen.CheneyDisjoint
module Reach = GC.Gen.Reachability
module RBridge = GC.Gen.ReachabilityBridge
module HeaderPres = GC.Gen.MinorCollectIso.HeaderPres
module HeapGraph = GC.Spec.HeapGraph
module EdgePres = GC.Gen.CombinedGraph.EdgePreservation
module MajorBridge = GC.Gen.CombinedGraph.MajorBridge
module Mark = GC.Spec.Mark
module Helpers = GC.Gen.MinorCollectIso.Helpers

/// ---------------------------------------------------------------------------
/// Helper: rewrite_roots membership inversion
/// ---------------------------------------------------------------------------

private
#push-options "--z3rlimit 50 --fuel 2 --ifuel 0"
let rec rewrite_roots_mem_inv (roots: seq U64.t) (fwd: forwarding_map) (y: U64.t)
  : Lemma (requires Seq.mem y (rewrite_roots roots fwd))
          (ensures exists (x: U64.t). Seq.mem x roots /\ rewrite_root x fwd == y)
          (decreases Seq.length roots)
  = if Seq.length roots = 0 then ()
    else begin
      let hd = Seq.head roots in
      let tl = Seq.tail roots in
      if rewrite_root hd fwd = y then ()
      else begin
        assert (rewrite_roots roots fwd == Seq.cons (rewrite_root hd fwd) (rewrite_roots tl fwd));
        FStar.Seq.Properties.mem_cons (rewrite_root hd fwd) (rewrite_roots tl fwd);
        assert (Seq.mem y (rewrite_roots tl fwd));
        rewrite_roots_mem_inv tl fwd y
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: graph_edge → points_to (for mc_edge_target_nonblue)
/// ---------------------------------------------------------------------------

private
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let graph_edge_implies_points_to (g: heap) (src dst: obj_addr)
  : Lemma
    (requires
      well_formed_heap g /\
      graph_wf (create_graph g) /\
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
    GC.Spec.Fields.wf_object_bound g src;
    hd_address_spec src;
    wosize_of_object_bound src g;
    assert (U64.v wz < pow2 54);
    FStar.Math.Lemmas.pow2_lt_compat 61 54;
    assert (U64.v k < pow2 61);
    Helpers.field_addr_arithmetic (U64.v src) (U64.v k) (U64.v (wosize_of_object src g));
    HeapGraph.get_field_addr_eq g src j;
    let far = U64.add_mod src (U64.mul_mod k mword) in
    assert (GC.Spec.Fields.is_pointer_to (dst <: U64.t) dst);
    GC.Spec.Fields.field_read_implies_exists_pointing g src wz k dst
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: mc edge target is non-blue
/// ---------------------------------------------------------------------------

private
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let mc_edge_target_nonblue
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src dst: obj_addr)
  : Lemma
    (requires minor_collect_iso_preconditions minor major fp roots /\
             (let res = cheney_collect_spec minor major fp roots in
              let g_mc = create_graph res.mc_major in
              Seq.mem src (objects zero_addr res.mc_major) /\
              Seq.mem dst (objects zero_addr res.mc_major) /\
              ~(is_blue src res.mc_major) /\
              Seq.mem ((src <: hp_addr), (dst <: hp_addr)) g_mc.edges))
    (ensures (let res = cheney_collect_spec minor major fp roots in
              ~(is_blue dst res.mc_major)))
  = let res = cheney_collect_spec minor major fp roots in
    let mc = res.mc_major in
    Helpers.mc_edge_source_not_no_scan minor major fp roots src dst;
    graph_edge_implies_points_to mc src dst;
    ()
#pop-options

/// ---------------------------------------------------------------------------
/// Strong edge backward: target in pre-existing major
/// ---------------------------------------------------------------------------

private
#restart-solver
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
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
      assert (Seq.mem (s <: obj_addr) (objects zero_addr major));
      CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
      assert (Seq.mem (s <: obj_addr) (objects zero_addr mc));
      CheneyDisj.cheney_promote_fwd_disjoint_nonblue minor major fp roots;
      Helpers.mc_edge_source_not_no_scan minor major fp roots (s <: obj_addr) dst;
      HeaderPres.minor_collect_preserves_wosize minor major fp roots (s <: obj_addr);
      HeaderPres.minor_collect_preserves_is_no_scan minor major fp roots (s <: obj_addr);
      objects_is_vertex_set mc;
      GC.Spec.Fields.wf_object_bound mc (s <: obj_addr);
      HeapGraph.object_fits_from_bound (s <: obj_addr) mc;
      HeapGraph.graph_edge_has_field_index mc (objects zero_addr mc) (s <: obj_addr) dst;
      let j = FStar.IndefiniteDescription.indefinite_description_ghost
        (j:U64.t{U64.v j >= 1})
        (fun j -> U64.v j <= U64.v (wosize_of_object (s <: obj_addr) mc) /\
                  HeapGraph.get_field mc (s <: obj_addr) j == dst /\
                  HeapGraph.is_pointer_field dst) in
      let i : nat = U64.v j - 1 in
      assert (U64.v j <= U64.v (wosize_of_object (s <: obj_addr) major));
      GC.Spec.Fields.wf_object_bound mc (s <: obj_addr);
      Helpers.field_addr_arithmetic (U64.v s) i (U64.v (wosize_of_object (s <: obj_addr) mc));
      wosize_of_object_bound (s <: obj_addr) mc;
      hd_address_spec (s <: obj_addr);
      HeapGraph.get_field_addr_eq mc (s <: obj_addr) j;
      Helpers.derive_mc_major_field_value minor major fp roots (s <: obj_addr) i;
      let field_addr : hp_addr = U64.uint_to_t (U64.v s + i * 8) in
      let old_val = read_word major field_addr in
      let mc_val = read_word mc field_addr in
      assert (mc_val == dst);
      assert (old_val == dst);
      GC.Spec.Fields.wf_object_bound major (s <: obj_addr);
      HeapGraph.object_fits_from_bound (s <: obj_addr) major;
      wosize_of_object_bound (s <: obj_addr) major;
      hd_address_spec (s <: obj_addr);
      HeapGraph.get_field_addr_eq major (s <: obj_addr) j;
      objects_is_vertex_set major;
      HeapGraph.pointer_field_is_graph_edge major (objects zero_addr major) (s <: obj_addr) j;
      MajorBridge.heapgraph_edge_implies_combined minor major (s <: obj_addr) (dst <: obj_addr)
    | MinorV s ->
      Helpers.reachable_minor_gives_fwd_nonzero minor major fp roots s;
      let fwd_s : obj_addr = fwd s in
      CheneyDisch.cheney_fwd_targets_in_mc_major minor major fp roots;
      assert (Seq.mem fwd_s (objects zero_addr mc));
      CheneyDisj.cheney_promote_fwd_disjoint_nonblue minor major fp roots;
      CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
      Helpers.mc_edge_source_not_no_scan minor major fp roots fwd_s dst;
      objects_is_vertex_set mc;
      GC.Spec.Fields.wf_object_bound mc fwd_s;
      HeapGraph.object_fits_from_bound fwd_s mc;
      HeapGraph.graph_edge_has_field_index mc (objects zero_addr mc) fwd_s dst;
      let j = FStar.IndefiniteDescription.indefinite_description_ghost
        (j:U64.t{U64.v j >= 1})
        (fun j -> U64.v j <= U64.v (wosize_of_object fwd_s mc) /\
                  HeapGraph.get_field mc fwd_s j == dst /\
                  HeapGraph.is_pointer_field dst) in
      let i : nat = U64.v j - 1 in
      assert (i < minor_wosize minor s);
      GC.Spec.Fields.wf_object_bound mc fwd_s;
      Helpers.field_addr_arithmetic (U64.v fwd_s) i (U64.v (wosize_of_object fwd_s mc));
      wosize_of_object_bound fwd_s mc;
      hd_address_spec fwd_s;
      HeapGraph.get_field_addr_eq mc fwd_s j;
      let field_addr_v = U64.v fwd_s + i * 8 in
      assert (read_word mc (U64.uint_to_t field_addr_v) == dst);
      Helpers.field_correspondence_instance minor major mc fwd roots s i;
      let minor_val = minor_read_field minor s i in
      assert (minor_val == dst);
      MajorBridge.major_object_not_minor_pointer major (dst <: obj_addr);
      classify_minor_field_major minor major dst;
      minor_field_edge_intro minor major s i (MajorV dst)
#pop-options

/// ---------------------------------------------------------------------------
/// Strong edge backward: target is a forwarding target
/// ---------------------------------------------------------------------------

private
#restart-solver
#push-options "--z3rlimit 80 --fuel 1 --ifuel 1 --split_queries always"
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
      // --- Establish context ---
      RBridge.reachable_major_valid_nonblue minor major roots;
      CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
      CheneyDisj.cheney_promote_fwd_disjoint_nonblue minor major fp roots;
      CheneyInj.cheney_promote_fwd_injective minor major fp roots;
      // --- Extract field index from mc edge ---
      Helpers.mc_edge_source_not_no_scan minor major fp roots (s <: obj_addr) fwd_a;
      HeaderPres.minor_collect_preserves_wosize minor major fp roots (s <: obj_addr);
      HeaderPres.minor_collect_preserves_is_no_scan minor major fp roots (s <: obj_addr);
      objects_is_vertex_set mc;
      GC.Spec.Fields.wf_object_bound mc (s <: obj_addr);
      HeapGraph.object_fits_from_bound (s <: obj_addr) mc;
      HeapGraph.graph_edge_has_field_index mc (objects zero_addr mc) (s <: obj_addr) fwd_a;
      let j = FStar.IndefiniteDescription.indefinite_description_ghost
        (j:U64.t{U64.v j >= 1})
        (fun j -> U64.v j <= U64.v (wosize_of_object (s <: obj_addr) mc) /\
                  HeapGraph.get_field mc (s <: obj_addr) j == fwd_a /\
                  HeapGraph.is_pointer_field fwd_a) in
      let i : nat = U64.v j - 1 in
      assert (U64.v j <= U64.v (wosize_of_object (s <: obj_addr) major));
      // --- Bridge get_field to read_word ---
      GC.Spec.Fields.wf_object_bound mc (s <: obj_addr);
      Helpers.field_addr_arithmetic (U64.v s) i (U64.v (wosize_of_object (s <: obj_addr) mc));
      hd_address_spec (s <: obj_addr);
      wosize_of_object_bound (s <: obj_addr) mc;
      HeapGraph.get_field_addr_eq mc (s <: obj_addr) j;
      // --- Derive field relationship ---
      Helpers.derive_mc_major_field_value minor major fp roots (s <: obj_addr) i;
      let field_addr : hp_addr = U64.uint_to_t (U64.v s + i * 8) in
      let old_val = read_word major field_addr in
      let mc_val = read_word mc field_addr in
      assert (mc_val == fwd_a);
      // --- Blue elimination: fwd(a) was blue → field can't equal it directly ---
      assert (is_blue (fwd_a <: obj_addr) major);
      Helpers.major_field_not_equal_blue major (s <: obj_addr) i (fwd_a <: obj_addr);
      // Not-rewritable case impossible (old_val ≠ fwd_a), so rewritable case holds:
      assert (is_minor_pointer old_val /\ fwd old_val <> 0UL);
      // fwd(old_val) == mc_val == fwd_a == fwd(a). By injectivity: old_val == a
      assert (old_val == (a <: U64.t));
      // --- Construct combined edge ---
      GC.Gen.MinorHeap.minor_objects_valid minor (a <: U64.t);
      classify_major_field_is_minor minor major (a <: U64.t);
      major_field_edge_intro minor major (s <: obj_addr) i (MinorV a)
    | MinorV s ->
      // --- Establish context ---
      Helpers.reachable_minor_gives_fwd_nonzero minor major fp roots s;
      let fwd_s : obj_addr = fwd s in
      CheneyDisch.cheney_fwd_targets_in_mc_major minor major fp roots;
      CheneyInj.cheney_promote_fwd_injective minor major fp roots;
      // --- Extract field index from mc edge ---
      objects_is_vertex_set mc;
      Helpers.mc_edge_source_not_no_scan minor major fp roots fwd_s fwd_a;
      GC.Spec.Fields.wf_object_bound mc fwd_s;
      HeapGraph.object_fits_from_bound fwd_s mc;
      HeapGraph.graph_edge_has_field_index mc (objects zero_addr mc) fwd_s fwd_a;
      let j = FStar.IndefiniteDescription.indefinite_description_ghost
        (j:U64.t{U64.v j >= 1})
        (fun j -> U64.v j <= U64.v (wosize_of_object fwd_s mc) /\
                  HeapGraph.get_field mc fwd_s j == fwd_a /\
                  HeapGraph.is_pointer_field fwd_a) in
      let i : nat = U64.v j - 1 in
      assert (i < minor_wosize minor s);
      // --- Bridge get_field to read_word ---
      GC.Spec.Fields.wf_object_bound mc fwd_s;
      hd_address_spec fwd_s;
      wosize_of_object_bound fwd_s mc;
      Helpers.field_addr_arithmetic (U64.v fwd_s) i (U64.v (wosize_of_object fwd_s mc));
      HeapGraph.get_field_addr_eq mc fwd_s j;
      let field_addr_v = U64.v fwd_s + i * 8 in
      assert (read_word mc (U64.uint_to_t field_addr_v) == fwd_a);
      // --- Use field_correspondence (cheap) instead of promoted_field_through_minor_collect ---
      Helpers.field_correspondence_instance minor major mc fwd roots s i;
      let minor_val = minor_read_field minor s i in
      // field_correspondence gives: fwd(minor_val) == mc_val == fwd_a == fwd(a)
      // By injectivity: minor_val == a
      assert (minor_val == (a <: U64.t));
      // --- Construct combined edge ---
      GC.Gen.MinorHeap.minor_objects_valid minor (a <: U64.t);
      GC.Gen.Base.is_minor_addr_intro (a <: U64.t);
      classify_minor_field_minor minor major (a <: U64.t);
      minor_field_edge_intro minor major s i (MinorV a)
#pop-options

/// ---------------------------------------------------------------------------
/// Main surjectivity recursive proof
/// ---------------------------------------------------------------------------

private
#restart-solver
#push-options "--z3rlimit 300 --fuel 1 --ifuel 1 --split_queries always"
let rec prove_surjectivity_aux
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (root: vertex_id{mem_graph_vertex (create_graph (cheney_collect_spec minor major fp roots).mc_major) root /\
                   U64.v root >= U64.v mword})
  (v: vertex_id{mem_graph_vertex (create_graph (cheney_collect_spec minor major fp roots).mc_major) v /\
                U64.v v >= U64.v mword})
  (r: reach (create_graph (cheney_collect_spec minor major fp roots).mc_major) root v)
  : Lemma
    (requires minor_collect_iso_preconditions minor major fp roots /\
             (let res = cheney_collect_spec minor major fp roots in
              let mc_roots = res.mc_roots in
              Seq.mem (root <: U64.t) mc_roots /\
              ~(is_blue (root <: obj_addr) res.mc_major)))
    (ensures (let prom = cheney_promote minor major fp roots in
              let fwd = prom.fwd_map in
              let cg = build_combined_graph minor major in
              let combined_roots = pre_gc_roots roots in
              let res = cheney_collect_spec minor major fp roots in
              (exists (cv: combined_vertex).
                combined_reachable cg combined_roots cv /\
                Iso.fwd_morphism fwd cv == (v <: U64.t)) /\
              ~(is_blue (v <: obj_addr) res.mc_major)))
    (decreases r)
  = let prom = cheney_promote minor major fp roots in
    let fwd = prom.fwd_map in
    let cg = build_combined_graph minor major in
    let combined_roots = pre_gc_roots roots in
    let res = cheney_collect_spec minor major fp roots in
    let mc = res.mc_major in
    let g_mc = create_graph mc in
    let live_set = live_set_of minor major roots in
    match r with
    | ReachRefl _ ->
      rewrite_roots_mem_inv roots fwd (root <: U64.t);
      let x = FStar.IndefiniteDescription.indefinite_description_ghost U64.t
        (fun x -> Seq.mem x roots /\ rewrite_root x fwd == (root <: U64.t)) in
      // From mc_roots_valid: root ∈ mc_roots → root ∈ objects(mc) ∧ ~is_blue
      let mc_roots = res.mc_roots in
      if is_minor_pointer x && fwd x <> 0UL then begin
        classify_roots_minor_mem roots x;
        Reach.minor_reachable_subset minor (Seq.append roots (minor_roots_from_major major));
        minor_vertex_char minor major x;
        combined_reachable_root cg combined_roots (MinorV x)
      end else begin
        // rewrite_root x fwd = x = root in else branch. Pre-image = MajorV root
        // First establish root ∈ objects(mc) from mem_graph_vertex
        graph_vertices_mem mc (root <: obj_addr);
        // root ∈ objects(zero_addr, mc) → ~(is_minor_pointer root)
        Helpers.major_object_not_minor mc (root <: obj_addr);
        // x = root (from rewrite_root semantics in else branch), so ~(is_minor_pointer x)
        classify_roots_major_mem roots x;
        major_vertex_char minor major (root <: obj_addr);
        combined_reachable_root cg combined_roots (MajorV (root <: U64.t))
      end
    | ReachTrans _ mid _ r_to_mid ->
      // From ReachTrans pattern: mem_graph_vertex g_mc mid and mem_graph_edge g_mc mid v
      assert (mem_graph_vertex g_mc mid);
      assert (mem_graph_vertex g_mc v);
      // Establish mid >= mword for obj_addr coercions and recursive call
      Helpers.graph_vertex_ge_mword mc mid;
      prove_surjectivity_aux minor major fp roots root mid r_to_mid;
      let cv_mid = FStar.IndefiniteDescription.indefinite_description_ghost combined_vertex
        (fun cv -> combined_reachable cg combined_roots cv /\
                   Iso.fwd_morphism fwd cv == (mid <: U64.t)) in
      graph_vertices_mem mc (mid <: obj_addr);
      graph_vertices_mem mc (v <: obj_addr);
      mc_edge_target_nonblue minor major fp roots (mid <: obj_addr) (v <: obj_addr);
      if FStar.IndefiniteDescription.strong_excluded_middle
          (Seq.mem (v <: obj_addr) (objects zero_addr major) /\ ~(is_blue (v <: obj_addr) major))
      then begin
        CheneyDisch.cheney_fwd_targets_in_mc_major minor major fp roots;
        strong_edge_backward_to_major minor major fp roots cv_mid (v <: U64.t);
        combined_reachable_step cg combined_roots cv_mid (MajorV (v <: U64.t))
      end else begin
        let a = FStar.IndefiniteDescription.indefinite_description_ghost U64.t
          (fun a -> Seq.mem a live_set /\ fwd a == (v <: U64.t)) in
        Reach.minor_reachable_subset minor (Seq.append roots (minor_roots_from_major major));
        CheneyDisch.cheney_fwd_targets_in_mc_major minor major fp roots;
        strong_edge_backward_to_minor minor major fp roots cv_mid a;
        combined_reachable_step cg combined_roots cv_mid (MinorV a)
      end
#pop-options

/// ---------------------------------------------------------------------------
/// Universal quantifier lift
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let prove_surjectivity
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
      forall (v: U64.t) (root: U64.t).
        Seq.mem root mc_roots /\
        U64.v root >= U64.v mword /\ U64.v root < heap_size /\ U64.v root % U64.v mword == 0 /\
        Seq.mem (root <: hp_addr) g_mc.vertices /\
        U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
        Seq.mem (v <: hp_addr) g_mc.vertices /\
        reachable g_mc (root <: hp_addr) (v <: hp_addr) ==>
        (exists (cv: combined_vertex).
          combined_reachable cg combined_roots cv /\
          Iso.fwd_morphism fwd cv == v)))
  = let res = cheney_collect_spec minor major fp roots in
    let mc = res.mc_major in
    let g_mc = create_graph mc in
    let mc_roots = res.mc_roots in
    let prom = cheney_promote minor major fp roots in
    let fwd = prom.fwd_map in
    let cg = build_combined_graph minor major in
    let combined_roots = pre_gc_roots roots in
    let aux (v root: U64.t) : Lemma
      (requires
        Seq.mem root mc_roots /\
        U64.v root >= U64.v mword /\ U64.v root < heap_size /\ U64.v root % U64.v mword == 0 /\
        Seq.mem (root <: hp_addr) g_mc.vertices /\
        U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
        Seq.mem (v <: hp_addr) g_mc.vertices /\
        reachable g_mc (root <: hp_addr) (v <: hp_addr))
      (ensures (exists (cv: combined_vertex).
          combined_reachable cg combined_roots cv /\
          Iso.fwd_morphism fwd cv == v))
    = graph_vertices_mem mc (root <: obj_addr);
      let reach_wit = FStar.IndefiniteDescription.indefinite_description_ghost
        (reach g_mc (root <: hp_addr) (v <: hp_addr))
        (fun _ -> True) in
      prove_surjectivity_aux minor major fp roots (root <: hp_addr) (v <: hp_addr) reach_wit
    in
    let lift (v root: U64.t) : Lemma
      (Seq.mem root mc_roots /\
       U64.v root >= U64.v mword /\ U64.v root < heap_size /\ U64.v root % U64.v mword == 0 /\
       Seq.mem (root <: hp_addr) g_mc.vertices /\
       U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
       Seq.mem (v <: hp_addr) g_mc.vertices /\
       reachable g_mc (root <: hp_addr) (v <: hp_addr) ==>
       (exists (cv: combined_vertex).
         combined_reachable cg combined_roots cv /\
         Iso.fwd_morphism fwd cv == v))
    = FStar.Classical.move_requires (aux v) root
    in
    FStar.Classical.forall_intro_2 lift
#pop-options
