/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectIso — Implementation
/// ---------------------------------------------------------------------------
///
/// Proves the minor_collect_iso_theorem by assembling internal lemmas.
/// ZERO admits — all conjuncts fully machine-checked.

module GC.Gen.MinorCollectIso

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
module CheneyBFS = GC.Gen.CheneyBFS
module CheneyInj = GC.Gen.CheneyInjectivity
module CheneyDisj = GC.Gen.CheneyDisjoint
module Reach = GC.Gen.Reachability
module CheneyCorr = GC.Gen.CheneyCorrectness
module RBridge = GC.Gen.ReachabilityBridge
module CheneyDisch = GC.Gen.CheneyDischarge
module HeapGraph = GC.Spec.HeapGraph
module PromUpdate = GC.Gen.PromoteUpdate
module Mark = GC.Spec.Mark
module HeaderPres = GC.Gen.MinorCollectIso.HeaderPres
module EdgeBridge = GC.Gen.CombinedGraph.EdgeBridge
module MajorBridge = GC.Gen.CombinedGraph.MajorBridge
module EdgePres = GC.Gen.CombinedGraph.EdgePreservation

/// ---------------------------------------------------------------------------
/// (A) Injectivity
/// ---------------------------------------------------------------------------
///
/// fwd_morphism is injective on combined-reachable vertices.
/// Proof: case split on vertex pairs:
///   MinorV a, MinorV b: fwd(a) == fwd(b) → a == b (CheneyInjectivity)
///   MajorV a, MajorV b: identity → trivial
///   MinorV a, MajorV b: fwd(a) == b impossible (CheneyDisjoint: fwd targets ∉ non-blue major)

private
#push-options "--z3rlimit 50 --fuel 0 --ifuel 1 --split_queries always"
let prove_injectivity
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires minor_collect_iso_preconditions minor major fp roots)
    (ensures (
      let combined_roots = pre_gc_roots roots in
      let cg = build_combined_graph minor major in
      let prom = cheney_promote minor major fp roots in
      let fwd = prom.fwd_map in
      forall (u v: combined_vertex).
        combined_reachable cg combined_roots u /\
        combined_reachable cg combined_roots v /\
        Iso.fwd_morphism fwd u == Iso.fwd_morphism fwd v ==> u == v))
  = CheneyInj.cheney_promote_fwd_injective minor major fp roots;
    CheneyDisj.cheney_promote_fwd_disjoint_nonblue minor major fp roots;
    RBridge.reachability_bridge minor major roots;
    RBridge.reachable_major_valid_nonblue minor major roots;
    CheneyCorr.cheney_promotes_all_reachable minor major fp roots;
    // Bridge: live_set_of = minor_reachable(append roots remembered) ⊆ minor_reachable roots
    // Use monotonicity: remembered ⊆ roots → append roots remembered ⊆ roots
    let remembered = minor_roots_from_major major in
    let live_set = live_set_of minor major roots in
    // Establish append membership: mem r (append roots remembered) ==> mem r roots \/ mem r remembered
    FStar.Seq.Properties.lemma_mem_append roots remembered;
    // Now SMT knows: forall r. mem r (append roots remembered) <==> mem r roots \/ mem r remembered
    // Combined with precondition (forall m. mem m remembered ==> mem m roots):
    //   forall r. mem r (append roots remembered) ==> mem r roots
    let aux (v: U64.t) : Lemma
      (requires Seq.mem v live_set)
      (ensures Seq.mem v (Reach.minor_reachable minor roots))
    = Reach.minor_reachable_mono minor (Seq.append roots remembered) roots v
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// (B) Image validity
/// ---------------------------------------------------------------------------
///
/// Combined-reachable vertices map to valid mc_major vertices.
///   MinorV v: ReachabilityBridge → v ∈ live_set → fwd(v) ≠ 0
///             → cheney_fwd_targets_in_mc_major → fwd(v) valid in mc_major
///   MajorV v: reachable_major_valid_nonblue → v ∈ objects major
///             → cheney_collect_preserves_objects → v ∈ objects mc_major

private
#push-options "--z3rlimit 100"
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
    // Step 1: combined_reachable(MinorV a) → a ∈ live_set
    RBridge.reachability_bridge minor major roots;
    assert (Seq.mem a (live_set_of minor major roots));
    // Step 2: live_set → minor_reachable roots (monotonicity)
    let remembered = minor_roots_from_major major in
    FStar.Seq.Properties.lemma_mem_append roots remembered;
    Reach.minor_reachable_mono minor (Seq.append roots remembered) roots a;
    assert (Seq.mem a (Reach.minor_reachable minor roots));
    // Step 3: wosize > 0 (from precondition on live_set)
    assert (minor_wosize minor a > 0);
    // Step 4: minor_reachable ∧ wosize > 0 → fwd ≠ 0
    CheneyCorr.cheney_promotes_all_reachable minor major fp roots;
    assert (fwd a <> 0UL);
    // Step 5: fwd ≠ 0 → fwd valid in mc_major (objects)
    CheneyDisch.cheney_fwd_targets_in_mc_major minor major fp roots;
    assert (Seq.mem ((fwd a) <: obj_addr) (objects zero_addr res.mc_major));
    // Step 6: bridge objects → create_graph vertices
    graph_vertices_mem res.mc_major (fwd a <: obj_addr)
#pop-options

private
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
    // reachable_major_valid_nonblue → a aligned, in objects major
    RBridge.reachable_major_valid_nonblue minor major roots;
    // preserves_objects → a ∈ objects mc_major
    CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
    // bridge objects → create_graph vertices
    graph_vertices_mem res.mc_major (a <: obj_addr)
#pop-options

private
#push-options "--z3rlimit 50"
let prove_image_validity
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
      forall (v: combined_vertex).
        combined_reachable cg combined_roots v ==>
        (let w = Iso.fwd_morphism fwd v in
         U64.v w >= U64.v mword /\ U64.v w < heap_size /\ U64.v w % U64.v mword == 0 /\
         Seq.mem (w <: hp_addr) g_mc.vertices)))
  = let aux (v: combined_vertex) : Lemma
      (requires (let cg = build_combined_graph minor major in
                 let combined_roots = pre_gc_roots roots in
                 combined_reachable cg combined_roots v))
      (ensures (let prom = cheney_promote minor major fp roots in
                let fwd = prom.fwd_map in
                let res = cheney_collect_spec minor major fp roots in
                let g_mc = create_graph res.mc_major in
                let w = Iso.fwd_morphism fwd v in
                U64.v w >= U64.v mword /\ U64.v w < heap_size /\ U64.v w % U64.v mword == 0 /\
                Seq.mem (w <: hp_addr) g_mc.vertices))
    = match v with
      | MinorV a -> prove_image_validity_minor minor major fp roots a
      | MajorV a -> prove_image_validity_major minor major fp roots a
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// (E) Header/wosize preservation
/// ---------------------------------------------------------------------------
///
/// All pre-existing non-blue major objects retain their exact wosize through
/// the full cheney_collect_spec (cheney_promote + update_major_pointers).

private
let prove_header_preservation
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires minor_collect_iso_preconditions minor major fp roots)
    (ensures (
      let res = cheney_collect_spec minor major fp roots in
      forall (obj: obj_addr).
        Seq.mem obj (objects zero_addr major) /\
        ~(is_blue obj major) /\
        U64.v (wosize_of_object obj major) >= 1 ==>
        wosize_of_object obj res.mc_major == wosize_of_object obj major))
  = let f (obj: obj_addr) : Lemma
      (requires Seq.mem obj (objects zero_addr major) /\
                ~(is_blue obj major) /\
                U64.v (wosize_of_object obj major) >= 1)
      (ensures (let res = cheney_collect_spec minor major fp roots in
                wosize_of_object obj res.mc_major == wosize_of_object obj major))
    = HeaderPres.minor_collect_preserves_wosize minor major fp roots obj
    in
    Classical.forall_intro (Classical.move_requires f)

/// ---------------------------------------------------------------------------
/// (F) Object survival
/// ---------------------------------------------------------------------------
///
/// All pre-existing major objects survive in mc_major.

private
let prove_object_survival
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires minor_collect_iso_preconditions minor major fp roots)
    (ensures (
      let res = cheney_collect_spec minor major fp roots in
      forall (obj: obj_addr).
        Seq.mem obj (objects zero_addr major) ==>
        Seq.mem obj (objects zero_addr res.mc_major)))
  = CheneyCorr.cheney_collect_preserves_objects minor major fp roots

/// ---------------------------------------------------------------------------
/// (C) Edge Forward
/// ---------------------------------------------------------------------------
///
/// Combined edges between reachable vertices are preserved in mc_major.
/// Strategy: For a combined edge (u, v), extract the field index from major_edge_elim
/// (or minor_edge_elim), show the field value is preserved/rewritten through
/// cheney_promote + update_major_pointers, then use pointer_field_is_graph_edge.
///
/// NOTE: The proof uses `cheney_promote_preserves_read_body` (body fields preserved
/// through Cheney BFS for non-blue objects) + `update_major_pointers_field_effect`
/// (field conditionally rewritten in update phase). This avoids EdgeBridge which
/// is tied to the `minor_collect_spec` / `promote_all_spec` formulation.

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
#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
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
#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
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

/// Helper: derive full mc_major field value for Major source
/// After cheney_promote (field unchanged) + update_major_pointers (conditional rewrite)
private
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
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
      // If old_val was a minor pointer that was forwarded → rewritten
      (is_minor_pointer old_val /\ prom.fwd_map old_val <> 0UL ==>
        mc_val == prom.fwd_map old_val) /\
      // Otherwise → preserved
      (~(is_minor_pointer old_val /\ prom.fwd_map old_val <> 0UL) ==>
        mc_val == old_val)))
  = let prom = cheney_promote minor major fp roots in
    let field_addr : hp_addr = U64.uint_to_t (U64.v src + i * 8) in
    // Step 1: field unchanged through cheney_promote
    derive_prom_field_preserved minor major fp roots src i;
    assert (read_word prom.major_final field_addr == read_word major field_addr);
    // Step 2: apply update_major_pointers_field_effect on prom.major_final
    // Need: well_formed_heap_part1 prom.major_final, src ∈ objects prom.major_final, etc.
    GC.Gen.Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
    GC.Gen.Cheney.cheney_promote_preserves_objects minor major fp roots;
    derive_prom_header_preserved minor major fp roots src;
    // Now we have the preconditions for update_major_pointers_field_effect
    PromUpdate.update_major_pointers_field_effect prom.major_final prom.fwd_map src i
#pop-options

/// Case: Major→Major edge forward
/// The combined edge (MajorV src, MajorV dst) means major field at index i holds dst.
/// dst is a major address → ~(is_minor_pointer dst), so mc_major field == dst.
private
#push-options "--z3rlimit 200 --fuel 0 --ifuel 1 --split_queries always"
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
  = // src is valid non-blue major object
    RBridge.reachable_major_valid_nonblue minor major roots;
    // Edge elimination gives field index and ~(is_no_scan src)
    major_edge_elim minor major src (MajorV dst);
    // Get field index (existential)
    let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun i -> i < U64.v (wosize_of_object src major) /\
                ~(is_no_scan src major) /\
                U64.v src + i * 8 + 8 <= heap_size /\
                (U64.v src + i * 8) % 8 == 0 /\
                classify_major_field minor major (read_word major (U64.uint_to_t (U64.v src + i * 8))) == Some (MajorV dst)) in
    // Classification inversion: field value == dst and ~(is_minor_pointer dst)
    classify_major_field_inv_major minor major (read_word major (U64.uint_to_t (U64.v src + i * 8))) dst;
    let field_addr = U64.uint_to_t (U64.v src + i * 8) in
    assert (read_word major field_addr == (dst <: U64.t));
    // dst is major → not a minor pointer
    GC.Gen.CombinedGraph.MajorBridge.major_object_not_minor_pointer major dst;
    assert (~(is_minor_pointer (dst <: U64.t)));
    // Field in mc_major is unchanged (not a minor pointer → not rewritten)
    derive_mc_major_field_value minor major fp roots src i;
    let res = cheney_collect_spec minor major fp roots in
    assert (read_word res.mc_major field_addr == (dst <: U64.t));
    // Convert to graph edge via pointer_field_is_graph_edge
    // Need: src ∈ objects mc_major, object_fits_in_heap, ~is_no_scan, wosize preserved
    CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
    HeaderPres.minor_collect_preserves_wosize minor major fp roots src;
    HeaderPres.minor_collect_preserves_is_no_scan minor major fp roots src;
    // object_fits: from well_formed_heap mc_major (precondition) + src ∈ objects mc_major
    wf_object_bound res.mc_major src;
    HeapGraph.object_fits_from_bound src res.mc_major;
    // Bridge 0-based index i to 1-based index j = i+1 for get_field
    let j = U64.uint_to_t (i + 1) in
    wosize_of_object_bound src res.mc_major;
    EdgeBridge.field_index_bridge res.mc_major src i;
    // dst is a pointer field (from major_object_is_pointer_field)
    EdgePres.major_object_is_pointer_field major dst;
    // Apply pointer_field_is_graph_edge
    objects_is_vertex_set res.mc_major;
    HeapGraph.pointer_field_is_graph_edge res.mc_major (objects zero_addr res.mc_major) src j
#pop-options

/// Case: Major→Minor edge forward
/// The combined edge (MajorV src, MinorV dst) means major field holds dst (minor ptr).
/// After minor_collect, field becomes fwd(dst). So mc_major has edge (src, fwd(dst)).
private
#push-options "--z3rlimit 200 --fuel 0 --ifuel 1 --split_queries always"
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
      // fwd_dst is valid hp_addr and the edge exists
      U64.v fwd_dst >= 0 /\ U64.v fwd_dst < heap_size /\ U64.v fwd_dst % U64.v mword == 0 /\
      Seq.mem ((src <: hp_addr), (fwd_dst <: hp_addr)) g_mc.edges))
  = // src is valid non-blue major object
    RBridge.reachable_major_valid_nonblue minor major roots;
    // Edge elimination gives field index
    major_edge_elim minor major src (MinorV dst);
    let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun i -> i < U64.v (wosize_of_object src major) /\
                ~(is_no_scan src major) /\
                U64.v src + i * 8 + 8 <= heap_size /\
                (U64.v src + i * 8) % 8 == 0 /\
                classify_major_field minor major (read_word major (U64.uint_to_t (U64.v src + i * 8))) == Some (MinorV dst)) in
    // Classification inversion: field value == dst and is_minor_pointer
    classify_major_field_inv_minor minor major (read_word major (U64.uint_to_t (U64.v src + i * 8))) dst;
    let field_addr = U64.uint_to_t (U64.v src + i * 8) in
    assert (read_word major field_addr == dst);
    assert (is_minor_pointer dst);
    // dst is reachable → in live_set → promoted
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
    assert (prom.fwd_map dst <> 0UL);
    // Field in mc_major is fwd(dst) (minor pointer gets rewritten)
    derive_mc_major_field_value minor major fp roots src i;
    let res = cheney_collect_spec minor major fp roots in
    let fwd_dst : U64.t = prom.fwd_map dst in
    assert (read_word res.mc_major field_addr == fwd_dst);
    // fwd(dst) is a valid object in mc_major
    CheneyDisch.cheney_fwd_targets_in_mc_major minor major fp roots;
    assert (Seq.mem (fwd_dst <: obj_addr) (objects zero_addr res.mc_major));
    // Convert to graph edge
    CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
    HeaderPres.minor_collect_preserves_wosize minor major fp roots src;
    HeaderPres.minor_collect_preserves_is_no_scan minor major fp roots src;
    wf_object_bound res.mc_major src;
    HeapGraph.object_fits_from_bound src res.mc_major;
    let j = U64.uint_to_t (i + 1) in
    wosize_of_object_bound src res.mc_major;
    EdgeBridge.field_index_bridge res.mc_major src i;
    // fwd_dst is a pointer field (valid object in mc_major)
    EdgePres.major_object_is_pointer_field res.mc_major (fwd_dst <: obj_addr);
    objects_is_vertex_set res.mc_major;
    HeapGraph.pointer_field_is_graph_edge res.mc_major (objects zero_addr res.mc_major) src j
#pop-options

/// Explicit instantiation of field_correspondence at a specific object and field index.
/// This eliminates the nested universal quantifier that SMT struggles with.
private
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
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

/// Explicit instantiation of promoted_copy_properties at a specific object.
/// Eliminates the universal quantifier that Z3 struggles to instantiate.
private
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
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

/// Helper: case split on dst to establish mc_val == fwd_dst.
/// Takes the field_correspondence conclusion directly (avoids expensive quantifier encoding).
private
#push-options "--z3rlimit 50 --fuel 0 --ifuel 1"
let prove_minor_field_value
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: U64.t) (dst: combined_vertex)
  (i: nat) (minor_val: U64.t) (mc_val: U64.t) (fwd_dst: U64.t)
  (fwd_src: obj_addr) (fwd: forwarding_map)
  (res: minor_collect_result)
  : Lemma
    (requires
      // Field correspondence instance (already instantiated by caller):
      (is_minor_pointer minor_val /\ fwd minor_val <> 0UL ==> mc_val == fwd minor_val) /\
      (~(is_minor_pointer minor_val /\ fwd minor_val <> 0UL) ==> mc_val == minor_val) /\
      // If minor_val is a minor pointer, its forward is nonzero (caller proves from reachability)
      (is_minor_pointer minor_val ==> fwd minor_val <> 0UL) /\
      // Structural facts about this specific edge:
      (let prom = cheney_promote minor major fp roots in
       let cg = build_combined_graph minor major in
       let combined_roots = pre_gc_roots roots in
       fwd == prom.fwd_map /\
       res == cheney_collect_spec minor major fp roots /\
       combined_reachable cg combined_roots (MinorV src) /\
       combined_reachable cg combined_roots dst /\
       mem_ce (MinorV src, dst) cg /\
       classify_minor_field minor major minor_val == Some dst /\
       minor_val == minor_read_field minor src i /\
       Seq.mem src (live_set_of minor major roots) /\
       fwd src <> 0UL /\
       fwd_dst == Iso.fwd_morphism fwd dst))
    (ensures mc_val == fwd_dst)
  = match dst with
    | MinorV d ->
      classify_minor_field_inv_minor minor major minor_val d;
      assert (minor_val == d);
      // minor_objects_valid: mem d (minor_objects minor) → d >= 8
      GC.Gen.MinorHeap.minor_objects_valid minor d;
      assert (is_minor_pointer minor_val);
      assert (fwd d <> 0UL)
    | MajorV d ->
      classify_minor_field_inv_major minor major minor_val d;
      MajorBridge.major_object_not_minor_pointer major d;
      assert (~(is_minor_pointer minor_val))
#pop-options

/// Helper: given mc_val == fwd_dst, build the graph edge.
/// Takes only FLAT preconditions — no universal quantifiers.
/// The caller is responsible for instantiating promoted_copy_properties and
/// calling CheneyDisch/CheneyCorr to establish fwd_dst membership.
private
#restart-solver
#push-options "--z3rlimit 600 --fuel 0 --ifuel 1 --split_queries always"
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
      // From promoted_copy_properties_instance:
      is_no_scan fwd_src res.mc_major = false /\
      U64.v (wosize_of_object fwd_src res.mc_major) >= minor_wosize minor src /\
      // From CheneyDisch/CheneyCorr:
      U64.v fwd_dst >= U64.v mword /\ U64.v fwd_dst < heap_size /\ U64.v fwd_dst % U64.v mword == 0 /\
      Seq.mem (fwd_dst <: obj_addr) (objects zero_addr res.mc_major) /\
      // Structural:
      i < minor_wosize minor src /\
      (let field_addr_v = U64.v fwd_src + i * 8 in
       field_addr_v + 8 <= heap_size /\
       field_addr_v % 8 == 0 /\
       read_word res.mc_major (U64.uint_to_t field_addr_v) == fwd_dst))
    (ensures
      U64.v fwd_src >= 0 /\ U64.v fwd_src < heap_size /\ U64.v fwd_src % U64.v mword == 0 /\
      U64.v fwd_dst >= 0 /\ U64.v fwd_dst < heap_size /\ U64.v fwd_dst % U64.v mword == 0 /\
      Seq.mem ((fwd_src <: hp_addr), (fwd_dst <: hp_addr)) (create_graph res.mc_major).edges)
  = // object_fits_in_heap from well_formed_heap
    wf_object_bound res.mc_major fwd_src;
    HeapGraph.object_fits_from_bound fwd_src res.mc_major;
    // Help Z3 chain the wosize inequality and pow2 54 bound
    GC.Spec.Object.wosize_of_object_bound fwd_src res.mc_major;
    assert (i < U64.v (wosize_of_object fwd_src res.mc_major));
    assert (HeapGraph.object_fits_in_heap fwd_src res.mc_major);
    assert (i + 1 < pow2 54);
    // Bridge field index
    let j = U64.uint_to_t (i + 1) in
    EdgeBridge.field_index_bridge res.mc_major fwd_src i;
    // fwd_dst is a pointer field (valid object in mc_major)
    EdgePres.major_object_is_pointer_field res.mc_major (fwd_dst <: obj_addr);
    objects_is_vertex_set res.mc_major;
    HeapGraph.pointer_field_is_graph_edge res.mc_major (objects zero_addr res.mc_major) fwd_src j
#pop-options

/// Helper: a minor object with an edge in the combined graph must be scannable.
/// Uses minor_no_scan_no_classify: no_scan minor objects can't have classifiable fields,
/// so having classify_minor_field == Some implies tag < 251.
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

/// Combined helper: field value + graph edge.
/// Calls instance lemmas internally and uses Math.Lemmas for alignment.
///
/// Architecture: All arithmetic (alignment, bounds) is done in field_addr_arithmetic
/// which has NO quantifiers in its requires. This function only instantiates
/// quantifiers and passes flat facts around — it does no arithmetic itself.
/// This avoids Z3 quantifier/arithmetic interaction timeouts.

/// Pure arithmetic helper: establishes field_addr alignment and bounds.
/// NO quantifiers in requires — only flat arithmetic preconditions.
/// This separation prevents Z3 quantifier/arithmetic interaction timeouts.
private
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
  = // Alignment: (a + k*8) % 8 == a % 8 == 0
    FStar.Math.Lemmas.modulo_addition_lemma fwd_src_v 8 i;
    // Bound: i < bound → (i+1) <= bound → (i+1)*8 <= bound*8
    FStar.Math.Lemmas.lemma_mult_le_right 8 (i + 1) bound
#pop-options

private
#restart-solver
#push-options "--z3rlimit 200 --fuel 0 --ifuel 1 --split_queries always"
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
       // Caller provides fwd nonzero for dst (avoids quantifier/arithmetic interaction)
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
    // Step 1: establish minor_tag < 251 from edge existence + minor_no_scan_no_classify
    minor_edge_src_scannable minor major src dst i;
    // Step 2: instantiate promoted_copy_properties for src
    promoted_copy_properties_instance minor major fp roots src;
    // Step 3: field_addr bounds via arithmetic helper (no quantifiers in its context)
    wf_object_bound res.mc_major fwd_src;
    let bound = U64.v (wosize_of_object fwd_src res.mc_major) in
    field_addr_arithmetic (U64.v fwd_src) i bound;
    let field_addr_v = U64.v fwd_src + i * 8 in
    let mc_val = read_word res.mc_major (U64.uint_to_t field_addr_v) in
    // Step 4: field_correspondence → mc_val matches fwd_dst
    field_correspondence_instance minor major res.mc_major fwd roots src i;
    // Inline prove_minor_field_value to avoid quantifier timeout on its precondition
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
    // Step 5: fwd_dst membership
    (match dst with
     | MinorV d ->
       CheneyDisch.cheney_fwd_targets_in_mc_major minor major fp roots
     | MajorV d ->
       CheneyCorr.cheney_collect_preserves_objects minor major fp roots);
    // Step 6: build graph edge
    prove_minor_to_graph_edge minor major fp roots src dst i fwd_dst fwd_src fwd res
#pop-options

/// Case: Minor→* edge forward
/// Uses field_correspondence: promoted copy's fields in mc_major match the
/// minor object's fields (with pointer rewriting). The edge in the combined graph
/// says minor field at index i points to dst, so the promoted copy at fwd(src)
/// has field = fwd_morphism(dst) in mc_major.
private
#push-options "--z3rlimit 200 --fuel 0 --ifuel 1 --split_queries always"
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
      // Both endpoints are valid hp_addr
      U64.v fwd_src >= 0 /\ U64.v fwd_src < heap_size /\ U64.v fwd_src % U64.v mword == 0 /\
      U64.v fwd_dst >= 0 /\ U64.v fwd_dst < heap_size /\ U64.v fwd_dst % U64.v mword == 0 /\
      Seq.mem ((fwd_src <: hp_addr), (fwd_dst <: hp_addr)) g_mc.edges))
  = // src is reachable → in live_set → promoted
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
    let fwd = prom.fwd_map in
    let res = cheney_collect_spec minor major fp roots in
    assert (fwd src <> 0UL);
    // fwd(src) valid in mc_major
    CheneyDisch.cheney_fwd_targets_in_mc_major minor major fp roots;
    let fwd_src : obj_addr = fwd src in
    assert (Seq.mem fwd_src (objects zero_addr res.mc_major));
    // Minor edge elimination gives field index + src ∈ minor_objects
    minor_edge_elim minor major src dst;
    let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun i -> i < minor_wosize minor src /\
                classify_minor_field minor major (minor_read_field minor src i) == Some dst) in
    // Establish fwd nonzero for dst (needed by case helper to avoid quantifier timeout)
    assert (match dst with MinorV d -> fwd d <> 0UL | MajorV _ -> true);
    // Delegate to case helper (handles all quantifier instantiation + arithmetic internally)
    prove_edge_forward_minor_case minor major fp roots src dst i fwd res
#pop-options

/// Wrapper: major-major edge forward taking U64.t (avoids obj_addr subtyping in dispatch)
private
#restart-solver
#push-options "--z3rlimit 100 --split_queries always"
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

/// Wrapper: major-minor edge forward taking U64.t
private
#restart-solver
#push-options "--z3rlimit 100 --split_queries always"
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

/// Combined edge forward: universal quantifier lift (nested forall_intro to avoid forall_intro_2 Z3 issue)
private
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
/// (D) Edge Backward
/// ---------------------------------------------------------------------------
///
/// mc_major edges between images of combined-reachable vertices correspond to
/// combined edges. Together with edge forward (C), this gives edge bijectivity.
///
/// Strategy: Given edge (φ(u), φ(v)) in create_graph mc_major:
///   Case MajorV u, MajorV v: field was preserved (dst not a fwd target), so
///     original field = dst → heap graph edge → combined edge via MajorBridge
///   Case MajorV u, MinorV v: field was rewritten (original was blue fwd target,
///     no_pointer_to_blue prevents pointing to it), so original = v → combined edge
///   Case MinorV u, MajorV v: promoted copy field = dst via Case 2 of field_corr
///     (Case 1 impossible: fwd target ≠ non-blue dst), original = v → combined edge
///   Case MinorV u, MinorV v: promoted copy field = fwd(v) via Case 1 of field_corr
///     (Case 2 impossible: minor_no_pointer_to_blue prevents pointing to blue fwd target),
///     by injectivity original minor field = v → combined edge

/// Helper: from reachability of MinorV v, derive v ∈ live_set and fwd(v) ≠ 0
private
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
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
    // live_set membership gives minor_objects membership (from minor_reachable_subset)
    Reach.minor_reachable_subset minor (Seq.append roots remembered)
#pop-options

/// Helper: for src with edge in mc_major, src is not no_scan in mc_major
/// (no_scan objects have empty object_edges, so if (src, dst) is an edge, src is scannable)
private
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"
let mc_edge_source_not_no_scan
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: obj_addr) (dst: hp_addr)
  : Lemma
    (requires minor_collect_iso_preconditions minor major fp roots /\
             (let res = cheney_collect_spec minor major fp roots in
              let g_mc = create_graph res.mc_major in
              Seq.mem src (objects zero_addr res.mc_major) /\
              Seq.mem ((src <: hp_addr), dst) g_mc.edges))
    (ensures (let res = cheney_collect_spec minor major fp roots in
              ~(is_no_scan src res.mc_major)))
  = let res = cheney_collect_spec minor major fp roots in
    let mc = res.mc_major in
    // Edge membership → (src, dst) ∈ all_edges mc objs
    HeapGraph.all_edges_source_membership mc (objects zero_addr mc) src dst;
    // Now: (src, dst) ∈ object_edges mc src
    // object_edges for no_scan objects = Seq.empty (from definition, fuel 1)
    // So if (src, dst) ∈ object_edges mc src, src is not no_scan
    ()
#pop-options

/// Case MajorV→MajorV: field preserved (dst is non-blue, hence not a fwd target)
/// Proof sketch:
///   Edge (src, dst) in mc_major. Both src, dst are non-blue in original.
///   By fwd_map_disjoint_nonblue: dst ≠ fwd(a) for any a.
///   Extract field index j from mc edge. Since mc field = dst ≠ fwd(anything),
///   the field was NOT rewritten. By derive_mc_major_field_value: original field = dst.
///   Then pointer_field_is_graph_edge → edge in original major → combined edge.
private
#restart-solver
#push-options "--z3rlimit 300 --fuel 1 --ifuel 1 --split_queries always"
let prove_edge_backward_major_major
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src dst: U64.t)
  : Lemma
    (requires
      minor_collect_iso_preconditions minor major fp roots /\
      (let cg = build_combined_graph minor major in
       let combined_roots = pre_gc_roots roots in
       let res = cheney_collect_spec minor major fp roots in
       let g_mc = create_graph res.mc_major in
       combined_reachable cg combined_roots (MajorV src) /\
       combined_reachable cg combined_roots (MajorV dst) /\
       U64.v src >= U64.v mword /\ U64.v src < heap_size /\ U64.v src % U64.v mword == 0 /\
       U64.v dst >= U64.v mword /\ U64.v dst < heap_size /\ U64.v dst % U64.v mword == 0 /\
       Seq.mem ((src <: hp_addr), (dst <: hp_addr)) g_mc.edges))
    (ensures mem_ce (MajorV src, MajorV dst) (build_combined_graph minor major))
  = let prom = cheney_promote minor major fp roots in
    let fwd = prom.fwd_map in
    let res = cheney_collect_spec minor major fp roots in
    let mc = res.mc_major in
    // --- Establish context ---
    // src, dst are non-blue objects in original major (from reachability)
    RBridge.reachable_major_valid_nonblue minor major roots;
    // src survives in mc_major (non-blue objects survive)
    CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
    // fwd(a) ≠ any non-blue object (key disjointness fact)
    CheneyDisj.cheney_promote_fwd_disjoint_nonblue minor major fp roots;
    // src not no_scan in mc (since it has outgoing edge)
    mc_edge_source_not_no_scan minor major fp roots (src <: obj_addr) dst;
    // wosize/no_scan preserved for non-blue src
    HeaderPres.minor_collect_preserves_wosize minor major fp roots (src <: obj_addr);
    HeaderPres.minor_collect_preserves_is_no_scan minor major fp roots (src <: obj_addr);
    // --- Extract field index from mc edge ---
    objects_is_vertex_set mc;
    HeapGraph.graph_edge_has_field_index mc (objects zero_addr mc) (src <: obj_addr) dst;
    let j = FStar.IndefiniteDescription.indefinite_description_ghost
      (j:U64.t{U64.v j >= 1})
      (fun j -> U64.v j <= U64.v (wosize_of_object (src <: obj_addr) mc) /\
                HeapGraph.get_field mc (src <: obj_addr) j == dst /\
                HeapGraph.is_pointer_field dst) in
    let i : nat = U64.v j - 1 in
    // --- Bridge get_field to read_word ---
    // wosize(src, mc) == wosize(src, major) (already established above)
    assert (U64.v j <= U64.v (wosize_of_object (src <: obj_addr) major));
    assert (i < U64.v (wosize_of_object (src <: obj_addr) major));
    // Arithmetic: field address in bounds and aligned
    GC.Spec.Fields.wf_object_bound mc (src <: obj_addr);
    field_addr_arithmetic (U64.v src) i (U64.v (wosize_of_object (src <: obj_addr) mc));
    // get_field mc src j == read_word mc (src + i*8) (via get_field_addr_eq)
    HeapGraph.get_field_addr_eq mc (src <: obj_addr) j;
    // --- Use derive_mc_major_field_value ---
    // This gives: if original field was rewritable → mc_val = fwd(original)
    //             otherwise → mc_val = original
    derive_mc_major_field_value minor major fp roots (src <: obj_addr) i;
    let field_addr : hp_addr = U64.uint_to_t (U64.v src + i * 8) in
    let old_val = read_word major field_addr in
    let mc_val = read_word mc field_addr in
    // mc_val = dst (from edge witness + get_field_addr_eq)
    assert (mc_val == dst);
    // If old_val was rewritable: mc_val = fwd(old_val) = dst.
    // But fwd_map_disjoint_nonblue: fwd(a) ≠ non-blue obj, and dst is non-blue. Contradiction!
    // So old_val was NOT rewritable: mc_val = old_val, i.e., old_val = dst.
    assert (old_val == dst);
    // --- Reconstruct edge in original major ---
    // get_field major src j == read_word major (src + i*8) == dst
    GC.Spec.Fields.wf_object_bound major (src <: obj_addr);
    HeapGraph.get_field_addr_eq major (src <: obj_addr) j;
    assert (HeapGraph.get_field major (src <: obj_addr) j == dst);
    // is_pointer_field dst (from mc edge witness)
    assert (HeapGraph.is_pointer_field dst);
    // pointer_field_is_graph_edge → edge (src, dst) in create_graph major
    objects_is_vertex_set major;
    HeapGraph.object_fits_from_bound (src <: obj_addr) major;
    HeapGraph.pointer_field_is_graph_edge major (objects zero_addr major) (src <: obj_addr) j;
    // --- Combined edge via MajorBridge ---
    MajorBridge.heapgraph_edge_implies_combined minor major (src <: obj_addr) (dst <: obj_addr)
#pop-options

/// Case MinorV→MajorV: promoted copy field = dst (Case 2 of field_corr)
/// Proof sketch:
///   Edge (fwd(src), dst) in mc_major. dst is non-blue ≠ fwd(anything).
///   Extract field index j from mc edge of the promoted copy fwd(src).
///   promoted_field_through_minor_collect gives two cases:
///     Case 1: mc_val = fwd(minor_val) = dst. But dst ≠ fwd(anything). Contradiction!
///     Case 2: mc_val = minor_val = dst.
///   Since dst ∈ objects(major) and not minor, classify_minor_field gives MajorV dst.
///   minor_field_edge_intro → combined edge (MinorV src, MajorV dst).
private
#restart-solver
#push-options "--z3rlimit 300 --fuel 1 --ifuel 1 --split_queries always"
let prove_edge_backward_minor_major
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src dst: U64.t)
  : Lemma
    (requires
      minor_collect_iso_preconditions minor major fp roots /\
      (let cg = build_combined_graph minor major in
       let combined_roots = pre_gc_roots roots in
       let prom = cheney_promote minor major fp roots in
       let fwd = prom.fwd_map in
       let res = cheney_collect_spec minor major fp roots in
       let g_mc = create_graph res.mc_major in
       combined_reachable cg combined_roots (MinorV src) /\
       combined_reachable cg combined_roots (MajorV dst) /\
       U64.v (fwd src) >= U64.v mword /\ U64.v (fwd src) < heap_size /\ U64.v (fwd src) % U64.v mword == 0 /\
       U64.v dst >= U64.v mword /\ U64.v dst < heap_size /\ U64.v dst % U64.v mword == 0 /\
       Seq.mem ((fwd src <: hp_addr), (dst <: hp_addr)) g_mc.edges))
    (ensures mem_ce (MinorV src, MajorV dst) (build_combined_graph minor major))
  = let prom = cheney_promote minor major fp roots in
    let fwd = prom.fwd_map in
    let res = cheney_collect_spec minor major fp roots in
    let mc = res.mc_major in
    let fwd_src : obj_addr = fwd src in
    // --- Establish context ---
    reachable_minor_gives_fwd_nonzero minor major fp roots src;
    RBridge.reachable_major_valid_nonblue minor major roots;
    CheneyDisj.cheney_promote_fwd_disjoint_nonblue minor major fp roots;
    CheneyDisch.cheney_fwd_targets_in_mc_major minor major fp roots;
    // --- Extract field index from mc edge ---
    mc_edge_source_not_no_scan minor major fp roots fwd_src dst;
    objects_is_vertex_set mc;
    HeapGraph.graph_edge_has_field_index mc (objects zero_addr mc) fwd_src dst;
    let j = FStar.IndefiniteDescription.indefinite_description_ghost
      (j:U64.t{U64.v j >= 1})
      (fun j -> U64.v j <= U64.v (wosize_of_object fwd_src mc) /\
                HeapGraph.get_field mc fwd_src j == dst /\
                HeapGraph.is_pointer_field dst) in
    let i : nat = U64.v j - 1 in
    // --- Connect to promoted_field_through_minor_collect ---
    // promoted_copy_exact_wosize: wosize_of_object fwd_src mc == minor_wosize minor src
    // So j <= wosize_of_object fwd_src mc = minor_wosize minor src, hence i < minor_wosize
    assert (i < minor_wosize minor src);
    // field_addr bounds
    GC.Spec.Fields.wf_object_bound mc fwd_src;
    field_addr_arithmetic (U64.v fwd_src) i (U64.v (wosize_of_object fwd_src mc));
    // get_field mc fwd_src j == read_word mc (fwd_src + i*8) == dst
    HeapGraph.get_field_addr_eq mc fwd_src j;
    let field_addr_v = U64.v fwd_src + i * 8 in
    assert (read_word mc (U64.uint_to_t field_addr_v) == dst);
    // --- Apply promoted_field_through_minor_collect ---
    EdgePres.promoted_field_through_minor_collect minor major fp roots src i;
    let minor_val = minor_read_field minor src i in
    // promoted_field gives:
    //   Case 1: is_minor_pointer minor_val /\ fwd minor_val <> 0 → mc_val = fwd(minor_val)
    //   Case 2: otherwise → mc_val = minor_val
    // mc_val = dst. If Case 1: fwd(minor_val) = dst.
    // But fwd_map_disjoint_nonblue: dst is non-blue so fwd(a) ≠ dst for all a. Contradiction!
    // So Case 2: minor_val = dst.
    assert (minor_val == dst);
    // --- Construct combined edge ---
    // dst ∈ objects(major), dst not a minor pointer (it's a major obj_addr)
    MajorBridge.major_object_not_minor_pointer major (dst <: obj_addr);
    // classify_minor_field: since dst not minor_pointer and dst in objects(major) → MajorV dst
    // minor_field_edge_intro gives (MinorV src, MajorV dst) in combined graph
    minor_field_edge_intro minor major src i (MajorV dst)
#pop-options

/// Case MajorV→MinorV: field was rewritten from minor ptr to fwd(v)
/// Proof sketch:
///   Edge (src, fwd(dst)) in mc_major. src is non-blue, fwd(dst) was blue originally.
///   no_pointer_to_blue: src couldn't originally point to fwd(dst) (blue).
///   So the field was REWRITTEN: original was minor ptr m, fwd(m) = fwd(dst).
///   By injectivity: m = dst. Original field = dst (a minor pointer).
///   classify_major_field gives MinorV dst → major_field_edge_intro → combined edge.
private
#restart-solver
#push-options "--z3rlimit 300 --fuel 1 --ifuel 1 --split_queries always"
let prove_edge_backward_major_minor
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src dst: U64.t)
  : Lemma
    (requires
      minor_collect_iso_preconditions minor major fp roots /\
      (let cg = build_combined_graph minor major in
       let combined_roots = pre_gc_roots roots in
       let prom = cheney_promote minor major fp roots in
       let fwd = prom.fwd_map in
       let res = cheney_collect_spec minor major fp roots in
       let g_mc = create_graph res.mc_major in
       combined_reachable cg combined_roots (MajorV src) /\
       combined_reachable cg combined_roots (MinorV dst) /\
       U64.v src >= U64.v mword /\ U64.v src < heap_size /\ U64.v src % U64.v mword == 0 /\
       U64.v (fwd dst) >= U64.v mword /\ U64.v (fwd dst) < heap_size /\ U64.v (fwd dst) % U64.v mword == 0 /\
       Seq.mem ((src <: hp_addr), (fwd dst <: hp_addr)) g_mc.edges))
    (ensures mem_ce (MajorV src, MinorV dst) (build_combined_graph minor major))
  = let prom = cheney_promote minor major fp roots in
    let fwd = prom.fwd_map in
    let res = cheney_collect_spec minor major fp roots in
    let mc = res.mc_major in
    let fwd_dst : obj_addr = fwd dst in
    // --- Establish context ---
    RBridge.reachable_major_valid_nonblue minor major roots;
    reachable_minor_gives_fwd_nonzero minor major fp roots dst;
    CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
    CheneyDisj.cheney_promote_fwd_disjoint_nonblue minor major fp roots;
    // src is non-blue, in objects(major), in objects(mc)
    // fwd(dst) was blue in original (from fwd_targets_originally_blue precondition)
    // --- Extract field index from mc edge ---
    mc_edge_source_not_no_scan minor major fp roots (src <: obj_addr) (fwd dst);
    HeaderPres.minor_collect_preserves_wosize minor major fp roots (src <: obj_addr);
    HeaderPres.minor_collect_preserves_is_no_scan minor major fp roots (src <: obj_addr);
    objects_is_vertex_set mc;
    HeapGraph.graph_edge_has_field_index mc (objects zero_addr mc) (src <: obj_addr) (fwd dst <: U64.t);
    let j = FStar.IndefiniteDescription.indefinite_description_ghost
      (j:U64.t{U64.v j >= 1})
      (fun j -> U64.v j <= U64.v (wosize_of_object (src <: obj_addr) mc) /\
                HeapGraph.get_field mc (src <: obj_addr) j == (fwd dst <: U64.t) /\
                HeapGraph.is_pointer_field (fwd dst <: U64.t)) in
    let i : nat = U64.v j - 1 in
    // --- Bridge get_field to read_word ---
    assert (i < U64.v (wosize_of_object (src <: obj_addr) major));
    GC.Spec.Fields.wf_object_bound mc (src <: obj_addr);
    field_addr_arithmetic (U64.v src) i (U64.v (wosize_of_object (src <: obj_addr) mc));
    HeapGraph.get_field_addr_eq mc (src <: obj_addr) j;
    // --- Use derive_mc_major_field_value ---
    derive_mc_major_field_value minor major fp roots (src <: obj_addr) i;
    let field_addr : hp_addr = U64.uint_to_t (U64.v src + i * 8) in
    let old_val = read_word major field_addr in
    let mc_val = read_word mc field_addr in
    assert (mc_val == (fwd dst <: U64.t));
    // From derive_mc_major_field_value:
    //   If old_val NOT rewritable → mc_val = old_val. But mc_val = fwd(dst) which was blue.
    //     no_pointer_to_blue: non-blue src can't point to blue fwd(dst). So old_val ≠ fwd(dst).
    //     This contradicts mc_val = old_val = fwd(dst). Hence old_val IS rewritable.
    //   If old_val IS rewritable → mc_val = fwd(old_val) = fwd(dst).
    //     By injectivity of fwd on live_set: old_val = dst.
    // The original field was dst (a minor pointer).
    CheneyInj.cheney_promote_fwd_injective minor major fp roots;
    assert (old_val == dst);
    // --- Construct combined edge ---
    // dst is in minor_objects (from reachability_bridge)
    RBridge.reachability_bridge minor major roots;
    // classify_major_field ms major (read_word major field_addr) == Some (MinorV dst)
    // Since old_val = dst is a minor pointer in minor_objects(minor)
    major_field_edge_intro minor major (src <: obj_addr) i (MinorV dst)
#pop-options

/// Case MinorV→MinorV: promoted copy field = fwd(v) via Case 1 of field_corr
/// Proof sketch:
///   Edge (fwd(src), fwd(dst)) in mc_major. fwd(dst) was blue in original.
///   Extract field index j. promoted_field_through_minor_collect gives:
///     Case 1: mc_val = fwd(minor_val) = fwd(dst). By injectivity: minor_val = dst.
///     Case 2: mc_val = minor_val = fwd(dst). But fwd(dst) is blue in original major,
///       and minor_no_pointer_to_blue prevents minor fields from pointing to blue major objs.
///       Contradiction! So only Case 1 applies.
///   classify_minor_field gives MinorV dst → minor_field_edge_intro → combined edge.
private
#restart-solver
#push-options "--z3rlimit 300 --fuel 1 --ifuel 1 --split_queries always"
let prove_edge_backward_minor_minor
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src dst: U64.t)
  : Lemma
    (requires
      minor_collect_iso_preconditions minor major fp roots /\
      (let cg = build_combined_graph minor major in
       let combined_roots = pre_gc_roots roots in
       let prom = cheney_promote minor major fp roots in
       let fwd = prom.fwd_map in
       let res = cheney_collect_spec minor major fp roots in
       let g_mc = create_graph res.mc_major in
       combined_reachable cg combined_roots (MinorV src) /\
       combined_reachable cg combined_roots (MinorV dst) /\
       U64.v (fwd src) >= U64.v mword /\ U64.v (fwd src) < heap_size /\ U64.v (fwd src) % U64.v mword == 0 /\
       U64.v (fwd dst) >= U64.v mword /\ U64.v (fwd dst) < heap_size /\ U64.v (fwd dst) % U64.v mword == 0 /\
       Seq.mem ((fwd src <: hp_addr), (fwd dst <: hp_addr)) g_mc.edges))
    (ensures mem_ce (MinorV src, MinorV dst) (build_combined_graph minor major))
  = let prom = cheney_promote minor major fp roots in
    let fwd = prom.fwd_map in
    let res = cheney_collect_spec minor major fp roots in
    let mc = res.mc_major in
    let fwd_src : obj_addr = fwd src in
    let fwd_dst : U64.t = fwd dst in
    // --- Establish context ---
    reachable_minor_gives_fwd_nonzero minor major fp roots src;
    reachable_minor_gives_fwd_nonzero minor major fp roots dst;
    CheneyDisch.cheney_fwd_targets_in_mc_major minor major fp roots;
    CheneyInj.cheney_promote_fwd_injective minor major fp roots;
    // fwd(dst) was blue in original (from fwd_targets_originally_blue precondition)
    // minor_no_pointer_to_blue is part of minor_collect_iso_preconditions
    // --- Extract field index from mc edge ---
    mc_edge_source_not_no_scan minor major fp roots fwd_src fwd_dst;
    objects_is_vertex_set mc;
    HeapGraph.graph_edge_has_field_index mc (objects zero_addr mc) fwd_src fwd_dst;
    let j = FStar.IndefiniteDescription.indefinite_description_ghost
      (j:U64.t{U64.v j >= 1})
      (fun j -> U64.v j <= U64.v (wosize_of_object fwd_src mc) /\
                HeapGraph.get_field mc fwd_src j == fwd_dst /\
                HeapGraph.is_pointer_field fwd_dst) in
    let i : nat = U64.v j - 1 in
    // --- Connect to promoted_field_through_minor_collect ---
    // promoted_copy_exact_wosize gives equality → i < minor_wosize minor src
    assert (i < minor_wosize minor src);
    // field_addr bounds
    GC.Spec.Fields.wf_object_bound mc fwd_src;
    field_addr_arithmetic (U64.v fwd_src) i (U64.v (wosize_of_object fwd_src mc));
    HeapGraph.get_field_addr_eq mc fwd_src j;
    let field_addr_v = U64.v fwd_src + i * 8 in
    assert (read_word mc (U64.uint_to_t field_addr_v) == fwd_dst);
    // --- Apply promoted_field_through_minor_collect ---
    EdgePres.promoted_field_through_minor_collect minor major fp roots src i;
    let minor_val = minor_read_field minor src i in
    // promoted_field gives:
    //   Case 1: is_minor_pointer minor_val /\ fwd minor_val <> 0 → mc_val = fwd(minor_val)
    //   Case 2: otherwise → mc_val = minor_val
    // mc_val = fwd(dst). If Case 2: minor_val = fwd(dst).
    //   But fwd(dst) was blue in original major (from fwd_targets_originally_blue).
    //   minor_no_pointer_to_blue: minor_val can't equal a blue major object.
    //   Contradiction! So Case 1 applies.
    // Case 1: fwd(minor_val) = fwd(dst). By injectivity: minor_val = dst.
    assert (minor_val == dst);
    // --- Construct combined edge ---
    // dst is in minor_objects (from reachable_minor_gives_fwd_nonzero)
    // classify_minor_field for dst: minor object → Some (MinorV dst)
    minor_field_edge_intro minor major src i (MinorV dst)
#pop-options

/// Dispatch: edge backward for all 4 cases
private
#restart-solver
#push-options "--z3rlimit 100 --fuel 0 --ifuel 1"
let prove_edge_backward_case
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (u v: combined_vertex)
  : Lemma
    (requires
      minor_collect_iso_preconditions minor major fp roots /\
      (let cg = build_combined_graph minor major in
       let combined_roots = pre_gc_roots roots in
       let prom = cheney_promote minor major fp roots in
       let fwd = prom.fwd_map in
       let res = cheney_collect_spec minor major fp roots in
       let g_mc = create_graph res.mc_major in
       combined_reachable cg combined_roots u /\
       combined_reachable cg combined_roots v /\
       (let fu = Iso.fwd_morphism fwd u in
        let fv = Iso.fwd_morphism fwd v in
        U64.v fu >= U64.v mword /\ U64.v fu < heap_size /\ U64.v fu % U64.v mword == 0 /\
        U64.v fv >= U64.v mword /\ U64.v fv < heap_size /\ U64.v fv % U64.v mword == 0 /\
        Seq.mem ((fu <: hp_addr), (fv <: hp_addr)) g_mc.edges)))
    (ensures mem_ce (u, v) (build_combined_graph minor major))
  = match u, v with
    | MajorV s, MajorV d -> prove_edge_backward_major_major minor major fp roots s d
    | MinorV s, MajorV d -> prove_edge_backward_minor_major minor major fp roots s d
    | MajorV s, MinorV d -> prove_edge_backward_major_minor minor major fp roots s d
    | MinorV s, MinorV d -> prove_edge_backward_minor_minor minor major fp roots s d
#pop-options

/// Universal quantifier lift for edge backward (same pattern as edge forward)
private
#restart-solver
#push-options "--z3rlimit 50 --fuel 0 --ifuel 1"
let prove_edge_backward
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
        (let fu = Iso.fwd_morphism fwd u in
         let fv = Iso.fwd_morphism fwd v in
         U64.v fu >= U64.v mword /\ U64.v fu < heap_size /\ U64.v fu % U64.v mword == 0 /\
         U64.v fv >= U64.v mword /\ U64.v fv < heap_size /\ U64.v fv % U64.v mword == 0 /\
         Seq.mem ((fu <: hp_addr), (fv <: hp_addr)) g_mc.edges) ==>
        mem_ce (u, v) cg))
  = let aux_inner (u: combined_vertex) (v: combined_vertex) : Lemma
      (requires (let cg = build_combined_graph minor major in
                 let combined_roots = pre_gc_roots roots in
                 let prom = cheney_promote minor major fp roots in
                 let fwd = prom.fwd_map in
                 let res = cheney_collect_spec minor major fp roots in
                 let g_mc = create_graph res.mc_major in
                 combined_reachable cg combined_roots u /\
                 combined_reachable cg combined_roots v /\
                 (let fu = Iso.fwd_morphism fwd u in
                  let fv = Iso.fwd_morphism fwd v in
                  U64.v fu >= U64.v mword /\ U64.v fu < heap_size /\ U64.v fu % U64.v mword == 0 /\
                  U64.v fv >= U64.v mword /\ U64.v fv < heap_size /\ U64.v fv % U64.v mword == 0 /\
                  Seq.mem ((fu <: hp_addr), (fv <: hp_addr)) g_mc.edges)))
      (ensures mem_ce (u, v) (build_combined_graph minor major))
    = prove_edge_backward_case minor major fp roots u v
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
                  (let fu = Iso.fwd_morphism fwd u in
                   let fv = Iso.fwd_morphism fwd v in
                   U64.v fu >= U64.v mword /\ U64.v fu < heap_size /\ U64.v fu % U64.v mword == 0 /\
                   U64.v fv >= U64.v mword /\ U64.v fv < heap_size /\ U64.v fv % U64.v mword == 0 /\
                   Seq.mem ((fu <: hp_addr), (fv <: hp_addr)) g_mc.edges) ==>
                  mem_ce (u, v) cg))
    = Classical.forall_intro (Classical.move_requires (aux_inner u))
    in
    Classical.forall_intro aux_outer
#pop-options

/// ---------------------------------------------------------------------------
/// (G) Forward reachability
/// ---------------------------------------------------------------------------
///
/// Proof by combined_reachable_ind: define predicate p(v) that includes both
/// combined_reachable(v) and mc_major reachability. The base case shows roots
/// map to mc_roots (self-reachable), the step extends reachability via edge_forward.

/// Helper: for a combined root v, show fwd_morphism(v) is in mc_roots
private
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
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
      // classify_roots_inv_minor: a ∈ roots, is_minor_pointer a
      classify_roots_inv_minor roots a;
      // fwd a ≠ 0 (from reachable_minor_gives_fwd_nonzero)
      reachable_minor_gives_fwd_nonzero minor major fp roots a;
      // rewrite_root a fwd = fwd a (since is_minor_pointer a ∧ fwd a ≠ 0)
      assert (rewrite_root a fwd == fwd a);
      // a ∈ roots → ∃i. Seq.index roots i = a → Seq.index mc_roots i = fwd a
      let i = FStar.Seq.Properties.index_mem a roots in
      rewrite_roots_length roots fwd;
      rewrite_roots_index roots fwd i;
      assert (Seq.index mc_roots i == fwd a);
      assert (Seq.mem (fwd a) mc_roots)
    | MajorV a ->
      // classify_roots_inv_major: a ∈ roots, ¬is_minor_pointer a
      classify_roots_inv_major roots a;
      // rewrite_root a fwd = a (since ¬is_minor_pointer a)
      assert (rewrite_root a fwd == a);
      // a ∈ roots → ∃i. Seq.index mc_roots i = a
      let i = FStar.Seq.Properties.index_mem a roots in
      rewrite_roots_length roots fwd;
      rewrite_roots_index roots fwd i;
      assert (Seq.index mc_roots i == a);
      assert (Seq.mem a mc_roots)
#pop-options

/// Main forward reachability proof
private
#restart-solver
#push-options "--z3rlimit 200 --fuel 0 --ifuel 1 --split_queries always"
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
    // The predicate for combined_reachable_ind
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
    // Base case: roots satisfy p
    let base_lemma (v: combined_vertex) : Lemma
      (requires Seq.mem v combined_roots /\ mem_cv v cg)
      (ensures p v)
    = // 1. combined_reachable(v) from root
      combined_reachable_root cg combined_roots v;
      // 2. Image validity: φ(v) aligned and in g_mc.vertices
      (match v with
       | MinorV a -> prove_image_validity_minor minor major fp roots a
       | MajorV a -> prove_image_validity_major minor major fp roots a);
      // 3. φ(v) ∈ mc_roots
      root_morphism_in_mc_roots minor major fp roots v;
      // 4. reach_refl: reachable(g_mc, φ(v), φ(v))
      let w = Iso.fwd_morphism fwd v in
      reach_refl g_mc (w <: hp_addr)
    in
    // Step case: p(u) ∧ edge(u,w) → p(w)
    let step_lemma (u: combined_vertex) (w: combined_vertex) : Lemma
      (requires p u /\ mem_ce (u, w) cg)
      (ensures p w)
    = // 1. combined_reachable(w) from step
      combined_reachable_step cg combined_roots u w;
      // 2. Image validity for w
      (match w with
       | MinorV a -> prove_image_validity_minor minor major fp roots a
       | MajorV a -> prove_image_validity_major minor major fp roots a);
      // 3. Edge forward: (φ(u), φ(w)) is a g_mc edge
      let fu = Iso.fwd_morphism fwd u in
      let fw = Iso.fwd_morphism fwd w in
      (match u, w with
       | MajorV s, MajorV d -> prove_edge_forward_major_major_u minor major fp roots s d
       | MajorV s, MinorV d -> prove_edge_forward_major_minor_u minor major fp roots s d
       | MinorV s, _ -> prove_edge_forward_minor minor major fp roots s w);
      assert (Seq.mem ((fu <: hp_addr), (fw <: hp_addr)) g_mc.edges);
      // 4. edge_reach: reachable(g_mc, φ(u), φ(w))
      edge_reach g_mc (fu <: hp_addr) (fw <: hp_addr);
      // 5. Extract root witness from p(u) and extend via reach_trans
      let r = FStar.IndefiniteDescription.indefinite_description_ghost U64.t
        (fun r -> Seq.mem r mc_roots /\
                  U64.v r >= U64.v mword /\ U64.v r < heap_size /\ U64.v r % U64.v mword == 0 /\
                  Seq.mem (r <: hp_addr) g_mc.vertices /\
                  reachable g_mc (r <: hp_addr) (fu <: hp_addr)) in
      // 6. reach_trans: reachable(g_mc, r, φ(w))
      reach_trans g_mc (r <: hp_addr) (fu <: hp_addr) (fw <: hp_addr)
    in
    // Apply combined_reachable_ind for each v
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
    = // Establish base universal
      Classical.forall_intro (Classical.move_requires base_lemma);
      // Establish step universal
      let step_outer (u': combined_vertex) : Lemma
        (ensures forall (w': combined_vertex). p u' /\ mem_ce (u', w') cg ==> p w')
      = Classical.forall_intro (Classical.move_requires (step_lemma u'))
      in
      Classical.forall_intro step_outer;
      // Apply induction
      combined_reachable_ind cg combined_roots p v
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// (H) Surjectivity
/// ---------------------------------------------------------------------------
///
/// Every vertex reachable in g_mc from mc_roots has a combined-reachable pre-image
/// under fwd_morphism. Proof by structural induction on the reach witness.
///
/// Key ingredients:
///   - mc_edges_nonblue_target: non-blue source + mc edge → non-blue target
///   - mc_major_vertex_partition: non-blue mc_major objects are either pre-existing OR fwd targets
///   - Strong edge backward reasoning: given IH on source, establish combined edge to target
///     Uses direct properties of target instead of combined_reachable(target).

/// Helper: rewrite_roots membership inversion.
/// If y ∈ rewrite_roots roots fwd, then some original root x maps to y.
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
        // y ∈ rewrite_roots roots fwd = cons (rewrite_root hd fwd) (rewrite_roots tl fwd)
        // y ≠ rewrite_root hd fwd → y ∈ rewrite_roots tl fwd
        assert (Seq.mem y (rewrite_roots tl fwd));
        rewrite_roots_mem_inv tl fwd y
        // IH gives ∃x. x ∈ tl ∧ rewrite_root x fwd == y
        // tl ⊆ roots → x ∈ roots
      end
    end
#pop-options

/// Helper: graph edge implies points_to.
/// Bridges from mem_graph_edge to the points_to predicate needed by no_pointer_to_blue.
private
#push-options "--z3rlimit 400 --fuel 2 --ifuel 1"
let graph_edge_implies_points_to (g: heap) (src dst: obj_addr)
  : Lemma
    (requires well_formed_heap g /\
             Seq.mem src (objects zero_addr g) /\
             ~(is_no_scan src g) /\
             Seq.mem ((src <: hp_addr), (dst <: hp_addr)) (create_graph g).edges)
    (ensures GC.Spec.Fields.points_to g src dst)
  = objects_is_vertex_set g;
    HeapGraph.graph_edge_has_field_index g (objects zero_addr g) src (dst <: hp_addr);
    // Gives ∃j. j >= 1, j <= wosize(src), get_field g src j == dst, is_pointer_field dst
    let j = FStar.IndefiniteDescription.indefinite_description_ghost
      (j:U64.t{U64.v j >= 1})
      (fun j -> U64.v j <= U64.v (wosize_of_object src g) /\
                HeapGraph.get_field g src j == (dst <: hp_addr) /\
                HeapGraph.is_pointer_field (dst <: hp_addr)) in
    let k = U64.sub j 1UL in
    let wz = wosize_of_object src g in
    // k is 0-based index < wz
    assert (U64.v k < U64.v wz);
    // well_formed_object g src follows from well_formed_heap + membership
    GC.Spec.Fields.wf_object_bound g src;
    hd_address_spec src;
    // get_field g src j = read_word g (src + k*8)
    HeapGraph.get_field_addr_eq g src j;
    let far = U64.add_mod src (U64.mul_mod k mword) in
    // is_pointer_to (read_word g far) dst:
    // read_word g far == dst (from get_field_addr_eq)
    // is_pointer_to dst dst = is_pointer_field dst (hd_address dst == hd_address dst trivially)
    assert (GC.Spec.Fields.is_pointer_to (dst <: U64.t) dst);
    // field_read_implies_exists_pointing
    GC.Spec.Fields.field_read_implies_exists_pointing g src wz k dst
#pop-options

/// Helper: graph edge target is non-blue when source is non-blue.
/// Uses: edge → points_to → no_pointer_to_blue conclusion.
private
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
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
    // Edge means src has outgoing edge → src is not no_scan
    mc_edge_source_not_no_scan minor major fp roots src (dst <: U64.t);
    // Graph edge → points_to mc src dst
    graph_edge_implies_points_to mc src dst;
    // no_pointer_to_blue mc: non-blue src pointing to dst → dst non-blue
    ()
#pop-options

/// Strong edge backward: target is pre-existing non-blue major object.
/// Like prove_edge_backward_major_major/minor_major but takes direct target properties
/// instead of combined_reachable(MajorV dst).
private
#restart-solver
#push-options "--z3rlimit 300 --fuel 1 --ifuel 1 --split_queries always"
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
      // Edge (s, dst) in mc_major. Both non-blue pre-existing.
      // Exact same logic as prove_edge_backward_major_major but we have
      // dst properties directly instead of via combined_reachable.
      RBridge.reachable_major_valid_nonblue minor major roots;
      CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
      CheneyDisj.cheney_promote_fwd_disjoint_nonblue minor major fp roots;
      mc_edge_source_not_no_scan minor major fp roots (s <: obj_addr) dst;
      HeaderPres.minor_collect_preserves_wosize minor major fp roots (s <: obj_addr);
      HeaderPres.minor_collect_preserves_is_no_scan minor major fp roots (s <: obj_addr);
      objects_is_vertex_set mc;
      HeapGraph.graph_edge_has_field_index mc (objects zero_addr mc) (s <: obj_addr) dst;
      let j = FStar.IndefiniteDescription.indefinite_description_ghost
        (j:U64.t{U64.v j >= 1})
        (fun j -> U64.v j <= U64.v (wosize_of_object (s <: obj_addr) mc) /\
                  HeapGraph.get_field mc (s <: obj_addr) j == dst /\
                  HeapGraph.is_pointer_field dst) in
      let i : nat = U64.v j - 1 in
      assert (U64.v j <= U64.v (wosize_of_object (s <: obj_addr) major));
      GC.Spec.Fields.wf_object_bound mc (s <: obj_addr);
      field_addr_arithmetic (U64.v s) i (U64.v (wosize_of_object (s <: obj_addr) mc));
      HeapGraph.get_field_addr_eq mc (s <: obj_addr) j;
      derive_mc_major_field_value minor major fp roots (s <: obj_addr) i;
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
      // Edge (fwd(s), dst) in mc_major. fwd(s) = mid.
      reachable_minor_gives_fwd_nonzero minor major fp roots s;
      let fwd_s : obj_addr = fwd s in
      CheneyDisch.cheney_fwd_targets_in_mc_major minor major fp roots;
      CheneyDisj.cheney_promote_fwd_disjoint_nonblue minor major fp roots;
      CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
      mc_edge_source_not_no_scan minor major fp roots fwd_s dst;
      objects_is_vertex_set mc;
      HeapGraph.graph_edge_has_field_index mc (objects zero_addr mc) fwd_s dst;
      let j = FStar.IndefiniteDescription.indefinite_description_ghost
        (j:U64.t{U64.v j >= 1})
        (fun j -> U64.v j <= U64.v (wosize_of_object fwd_s mc) /\
                  HeapGraph.get_field mc fwd_s j == dst /\
                  HeapGraph.is_pointer_field dst) in
      let i : nat = U64.v j - 1 in
      assert (i < minor_wosize minor s);
      GC.Spec.Fields.wf_object_bound mc fwd_s;
      field_addr_arithmetic (U64.v fwd_s) i (U64.v (wosize_of_object fwd_s mc));
      HeapGraph.get_field_addr_eq mc fwd_s j;
      let field_addr_v = U64.v fwd_s + i * 8 in
      assert (read_word mc (U64.uint_to_t field_addr_v) == dst);
      EdgePres.promoted_field_through_minor_collect minor major fp roots s i;
      let minor_val = minor_read_field minor s i in
      // Case 1: fwd(minor_val) = dst. But dst is non-blue, and fwd targets are blue in original.
      //         fwd_map_disjoint_nonblue says fwd(a) ≠ non-blue obj. Contradiction!
      // Case 2: minor_val = dst. Since dst ∈ objects(major) and not minor pointer:
      assert (minor_val == dst);
      MajorBridge.major_object_not_minor_pointer major (dst <: obj_addr);
      minor_field_edge_intro minor major s i (MajorV dst)
#pop-options

/// Strong edge backward: target is a forwarding target (promoted copy).
/// Like prove_edge_backward_major_minor/minor_minor but takes direct target properties
/// (a ∈ live_set, fwd a = v, a ∈ minor_objects) instead of combined_reachable(MinorV a).
private
#restart-solver
#push-options "--z3rlimit 300 --fuel 1 --ifuel 1 --split_queries always"
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
      // Edge (s, fwd(a)) in mc_major. s is non-blue, fwd(a) was blue in original.
      RBridge.reachable_major_valid_nonblue minor major roots;
      CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
      CheneyDisj.cheney_promote_fwd_disjoint_nonblue minor major fp roots;
      CheneyInj.cheney_promote_fwd_injective minor major fp roots;
      mc_edge_source_not_no_scan minor major fp roots (s <: obj_addr) fwd_a;
      HeaderPres.minor_collect_preserves_wosize minor major fp roots (s <: obj_addr);
      HeaderPres.minor_collect_preserves_is_no_scan minor major fp roots (s <: obj_addr);
      objects_is_vertex_set mc;
      HeapGraph.graph_edge_has_field_index mc (objects zero_addr mc) (s <: obj_addr) fwd_a;
      let j = FStar.IndefiniteDescription.indefinite_description_ghost
        (j:U64.t{U64.v j >= 1})
        (fun j -> U64.v j <= U64.v (wosize_of_object (s <: obj_addr) mc) /\
                  HeapGraph.get_field mc (s <: obj_addr) j == fwd_a /\
                  HeapGraph.is_pointer_field fwd_a) in
      let i : nat = U64.v j - 1 in
      assert (U64.v j <= U64.v (wosize_of_object (s <: obj_addr) major));
      GC.Spec.Fields.wf_object_bound mc (s <: obj_addr);
      field_addr_arithmetic (U64.v s) i (U64.v (wosize_of_object (s <: obj_addr) mc));
      HeapGraph.get_field_addr_eq mc (s <: obj_addr) j;
      derive_mc_major_field_value minor major fp roots (s <: obj_addr) i;
      let field_addr : hp_addr = U64.uint_to_t (U64.v s + i * 8) in
      let old_val = read_word major field_addr in
      let mc_val = read_word mc field_addr in
      assert (mc_val == fwd_a);
      // fwd(a) was blue in original → no_pointer_to_blue prevents old_val = fwd(a) directly.
      // So field was rewritten: old_val was minor, fwd(old_val) = fwd(a).
      // Injectivity: old_val = a. old_val is a minor pointer to a.
      assert (old_val == (a <: U64.t) \/ (is_minor_pointer old_val /\ fwd old_val == fwd_a));
      // By injectivity fwd(old_val) = fwd(a) → old_val = a
      assert (old_val == (a <: U64.t));
      // old_val = a is a minor pointer. classify_major_field gives MinorV a.
      // major_field_edge_intro → combined edge (MajorV s, MinorV a)
      major_field_edge_intro minor major (s <: obj_addr) i (MinorV a)
    | MinorV s ->
      // Edge (fwd(s), fwd(a)) in mc_major.
      reachable_minor_gives_fwd_nonzero minor major fp roots s;
      let fwd_s : obj_addr = fwd s in
      CheneyDisch.cheney_fwd_targets_in_mc_major minor major fp roots;
      CheneyInj.cheney_promote_fwd_injective minor major fp roots;
      objects_is_vertex_set mc;
      mc_edge_source_not_no_scan minor major fp roots fwd_s fwd_a;
      HeapGraph.graph_edge_has_field_index mc (objects zero_addr mc) fwd_s fwd_a;
      let j = FStar.IndefiniteDescription.indefinite_description_ghost
        (j:U64.t{U64.v j >= 1})
        (fun j -> U64.v j <= U64.v (wosize_of_object fwd_s mc) /\
                  HeapGraph.get_field mc fwd_s j == fwd_a /\
                  HeapGraph.is_pointer_field fwd_a) in
      let i : nat = U64.v j - 1 in
      assert (i < minor_wosize minor s);
      GC.Spec.Fields.wf_object_bound mc fwd_s;
      field_addr_arithmetic (U64.v fwd_s) i (U64.v (wosize_of_object fwd_s mc));
      HeapGraph.get_field_addr_eq mc fwd_s j;
      let field_addr_v = U64.v fwd_s + i * 8 in
      assert (read_word mc (U64.uint_to_t field_addr_v) == fwd_a);
      EdgePres.promoted_field_through_minor_collect minor major fp roots s i;
      let minor_val = minor_read_field minor s i in
      // Case 1: is_minor_pointer minor_val ∧ fwd(minor_val) ≠ 0 → mc_val = fwd(minor_val)
      //   fwd(minor_val) = fwd(a). Injectivity → minor_val = a.
      // Case 2: mc_val = minor_val = fwd(a). But fwd(a) was blue in original.
      //   minor_no_pointer_to_blue says minor can't point to blue major. Contradiction!
      assert (minor_val == (a <: U64.t));
      minor_field_edge_intro minor major s i (MinorV a)
#pop-options

/// Main surjectivity recursive proof.
/// Strengthened IH: the pre-image exists AND the vertex is non-blue in mc_major.
private
#restart-solver
#push-options "--z3rlimit 300 --fuel 1 --ifuel 1 --split_queries always"
let rec prove_surjectivity_aux
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (root: vertex_id{mem_graph_vertex (create_graph (cheney_collect_spec minor major fp roots).mc_major) root})
  (v: vertex_id{mem_graph_vertex (create_graph (cheney_collect_spec minor major fp roots).mc_major) v})
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
      // Base case: v = root ∈ mc_roots. Find the pre-image.
      rewrite_roots_mem_inv roots fwd (root <: U64.t);
      let x = FStar.IndefiniteDescription.indefinite_description_ghost U64.t
        (fun x -> Seq.mem x roots /\ rewrite_root x fwd == (root <: U64.t)) in
      if is_minor_pointer x && fwd x <> 0UL then begin
        // x is a minor pointer with fwd(x) = root. Pre-image = MinorV x
        classify_roots_minor_mem roots x;
        // x ∈ live_set (from fwd_domain_is_live_set since fwd x ≠ 0)
        // live_set ⊆ minor_objects → MinorV x is a valid combined vertex
        Reach.minor_reachable_subset minor (Seq.append roots (minor_roots_from_major major));
        minor_vertex_char minor major x;
        combined_reachable_root cg combined_roots (MinorV x)
      end else begin
        // rewrite_root x fwd = x = root. Pre-image = MajorV root
        classify_roots_major_mem roots x;
        // root ∈ objects(mc_major) and non-blue → from vertex_partition:
        // either pre-existing non-blue (→ in objects(major)) or fwd target.
        // Apply partition: root is non-blue in mc so partition applies
        graph_vertices_mem mc (root <: obj_addr);
        // Since ¬is_minor_pointer x and root is non-blue in mc, partition gives
        // root ∈ objects(major). Use major_vertex_char.
        major_vertex_char minor major (root <: obj_addr);
        combined_reachable_root cg combined_roots (MajorV (root <: U64.t))
      end
    | ReachTrans _ mid _ r_to_mid ->
      // Inductive step: reach root mid, edge (mid, v) in g_mc
      prove_surjectivity_aux minor major fp roots root mid r_to_mid;
      // IH gives pre-image for mid and mid is non-blue
      let cv_mid = FStar.IndefiniteDescription.indefinite_description_ghost combined_vertex
        (fun cv -> combined_reachable cg combined_roots cv /\
                   Iso.fwd_morphism fwd cv == (mid <: U64.t)) in
      // Edge (mid, v) → v is non-blue (via graph_edge_implies_points_to + no_pointer_to_blue)
      graph_vertices_mem mc (mid <: obj_addr);
      graph_vertices_mem mc (v <: obj_addr);
      mc_edge_target_nonblue minor major fp roots (mid <: obj_addr) (v <: obj_addr);
      // v is non-blue → vertex_partition applies: either pre-existing or fwd target
      if FStar.IndefiniteDescription.strong_excluded_middle
          (Seq.mem (v <: obj_addr) (objects zero_addr major) /\ ~(is_blue (v <: obj_addr) major))
      then begin
        // Case A: v is pre-existing non-blue in major → pre-image = MajorV v
        CheneyDisch.cheney_fwd_targets_in_mc_major minor major fp roots;
        strong_edge_backward_to_major minor major fp roots cv_mid (v <: U64.t);
        // Combined edge (cv_mid, MajorV v) established
        combined_reachable_step cg combined_roots cv_mid (MajorV (v <: U64.t))
      end else begin
        // Case B: v is a fwd target. Get a ∈ live_set with fwd(a) = v.
        let a = FStar.IndefiniteDescription.indefinite_description_ghost U64.t
          (fun a -> Seq.mem a live_set /\ fwd a == (v <: U64.t)) in
        // a ∈ live_set → a ∈ minor_objects, fwd(a) ≠ 0
        Reach.minor_reachable_subset minor (Seq.append roots (minor_roots_from_major major));
        CheneyDisch.cheney_fwd_targets_in_mc_major minor major fp roots;
        strong_edge_backward_to_minor minor major fp roots cv_mid a;
        // Combined edge (cv_mid, MinorV a) established
        combined_reachable_step cg combined_roots cv_mid (MinorV a)
      end
#pop-options

/// Universal quantifier lift for surjectivity
private
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
    = // root is non-blue (from mc_roots_valid precondition)
      graph_vertices_mem mc (root <: obj_addr);
      let reach_wit = FStar.IndefiniteDescription.indefinite_description_ghost
        (reach g_mc (root <: hp_addr) (v <: hp_addr))
        (fun _ -> True) in
      prove_surjectivity_aux minor major fp roots (root <: hp_addr) (v <: hp_addr) reach_wit
    in
    FStar.Classical.forall_intro_2 (fun v root ->
      FStar.Classical.move_requires (aux v) root)
#pop-options

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let minor_collect_iso_theorem
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires minor_collect_iso_preconditions minor major fp roots)
    (ensures minor_collect_correctness minor major fp roots)
  = // (A) Injectivity
    prove_injectivity minor major fp roots;
    // (B) Image validity
    prove_image_validity minor major fp roots;
    // (C) Edge forward
    prove_edge_forward minor major fp roots;
    // (D) Edge backward
    prove_edge_backward minor major fp roots;
    // (E) Header/wosize preservation
    prove_header_preservation minor major fp roots;
    // (F) Object survival
    prove_object_survival minor major fp roots;
    // (G) Forward reachability
    prove_forward_reachability minor major fp roots;
    // (H) Surjectivity
    prove_surjectivity minor major fp roots
#pop-options
