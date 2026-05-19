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
/// Main theorem: assemble all pieces
/// ---------------------------------------------------------------------------

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
    // (E) Header/wosize preservation
    prove_header_preservation minor major fp roots;
    // (F) Object survival
    prove_object_survival minor major fp roots
#pop-options
