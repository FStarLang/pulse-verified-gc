/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph.Isomorphism — Proof of the isomorphism theorem
/// ---------------------------------------------------------------------------
///
/// Proves generational_gc_isomorphism: the pre-GC combined graph (minor + major)
/// is isomorphic (on reachable subgraphs) to the post-GC major graph.
///
/// Structure:
///   1. Property (A): Injectivity of fwd_morphism on reachable vertices
///   2. Property (B): Image of reachable vertices lands in post-GC graph
///   3. Property (C): Surjectivity — post-GC reachable vertices have pre-images
///   4. Property (D): Edge biconditional — edges preserved in both directions
///   5. Composition into the main theorem

module GC.Gen.CombinedGraph.Isomorphism

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
open GC.Gen.Reachability
open GC.Gen.Remembered
open GC.Gen.Promote
open GC.Gen.CombinedGraph
open GC.Gen.Allocator
open GC.Gen.Correctness

module HeapGraph = GC.Spec.HeapGraph
module AllocLemmas = GC.Spec.Allocator.Lemmas
module Mark = GC.Spec.Mark
module Sweep = GC.Spec.Sweep
module MajorCorrectness = GC.Spec.Correctness
module DFS = GC.Spec.DFS
module MSFrame = GC.Gen.CombinedGraph.MarkSweepFrame
module MajorBridge = GC.Gen.CombinedGraph.MajorBridge
module EdgePres = GC.Gen.CombinedGraph.EdgePreservation
module Bridge = GC.Gen.CombinedGraph.Bridge

/// ---------------------------------------------------------------------------
/// Standard GC preconditions (bundled for readability)
/// ---------------------------------------------------------------------------

/// The standard preconditions that appear in generational_gc_isomorphism.
/// We bundle them to keep sub-lemma signatures manageable.
let standard_gc_preconditions
  (gs: gen_state) (roots: seq U64.t) (fp: U64.t)
  (major_stack major_roots: seq obj_addr) (major_fp: U64.t) : prop =
  gen_wf gs /\
  well_formed_heap gs.gs_major /\
  AllocLemmas.fl_valid gs.gs_major fp (heap_size / U64.v mword) /\
  AllocLemmas.fl_chain_terminates gs.gs_major fp (heap_size / U64.v mword) /\
  minor_fields_well_formed gs.gs_minor gs.gs_major roots /\
  all_promotions_succeed gs.gs_minor gs.gs_major fp roots /\
  allocated_objects_avoid_chain gs.gs_major fp /\
  post_promote_pointer_closure gs.gs_minor gs.gs_major fp roots /\
  live_set_no_infix gs.gs_minor (live_set_of gs.gs_minor gs.gs_major roots) /\
  no_scan_invariant gs.gs_major /\
  minor_no_scan_invariant gs.gs_minor /\
  // Live objects have positive wosize (ensures promotion succeeds)
  (let live_set = live_set_of gs.gs_minor gs.gs_major roots in
   forall (v: U64.t). Seq.mem v live_set ==> minor_wosize gs.gs_minor v > 0) /\
  (let mc = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
   Mark.stack_props mc.mc_major major_stack /\
   Mark.root_props mc.mc_major major_roots /\
   Sweep.fp_in_heap major_fp mc.mc_major /\
   Mark.no_black_objects mc.mc_major /\
   Mark.no_pointer_to_blue mc.mc_major /\
   (forall (r: obj_addr). Seq.mem r major_roots <==> Seq.mem r major_stack))

/// ---------------------------------------------------------------------------
/// Property (A): Injectivity
/// ---------------------------------------------------------------------------

/// Injectivity of fwd_morphism on reachable combined vertices.
///
/// Three cases:
///   MajorV u, MajorV v: fwd_morphism is identity, so u = v trivially.
///   MinorV u, MinorV v: fwd u = fwd v implies u = v by fwd injectivity
///     on live_set (given as precondition).
///   MinorV u, MajorV v: fwd u = v. fwd u is a newly allocated address
///     (from free list), while v is a pre-existing reachable major object.
///     These are disjoint because allocation uses free-list blocks that
///     are not reachable objects (allocated_objects_avoid_chain).
///
/// The mixed case (MinorV u == MajorV v with fwd u == v) is the hardest.
/// It requires showing that promoted targets don't collide with pre-existing
/// reachable major objects.
let property_a_injectivity
  (ms: minor_state) (major: heap) (fwd: forwarding_map)
  (combined_roots: seq combined_vertex) : prop =
  let cg = pre_gc_graph ms major in
  forall (u v: combined_vertex).
    combined_reachable cg combined_roots u /\
    combined_reachable cg combined_roots v /\
    fwd_morphism fwd u == fwd_morphism fwd v ==> u == v

/// ---------------------------------------------------------------------------
/// Property (B): Image in post-GC
/// ---------------------------------------------------------------------------

/// Every reachable pre-GC vertex maps to a vertex in the post-GC graph.
///
/// For MajorV v: v is reachable in the combined pre-GC graph. After minor
///   collection, v is still a vertex in mc_major. After mark (v is reachable
///   from major_roots), v is black. After sweep, v survives.
///
/// For MinorV v: fwd v is a newly promoted object in mc_major. After mark
///   (fwd v is reachable from major_roots via root correspondence), fwd v
///   is black. After sweep, fwd v survives.
let property_b_image
  (ms: minor_state) (major: heap) (fwd: forwarding_map)
  (combined_roots: seq combined_vertex)
  (h_final: heap) : prop =
  let cg = pre_gc_graph ms major in
  let g_final = create_graph h_final in
  forall (v: combined_vertex).
    combined_reachable cg combined_roots v ==>
    (let w = fwd_morphism fwd v in
     U64.v w >= 0 /\ U64.v w < heap_size /\ U64.v w % U64.v mword == 0 /\
     Seq.mem (w <: hp_addr) g_final.vertices)

/// ---------------------------------------------------------------------------
/// Property (C): Surjectivity on reachable
/// ---------------------------------------------------------------------------

/// Every post-GC reachable vertex has a pre-image in the pre-GC combined graph.
///
/// Post-GC reachable vertex w is either:
///   1. A pre-existing major object (not newly promoted) → pre-image is MajorV w
///   2. A promoted minor object → pre-image is MinorV (fwd_inv w)
///
/// This uses the fact that the post-GC graph only contains objects from
/// the pre-minor-collection major heap plus newly promoted objects.
let property_c_surjectivity
  (ms: minor_state) (major: heap) (fwd: forwarding_map)
  (combined_roots: seq combined_vertex)
  (h_final: heap) (major_roots: seq obj_addr) : prop =
  let cg = pre_gc_graph ms major in
  let g_final = create_graph h_final in
  forall (w: vertex_id).
    Seq.mem w g_final.vertices /\
    (exists (r: obj_addr). Seq.mem r major_roots /\
                           Seq.mem r g_final.vertices /\
                           reachable g_final r w) ==>
    (exists (v: combined_vertex).
      combined_reachable cg combined_roots v /\
      fwd_morphism fwd v == (w <: U64.t))

/// ---------------------------------------------------------------------------
/// Property (D): Edge biconditional
/// ---------------------------------------------------------------------------

/// Edges are preserved in both directions between the pre-GC combined graph
/// and the post-GC major graph.
///
/// Forward (⟹): Uses EdgePreservation (4 cases) + MarkSweepFrame.
///   Combined edge (u, v) → mc_major has edge (φ(u), φ(v)) → mark/sweep
///   preserves edges of surviving objects → post-GC has edge (φ(u), φ(v)).
///
/// Backward (⟸): Post-GC edge (φ(u), φ(v)) exists. Since mark/sweep
///   preserves fields of black objects (Pillar 5), the edge was present in
///   mc_major. Then by edge preservation reverse, it came from a combined edge.
let property_d_edges
  (ms: minor_state) (major: heap) (fwd: forwarding_map)
  (combined_roots: seq combined_vertex)
  (h_final: heap) : prop =
  let cg = pre_gc_graph ms major in
  let g_final = create_graph h_final in
  forall (u v: combined_vertex).
    combined_reachable cg combined_roots u /\
    combined_reachable cg combined_roots v /\
    (let fu = fwd_morphism fwd u in
     let fv = fwd_morphism fwd v in
     U64.v fu < heap_size /\ U64.v fu % U64.v mword == 0 /\
     U64.v fv < heap_size /\ U64.v fv % U64.v mword == 0) ==>
    (mem_ce (u, v) cg <==>
     Seq.mem ((fwd_morphism fwd u <: hp_addr), (fwd_morphism fwd v <: hp_addr)) g_final.edges)

/// ---------------------------------------------------------------------------
/// Main theorem proof
/// ---------------------------------------------------------------------------

/// The main theorem composes all four properties.
///
/// Current status: This proof uses admits for each property sub-proof.
/// The admits are annotated with what infrastructure is needed.
///
/// Admits breakdown:
///   Property (A): 1 admit — mixed case (MinorV/MajorV non-collision)
///   Property (B): 1 admit — reachability preservation through minor collect + mark/sweep  
///   Property (C): 1 admit — image decomposition (old major ∪ promoted)
///   Property (D): 1 admit — edge biconditional through full GC cycle
let generational_gc_isomorphism
  (gs: gen_state) (roots: seq U64.t) (fp: U64.t)
  (combined_roots: seq combined_vertex)
  (major_roots: seq obj_addr) (major_stack: seq obj_addr) (major_fp: U64.t)
  : Lemma
    (requires
      standard_gc_preconditions gs roots fp major_stack major_roots major_fp /\
      // Root correspondence
      (forall (r: obj_addr). Seq.mem r major_roots <==>
        Seq.mem (MajorV r) combined_roots \/ 
        (exists (m: U64.t). Seq.mem (MinorV m) combined_roots /\
          (let live_set = live_set_of gs.gs_minor gs.gs_major roots in
           let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
           prom_res.fwd_map m == r))) /\
      // Injectivity of forwarding on live set
      (let live_set = live_set_of gs.gs_minor gs.gs_major roots in
       let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
       forall (i j: nat). i < Seq.length live_set /\ j < Seq.length live_set /\ i <> j ==>
         (let oi = Seq.index live_set i in
          let oj = Seq.index live_set j in
          prom_res.fwd_map oi <> 0UL /\ prom_res.fwd_map oj <> 0UL ==>
          prom_res.fwd_map oi <> prom_res.fwd_map oj)) /\
      // Field correspondence for promoted objects
      (let live_set = live_set_of gs.gs_minor gs.gs_major roots in
       let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
       let mc = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
       field_correspondence gs.gs_minor gs.gs_major mc.mc_major prom_res.fwd_map roots) /\
      // Reachability bridge: combined-reachable minor vertices are in the live set
      (let cg = build_combined_graph gs.gs_minor gs.gs_major in
       let live_set = live_set_of gs.gs_minor gs.gs_major roots in
       forall (v: U64.t).
         combined_reachable cg combined_roots (MinorV v) ==>
         Seq.mem v live_set))
    (ensures
      (let live_set = live_set_of gs.gs_minor gs.gs_major roots in
       let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
       let fwd = prom_res.fwd_map in
       let h_final = post_gc_heap gs.gs_minor gs.gs_major fp roots major_stack major_fp in
       reachable_implies_forwarded (pre_gc_graph gs.gs_minor gs.gs_major)
                                   combined_roots fwd /\
       reachable_subgraph_isomorphism gs.gs_minor gs.gs_major fwd
                                      combined_roots h_final major_roots))
  = let ms = gs.gs_minor in
    let major = gs.gs_major in
    let live_set = live_set_of ms major roots in
    let prom_res = promote_all_spec ms major fp live_set in
    let fwd = prom_res.fwd_map in
    let h_final = post_gc_heap ms major fp roots major_stack major_fp in
    let cg = pre_gc_graph ms major in
    let g_final = create_graph h_final in
    // Property (A): Injectivity
    // TODO: prove via fwd injectivity precondition + disjointness of promoted/pre-existing
    assume (property_a_injectivity ms major fwd combined_roots);
    // Property (B): Image in post-GC
    // TODO: prove via reachability preservation + mark/sweep survival
    assume (property_b_image ms major fwd combined_roots h_final);
    // Property (C): Surjectivity
    // TODO: prove via image decomposition (old major ∪ promoted minor)
    assume (property_c_surjectivity ms major fwd combined_roots h_final major_roots);
    // Property (D): Edge biconditional
    // TODO: prove via EdgePreservation + MarkSweepFrame composition
    assume (property_d_edges ms major fwd combined_roots h_final);
    // reachable_implies_forwarded: follows from the preconditions
    // Chain: combined_reachable(MinorV v) → v ∈ live_set → wosize > 0 → fwd v ≠ 0
    let aux_rif (v: U64.t) : Lemma
      (requires combined_reachable cg combined_roots (MinorV v))
      (ensures fwd v <> 0UL)
    = // v ∈ live_set (from reachability bridge precondition)
      assert (Seq.mem v live_set);
      // Get index k such that Seq.index live_set k == v
      let k = Seq.index_mem v live_set in
      // all_promotions_succeed quantifies over indices
      assert (k < Seq.length live_set);
      assert (Seq.index live_set k == v);
      // wosize > 0 (from live_set_wosize_positive precondition)
      assert (minor_wosize ms v > 0);
      // all_promotions_succeed gives fwd v ≠ 0
      ()
    in
    Classical.forall_intro (Classical.move_requires aux_rif);
    // Compose into reachable_subgraph_isomorphism
    // The four properties exactly match the conjunction in the definition
    ()
