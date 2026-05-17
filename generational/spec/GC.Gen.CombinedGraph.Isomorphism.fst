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
   well_formed_heap mc.mc_major /\
   Mark.stack_props mc.mc_major major_stack /\
   Mark.root_props mc.mc_major major_roots /\
   Sweep.fp_in_heap major_fp mc.mc_major /\
   Mark.no_black_objects mc.mc_major /\
   Mark.no_pointer_to_blue mc.mc_major /\
   (forall (r: obj_addr). Seq.mem r major_roots <==> Seq.mem r major_stack) /\
   // Graph well-formedness of mc_major (needed for mark/sweep composition)
   (let g_mc = create_graph mc.mc_major in
    let mc_roots = HeapGraph.coerce_to_vertex_list major_roots in
    graph_wf g_mc /\ is_vertex_set mc_roots /\ subset_vertices mc_roots g_mc.vertices))

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

/// Standalone proof of Property (A).
#push-options "--z3rlimit 50 --split_queries always"
let prove_property_a
  (gs: gen_state) (roots: seq U64.t) (fp: U64.t)
  (combined_roots: seq combined_vertex)
  (major_roots: seq obj_addr) (major_stack: seq obj_addr) (major_fp: U64.t)
  : Lemma
    (requires
      standard_gc_preconditions gs roots fp major_stack major_roots major_fp /\
      // Reachability bridge
      (let ms = gs.gs_minor in
       let major = gs.gs_major in
       let cg = pre_gc_graph ms major in
       let live_set = live_set_of ms major roots in
       forall (v: U64.t).
         combined_reachable cg combined_roots (MinorV v) ==> Seq.mem v live_set) /\
      // Fwd injectivity on live_set
      (let ms = gs.gs_minor in
       let major = gs.gs_major in
       let live_set = live_set_of ms major roots in
       let prom_res = promote_all_spec ms major fp live_set in
       forall (i j: nat). i < Seq.length live_set /\ j < Seq.length live_set /\ i <> j ==>
         (let oi = Seq.index live_set i in
          let oj = Seq.index live_set j in
          prom_res.fwd_map oi <> 0UL /\ prom_res.fwd_map oj <> 0UL ==>
          prom_res.fwd_map oi <> prom_res.fwd_map oj)) /\
      // Promoted targets disjoint from allocated major objects
      (let ms = gs.gs_minor in
       let major = gs.gs_major in
       let live_set = live_set_of ms major roots in
       let prom_res = promote_all_spec ms major fp live_set in
       forall (v: U64.t) (obj: obj_addr).
         Seq.mem v live_set /\ prom_res.fwd_map v <> 0UL /\
         Seq.mem obj (objects zero_addr major) /\ ~(is_blue obj major) ==>
         prom_res.fwd_map v <> obj) /\
      // Reachable major vertices are valid non-blue objects
      (let cg = pre_gc_graph gs.gs_minor gs.gs_major in
       forall (v: U64.t).
         combined_reachable cg combined_roots (MajorV v) ==>
         U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
         Seq.mem (v <: obj_addr) (objects zero_addr gs.gs_major) /\
         ~(is_blue (v <: obj_addr) gs.gs_major)))
    (ensures
      (let ms = gs.gs_minor in
       let major = gs.gs_major in
       let fwd = (promote_all_spec ms major fp (live_set_of ms major roots)).fwd_map in
       property_a_injectivity ms major fwd combined_roots))
  = let ms = gs.gs_minor in
    let major = gs.gs_major in
    let live_set = live_set_of ms major roots in
    let prom_res = promote_all_spec ms major fp live_set in
    let fwd = prom_res.fwd_map in
    let cg = pre_gc_graph ms major in
    let aux_inj (u v: combined_vertex) : Lemma
      (requires
        combined_reachable cg combined_roots u /\
        combined_reachable cg combined_roots v /\
        fwd_morphism fwd u == fwd_morphism fwd v)
      (ensures u == v)
    = match u, v with
      | MajorV a, MajorV b -> ()
      | MinorV a, MinorV b ->
        assert (Seq.mem a live_set);
        assert (Seq.mem b live_set);
        let ia = Seq.index_mem a live_set in
        let ib = Seq.index_mem b live_set in
        assert (minor_wosize ms a > 0);
        assert (minor_wosize ms b > 0);
        assert (fwd a <> 0UL);
        assert (fwd b <> 0UL);
        if ia = ib then ()
        else begin
          assert (prom_res.fwd_map (Seq.index live_set ia) <> prom_res.fwd_map (Seq.index live_set ib));
          ()
        end
      | MinorV a, MajorV b ->
        assert (Seq.mem a live_set);
        let _ka = Seq.index_mem a live_set in
        assert (minor_wosize ms a > 0);
        assert (fwd a <> 0UL);
        assert (U64.v b >= U64.v mword);
        assert (Seq.mem (b <: obj_addr) (objects zero_addr major));
        assert (~(is_blue (b <: obj_addr) major));
        ()
      | MajorV b, MinorV a ->
        assert (Seq.mem a live_set);
        let _ka2 = Seq.index_mem a live_set in
        assert (minor_wosize ms a > 0);
        assert (fwd a <> 0UL);
        assert (U64.v b >= U64.v mword);
        assert (Seq.mem (b <: obj_addr) (objects zero_addr major));
        assert (~(is_blue (b <: obj_addr) major));
        ()
    in
    Classical.forall_intro_2 (fun u -> Classical.move_requires (aux_inj u))
#pop-options

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

/// Standalone proof of Property (B).
/// Uses the mark/sweep composition: morphism_image_preservation gives
/// reachability in g_mc, reachable_set_correct converts to DFS membership,
/// mark_black_iff_reachable gives is_black, black_survives_sweep gives survival.
#push-options "--z3rlimit 50 --split_queries always"
let prove_property_b
  (gs: gen_state) (roots: seq U64.t) (fp: U64.t)
  (combined_roots: seq combined_vertex)
  (major_roots: seq obj_addr) (major_stack: seq obj_addr) (major_fp: U64.t)
  : Lemma
    (requires
      standard_gc_preconditions gs roots fp major_stack major_roots major_fp /\
      (let ms = gs.gs_minor in
       let major = gs.gs_major in
       let cg = pre_gc_graph ms major in
       let live_set = live_set_of ms major roots in
       let prom_res = promote_all_spec ms major fp live_set in
       let mc = minor_collect_spec ms major fp roots in
       let g_mc = create_graph mc.mc_major in
       // morphism_image_preservation
       (forall (v: combined_vertex).
         combined_reachable cg combined_roots v ==>
         (let w = fwd_morphism prom_res.fwd_map v in
          U64.v w >= U64.v mword /\ U64.v w < heap_size /\ U64.v w % U64.v mword == 0 /\
          mem_graph_vertex g_mc (w <: obj_addr) /\
          (exists (r: obj_addr). Seq.mem r major_roots /\
                                 mem_graph_vertex g_mc r /\
                                 reachable g_mc r (w <: obj_addr))))))
    (ensures
      (let ms = gs.gs_minor in
       let major = gs.gs_major in
       let fwd = (promote_all_spec ms major fp (live_set_of ms major roots)).fwd_map in
       let h_final = post_gc_heap ms major fp roots major_stack major_fp in
       property_b_image ms major fwd combined_roots h_final))
  = let ms = gs.gs_minor in
    let major = gs.gs_major in
    let live_set = live_set_of ms major roots in
    let prom_res = promote_all_spec ms major fp live_set in
    let fwd = prom_res.fwd_map in
    let h_final = post_gc_heap ms major fp roots major_stack major_fp in
    let cg = pre_gc_graph ms major in
    let g_final = create_graph h_final in
    let mc = minor_collect_spec ms major fp roots in
    let h_mc = mc.mc_major in
    let g_mc = create_graph h_mc in
    let mc_roots_v = HeapGraph.coerce_to_vertex_list major_roots in
    let aux_image (v: combined_vertex) : Lemma
      (requires combined_reachable cg combined_roots v)
      (ensures
        (let w = fwd_morphism fwd v in
         U64.v w >= 0 /\ U64.v w < heap_size /\ U64.v w % U64.v mword == 0 /\
         Seq.mem (w <: hp_addr) g_final.vertices))
    = let w : U64.t = fwd_morphism fwd v in
      let w_oa : obj_addr = w in
      assert (mem_graph_vertex g_mc w_oa);
      // Eliminate the existential root witness from morphism_image_preservation
      let elim_root (r: obj_addr) : Lemma
        (requires Seq.mem r major_roots /\ mem_graph_vertex g_mc r /\ reachable g_mc r w_oa)
        (ensures Seq.mem w_oa (DFS.reachable_set g_mc mc_roots_v))
      = HeapGraph.coerce_mem_lemma major_roots r;
        DFS.reachable_set_correct g_mc mc_roots_v
      in
      Classical.exists_elim
        (Seq.mem w_oa (DFS.reachable_set g_mc mc_roots_v))
        #obj_addr
        #(fun r -> Seq.mem r major_roots /\ mem_graph_vertex g_mc r /\ reachable g_mc r w_oa)
        ()
        (fun (r: obj_addr{Seq.mem r major_roots /\ mem_graph_vertex g_mc r /\ reachable g_mc r w_oa}) ->
          elim_root r);
      MSFrame.mark_black_iff_reachable h_mc major_stack major_roots major_fp w_oa;
      MSFrame.black_survives_sweep h_mc major_stack major_roots major_fp w_oa;
      ()
    in
    Classical.forall_intro (Classical.move_requires aux_image)
#pop-options

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

/// Forward direction: combined edge → post-GC edge
let property_d_forward
  (ms: minor_state) (major: heap) (fwd: forwarding_map)
  (combined_roots: seq combined_vertex)
  (h_final: heap) : prop =
  let cg = pre_gc_graph ms major in
  let g_final = create_graph h_final in
  forall (u v: combined_vertex).
    combined_reachable cg combined_roots u /\
    combined_reachable cg combined_roots v /\
    mem_ce (u, v) cg /\
    (let fu = fwd_morphism fwd u in
     let fv = fwd_morphism fwd v in
     U64.v fu < heap_size /\ U64.v fu % U64.v mword == 0 /\
     U64.v fv < heap_size /\ U64.v fv % U64.v mword == 0) ==>
    Seq.mem ((fwd_morphism fwd u <: hp_addr), (fwd_morphism fwd v <: hp_addr)) g_final.edges

/// Backward direction: post-GC edge → combined edge
let property_d_backward
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
     U64.v fv < heap_size /\ U64.v fv % U64.v mword == 0) /\
    Seq.mem ((fwd_morphism fwd u <: hp_addr), (fwd_morphism fwd v <: hp_addr)) g_final.edges ==>
    mem_ce (u, v) cg

/// Combined (biconditional): the full edge equivalence
let property_d_edges
  (ms: minor_state) (major: heap) (fwd: forwarding_map)
  (combined_roots: seq combined_vertex)
  (h_final: heap) : prop =
  property_d_forward ms major fwd combined_roots h_final /\
  property_d_backward ms major fwd combined_roots h_final

/// ---------------------------------------------------------------------------
/// Property (D) Forward: Proof via bridge + mark/sweep
/// ---------------------------------------------------------------------------

/// Bridge assumption: combined edge → mc_major edge.
/// This composes the 4 cases of EdgePreservation:
///   Case 1 (minor→minor): promoted field becomes fwd(minor_val)
///   Case 2 (minor→major): promoted field preserved verbatim
///   Case 3 (major→minor): field rewritten to fwd(dst) by update_major_pointers
///   Case 4 (major→major): field unchanged through promotion
///
/// Proving this requires combined-edge elimination lemmas (decomposing
/// mem_ce into a field index + classification) and classification inversion.
/// These are not yet implemented in CombinedGraph.fsti.
let combined_edge_to_mc_edge
  (ms: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (fwd: forwarding_map)
  (u v: combined_vertex) (mc_major: heap) : prop =
  let g_mc = create_graph mc_major in
  let fu : U64.t = fwd_morphism fwd u in
  let fv : U64.t = fwd_morphism fwd v in
  U64.v fu >= U64.v mword /\ U64.v fu < heap_size /\ U64.v fu % U64.v mword == 0 /\
  U64.v fv >= U64.v mword /\ U64.v fv < heap_size /\ U64.v fv % U64.v mword == 0 /\
  Seq.mem ((fu <: hp_addr), (fv <: hp_addr)) g_mc.edges

/// Property D forward proof.
/// Given the bridge assumption (combined edge → mc_major edge) and
/// morphism_image_preservation, chains:
///   1. combined edge → mc_major edge (bridge)
///   2. φ(u) is black after mark (reachable → DFS → mark_black_iff_reachable)
///   3. successors g_mc φ(u) == successors g_final φ(u) (mark_sweep_preserves_successors)
///   4. φ(v) ∈ successors g_mc φ(u) → φ(v) ∈ successors g_final φ(u) → edge in g_final
#push-options "--z3rlimit 100"
let prove_property_d_forward
  (gs: gen_state) (roots: seq U64.t) (fp: U64.t)
  (combined_roots: seq combined_vertex)
  (major_roots: seq obj_addr) (major_stack: seq obj_addr) (major_fp: U64.t)
  : Lemma
    (requires
      standard_gc_preconditions gs roots fp major_stack major_roots major_fp /\
      (let ms = gs.gs_minor in
       let major = gs.gs_major in
       let cg = pre_gc_graph ms major in
       let live_set = live_set_of ms major roots in
       let prom_res = promote_all_spec ms major fp live_set in
       let mc = minor_collect_spec ms major fp roots in
       let g_mc = create_graph mc.mc_major in
       // morphism_image_preservation
       (forall (v: combined_vertex).
         combined_reachable cg combined_roots v ==>
         (let w = fwd_morphism prom_res.fwd_map v in
          U64.v w >= U64.v mword /\ U64.v w < heap_size /\ U64.v w % U64.v mword == 0 /\
          mem_graph_vertex g_mc (w <: obj_addr) /\
          (exists (r: obj_addr). Seq.mem r major_roots /\
                                 mem_graph_vertex g_mc r /\
                                 reachable g_mc r (w <: obj_addr)))) /\
       // Bridge: combined edges map to mc_major edges
       (forall (u v: combined_vertex).
         combined_reachable cg combined_roots u /\
         combined_reachable cg combined_roots v /\
         mem_ce (u, v) cg ==>
         combined_edge_to_mc_edge ms major fp roots prom_res.fwd_map u v mc.mc_major)))
    (ensures
      (let ms = gs.gs_minor in
       let major = gs.gs_major in
       let fwd = (promote_all_spec ms major fp (live_set_of ms major roots)).fwd_map in
       let h_final = post_gc_heap ms major fp roots major_stack major_fp in
       property_d_forward ms major fwd combined_roots h_final))
  = let ms = gs.gs_minor in
    let major = gs.gs_major in
    let live_set = live_set_of ms major roots in
    let prom_res = promote_all_spec ms major fp live_set in
    let fwd = prom_res.fwd_map in
    let h_final = post_gc_heap ms major fp roots major_stack major_fp in
    let cg = pre_gc_graph ms major in
    let g_final = create_graph h_final in
    let mc = minor_collect_spec ms major fp roots in
    let h_mc = mc.mc_major in
    let g_mc = create_graph h_mc in
    let mc_roots_v = HeapGraph.coerce_to_vertex_list major_roots in
    let aux_fwd (u v: combined_vertex) : Lemma
      (ensures
        (combined_reachable cg combined_roots u /\
         combined_reachable cg combined_roots v /\
         mem_ce (u, v) cg /\
         (let fu = fwd_morphism fwd u in
          let fv = fwd_morphism fwd v in
          U64.v fu < heap_size /\ U64.v fu % U64.v mword == 0 /\
          U64.v fv < heap_size /\ U64.v fv % U64.v mword == 0) ==>
         Seq.mem ((fwd_morphism fwd u <: hp_addr), (fwd_morphism fwd v <: hp_addr)) g_final.edges))
    = let fu : U64.t = fwd_morphism fwd u in
      let fv : U64.t = fwd_morphism fwd v in
      // Branch on decidable bounds/alignment — after this, fu/fv are hp_addr
      if not (U64.v fu < heap_size && U64.v fu % U64.v mword = 0 &&
              U64.v fv < heap_size && U64.v fv % U64.v mword = 0) then ()
      else begin
        let fu_hp : hp_addr = fu in
        let fv_hp : hp_addr = fv in
        // Use impl_intro for the non-decidable prop parts only
        let inner (_: squash (combined_reachable cg combined_roots u /\
                              combined_reachable cg combined_roots v /\
                              mem_ce (u, v) cg))
          : Lemma (Seq.mem (fu_hp, fv_hp) g_final.edges) =
          // From morphism_image_preservation: reachable vertex → image is obj_addr
          assert (U64.v fu >= U64.v mword);
          assert (U64.v fv >= U64.v mword);
          let fu_oa : obj_addr = fu in
          // Step 1: bridge gives mc_major edge
          assert (Seq.mem (fu_hp, fv_hp) g_mc.edges);
          // Step 2: φ(u) is reachable → black after mark
          assert (mem_graph_vertex g_mc fu_oa);
          let elim_root (r: obj_addr) : Lemma
            (requires Seq.mem r major_roots /\ mem_graph_vertex g_mc r /\ reachable g_mc r fu_oa)
            (ensures Seq.mem fu_oa (DFS.reachable_set g_mc mc_roots_v))
          = HeapGraph.coerce_mem_lemma major_roots r;
            DFS.reachable_set_correct g_mc mc_roots_v
          in
          Classical.exists_elim
            (Seq.mem fu_oa (DFS.reachable_set g_mc mc_roots_v))
            #obj_addr
            #(fun r -> Seq.mem r major_roots /\ mem_graph_vertex g_mc r /\ reachable g_mc r fu_oa)
            ()
            (fun (r: obj_addr{Seq.mem r major_roots /\ mem_graph_vertex g_mc r /\ reachable g_mc r fu_oa}) ->
              elim_root r);
          MSFrame.mark_black_iff_reachable h_mc major_stack major_roots major_fp fu_oa;
          MSFrame.black_survives_sweep h_mc major_stack major_roots major_fp fu_oa;
          // Step 3: successors preserved
          MSFrame.mark_sweep_preserves_successors h_mc major_stack major_roots major_fp fu_oa;
          // Step 4: edge in g_mc → successor → same successor in g_final → edge
          edge_mem_successors g_mc fu_hp fv_hp;
          successors_mem_edge g_final fu_hp fv_hp
        in
        Classical.impl_intro inner
      end
    in
    Classical.forall_intro_2 aux_fwd
#pop-options

/// ---------------------------------------------------------------------------
/// Main theorem proof
/// ---------------------------------------------------------------------------

/// The main theorem composes all four properties.
///
/// Proof status:
///   Property (A): ✅ Fully proven (prove_property_a — 4 match cases)
///   Property (B): ✅ Fully proven (prove_property_b — mark/sweep composition)
///   Property (C): assume — needs image decomposition (old major ∪ promoted)
///   Property (D): assume — split into forward/backward; forward via EdgePres + MSFrame
///   reachable_implies_forwarded: ✅ Fully proven (Seq.index_mem chain)
#push-options "--z3rlimit 100 --split_queries always"
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
         Seq.mem v live_set) /\
      // Promoted targets are disjoint from pre-existing non-blue major objects
      (let live_set = live_set_of gs.gs_minor gs.gs_major roots in
       let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
       forall (v: U64.t) (obj: obj_addr).
         Seq.mem v live_set /\ prom_res.fwd_map v <> 0UL /\
         Seq.mem obj (objects zero_addr gs.gs_major) /\ ~(is_blue obj gs.gs_major) ==>
         prom_res.fwd_map v <> obj) /\
      // Reachable major vertices are valid non-blue objects
      (let cg = build_combined_graph gs.gs_minor gs.gs_major in
       forall (v: U64.t).
         combined_reachable cg combined_roots (MajorV v) ==>
         U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
         Seq.mem (v <: obj_addr) (objects zero_addr gs.gs_major) /\
         ~(is_blue (v <: obj_addr) gs.gs_major)) /\
      // Morphism image preservation: combined-reachable → mc_major reachable
      (let cg = build_combined_graph gs.gs_minor gs.gs_major in
       let live_set = live_set_of gs.gs_minor gs.gs_major roots in
       let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
       let mc = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
       let g_mc = create_graph mc.mc_major in
       forall (v: combined_vertex).
         combined_reachable cg combined_roots v ==>
         (let w = fwd_morphism prom_res.fwd_map v in
          U64.v w >= U64.v mword /\ U64.v w < heap_size /\ U64.v w % U64.v mword == 0 /\
          mem_graph_vertex g_mc (w <: obj_addr) /\
          (exists (r: obj_addr). Seq.mem r major_roots /\
                                 mem_graph_vertex g_mc r /\
                                 reachable g_mc r (w <: obj_addr)))))
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
    prove_property_a gs roots fp combined_roots major_roots major_stack major_fp;
    // Property (B): Image in post-GC
    prove_property_b gs roots fp combined_roots major_roots major_stack major_fp;
    // Property (C): Surjectivity
    assume (property_c_surjectivity ms major fwd combined_roots h_final major_roots);
    // Property (D): Edge biconditional
    let mc = minor_collect_spec ms major fp roots in
    // Forward: proven from bridge assumption + mark/sweep preservation
    assume (forall (u v: combined_vertex).
      combined_reachable cg combined_roots u /\
      combined_reachable cg combined_roots v /\
      mem_ce (u, v) cg ==>
      combined_edge_to_mc_edge ms major fp roots fwd u v mc.mc_major);
    prove_property_d_forward gs roots fp combined_roots major_roots major_stack major_fp;
    // Backward: assumed — needs EdgePreservation reverse + field decomposition
    assume (property_d_backward ms major fwd combined_roots h_final);
    // reachable_implies_forwarded: combined_reachable(MinorV v) → fwd v ≠ 0
    let aux_rif (v: U64.t) : Lemma
      (requires combined_reachable cg combined_roots (MinorV v))
      (ensures fwd v <> 0UL)
    = assert (Seq.mem v live_set);
      let k = Seq.index_mem v live_set in
      assert (k < Seq.length live_set);
      assert (minor_wosize ms v > 0);
      ()
    in
    Classical.forall_intro (Classical.move_requires aux_rif);
    // Help Z3 compose the individual properties into the postcondition
    assert (property_d_forward ms major fwd combined_roots h_final);
    assert (property_d_backward ms major fwd combined_roots h_final);
    assert (property_d_edges ms major fwd combined_roots h_final);
    ()
#pop-options
