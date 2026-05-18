/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph.Isomorphism.TopLevel — Implementation
/// ---------------------------------------------------------------------------
///
/// Proves the isomorphism directly from cheney_collect_spec, without requiring
/// equivalence to promote_all_spec. Uses MarkSweepFrame to bridge from the
/// post-minor-collection heap (mc_major) to the final swept heap (g_final).
///
/// Key insight: reachable_subgraph_isomorphism is parametric in the forwarding
/// map. It only requires structural properties (injectivity, image, surjectivity,
/// edge preservation) — not any specific computation path. The iso_* preconditions
/// state exactly these properties for cheney_promote's forwarding map.

module GC.Gen.CombinedGraph.Isomorphism.TopLevel

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
open GC.Gen.CombinedGraph
open GC.Gen.Cheney
open GC.Gen.Correctness
open GC.Gen.Allocator
open GC.Gen.Reachability
open GC.Gen.Remembered

module HeapGraph = GC.Spec.HeapGraph
module AllocLemmas = GC.Spec.Allocator.Lemmas
module Mark = GC.Spec.Mark
module Sweep = GC.Spec.Sweep
module DFS = GC.Spec.DFS
module Iso = GC.Gen.CombinedGraph.Isomorphism
module MSFrame = GC.Gen.CombinedGraph.MarkSweepFrame

/// Definition of isomorphism_postcondition (opaque in .fsti for Pulse compatibility)
let isomorphism_postcondition
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (combined_roots: seq combined_vertex)
  (major_stack: seq obj_addr) (major_fp: U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  let fwd = prom.fwd_map in
  let res = cheney_collect_spec minor major fp roots in
  let h_final = fst (Sweep.sweep (Mark.mark res.mc_major major_stack) major_fp) in
  Iso.reachable_implies_forwarded
    (build_combined_graph minor major)
    combined_roots fwd /\
  Iso.reachable_subgraph_isomorphism minor major fwd
    combined_roots h_final major_stack

let isomorphism_postcondition_elim
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (combined_roots: seq combined_vertex)
  (major_stack: seq obj_addr) (major_fp: U64.t)
  : Lemma
    (requires isomorphism_postcondition minor major fp roots combined_roots major_stack major_fp)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let fwd = prom.fwd_map in
      let res = cheney_collect_spec minor major fp roots in
      let h_final = fst (Sweep.sweep (Mark.mark res.mc_major major_stack) major_fp) in
      Iso.reachable_implies_forwarded
        (build_combined_graph minor major)
        combined_roots fwd /\
      Iso.reachable_subgraph_isomorphism minor major fwd
        combined_roots h_final major_stack))
  = ()

/// Helper: if successors are equal, edges are equivalent
private let successors_eq_implies_edge_equiv (g1 g2: graph_state) (u v: vertex_id)
  : Lemma (requires successors g1 u == successors g2 u)
          (ensures Seq.mem (u, v) g1.edges <==> Seq.mem (u, v) g2.edges)
  = Classical.move_requires (edge_mem_successors g1 u) v;
    Classical.move_requires (successors_mem_edge g1 u) v;
    Classical.move_requires (edge_mem_successors g2 u) v;
    Classical.move_requires (successors_mem_edge g2 u) v


/// ---------------------------------------------------------------------------
/// Helper: mc_major standard preconditions for MSFrame calls
/// ---------------------------------------------------------------------------

/// Bundle the preconditions that MSFrame lemmas need about mc_major.
/// These are exactly the standard mark/sweep preconditions.
let msframe_preconditions
  (mc_major: heap) (major_stack: seq obj_addr) (major_fp: U64.t) : prop =
  well_formed_heap mc_major /\
  Mark.stack_props mc_major major_stack /\
  Mark.root_props mc_major major_stack /\
  Sweep.fp_in_heap major_fp mc_major /\
  Mark.no_black_objects mc_major /\
  Mark.no_pointer_to_blue mc_major /\
  (let g = create_graph mc_major in
   let rs = HeapGraph.coerce_to_vertex_list major_stack in
   graph_wf g /\ is_vertex_set rs /\ subset_vertices rs g.vertices)


/// ---------------------------------------------------------------------------
/// Property (A): Injectivity of fwd_morphism on reachable vertices
/// ---------------------------------------------------------------------------

/// fwd_morphism is injective on combined-reachable vertices.
/// Three cases: Major-Major (identity), Minor-Minor (fwd injectivity),
/// Minor-Major (promoted targets disjoint from non-blue major objects).
#push-options "--z3rlimit 40 --split_queries always"
let prove_injectivity
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (combined_roots: seq combined_vertex) (major_stack: seq obj_addr)
  : Lemma
    (requires
      iso_structural_preconditions minor major fp roots combined_roots major_stack)
    (ensures
      (let cg = build_combined_graph minor major in
       let fwd = (cheney_promote minor major fp roots).fwd_map in
       forall (u v: combined_vertex).
         combined_reachable cg combined_roots u /\
         combined_reachable cg combined_roots v /\
         Iso.fwd_morphism fwd u == Iso.fwd_morphism fwd v ==> u == v))
  = let cg = build_combined_graph minor major in
    let prom = cheney_promote minor major fp roots in
    let fwd = prom.fwd_map in
    let live_set = live_set_of minor major roots in
    let aux (u v: combined_vertex) : Lemma
      (requires
        combined_reachable cg combined_roots u /\
        combined_reachable cg combined_roots v /\
        Iso.fwd_morphism fwd u == Iso.fwd_morphism fwd v)
      (ensures u == v)
    = match u, v with
      | MajorV a, MajorV b ->
        // fwd_morphism(MajorV a) = a, fwd_morphism(MajorV b) = b, so a == b
        ()
      | MinorV a, MinorV b ->
        // Both in live_set (reachability bridge), fwd a == fwd b (hypothesis)
        // Element-based injectivity gives a == b
        assert (Seq.mem a live_set);
        assert (Seq.mem b live_set);
        assert (fwd a == fwd b)
      | MinorV a, MajorV b ->
        // fwd a == b (hypothesis). But a ∈ live_set → fwd a ≠ 0,
        // and b ∈ non-blue major objects → promoted_disjoint gives fwd a ≠ b
        assert (Seq.mem a live_set);
        assert (fwd a <> 0UL);
        assert (U64.v b >= U64.v mword);
        assert (Seq.mem (b <: obj_addr) (objects zero_addr major));
        assert (~(is_blue (b <: obj_addr) major));
        assert (fwd a <> (b <: U64.t))
      | MajorV b, MinorV a ->
        // Symmetric to MinorV/MajorV
        assert (Seq.mem a live_set);
        assert (fwd a <> 0UL);
        assert (U64.v b >= U64.v mword);
        assert (Seq.mem (b <: obj_addr) (objects zero_addr major));
        assert (~(is_blue (b <: obj_addr) major));
        assert (fwd a <> (b <: U64.t))
    in
    Classical.forall_intro_2 (fun u -> Classical.move_requires (aux u))
#pop-options


/// ---------------------------------------------------------------------------
/// Property (B): Image of reachable vertices in g_final
/// ---------------------------------------------------------------------------

/// For each combined-reachable vertex v, fwd_morphism(v) is a vertex
/// in the final swept graph. Chain: reachable in combined → image in mc
/// (from iso_structural_preconditions) → reachable in mc → black after mark
/// → survives sweep.
#push-options "--z3rlimit 60 --split_queries always"
let prove_image
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (combined_roots: seq combined_vertex)
  (major_stack: seq obj_addr) (major_fp: U64.t)
  : Lemma
    (requires
      iso_structural_preconditions minor major fp roots combined_roots major_stack /\
      (let res = cheney_collect_spec minor major fp roots in
       msframe_preconditions res.mc_major major_stack major_fp))
    (ensures
      (let prom = cheney_promote minor major fp roots in
       let fwd = prom.fwd_map in
       let res = cheney_collect_spec minor major fp roots in
       let h_final = fst (Sweep.sweep (Mark.mark res.mc_major major_stack) major_fp) in
       let cg = build_combined_graph minor major in
       let g_final = create_graph h_final in
       forall (v: combined_vertex).
         combined_reachable cg combined_roots v ==>
         (let w = Iso.fwd_morphism fwd v in
          U64.v w >= 0 /\ U64.v w < heap_size /\ U64.v w % U64.v mword == 0 /\
          Seq.mem (w <: hp_addr) g_final.vertices)))
  = let prom = cheney_promote minor major fp roots in
    let fwd = prom.fwd_map in
    let res = cheney_collect_spec minor major fp roots in
    let mc_major = res.mc_major in
    let g_mc = create_graph mc_major in
    let mc_roots_v = HeapGraph.coerce_to_vertex_list major_stack in
    let cg = build_combined_graph minor major in
    // Establish DFS.reachable_set correctness once for all vertices
    DFS.reachable_set_correct g_mc mc_roots_v;
    let aux (v: combined_vertex) : Lemma
      (requires combined_reachable cg combined_roots v)
      (ensures
        (let w = Iso.fwd_morphism fwd v in
         let h_final = fst (Sweep.sweep (Mark.mark mc_major major_stack) major_fp) in
         let g_final = create_graph h_final in
         U64.v w >= 0 /\ U64.v w < heap_size /\ U64.v w % U64.v mword == 0 /\
         Seq.mem (w <: hp_addr) g_final.vertices))
    = let w = Iso.fwd_morphism fwd v in
      // From morphism_image_preservation: w is valid, in g_mc, and mc-reachable
      assert (U64.v w >= U64.v mword);
      assert (mem_graph_vertex g_mc (w <: obj_addr));
      // Bridge: the existential reachability + coerce_mem_lemma + DFS correctness
      // gives membership in DFS.reachable_set
      let w_obj : obj_addr = w in
      assert (exists (r: obj_addr). Seq.mem r major_stack /\
                                    mem_graph_vertex g_mc r /\
                                    reachable g_mc r w_obj);
      // coerce_mem_lemma ensures major_stack membership ↔ mc_roots_v membership
      Classical.forall_intro (HeapGraph.coerce_mem_lemma major_stack);
      // DFS.reachable_set_correct already called above — Z3 has the universal
      assert (Seq.mem w_obj (DFS.reachable_set g_mc mc_roots_v));
      // Reachable ↔ black (mark_black_iff_reachable)
      MSFrame.mark_black_iff_reachable mc_major major_stack major_stack major_fp w_obj;
      assert (is_black w_obj (Mark.mark mc_major major_stack));
      // Black → survives sweep
      MSFrame.black_survives_sweep mc_major major_stack major_stack major_fp w_obj;
      ()
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options


/// ---------------------------------------------------------------------------
/// Property (C): Surjectivity — g_final-reachable has combined pre-image
/// ---------------------------------------------------------------------------

/// Every vertex reachable in g_final has a pre-image under fwd_morphism.
/// This follows directly from iso_surjectivity which now states property (C).
let prove_surjectivity
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (combined_roots: seq combined_vertex)
  (major_stack: seq obj_addr) (major_fp: U64.t)
  : Lemma
    (requires
      iso_surjectivity minor major fp roots combined_roots major_stack major_fp)
    (ensures
      (let prom = cheney_promote minor major fp roots in
       let fwd = prom.fwd_map in
       let res = cheney_collect_spec minor major fp roots in
       let h_final = fst (Sweep.sweep (Mark.mark res.mc_major major_stack) major_fp) in
       let cg = build_combined_graph minor major in
       let g_final = create_graph h_final in
       forall (w: vertex_id).
         Seq.mem w g_final.vertices /\
         (exists (r: obj_addr). Seq.mem r major_stack /\
                                Seq.mem r g_final.vertices /\
                                reachable g_final r w) ==>
         (exists (v: combined_vertex).
           combined_reachable cg combined_roots v /\
           Iso.fwd_morphism fwd v == (w <: U64.t))))
  = ()


/// ---------------------------------------------------------------------------
/// Property (D): Edge biconditional
/// ---------------------------------------------------------------------------

/// Combined edges between reachable vertices ↔ g_final edges between images.
/// Forward: iso_edge_bridge_forward gives mc edge, MSFrame preserves to g_final.
/// Backward: MSFrame shows g_final edge → mc edge, iso_edge_backward gives combined.
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0 --split_queries always"
let prove_edge_biconditional
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (combined_roots: seq combined_vertex)
  (major_stack: seq obj_addr) (major_fp: U64.t)
  : Lemma
    (requires
      iso_structural_preconditions minor major fp roots combined_roots major_stack /\
      iso_edge_bridge_forward minor major fp roots combined_roots major_stack /\
      iso_edge_backward minor major fp roots combined_roots /\
      (let res = cheney_collect_spec minor major fp roots in
       msframe_preconditions res.mc_major major_stack major_fp))
    (ensures
      (let prom = cheney_promote minor major fp roots in
       let fwd = prom.fwd_map in
       let res = cheney_collect_spec minor major fp roots in
       let h_final = fst (Sweep.sweep (Mark.mark res.mc_major major_stack) major_fp) in
       let cg = build_combined_graph minor major in
       let g_final = create_graph h_final in
       forall (u v: combined_vertex).
         combined_reachable cg combined_roots u /\
         combined_reachable cg combined_roots v /\
         (let fu = Iso.fwd_morphism fwd u in
          let fv = Iso.fwd_morphism fwd v in
          U64.v fu < heap_size /\ U64.v fu % U64.v mword == 0 /\
          U64.v fv < heap_size /\ U64.v fv % U64.v mword == 0) ==>
         (mem_ce (u, v) cg <==>
          Seq.mem ((Iso.fwd_morphism fwd u <: hp_addr),
                   (Iso.fwd_morphism fwd v <: hp_addr)) g_final.edges)))
  = let prom = cheney_promote minor major fp roots in
    let fwd = prom.fwd_map in
    let res = cheney_collect_spec minor major fp roots in
    let mc_major = res.mc_major in
    let g_mc = create_graph mc_major in
    let h_final = fst (Sweep.sweep (Mark.mark mc_major major_stack) major_fp) in
    let g_final = create_graph h_final in
    let cg = build_combined_graph minor major in
    let mc_roots_v = HeapGraph.coerce_to_vertex_list major_stack in

    let aux (u v: combined_vertex) : Lemma
      (ensures
        (combined_reachable cg combined_roots u /\
         combined_reachable cg combined_roots v /\
         (let fu = Iso.fwd_morphism fwd u in
          let fv = Iso.fwd_morphism fwd v in
          U64.v fu < heap_size /\ U64.v fu % U64.v mword == 0 /\
          U64.v fv < heap_size /\ U64.v fv % U64.v mword == 0) ==>
         (mem_ce (u, v) cg <==>
          Seq.mem ((Iso.fwd_morphism fwd u <: hp_addr),
                   (Iso.fwd_morphism fwd v <: hp_addr)) g_final.edges)))
    = let fu : U64.t = Iso.fwd_morphism fwd u in
      let fv : U64.t = Iso.fwd_morphism fwd v in
      if not (U64.v fu < heap_size && U64.v fu % U64.v mword = 0 &&
              U64.v fv < heap_size && U64.v fv % U64.v mword = 0) then ()
      else begin
        let fu_hp : hp_addr = fu in
        let fv_hp : hp_addr = fv in
        let inner (_: squash (combined_reachable cg combined_roots u /\
                              combined_reachable cg combined_roots v))
          : Lemma (mem_ce (u, v) cg <==> Seq.mem (fu_hp, fv_hp) g_final.edges) =
          let fu_oa : obj_addr = fu in
          // fu is in g_mc (from iso_structural_preconditions)
          assert (mem_graph_vertex g_mc fu_oa);
          // Eliminate existential to get Seq.mem fu (DFS.reachable_set)
          let elim_root (r: obj_addr) : Lemma
            (requires Seq.mem r major_stack /\ mem_graph_vertex g_mc r /\ reachable g_mc r fu_oa)
            (ensures Seq.mem fu_oa (DFS.reachable_set g_mc mc_roots_v))
          = HeapGraph.coerce_mem_lemma major_stack r;
            DFS.reachable_set_correct g_mc mc_roots_v
          in
          Classical.exists_elim
            (Seq.mem fu_oa (DFS.reachable_set g_mc mc_roots_v))
            #obj_addr
            #(fun r -> Seq.mem r major_stack /\ mem_graph_vertex g_mc r /\ reachable g_mc r fu_oa)
            ()
            (fun (r: obj_addr{Seq.mem r major_stack /\ mem_graph_vertex g_mc r /\ reachable g_mc r fu_oa}) ->
              elim_root r);
          // fu ∈ reachable_set → black after mark → survives sweep
          MSFrame.mark_black_iff_reachable mc_major major_stack major_stack major_fp fu_oa;
          MSFrame.black_survives_sweep mc_major major_stack major_stack major_fp fu_oa;
          MSFrame.mark_sweep_preserves_successors mc_major major_stack major_stack major_fp fu_oa;
          // Edge equivalence from successor equality
          successors_eq_implies_edge_equiv g_mc g_final fu_hp fv_hp
        in
        Classical.impl_intro inner
      end
    in
    Classical.forall_intro_2 aux
#pop-options


/// ---------------------------------------------------------------------------
/// Opaque bundle implementation
/// ---------------------------------------------------------------------------

let iso_preconditions_bundle
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (combined_roots: seq combined_vertex)
  (major_stack: seq obj_addr) (major_fp: U64.t) : prop =
  iso_structural_preconditions minor major fp roots combined_roots major_stack /\
  iso_edge_bridge_forward minor major fp roots combined_roots major_stack /\
  iso_surjectivity minor major fp roots combined_roots major_stack major_fp /\
  iso_edge_backward minor major fp roots combined_roots

let iso_preconditions_bundle_intro
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (combined_roots: seq combined_vertex)
  (major_stack: seq obj_addr) (major_fp: U64.t)
  : Lemma
    (requires
      iso_structural_preconditions minor major fp roots combined_roots major_stack /\
      iso_edge_bridge_forward minor major fp roots combined_roots major_stack /\
      iso_surjectivity minor major fp roots combined_roots major_stack major_fp /\
      iso_edge_backward minor major fp roots combined_roots)
    (ensures
      iso_preconditions_bundle minor major fp roots combined_roots major_stack major_fp)
  = ()

let iso_preconditions_bundle_elim
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (combined_roots: seq combined_vertex)
  (major_stack: seq obj_addr) (major_fp: U64.t)
  : Lemma
    (requires
      iso_preconditions_bundle minor major fp roots combined_roots major_stack major_fp)
    (ensures
      iso_structural_preconditions minor major fp roots combined_roots major_stack /\
      iso_edge_bridge_forward minor major fp roots combined_roots major_stack /\
      iso_surjectivity minor major fp roots combined_roots major_stack major_fp /\
      iso_edge_backward minor major fp roots combined_roots)
  = ()


/// ---------------------------------------------------------------------------
/// Main theorem: 0 admits
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --split_queries always"
let gen_gc_isomorphism
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (combined_roots: seq combined_vertex)
  (major_stack: seq obj_addr) (major_fp: U64.t)
  : Lemma
    (requires
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp /\
      Mark.no_black_objects major /\
      minor_wf minor /\
      // --- Additional standard_gc_preconditions ---
      minor_fields_well_formed minor major roots /\
      all_promotions_succeed minor major fp roots /\
      allocated_objects_avoid_chain major fp /\
      post_promote_pointer_closure minor major fp roots /\
      live_set_no_infix minor (live_set_of minor major roots) /\
      no_scan_invariant major /\
      minor_no_scan_invariant minor /\
      (let live_set = live_set_of minor major roots in
       forall (v: U64.t). Seq.mem v live_set ==> minor_wosize minor v > 0) /\
      // --- Post-Cheney major GC preconditions ---
      (let res = cheney_collect_spec minor major fp roots in
       well_formed_heap res.mc_major /\
       Mark.no_pointer_to_blue res.mc_major /\
       Mark.stack_props res.mc_major major_stack /\
       Mark.root_props res.mc_major major_stack /\
       Sweep.fp_in_heap major_fp res.mc_major /\
       Mark.no_black_objects res.mc_major /\
       no_scan_invariant res.mc_major /\
       (let g = create_graph res.mc_major in
        let rs = HeapGraph.coerce_to_vertex_list major_stack in
        graph_wf g /\ is_vertex_set rs /\ subset_vertices rs g.vertices)) /\
      // --- Isomorphism-specific assumptions ---
      iso_structural_preconditions minor major fp roots combined_roots major_stack /\
      iso_edge_bridge_forward minor major fp roots combined_roots major_stack /\
      iso_surjectivity minor major fp roots combined_roots major_stack major_fp /\
      iso_edge_backward minor major fp roots combined_roots)
    (ensures
      isomorphism_postcondition minor major fp roots combined_roots major_stack major_fp)
  = // Prove each property of reachable_subgraph_isomorphism
    prove_injectivity minor major fp roots combined_roots major_stack;
    prove_image minor major fp roots combined_roots major_stack major_fp;
    prove_surjectivity minor major fp roots combined_roots major_stack major_fp;
    prove_edge_biconditional minor major fp roots combined_roots major_stack major_fp;
    // reachable_implies_forwarded: MinorV v reachable → fwd v ≠ 0
    let cg = build_combined_graph minor major in
    let prom = cheney_promote minor major fp roots in
    let fwd = prom.fwd_map in
    let live_set = live_set_of minor major roots in
    let aux_rif (v: U64.t) : Lemma
      (requires combined_reachable cg combined_roots (MinorV v))
      (ensures fwd v <> 0UL)
    = // reachability_bridge: combined-reachable minor → in live_set
      assert (Seq.mem v live_set);
      // live_set members have wosize > 0 → fwd ≠ 0 (promotion succeeded)
      ()
    in
    Classical.forall_intro (Classical.move_requires aux_rif)
#pop-options


/// ---------------------------------------------------------------------------
/// Pulse-safe bridge: opaque bundle → opaque postcondition
/// ---------------------------------------------------------------------------

let gen_gc_isomorphism_opaque
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (combined_roots: seq combined_vertex)
  (major_stack: seq obj_addr) (major_fp: U64.t)
  : Lemma
    (requires
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp /\
      Mark.no_black_objects major /\
      minor_wf minor /\
      minor_fields_well_formed minor major roots /\
      all_promotions_succeed minor major fp roots /\
      allocated_objects_avoid_chain major fp /\
      post_promote_pointer_closure minor major fp roots /\
      live_set_no_infix minor (live_set_of minor major roots) /\
      no_scan_invariant major /\
      minor_no_scan_invariant minor /\
      (let live_set = live_set_of minor major roots in
       forall (v: U64.t). Seq.mem v live_set ==> minor_wosize minor v > 0) /\
      (let res = cheney_collect_spec minor major fp roots in
       well_formed_heap res.mc_major /\
       Mark.no_pointer_to_blue res.mc_major /\
       Mark.stack_props res.mc_major major_stack /\
       Mark.root_props res.mc_major major_stack /\
       Sweep.fp_in_heap major_fp res.mc_major /\
       Mark.no_black_objects res.mc_major /\
       no_scan_invariant res.mc_major /\
       (let g = create_graph res.mc_major in
        let rs = HeapGraph.coerce_to_vertex_list major_stack in
        graph_wf g /\ is_vertex_set rs /\ subset_vertices rs g.vertices)) /\
      iso_preconditions_bundle minor major fp roots combined_roots major_stack major_fp)
    (ensures
      isomorphism_postcondition minor major fp roots combined_roots major_stack major_fp)
  = iso_preconditions_bundle_elim minor major fp roots combined_roots major_stack major_fp;
    gen_gc_isomorphism minor major fp roots combined_roots major_stack major_fp
