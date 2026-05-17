/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph.Isomorphism.Discharge — Implementation
/// ---------------------------------------------------------------------------
///
/// Bridges mc_major-level assumptions to g_final-level preconditions
/// using MarkSweepFrame, then calls the main isomorphism theorem.

module GC.Gen.CombinedGraph.Isomorphism.Discharge

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
open GC.Gen.Correctness
open GC.Gen.Allocator

module HeapGraph = GC.Spec.HeapGraph
module AllocLemmas = GC.Spec.Allocator.Lemmas
module Mark = GC.Spec.Mark
module Sweep = GC.Spec.Sweep
module DFS = GC.Spec.DFS
module MajorCorrectness = GC.Spec.Correctness
module MSFrame = GC.Gen.CombinedGraph.MarkSweepFrame
module Iso = GC.Gen.CombinedGraph.Isomorphism


/// ---------------------------------------------------------------------------
/// NOTE: The allocator framing lemma (showing that promotion preserves
/// existing non-blue major objects — membership, wosize, color, no_scan)
/// is needed for the full end-to-end wrapper but lives in the Allocator
/// infrastructure, not here. See GC.Spec.Allocator.Lemmas for the building
/// blocks: fl_valid_preserved, chain_avoids, promote_preserves_objects, etc.
/// ---------------------------------------------------------------------------


/// ---------------------------------------------------------------------------
/// Helper: bridge surjectivity from mc_major to g_final
/// ---------------------------------------------------------------------------
///
/// If every mc-reachable vertex has a combined pre-image, then every
/// g_final-reachable vertex also has a combined pre-image.
///
/// Proof strategy (induction on reachability path in g_final):
///   Base: root r ∈ major_roots → r ∈ DFS.reachable_set g_mc → pre-image
///   Step: w reachable via (x, w) edge in g_final, x already mc-reachable
///     → mark_black_iff_reachable: x black in h_mark
///     → black_survives_sweep: x in g_final.vertices
///     → mark_sweep_preserves_successors: successors g_mc x == successors g_final x
///     → (x, w) edge in g_mc → w mc-reachable
///     → surjectivity_at_mc: w has pre-image

/// Helper: given reach g_final r w, prove w ∈ DFS.reachable_set g_mc mc_roots_v
/// by induction on the reach derivation.
///
/// At each step:
///   - IH gives source is in mc reachable set
///   - mark_black_iff_reachable → source is black after mark
///   - mark_sweep_preserves_successors → edge preserved from g_mc
///   - reachable_successor_closed → target also in mc reachable set
private let rec final_reach_implies_mc_reachable
  (h_mc: heap) (major_stack: seq obj_addr) (major_roots: seq obj_addr) (major_fp: U64.t)
  (g_mc: graph_state) (g_final: graph_state) (mc_roots_v: vertex_set)
  (r: vertex_id{mem_graph_vertex g_final r})
  (w: vertex_id{mem_graph_vertex g_final w})
  (p: reach g_final r w)
  : Lemma
    (requires
      g_mc == create_graph h_mc /\
      g_final == create_graph (fst (Sweep.sweep (Mark.mark h_mc major_stack) major_fp)) /\
      mc_roots_v == HeapGraph.coerce_to_vertex_list major_roots /\
      well_formed_heap h_mc /\
      Mark.stack_props h_mc major_stack /\
      Mark.root_props h_mc major_roots /\
      Sweep.fp_in_heap major_fp h_mc /\
      Mark.no_black_objects h_mc /\
      Mark.no_pointer_to_blue h_mc /\
      (forall (r: obj_addr). Seq.mem r major_roots <==> Seq.mem r major_stack) /\
      graph_wf g_mc /\ is_vertex_set mc_roots_v /\ subset_vertices mc_roots_v g_mc.vertices /\
      // Root is in mc reachable set
      Seq.mem r (DFS.reachable_set g_mc mc_roots_v))
    (ensures Seq.mem w (DFS.reachable_set g_mc mc_roots_v))
    (decreases p)
  = match p with
    | ReachRefl _ -> ()
    | ReachTrans _ y z p' ->
      // IH: y is in mc reachable set
      final_reach_implies_mc_reachable h_mc major_stack major_roots major_fp
        g_mc g_final mc_roots_v r y p';
      // y is a graph vertex of g_final = create_graph h_sweep
      // Since vertices = coerce_to_vertex_list (objects zero_addr h_sweep),
      // y ∈ coerce_to_vertex_list → U64.v y >= U64.v mword
      let h_sweep = fst (Sweep.sweep (Mark.mark h_mc major_stack) major_fp) in
      HeapGraph.coerce_mem_is_obj_addr (objects zero_addr h_sweep) y;
      let y_obj : obj_addr = y in
      // y is mc-reachable → y ∈ g_mc.vertices
      // (reachable_set only contains graph vertices)
      DFS.reachable_set_correct g_mc mc_roots_v;
      assert (mem_graph_vertex g_mc y_obj);
      // y is mc-reachable → y is black after mark
      MSFrame.mark_black_iff_reachable h_mc major_stack major_roots major_fp y_obj;
      // y black → y survives sweep
      MSFrame.black_survives_sweep h_mc major_stack major_roots major_fp y_obj;
      // mark_sweep_preserves_successors → edges preserved
      MSFrame.mark_sweep_preserves_successors h_mc major_stack major_roots major_fp y_obj;
      // (y, z) is an edge in g_final → z ∈ successors g_final y = successors g_mc y
      edge_mem_successors g_final y z;
      successors_mem_edge g_mc y z;
      // z is also a vertex in g_final → z is an obj_addr
      HeapGraph.coerce_mem_is_obj_addr (objects zero_addr h_sweep) z;
      let z_obj : obj_addr = z in
      // (y, z) edge in g_mc + graph_wf → z is a vertex of g_mc
      assert (mem_graph_vertex g_mc z_obj);
      // z ∈ g_mc edges → z ∈ mc reachable set (successor closure)
      DFS.reachable_successor_closed g_mc mc_roots_v y_obj z_obj

private let surjectivity_mc_to_final
  (gs: gen_state) (roots: seq U64.t) (fp: U64.t)
  (combined_roots: seq combined_vertex)
  (major_roots: seq obj_addr) (major_stack: seq obj_addr) (major_fp: U64.t)
  (w: vertex_id)
  : Lemma
    (requires
      standard_gc_preconditions gs roots fp major_roots major_stack major_fp /\
      surjectivity_at_mc gs roots fp combined_roots major_roots major_stack major_fp /\
      (let h_final = Iso.post_gc_heap gs.gs_minor gs.gs_major fp roots major_stack major_fp in
       let g_final = create_graph h_final in
       Seq.mem w g_final.vertices /\
       (exists (r: obj_addr). Seq.mem r major_roots /\
                              Seq.mem r g_final.vertices /\
                              reachable g_final r w)))
    (ensures
      (let cg = build_combined_graph gs.gs_minor gs.gs_major in
       let live_set = live_set_of gs.gs_minor gs.gs_major roots in
       let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
       exists (v: combined_vertex).
         combined_reachable cg combined_roots v /\
         Iso.fwd_morphism prom_res.fwd_map v == (w <: U64.t)))
  = let mc = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
    let h_mc = mc.mc_major in
    let h_mark = Mark.mark h_mc major_stack in
    let h_sweep = fst (Sweep.sweep h_mark major_fp) in
    let g_mc = create_graph h_mc in
    let g_final = create_graph h_sweep in
    let mc_roots_v = HeapGraph.coerce_to_vertex_list major_roots in

    // First: need the root r to be in DFS.reachable_set g_mc
    DFS.reachable_set_correct g_mc mc_roots_v;

    // Helper: given a specific root r with the right refinements,
    // prove w ∈ reachable_set g_mc mc_roots_v
    let prove_w_mc_reachable (r: obj_addr)
      : Lemma
        (requires
          Seq.mem r major_roots /\
          mem_graph_vertex g_final r /\
          reachable g_final r w)
        (ensures Seq.mem w (DFS.reachable_set g_mc mc_roots_v))
      = // Extract reach witness from reachable g_final r w
        let p_witness : reach g_final r w =
          FStar.IndefiniteDescription.indefinite_description_ghost
            (reach g_final r w) (fun _ -> True)
        in
        // r ∈ major_roots → r ∈ mc_roots_v → r ∈ reachable_set g_mc
        HeapGraph.coerce_mem_lemma major_roots r;
        // Call recursive helper
        final_reach_implies_mc_reachable h_mc major_stack major_roots major_fp
          g_mc g_final mc_roots_v r w p_witness
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires prove_w_mc_reachable);

    // Now we know: for all r, if r is a root with reachable g_final r w,
    // then w ∈ reachable_set g_mc. From our precondition, such r exists.
    assert (Seq.mem w (DFS.reachable_set g_mc mc_roots_v));

    // w is a vertex of g_final → w is an obj_addr
    HeapGraph.coerce_mem_is_obj_addr (objects zero_addr h_sweep) w;
    let w_obj : obj_addr = w in

    // w ∈ reachable_set g_mc + surjectivity_at_mc → pre-image
    assert (mem_graph_vertex g_mc w_obj);
    assert (surjectivity_at_mc gs roots fp combined_roots major_roots major_stack major_fp)


/// ---------------------------------------------------------------------------
/// Helper: bridge edge backward from mc_major to g_final
/// ---------------------------------------------------------------------------
///
/// Proof strategy (no color analysis needed):
///   1. u combined-reachable → morphism image preservation → fu reachable in g_mc
///   2. mark_black_iff_reachable → fu black after mark
///   3. black_survives_sweep → fu in g_final.vertices
///   4. mark_sweep_preserves_successors → successors g_mc fu == successors g_final fu
///   5. (fu, fv) edge in g_final → (fu, fv) edge in g_mc
///   6. edge_backward_at_mc → combined edge (u, v)

private let edge_backward_mc_to_final
  (gs: gen_state) (roots: seq U64.t) (fp: U64.t)
  (combined_roots: seq combined_vertex)
  (major_roots: seq obj_addr) (major_stack: seq obj_addr) (major_fp: U64.t)
  (u v: combined_vertex)
  : Lemma
    (requires
      standard_gc_preconditions gs roots fp major_roots major_stack major_fp /\
      structural_preconditions gs roots fp combined_roots major_roots /\
      edge_backward_at_mc gs roots fp combined_roots /\
      combined_reachable (build_combined_graph gs.gs_minor gs.gs_major) combined_roots u /\
      combined_reachable (build_combined_graph gs.gs_minor gs.gs_major) combined_roots v /\
      (let live_set = live_set_of gs.gs_minor gs.gs_major roots in
       let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
       let fwd = prom_res.fwd_map in
       let h_final = Iso.post_gc_heap gs.gs_minor gs.gs_major fp roots major_stack major_fp in
       let g_final = create_graph h_final in
       let fu = Iso.fwd_morphism fwd u in
       let fv = Iso.fwd_morphism fwd v in
       U64.v fu < heap_size /\ U64.v fu % U64.v mword == 0 /\
       U64.v fv < heap_size /\ U64.v fv % U64.v mword == 0 /\
       Seq.mem ((fu <: hp_addr), (fv <: hp_addr)) g_final.edges))
    (ensures
      mem_ce (u, v) (build_combined_graph gs.gs_minor gs.gs_major))
  = // Unpack
    let mc = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
    let h_mc = mc.mc_major in
    let h_mark = Mark.mark h_mc major_stack in
    let h_sweep = fst (Sweep.sweep h_mark major_fp) in
    let g_mc = create_graph h_mc in
    let g_final = create_graph h_sweep in
    let mc_roots_v = HeapGraph.coerce_to_vertex_list major_roots in
    let live_set = live_set_of gs.gs_minor gs.gs_major roots in
    let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
    let fu = Iso.fwd_morphism prom_res.fwd_map u in
    let fv = Iso.fwd_morphism prom_res.fwd_map v in

    // Step 1: From structural_preconditions, morphism image preservation gives
    // fu reachable from major_roots in g_mc
    assert (mem_graph_vertex g_mc (fu <: obj_addr));

    // Step 2: reachable from root → in DFS.reachable_set
    DFS.reachable_set_correct g_mc mc_roots_v;
    // Bridge: existential root in major_roots → root in mc_roots_v
    let bridge_reachable (r: obj_addr) : Lemma
      (requires
        Seq.mem r major_roots /\
        mem_graph_vertex g_mc r /\
        reachable g_mc r (fu <: obj_addr))
      (ensures Seq.mem (fu <: obj_addr) (DFS.reachable_set g_mc mc_roots_v))
    = HeapGraph.coerce_mem_lemma major_roots r
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires bridge_reachable);
    assert (Seq.mem (fu <: obj_addr) (DFS.reachable_set g_mc mc_roots_v));

    // Step 3: mark_black_iff_reachable → fu black after mark
    MSFrame.mark_black_iff_reachable h_mc major_stack major_roots major_fp (fu <: obj_addr);
    assert (is_black (fu <: obj_addr) h_mark);

    // Step 4: black_survives_sweep → fu in g_final.vertices
    MSFrame.black_survives_sweep h_mc major_stack major_roots major_fp (fu <: obj_addr);
    assert (Seq.mem (fu <: obj_addr) g_final.vertices);

    // Step 5: mark_sweep_preserves_successors → successors preserved
    MSFrame.mark_sweep_preserves_successors h_mc major_stack major_roots major_fp (fu <: obj_addr);
    assert (successors g_mc (fu <: obj_addr) == successors g_final (fu <: obj_addr));

    // Step 6: g_final edge → fv ∈ successors g_final fu → fv ∈ successors g_mc fu
    // → (fu, fv) edge in g_mc
    edge_mem_successors g_final (fu <: hp_addr) (fv <: hp_addr);
    assert (Seq.mem (fv <: hp_addr) (successors g_final (fu <: hp_addr)));
    assert (Seq.mem (fv <: hp_addr) (successors g_mc (fu <: hp_addr)));
    successors_mem_edge g_mc (fu <: hp_addr) (fv <: hp_addr);
    assert (Seq.mem ((fu <: hp_addr), (fv <: hp_addr)) g_mc.edges);

    // Step 7: edge_backward_at_mc → combined edge
    ()


/// ---------------------------------------------------------------------------
/// Main composition
/// ---------------------------------------------------------------------------

let isomorphism_from_gc
  (gs: gen_state) (roots: seq U64.t) (fp: U64.t)
  (combined_roots: seq combined_vertex)
  (major_roots: seq obj_addr) (major_stack: seq obj_addr) (major_fp: U64.t)
  : Lemma
    (requires
      standard_gc_preconditions gs roots fp major_roots major_stack major_fp /\
      structural_preconditions gs roots fp combined_roots major_roots /\
      edge_bridge_forward_at_mc gs roots fp combined_roots /\
      surjectivity_at_mc gs roots fp combined_roots major_roots major_stack major_fp /\
      edge_backward_at_mc gs roots fp combined_roots)
    (ensures
      (let live_set = live_set_of gs.gs_minor gs.gs_major roots in
       let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
       let fwd = prom_res.fwd_map in
       let h_final = Iso.post_gc_heap gs.gs_minor gs.gs_major fp roots major_stack major_fp in
       Iso.reachable_implies_forwarded (Iso.pre_gc_graph gs.gs_minor gs.gs_major)
                                       combined_roots fwd /\
       Iso.reachable_subgraph_isomorphism gs.gs_minor gs.gs_major fwd
                                          combined_roots h_final major_roots))
  = // Step 1: Edge bridge forward passes through directly
    // (Already at mc_major level, which is what the main theorem wants)

    // Step 2: Derive surjectivity at g_final from surjectivity at mc
    let h_final = Iso.post_gc_heap gs.gs_minor gs.gs_major fp roots major_stack major_fp in
    let g_final = create_graph h_final in
    let derive_surjectivity (w: vertex_id) : Lemma
      (requires
        Seq.mem w g_final.vertices /\
        (exists (r: obj_addr). Seq.mem r major_roots /\
                               Seq.mem r g_final.vertices /\
                               reachable g_final r w))
      (ensures
        (let cg = build_combined_graph gs.gs_minor gs.gs_major in
         let live_set = live_set_of gs.gs_minor gs.gs_major roots in
         let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
         exists (v: combined_vertex).
           combined_reachable cg combined_roots v /\
           Iso.fwd_morphism prom_res.fwd_map v == (w <: U64.t)))
    = surjectivity_mc_to_final gs roots fp combined_roots major_roots major_stack major_fp w
    in
    FStar.Classical.forall_intro (
      FStar.Classical.move_requires derive_surjectivity
    );

    // Step 3: Derive edge backward at g_final from edge backward at mc
    // We introduce the universally quantified fact by calling the admitted helper
    // for each pair, using introduce/forall/with syntax.
    introduce forall (u: combined_vertex) (v: combined_vertex).
      combined_reachable (build_combined_graph gs.gs_minor gs.gs_major) combined_roots u /\
      combined_reachable (build_combined_graph gs.gs_minor gs.gs_major) combined_roots v /\
      (let live_set = live_set_of gs.gs_minor gs.gs_major roots in
       let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
       let fu = Iso.fwd_morphism prom_res.fwd_map u in
       let fv = Iso.fwd_morphism prom_res.fwd_map v in
       U64.v fu < heap_size /\ U64.v fu % U64.v mword == 0 /\
       U64.v fv < heap_size /\ U64.v fv % U64.v mword == 0 /\
       Seq.mem ((fu <: hp_addr), (fv <: hp_addr)) g_final.edges)
      ==> mem_ce (u, v) (build_combined_graph gs.gs_minor gs.gs_major)
    with introduce _ ==> _
    with _. edge_backward_mc_to_final gs roots fp combined_roots major_roots major_stack major_fp u v;

    // Step 4: Now all 3 preconditions of the main theorem are satisfied.
    // Call it to get the isomorphism.
    Iso.generational_gc_isomorphism gs roots fp combined_roots major_roots major_stack major_fp
