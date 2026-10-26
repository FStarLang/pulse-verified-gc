/// ---------------------------------------------------------------------------
/// GC.Spec.Correctness - End-to-End GC Correctness
/// ---------------------------------------------------------------------------
///
/// Defines abstract GC postcondition predicates and proves the full
/// end-to-end correctness theorem with 5 pillars.
///
/// Colors used: White (initial/free), Gray (mark frontier), Black (marked/reachable).
/// After mark: black = reachable, white = unreachable, no gray.
/// After sweep: all objects white (black reset to white, white unchanged).

module GC.Spec.Correctness

#set-options "--z3rlimit 12 --fuel 2 --ifuel 1"

open FStar.Seq

module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Graph
open GC.Spec.Fields
open GC.Spec.HeapModel
open GC.Spec.Mark
open GC.Spec.DFS
module HeapGraph = GC.Spec.HeapGraph
module SweepInv = GC.Spec.SweepInv
module FL = GC.Spec.FreeList
module MarkInv = GC.Spec.MarkInv
module FS = GC.Spec.FusedSweep
module FSI = GC.Spec.FusedSweep.Inv
module FSE = GC.Spec.FusedSweep.End
module FLA = GC.Spec.FreeList.Ascending

/// ---------------------------------------------------------------------------
/// Abstract GC Postcondition (Pillars 1 + 4)
/// ---------------------------------------------------------------------------

let gc_postcondition (h_final: heap) : prop =
  well_formed_heap h_final /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr h_final) ==>
    is_white x h_final \/ is_blue x h_final)

let no_gray_or_black_objects (h_final: heap) : prop =
  forall (x: obj_addr). Seq.mem x (objects zero_addr h_final) ==>
    is_white x h_final \/ is_blue x h_final

let gc_postcondition_intro h_final = ()

let gc_postcondition_from_parts h_final = ()

let gc_postcondition_elim h_final = ()

/// ---------------------------------------------------------------------------
/// Full GC Correctness -- All 5 pillars
/// ---------------------------------------------------------------------------

/// The five pillars, for a given marked heap.
let fgc_pillars (h_init h_mark h_final: heap) (roots: seq obj_addr) : prop =
  (let g_init = create_graph h_init in
   let g_final = create_graph h_final in
   let roots' = HeapGraph.coerce_to_vertex_list roots in
   // Pillar 1
   well_formed_heap h_final /\
   // Pillar 2
   (graph_wf g_init /\ is_vertex_set roots' /\ subset_vertices roots' g_init.vertices ==>
     (forall (x: obj_addr). mem_graph_vertex g_init x ==>
       (is_black x h_mark <==> Seq.mem x (reachable_set g_init roots')))) /\
   // Pillar 3
   (forall (x: obj_addr).
     Seq.mem x g_final.vertices /\ is_black x h_mark ==>
     successors g_init x == successors g_final x) /\
   // Pillar 4
   (forall (x: obj_addr).
     Seq.mem x g_final.vertices ==>
     (is_white x h_final \/ is_blue x h_final)) /\
   (forall (x: obj_addr).
     Seq.mem x g_final.vertices /\ is_black x h_mark ==>
     is_white x h_final) /\
   // Pillar 5
   (forall (x: obj_addr) (i: U64.t).
     Seq.mem x g_final.vertices /\ is_black x h_mark /\
     U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x h_init) ==>
     HeapGraph.get_field h_init x i == HeapGraph.get_field h_final x i))

let full_gc_correctness (h_init h_final: heap) (roots: seq obj_addr) : prop =
  exists (h_mark: heap). fgc_pillars h_init h_mark h_final roots

let full_gc_correctness_intro h_init h_mark h_final roots = ()

let full_gc_correctness_elim_wfh h_init h_final roots = ()

let full_gc_correctness_elim_colors h_init h_final roots =
  let aux () : Lemma
    (requires full_gc_correctness h_init h_final roots)
    (ensures well_formed_heap h_final /\
             (forall (x: obj_addr). Seq.mem x (objects zero_addr h_final) ==>
               is_white x h_final \/ is_blue x h_final))
  = let bridge (x: obj_addr) : Lemma
      (Seq.mem x (objects zero_addr h_final) <==> Seq.mem x (create_graph h_final).vertices)
    = graph_vertices_mem h_final x
    in
    FStar.Classical.forall_intro bridge
  in
  aux ();
  gc_postcondition_intro h_final

let gc_completeness h_init st roots fp =
  mark_black_is_reachable h_init st roots

/// Helper: no_black_objects implies tri_color_invariant (vacuously true)
let no_black_implies_tri_color (g: heap) : Lemma
  (requires no_black_objects g)
  (ensures tri_color_invariant g)
= ()

/// ===========================================================================
/// Generalized Mark Postcondition and Bridges
/// ===========================================================================

/// Bundle of properties that any correct mark algorithm must establish
let mark_post (h_init h_mark: heap) (roots: seq obj_addr) (fp: U64.t) : prop =
  well_formed_heap h_init /\ well_formed_heap h_mark /\
  noGreyObjects h_mark /\
  objects zero_addr h_mark == objects zero_addr h_init /\
  heap_objects_dense h_mark /\
  Seq.length (objects zero_addr h_mark) > 0 /\
  no_pointer_to_blue h_mark /\
  tri_color_invariant h_mark /\
  FL.fp_in_heap fp h_init /\
  no_black_objects h_init /\
  no_pointer_to_blue h_init /\
  (let g_init = create_graph h_init in
   let roots' = HeapGraph.coerce_to_vertex_list roots in
   graph_wf g_init /\ is_vertex_set roots' /\ subset_vertices roots' g_init.vertices ==>
   (forall (x: obj_addr). mem_graph_vertex g_init x ==>
     (is_black x h_mark <==> Seq.mem x (reachable_set g_init roots')))) /\
  create_graph h_mark == create_graph h_init /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr h_init) ==>
    wosize_of_object x h_mark == wosize_of_object x h_init) /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr h_init) ==>
    is_blue x h_mark == is_blue x h_init) /\
  (forall (x: obj_addr) (i: U64.t). Seq.mem x (objects zero_addr h_init) /\
    U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x h_init) ==>
    HeapGraph.get_field h_mark x i == HeapGraph.get_field h_init x i)

let mark_post_intro h_init h_mark roots fp = ()
let mark_post_elim_wfh h_init h_mark roots fp = ()
let mark_post_elim_no_grey h_init h_mark roots fp = ()
let mark_post_elim_objects h_init h_mark roots fp = ()
let mark_post_elim_tri_color h_init h_mark roots fp = ()
let mark_post_elim_no_pointer_to_blue h_init h_mark roots fp = ()
let mark_post_elim_graph h_init h_mark roots fp = ()
let mark_post_elim_density h_init h_mark roots fp = ()
let mark_post_elim_objects_gt0 h_init h_mark roots fp = ()
let mark_post_elim_fp h_init h_mark roots fp =
  assert (objects zero_addr h_mark == objects zero_addr h_init);
  assert (FL.fp_in_heap fp h_init);
  // fp_in_heap depends on objects; since objects are the same, fp_in_heap transfers
  ()

let mark_post_elim_blue h_init h_mark roots fp = ()

/// `mark h_init st` satisfies mark_post
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let mark_satisfies_mark_post h_init st roots fp =
  let h_mark = mark h_init st in
  GC.Spec.MarkInv.mark_inv_elim_wfh h_init st;
  GC.Spec.MarkInv.mark_inv_elim_sp h_init st;
  GC.Spec.MarkInv.mark_inv_elim_density h_init st;
  GC.Spec.MarkInv.mark_inv_elim_objects h_init st;
  mark_preserves_wf h_init st;
  mark_no_grey_remains h_init st;
  mark_aux_preserves_objects h_init st heap_words;
  // density and objects > 0 for h_mark
  mark_preserves_density h_init st;
  mark_preserves_objects_gt0 h_init st;
  // no_pointer_to_blue
  mark_preserves_no_pointer_to_blue h_init st;
  // tri_color
  no_black_implies_tri_color h_init;
  mark_preserves_tri_color h_init st;
  // reachability
  mark_reachable_is_black h_init st roots;
  mark_black_is_reachable h_init st roots;
  // graph structure
  mark_preserves_create_graph h_init st;
  // wosize preservation
  let aux_ws (x: obj_addr) : Lemma
    (requires Seq.mem x (objects zero_addr h_init))
    (ensures wosize_of_object x h_mark == wosize_of_object x h_init)
  = mark_preserves_wosize h_init st x
  in FStar.Classical.forall_intro (FStar.Classical.move_requires aux_ws);
  // field preservation
  let aux_field (x: obj_addr) (i: U64.t) : Lemma
    (Seq.mem x (objects zero_addr h_init) /\
     U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x h_init) ==>
     HeapGraph.get_field h_mark x i == HeapGraph.get_field h_init x i)
  = if Seq.mem x (objects zero_addr h_init) && U64.v i >= 1 && U64.v i <= U64.v (wosize_of_object x h_init)
    then mark_preserves_get_field h_init st x i
    else ()
  in
  FStar.Classical.forall_intro_2 aux_field;
  // free blocks stay free, and nothing else becomes free
  let aux_blue (x: obj_addr) : Lemma
    (requires Seq.mem x (objects zero_addr h_init))
    (ensures is_blue x h_mark == is_blue x h_init)
  = if is_blue x h_init then mark_preserves_blue h_init st x
    else mark_no_new_blue h_init st x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux_blue);
  mark_post_intro h_init h_mark roots fp
#pop-options


#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
private let rec coerce_mem_is_obj_addr (s: seq obj_addr) (x: vertex_id)
  : Lemma
    (requires Seq.mem x (HeapGraph.coerce_to_vertex_list s))
    (ensures U64.v x >= U64.v mword)
    (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      mem_cons_lemma x (Seq.head s) (HeapGraph.coerce_to_vertex_list (Seq.tail s));
      if x = Seq.head s then ()
      else coerce_mem_is_obj_addr (Seq.tail s) x
    end

private let heap_graph_vertex_is_obj_addr (h: heap) (x: vertex_id)
  : Lemma
    (requires mem_graph_vertex (create_graph h) x)
    (ensures U64.v x >= U64.v mword)
  = coerce_mem_is_obj_addr (objects zero_addr h) x

private let root_heap_reachable
  (h: heap) (roots: seq obj_addr) (r: obj_addr)
  : Lemma
    (requires
      (let g = create_graph h in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf g /\ is_vertex_set roots' /\ subset_vertices roots' g.vertices /\
       Seq.mem r roots))
    (ensures heap_reachable h roots r)
  = let g = create_graph h in
    let roots' = HeapGraph.coerce_to_vertex_list roots in
    HeapGraph.coerce_mem_lemma roots r;
    assert (Seq.mem r roots');
    assert (mem_graph_vertex g r);
    assert (Seq.mem r (reachable_set g roots'))

private let roots_subset_coal_from_iso
  (h_init h_coal: heap) (roots: seq obj_addr)
  : Lemma
    (requires
      (let g_init = create_graph h_init in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf g_init /\ is_vertex_set roots' /\ subset_vertices roots' g_init.vertices) /\
      major_gc_live_subgraph_isomorphism h_init h_coal roots)
    (ensures subset_vertices (HeapGraph.coerce_to_vertex_list roots) (create_graph h_coal).vertices)
  = let roots' = HeapGraph.coerce_to_vertex_list roots in
    let aux (v: vertex_id) : Lemma
      (Seq.mem v roots' ==> Seq.mem v (create_graph h_coal).vertices)
    = if Seq.mem v roots' then begin
        coerce_mem_is_obj_addr roots v;
        let r: obj_addr = v in
        HeapGraph.coerce_mem_lemma roots r;
        assert (Seq.mem r roots);
        root_heap_reachable h_init roots r;
        assert (Seq.mem r (objects zero_addr h_coal));
        graph_vertices_mem h_coal r
      end
    in
    FStar.Classical.forall_intro aux

private let rec reach_transfer_init_to_coal
  (h_init h_coal: heap) (roots: seq obj_addr)
  (r: vertex_id{mem_graph_vertex (create_graph h_init) r /\
                mem_graph_vertex (create_graph h_coal) r})
  (x: vertex_id{mem_graph_vertex (create_graph h_init) x /\
                mem_graph_vertex (create_graph h_coal) x})
  (p: reach (create_graph h_init) r x)
  : Lemma
    (requires
      (let g_init = create_graph h_init in
       let g_coal = create_graph h_coal in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf g_init /\ is_vertex_set roots' /\ subset_vertices roots' g_init.vertices /\
       graph_wf g_coal /\ subset_vertices roots' g_coal.vertices /\
       Seq.mem r roots') /\
      major_gc_live_subgraph_isomorphism h_init h_coal roots)
    (ensures reachable (create_graph h_coal) r x)
    (decreases p)
  = let g_init = create_graph h_init in
    let g_coal = create_graph h_coal in
    let roots' = HeapGraph.coerce_to_vertex_list roots in
    match p with
    | ReachRefl _ ->
      reach_refl g_coal r
    | ReachTrans _ y z py ->
      heap_graph_vertex_is_obj_addr h_init y;
      heap_graph_vertex_is_obj_addr h_init z;
      let yy: obj_addr = y in
      let zz: obj_addr = z in
      // y is reachable in the initial graph since r is a root and r reaches y.
      FStar.Classical.exists_intro (fun (_: reach g_init r y) -> True) py;
      assert (reachable g_init r y);
      assert (Seq.mem r roots');
      reachable_set_correct g_init roots';
      assert (Seq.mem y (reachable_set g_init roots'));
      assert (Seq.mem yy (reachable_set g_init roots'));
      assert (heap_reachable h_init roots yy);
      reachable_successor_closed g_init roots' yy zz;
      assert (heap_reachable h_init roots zz);
      assert (heap_edge h_init yy zz);
      assert (heap_edge h_coal yy zz);
      assert (Seq.mem yy (objects zero_addr h_coal));
      assert (Seq.mem zz (objects zero_addr h_coal));
      graph_vertices_mem h_coal yy;
      graph_vertices_mem h_coal zz;
      assert (mem_graph_vertex g_coal y);
      assert (mem_graph_vertex g_coal z);
      reach_transfer_init_to_coal h_init h_coal roots r yy py;
      edge_reach g_coal yy zz;
      reach_trans g_coal r yy zz

private let heap_reachable_transfer_init_to_coal
  (h_init h_coal: heap) (roots: seq obj_addr) (x: obj_addr)
  : Lemma
    (requires
      (let g_init = create_graph h_init in
       let g_coal = create_graph h_coal in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf g_init /\ is_vertex_set roots' /\ subset_vertices roots' g_init.vertices /\
       graph_wf g_coal /\ subset_vertices roots' g_coal.vertices) /\
      major_gc_live_subgraph_isomorphism h_init h_coal roots /\
      heap_reachable h_init roots x)
    (ensures heap_reachable h_coal roots x)
  = let g_init = create_graph h_init in
    let g_coal = create_graph h_coal in
    let roots' = HeapGraph.coerce_to_vertex_list roots in
    reachable_set_correct g_init roots';
    assert (Seq.mem x (objects zero_addr h_coal));
    graph_vertices_mem h_coal x;
    let goal () : Lemma (Seq.mem x (reachable_set g_coal roots')) =
      FStar.Classical.exists_elim
        (Seq.mem x (reachable_set g_coal roots'))
        #_
        #(fun (r: vertex_id{mem_graph_vertex g_init r}) ->
            Seq.mem r roots' /\ reachable g_init r x)
        ()
        (fun r ->
          let finish (p: reach g_init r x) : Lemma
            (requires True)
            (ensures Seq.mem x (reachable_set g_coal roots'))
          = assert (mem_graph_vertex g_coal r);
            reach_transfer_init_to_coal h_init h_coal roots r x p;
            reachable_set_correct g_coal roots';
            assert (Seq.mem x (reachable_set g_coal roots'))
          in
          FStar.Classical.forall_intro finish)
    in
    goal ()
#pop-options

#push-options "--z3rlimit 25 --fuel 0 --ifuel 0"
let gc_coalesce_source_intro h_init h_mark roots fp s2 final_fp = ()
#pop-options

/// ---------------------------------------------------------------------------
/// The theorems, at the heap the fused sweep produces
/// ---------------------------------------------------------------------------

/// Marking keeps every free block, its size and its link, so it keeps the list.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let mark_post_sweep_pre h_init h_mark roots fp =
  let cells (x: U64.t) : Lemma (FL.fl_cell h_mark x <==> FL.fl_cell h_init x) = () in
  FStar.Classical.forall_intro cells;
  let links (x: U64.t)
    : Lemma (requires FL.fl_cell h_init x) (ensures FL.fl_next h_mark x == FL.fl_next h_init x)
    = FLA.fl_cell_facts h_init x;
      let o : obj_addr = x in
      hd_address_spec o;
      assert_norm (1 < pow2 54);
      HeapGraph.get_field_addr_eq h_mark o 1UL;
      HeapGraph.get_field_addr_eq h_init o 1UL;
      assert (HeapGraph.get_field h_mark o 1UL == HeapGraph.get_field h_init o 1UL)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires links);
  FLA.fl_ascending_transfer h_init h_mark fp
#pop-options

let fused_post_gen h_init h_mark roots fp =
  mark_post_sweep_pre h_init h_mark roots fp;
  FSE.fused_sweep_post h_mark fp;
  let r = FS.fused_sweep_coalesce h_mark fp in
  FSE.sweep_post_wf h_mark (fst r) (snd r)

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let gc_postcondition_fused h_init h_mark roots fp =
  fused_post_gen h_init h_mark roots fp;
  let r = FS.fused_sweep_coalesce h_mark fp in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires (FSE.sweep_post_white_or_blue h_mark (fst r) (snd r)));
  gc_postcondition_intro (fst r)
#pop-options

/// The five pillars at the fused result, with the marked heap as witness.
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
private let fgc_pillars_fused (h_init h_mark: heap) (roots: seq obj_addr) (fp: U64.t)
  : Lemma (requires mark_post h_init h_mark roots fp /\ FLA.fl_ascending h_init fp)
          (ensures fgc_pillars h_init h_mark (fst (FS.fused_sweep_coalesce h_mark fp)) roots)
  = let r = FS.fused_sweep_coalesce h_mark fp in
    let h_f = fst r in
    fused_post_gen h_init h_mark roots fp;
    FSE.sweep_post_elim h_mark h_f (snd r);
    mark_post_sweep_pre h_init h_mark roots fp;
    objects_is_vertex_set h_f;
    objects_is_vertex_set h_mark;
    let vert (x: obj_addr) : Lemma
      (Seq.mem x (objects zero_addr h_f) <==> Seq.mem x (create_graph h_f).vertices)
      = graph_vertices_mem h_f x
    in
    FStar.Classical.forall_intro vert;
    // Pillar 3: a survivor keeps its successors
    let succ (x: obj_addr) : Lemma
      (requires Seq.mem x (create_graph h_f).vertices /\ is_black x h_mark)
      (ensures successors (create_graph h_init) x == successors (create_graph h_f) x)
      = assert (Seq.mem x (objects zero_addr h_mark));
        FSE.sweep_post_pointer_fields h_mark h_f (snd r) x;
        HeapGraph.successors_eq_pointer_fields h_f (objects zero_addr h_f) x;
        HeapGraph.successors_eq_pointer_fields h_mark (objects zero_addr h_mark) x;
        Seq.lemma_eq_elim (successors (create_graph h_mark) x) (successors (create_graph h_f) x)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires succ);
    // Pillar 4
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires (FSE.sweep_post_white_or_blue h_mark h_f (snd r)));
    // Pillar 5: a survivor keeps its fields
    let fld (x: obj_addr) (i: U64.t{U64.v i >= 1}) : Lemma
      (requires Seq.mem x (create_graph h_f).vertices /\ is_black x h_mark /\
                U64.v i <= U64.v (wosize_of_object x h_init))
      (ensures HeapGraph.get_field h_init x i == HeapGraph.get_field h_f x i)
      = FSE.sweep_post_get_field h_mark h_f (snd r) x i
    in
    let fld' (x: obj_addr) : Lemma
      (forall (i: U64.t). Seq.mem x (create_graph h_f).vertices /\ is_black x h_mark /\
         U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x h_init) ==>
         HeapGraph.get_field h_init x i == HeapGraph.get_field h_f x i)
      = FStar.Classical.forall_intro (FStar.Classical.move_requires (fld x))
    in
    FStar.Classical.forall_intro fld'
#pop-options

let full_gc_correctness_fused h_init h_mark roots fp =
  fgc_pillars_fused h_init h_mark roots fp;
  full_gc_correctness_intro h_init h_mark (fst (FS.fused_sweep_coalesce h_mark fp)) roots

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
let major_gc_live_subgraph_isomorphism_fused h_init h_mark roots fp =
  let r = FS.fused_sweep_coalesce h_mark fp in
  let h_f = fst r in
  let g_init = create_graph h_init in
  let g_f = create_graph h_f in
  fgc_pillars_fused h_init h_mark roots fp;
  fused_post_gen h_init h_mark roots fp;
  FSE.sweep_post_elim h_mark h_f (snd r);
  mark_post_elim_objects h_init h_mark roots fp;
  let live_survives (x: obj_addr) : Lemma
    (heap_reachable h_init roots x ==>
     Seq.mem x (objects zero_addr h_f) /\ is_white x h_f)
  = if FStar.IndefiniteDescription.strong_excluded_middle (heap_reachable h_init roots x) then begin
      graph_vertices_mem h_init x;
      assert (is_black x h_mark)
    end
  in
  FStar.Classical.forall_intro live_survives;
  let succ_live (x: obj_addr) : Lemma
    (heap_reachable h_init roots x ==>
     mem_graph_vertex g_f x /\ successors g_init x == successors g_f x)
  = if FStar.IndefiniteDescription.strong_excluded_middle (heap_reachable h_init roots x) then begin
      graph_vertices_mem h_init x;
      live_survives x;
      graph_vertices_mem h_f x
    end
  in
  FStar.Classical.forall_intro succ_live;
  let edge_preserved (x y: obj_addr) : Lemma
    (heap_reachable h_init roots x /\ heap_reachable h_init roots y ==>
     (heap_edge h_init x y <==> heap_edge h_f x y))
  = if FStar.IndefiniteDescription.strong_excluded_middle
         (heap_reachable h_init roots x /\ heap_reachable h_init roots y) then begin
      succ_live x;
      graph_vertices_mem h_init x;
      (if heap_edge h_init x y then begin
         edge_mem_successors g_init x y;
         successors_mem_edge g_f x y
       end);
      (if heap_edge h_f x y then begin
         edge_mem_successors g_f x y;
         successors_mem_edge g_init x y
       end)
    end
  in
  FStar.Classical.forall_intro_2 edge_preserved;
  let field_preserved (x: obj_addr) (i: U64.t) : Lemma
    (heap_reachable h_init roots x /\ U64.v i >= 1 /\
     U64.v i <= U64.v (wosize_of_object x h_init) ==>
     HeapGraph.get_field h_init x i == HeapGraph.get_field h_f x i)
  = if FStar.IndefiniteDescription.strong_excluded_middle
         (heap_reachable h_init roots x /\ U64.v i >= 1 /\
          U64.v i <= U64.v (wosize_of_object x h_init)) then begin
      graph_vertices_mem h_init x;
      live_survives x;
      graph_vertices_mem h_f x
    end
  in
  FStar.Classical.forall_intro_2 field_preserved
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
let major_gc_unreachable_final_blue_fused h_init h_mark roots fp =
  let r = FS.fused_sweep_coalesce h_mark fp in
  let h_f = fst r in
  fused_post_gen h_init h_mark roots fp;
  FSE.sweep_post_elim h_mark h_f (snd r);
  mark_post_elim_objects h_init h_mark roots fp;
  major_gc_live_subgraph_isomorphism_fused h_init h_mark roots fp;
  create_graph_wf_from_heap h_f;
  roots_subset_coal_from_iso h_init h_f roots;
  let aux (x: obj_addr) : Lemma
    (requires Seq.mem x (objects zero_addr h_f) /\ ~(heap_reachable h_f roots x))
    (ensures is_blue x h_f)
  = assert (Seq.mem x (objects zero_addr h_mark));
    graph_vertices_mem h_init x;
    if is_black x h_mark then
      heap_reachable_transfer_init_to_coal h_init h_f roots x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let gc_result_fused h_init h_mark roots fp =
  gc_postcondition_fused h_init h_mark roots fp;
  full_gc_correctness_fused h_init h_mark roots fp;
  let g = create_graph h_init in
  let roots' = HeapGraph.coerce_to_vertex_list roots in
  if FStar.IndefiniteDescription.strong_excluded_middle
       (graph_wf g /\ is_vertex_set roots' /\ subset_vertices roots' g.vertices)
  then begin
    major_gc_live_subgraph_isomorphism_fused h_init h_mark roots fp;
    major_gc_unreachable_final_blue_fused h_init h_mark roots fp
  end
#pop-options


/// ---------------------------------------------------------------------------
/// End-to-end, with the unbounded mark
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
private let e2e_mark_post (h_init: heap) (st: seq obj_addr) (roots: seq obj_addr) (fp: U64.t)
  : Lemma (requires e2e_pre h_init st roots fp)
          (ensures mark_post h_init (mark h_init st) roots fp)
  = GC.Spec.MarkInv.mark_inv_intro h_init st;
    FLA.fl_ascending_head_cell h_init fp;
    (if fp <> 0UL then FLA.fl_cell_facts h_init fp);
    mark_satisfies_mark_post h_init st roots fp
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let end_to_end_correctness h_init st roots fp =
  e2e_mark_post h_init st roots fp;
  fgc_pillars_fused h_init (mark h_init st) roots fp

let gc_postcondition_from_correctness h_init st roots fp =
  e2e_mark_post h_init st roots fp;
  gc_postcondition_fused h_init (mark h_init st) roots fp

let full_gc_correctness_from_end_to_end h_init st roots fp =
  e2e_mark_post h_init st roots fp;
  full_gc_correctness_fused h_init (mark h_init st) roots fp

let gc_safety h_init st roots fp =
  let h_mark = mark h_init st in
  e2e_mark_post h_init st roots fp;
  major_gc_live_subgraph_isomorphism_fused h_init h_mark roots fp;
  let aux (x: obj_addr) : Lemma
    (mem_graph_vertex (create_graph h_init) x /\
     Seq.mem x (reachable_set (create_graph h_init) (HeapGraph.coerce_to_vertex_list roots)) ==>
     Seq.mem x (objects zero_addr (fst (FS.fused_sweep_coalesce h_mark fp))))
    = ()
  in
  FStar.Classical.forall_intro aux
#pop-options
