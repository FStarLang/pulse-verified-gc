/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.GcPillars - the collector's five pillars, for pages
/// ---------------------------------------------------------------------------
///
/// `GC.Spec.Correctness.full_gc_correctness h_init g roots` asks for a heap
/// `h_w` whose black objects are exactly the reachable ones of `h_init`
/// (pillar 2), and in which every object of the final heap `g` that is
/// black survived white with its successors and fields (pillars 3 to 5).
///
/// For the coalescing sweep `h_w` is the marked heap itself, since every
/// object of its result was an object of the marked heap.  The page sweep
/// also makes new blocks: a page it gives back from inside a dead large
/// object gets a new header, at a word that was a field of that object, and
/// a field may read as black.  So the witness here is `clean h_mark`: the
/// marked heap with the word at each page start that is not on its walk
/// set to a white header.  No header of the walk changes, so its black
/// objects are the marked heap's.
///
/// `GC.Spec.Pages.SweepStarts` gives what makes this enough: every free
/// block of the swept heap starts at a block of the marked heap or at a
/// page start (`black_clean`).
///
/// The isomorphism of the live subgraph (`iso`) is proved as for the
/// coalescing sweep, from the survivors of `GC.Spec.Pages.Survive`.

module GC.Spec.Pages.GcPillars

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Walk
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Inv
open GC.Spec.Pages.SweepAll

module U64 = FStar.UInt64
module Seq = FStar.Seq
module R = GC.Spec.Pages.Replace
module SS = GC.Spec.Pages.SweepStep
module SU = GC.Spec.Pages.SweepUnits
module SW = GC.Spec.Pages.SweepWf
module S3 = GC.Spec.Pages.SweepStarts
module SV = GC.Spec.Pages.Survive
module Corr = GC.Spec.Correctness
module HeapGraph = GC.Spec.HeapGraph
module HeapModel = GC.Spec.HeapModel
module Graph = GC.Spec.Graph
module DFS = GC.Spec.DFS

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The mark's result
/// ---------------------------------------------------------------------------

/// What a mark leaves, as `Corr.mark_post` and its clause on fields (which
/// `Corr` does not export an eliminator for).
let marked (h_init h_mark: heap) (roots: Seq.seq obj_addr) : prop =
  Corr.mark_post h_init h_mark roots 0UL /\
  (forall (x: obj_addr) (i: U64.t).
     Seq.mem x (objects zero_addr h_init) /\ U64.v i >= 1 /\
     U64.v i <= U64.v (wosize_of_object x h_init) ==>
     HeapGraph.get_field h_mark x i == HeapGraph.get_field h_init x i)

/// The graph-shape facts that guard pillar 2 (as `GC.Impl.Correct.graph_pre`).
let graph_pre (h_init: heap) (roots: Seq.seq obj_addr) : prop =
  let g = HeapModel.create_graph h_init in
  let roots' = HeapGraph.coerce_to_vertex_list roots in
  Graph.graph_wf g /\ Graph.is_vertex_set roots' /\ Graph.subset_vertices roots' g.vertices

/// ---------------------------------------------------------------------------
/// The witness
/// ---------------------------------------------------------------------------

let page_base_lt (k k': nat)
  : Lemma (requires k < k') (ensures page_base k + page_bytes <= page_base k')
  = FStar.Math.Lemmas.lemma_mult_le_right page_bytes (k + 1) k';
    FStar.Math.Lemmas.distributivity_add_left k 1 page_bytes

/// The start of page `j`, as an address.
let page_hp (j: nat{j < n_pages}) : (a: hp_addr{U64.v a == page_base j}) =
  page_base_aligned j;
  page_base_mono (j + 1) n_pages;
  page_base_lt j (j + 1);
  mk_hp_addr (page_base j)

/// A white header.
let wh0 : U64.t = colorHeader 0UL White

let rec clean_from (g0 g: heap) (j: nat) : GTot heap (decreases (if j < n_pages then n_pages - j else 0)) =
  if j >= n_pages then g
  else if steps_to g0 (U64.v zero_addr) (page_base j) then clean_from g0 g (j + 1)
  else clean_from g0 (write_word g (page_hp j) wh0) (j + 1)

/// The marked heap with each page start that is not on its walk made white.
let clean (g0: heap) : GTot heap = clean_from g0 g0 0

#push-options "--fuel 1 --ifuel 1"
let rec clean_from_kept (g0 g: heap) (j: nat) (a: hp_addr)
  : Lemma (requires forall (k: nat). j <= k /\ k < n_pages /\ U64.v a == page_base k ==>
                      steps_to g0 (U64.v zero_addr) (page_base k))
          (ensures read_word (clean_from g0 g j) a == read_word g a)
          (decreases (if j < n_pages then n_pages - j else 0))
  = if j >= n_pages then ()
    else if steps_to g0 (U64.v zero_addr) (page_base j) then clean_from_kept g0 g (j + 1) a
    else begin
      let pa = page_hp j in
      assert (pa <> a);
      if U64.v pa < U64.v a then SS.aligned_lt (U64.v pa) (U64.v a)
      else SS.aligned_lt (U64.v a) (U64.v pa);
      read_write_different g pa a wh0;
      clean_from_kept g0 (write_word g pa wh0) (j + 1) a
    end

let rec clean_from_page (g0 g: heap) (j: nat) (k: nat{k < n_pages})
  : Lemma (requires j <= k /\ ~(steps_to g0 (U64.v zero_addr) (page_base k)))
          (ensures read_word (clean_from g0 g j) (page_hp k) == wh0)
          (decreases (if j < n_pages then n_pages - j else 0))
  = if j = k then begin
      let g' = write_word g (page_hp k) wh0 in
      read_write_same g (page_hp k) wh0;
      let later (k': nat) : Lemma (k + 1 <= k' ==> page_base k <> page_base k')
        = if k + 1 <= k' then page_base_lt k k'
      in
      FStar.Classical.forall_intro later;
      clean_from_kept g0 g' (k + 1) (page_hp k)
    end
    else if steps_to g0 (U64.v zero_addr) (page_base j) then clean_from_page g0 g (j + 1) k
    else clean_from_page g0 (write_word g (page_hp j) wh0) (j + 1) k
#pop-options

/// A header on the walk is kept.
let clean_walk (g0: heap) (a: hp_addr)
  : Lemma (requires steps_to g0 (U64.v zero_addr) (U64.v a))
          (ensures read_word (clean g0) a == read_word g0 a)
  = clean_from_kept g0 g0 0 a

/// An object of the marked heap is black in the witness exactly when it is
/// black in the marked heap.
let black_same (g0: heap) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g0))
          (ensures is_black x (clean g0) == is_black x g0)
  = hd_address_spec x;
    R.obj_iff g0 x;
    clean_walk g0 (hd_address x);
    color_of_header_eq x g0 (clean g0)

/// A block of the marked heap that is free after the sweep was not black.
let walk_not_black (g0: heap) (st0: pstate) (g: heap) (st: pstate) (x: obj_addr)
  : Lemma (requires SV.swept g0 st0 g st /\ steps_to g0 (U64.v zero_addr) (U64.v x - 8) /\
                    Seq.mem x (objects zero_addr g) /\ is_blue x g)
          (ensures ~(is_black x (clean g0)))
  = let h = U64.v x - 8 in
    SV.swept_inv g0 st0 g st;
    hd_address_spec x;
    R.obj_iff g x;
    R.hdr_obj g x;
    R.hdr_obj g0 x;
    R.hdr_obj (clean g0) x;
    is_blue_iff x g;
    if color_at g0 h = Black then begin
      black_kept g0 g st0 st h;
      colorHeader_getColor (hdr g0 h) White
    end;
    clean_walk g0 (hd_address x);
    is_black_iff x (clean g0)

/// **An object of the swept heap that is black in the witness is not
/// free**, so it is a survivor of the mark.
let black_clean (g0: heap) (st0: pstate) (g: heap) (st: pstate) (x: obj_addr)
  : Lemma (requires SV.swept g0 st0 g st /\ Seq.mem x (objects zero_addr g) /\ is_black x (clean g0))
          (ensures ~(is_blue x g))
  = let h = U64.v x - 8 in
    SV.swept_inv g0 st0 g st;
    hd_address_spec x;
    R.obj_iff g x;
    R.hdr_obj g x;
    is_blue_iff x g;
    if is_blue x g then begin
      if h >= pages_end then begin
        pages_end_bound ();
        page_base_aligned n_pages;
        walk_pages_reached g st.pm n_pages;
        walk_pages_reached g0 st0.pm n_pages;
        R.steps_to_det g (U64.v zero_addr) pages_end h;
        if h > pages_end then begin
          steps_to_refl g pages_end;
          R.block_before g pages_end pages_end h
        end;
        walk_not_black g0 st0 g st x
      end else begin
        SW.in_unit_lt g st0.pm st.pm h;
        eliminate exists (i: nat{i < n_pages}).
          walk_page st0.pm i /\ page_base i <= h /\ h < page_base (i + span st0.pm i) /\
          steps_to g (page_base i) h
        with begin
          assert (S3.starts_ok g0 g i (span st0.pm i));
          walk_pages_reached g0 st0.pm i;
          if steps_to g0 (page_base i) h then begin
            steps_to_trans g0 (U64.v zero_addr) (page_base i) h;
            walk_not_black g0 st0 g st x
          end else
            eliminate exists (j: nat). h == page_base j
            with begin
              if j >= n_pages then FStar.Math.Lemmas.lemma_mult_le_right page_bytes n_pages j;
              if steps_to g0 (U64.v zero_addr) h then walk_not_black g0 st0 g st x
              else begin
                clean_from_page g0 g0 0 j;
                assert (hd_address x == page_hp j);
                colorHeader_getColor 0UL White;
                color_of_object_spec x (clean g0);
                is_black_iff x (clean g0)
              end
            end
        end
      end
    end

/// ---------------------------------------------------------------------------
/// The pillars
/// ---------------------------------------------------------------------------

/// The setting: `g, st` is the sweep of the marked heap `h_mark`.
let ctx (h_init h_mark: heap) (st0: pstate) (g: heap) (st: pstate) (roots: Seq.seq obj_addr) : prop =
  marked h_init h_mark roots /\ SV.swept h_mark st0 g st /\ well_formed_heap g

let ctx_facts (h_init h_mark: heap) (st0: pstate) (g: heap) (st: pstate) (roots: Seq.seq obj_addr)
  : Lemma (requires ctx h_init h_mark st0 g st roots)
          (ensures objects zero_addr h_mark == objects zero_addr h_init /\
                   HeapModel.create_graph h_mark == HeapModel.create_graph h_init /\
                   (forall (x: obj_addr). Seq.mem x (objects zero_addr h_init) ==>
                      wosize_of_object x h_mark == wosize_of_object x h_init))
  = Corr.mark_post_elim_objects h_init h_mark roots 0UL;
    Corr.mark_post_elim_graph h_init h_mark roots 0UL;
    Corr.mark_post_elim_wosize h_init h_mark roots 0UL

/// A survivor has the same successors as in the first heap.
let succ_kept (h_init h_mark: heap) (st0: pstate) (g: heap) (st: pstate) (roots: Seq.seq obj_addr) (x: obj_addr)
  : Lemma (requires ctx h_init h_mark st0 g st roots /\ Seq.mem x (objects zero_addr h_mark) /\ is_black x h_mark)
          (ensures Seq.mem x (objects zero_addr g) /\
                   Graph.successors (HeapModel.create_graph h_init) x ==
                   Graph.successors (HeapModel.create_graph g) x)
  = ctx_facts h_init h_mark st0 g st roots;
    SV.black_survives h_mark st0 g st x;
    SV.pointer_fields_kept h_mark st0 g st x;
    HeapModel.objects_is_vertex_set h_mark;
    HeapModel.objects_is_vertex_set g;
    HeapGraph.successors_eq_pointer_fields h_mark (objects zero_addr h_mark) x;
    HeapGraph.successors_eq_pointer_fields g (objects zero_addr g) x;
    Seq.lemma_eq_elim (Graph.successors (HeapModel.create_graph h_init) x)
                      (Graph.successors (HeapModel.create_graph g) x)

/// A survivor has the same fields as in the first heap.
let field_same (h_init h_mark: heap) (st0: pstate) (g: heap) (st: pstate) (roots: Seq.seq obj_addr)
               (x: obj_addr) (i: U64.t)
  : Lemma (requires ctx h_init h_mark st0 g st roots /\ Seq.mem x (objects zero_addr h_mark) /\
                    is_black x h_mark /\ U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x h_init))
          (ensures HeapGraph.get_field h_init x i == HeapGraph.get_field g x i)
  = ctx_facts h_init h_mark st0 g st roots;
    SV.black_survives h_mark st0 g st x;
    wosize_of_object_bound x h_mark;
    hd_address_spec x;
    R.obj_iff h_mark x;
    R.hdr_obj h_mark x;
    HeapGraph.get_field_addr_eq h_mark x i;
    HeapGraph.get_field_addr_eq g x i

/// An object of the final heap that is black in the witness is a survivor.
let final_black (h_init h_mark: heap) (st0: pstate) (g: heap) (st: pstate) (roots: Seq.seq obj_addr) (x: obj_addr)
  : Lemma (requires ctx h_init h_mark st0 g st roots /\ Seq.mem x (objects zero_addr g) /\
                    is_black x (clean h_mark))
          (ensures Seq.mem x (objects zero_addr h_mark) /\ is_black x h_mark /\ is_white x g)
  = black_clean h_mark st0 g st x;
    SV.survivor h_mark st0 g st x

let pillar2 (h_init h_mark: heap) (st0: pstate) (g: heap) (st: pstate) (roots: Seq.seq obj_addr)
  : Lemma (requires ctx h_init h_mark st0 g st roots)
          (ensures (let g_init = HeapModel.create_graph h_init in
                    let roots' = HeapGraph.coerce_to_vertex_list roots in
                    Graph.graph_wf g_init /\ Graph.is_vertex_set roots' /\
                    Graph.subset_vertices roots' g_init.vertices ==>
                    (forall (x: obj_addr). Graph.mem_graph_vertex g_init x ==>
                       (is_black x (clean h_mark) <==> Seq.mem x (DFS.reachable_set g_init roots')))))
  = ctx_facts h_init h_mark st0 g st roots;
    Corr.mark_post_elim_black_reachable h_init h_mark roots 0UL;
    let one (x: obj_addr)
      : Lemma (Graph.mem_graph_vertex (HeapModel.create_graph h_init) x ==>
               is_black x (clean h_mark) == is_black x h_mark)
      = HeapModel.graph_vertices_mem h_init x;
        if Seq.mem x (objects zero_addr h_init) then black_same h_mark x
    in
    FStar.Classical.forall_intro one

/// **The five pillars**, with `clean h_mark` as the marked heap.
let pillars (h_init h_mark: heap) (st0: pstate) (g: heap) (st: pstate) (roots: Seq.seq obj_addr)
  : Lemma (requires ctx h_init h_mark st0 g st roots)
          (ensures Corr.full_gc_correctness h_init g roots)
  = let hw = clean h_mark in
    let gf = HeapModel.create_graph g in
    pillar2 h_init h_mark st0 g st roots;
    let vert (x: obj_addr) : Lemma (Seq.mem x gf.vertices <==> Seq.mem x (objects zero_addr g))
      = HeapModel.graph_vertices_mem g x
    in
    FStar.Classical.forall_intro vert;
    let p3 (x: obj_addr)
      : Lemma (Seq.mem x gf.vertices /\ is_black x hw ==>
               Graph.successors (HeapModel.create_graph h_init) x == Graph.successors gf x)
      = if Seq.mem x gf.vertices && is_black x hw then begin
          final_black h_init h_mark st0 g st roots x;
          succ_kept h_init h_mark st0 g st roots x
        end
    in
    FStar.Classical.forall_intro p3;
    let p4 (x: obj_addr)
      : Lemma (Seq.mem x gf.vertices ==> (is_white x g \/ is_blue x g) /\ (is_black x hw ==> is_white x g))
      = if Seq.mem x gf.vertices then begin
          if not (is_blue x g) then SV.survivor h_mark st0 g st x;
          if is_black x hw then final_black h_init h_mark st0 g st roots x
        end
    in
    FStar.Classical.forall_intro p4;
    let p5 (x: obj_addr) (i: U64.t)
      : Lemma (Seq.mem x gf.vertices /\ is_black x hw /\
               U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x h_init) ==>
               HeapGraph.get_field h_init x i == HeapGraph.get_field g x i)
      = if Seq.mem x gf.vertices && is_black x hw && U64.v i >= 1 &&
           U64.v i <= U64.v (wosize_of_object x h_init) then begin
          final_black h_init h_mark st0 g st roots x;
          field_same h_init h_mark st0 g st roots x i
        end
    in
    FStar.Classical.forall_intro_2 p5;
    Corr.full_gc_correctness_intro h_init hw g roots

/// ---------------------------------------------------------------------------
/// The live subgraph
/// ---------------------------------------------------------------------------

/// A reachable object was black after the mark.
let reach_black (h_init h_mark: heap) (st0: pstate) (g: heap) (st: pstate) (roots: Seq.seq obj_addr) (x: obj_addr)
  : Lemma (requires ctx h_init h_mark st0 g st roots /\ Corr.heap_reachable h_init roots x)
          (ensures Seq.mem x (objects zero_addr h_mark) /\ is_black x h_mark)
  = ctx_facts h_init h_mark st0 g st roots;
    Corr.mark_post_elim_black_reachable h_init h_mark roots 0UL;
    HeapModel.graph_vertices_mem h_init x

/// **The live subgraph is kept**, as for the coalescing sweep.
let iso (h_init h_mark: heap) (st0: pstate) (g: heap) (st: pstate) (roots: Seq.seq obj_addr)
  : Lemma (requires ctx h_init h_mark st0 g st roots)
          (ensures Corr.major_gc_live_subgraph_isomorphism h_init g roots)
  = let gi = HeapModel.create_graph h_init in
    let gf = HeapModel.create_graph g in
    let live (x: obj_addr)
      : Lemma (Corr.heap_reachable h_init roots x ==>
               Seq.mem x (objects zero_addr g) /\ is_white x g /\
               Graph.mem_graph_vertex gf x /\ Graph.successors gi x == Graph.successors gf x)
      = if FStar.IndefiniteDescription.strong_excluded_middle (Corr.heap_reachable h_init roots x) then begin
          reach_black h_init h_mark st0 g st roots x;
          SV.black_survives h_mark st0 g st x;
          succ_kept h_init h_mark st0 g st roots x;
          HeapModel.graph_vertices_mem g x
        end
    in
    FStar.Classical.forall_intro live;
    let edge (x y: obj_addr)
      : Lemma (Corr.heap_reachable h_init roots x /\ Corr.heap_reachable h_init roots y ==>
               (Corr.heap_edge h_init x y <==> Corr.heap_edge g x y))
      = if FStar.IndefiniteDescription.strong_excluded_middle (Corr.heap_reachable h_init roots x) then begin
          live x;
          if Graph.mem_graph_edge gi x y then begin
            Graph.edge_mem_successors gi x y;
            Graph.successors_mem_edge gf x y
          end;
          if Graph.mem_graph_edge gf x y then begin
            Graph.edge_mem_successors gf x y;
            Graph.successors_mem_edge gi x y
          end
        end
    in
    FStar.Classical.forall_intro_2 edge;
    let field (x: obj_addr) (i: U64.t)
      : Lemma (Corr.heap_reachable h_init roots x /\ U64.v i >= 1 /\
               U64.v i <= U64.v (wosize_of_object x h_init) ==>
               HeapGraph.get_field h_init x i == HeapGraph.get_field g x i)
      = if FStar.IndefiniteDescription.strong_excluded_middle (Corr.heap_reachable h_init roots x) &&
           U64.v i >= 1 && U64.v i <= U64.v (wosize_of_object x h_init) then begin
          reach_black h_init h_mark st0 g st roots x;
          field_same h_init h_mark st0 g st roots x i
        end
    in
    FStar.Classical.forall_intro_2 field
