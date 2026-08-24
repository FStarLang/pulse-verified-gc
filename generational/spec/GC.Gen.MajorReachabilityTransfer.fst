module GC.Gen.MajorReachabilityTransfer

open FStar.Seq
open GC.Spec.Graph
module U64 = FStar.UInt64
module Seq = FStar.Seq

#push-options "--fuel 1 --ifuel 2 --z3rlimit 20"

let graphs_agree_on_sym g1 g2 live =
  let closure (x y: vertex_id) : Lemma
    (live x /\ mem_graph_edge g2 x y ==> live y)
  = if live x && mem_graph_edge g2 x y then begin
      edge_mem_successors g2 x y;
      assert (Seq.mem y (successors g1 x));
      successors_mem_edge g1 x y
    end
  in
  FStar.Classical.forall_intro_2 closure

let edge_transfer g1 g2 live x y =
  if mem_graph_edge g1 x y then begin
    edge_mem_successors g1 x y;
    assert (Seq.mem y (successors g2 x));
    successors_mem_edge g2 x y
  end;
  if mem_graph_edge g2 x y then begin
    edge_mem_successors g2 x y;
    assert (Seq.mem y (successors g1 x));
    successors_mem_edge g1 x y
  end

/// The induction that does the real work: a `g1`-path out of a live vertex is
/// also a `g2`-path, because every vertex it meets is live and live vertices
/// have identical successor lists in the two graphs.
let rec reachable_transfer_aux (g1 g2: graph_state) (live: vertex_id -> prop)
                               (r: vertex_id{mem_graph_vertex g1 r})
                               (w: vertex_id{mem_graph_vertex g1 w})
                               (wit: reach g1 r w)
  : Lemma (requires graphs_agree_on g1 g2 live /\ live r)
          (ensures live w /\ mem_graph_vertex g2 r /\ mem_graph_vertex g2 w /\
                   reachable g2 r w)
          (decreases wit)
  = match wit with
    | ReachRefl _ -> reach_refl g2 r
    | ReachTrans _ y z wit' ->
      reachable_transfer_aux g1 g2 live r y wit';
      edge_mem_successors g1 y z;
      assert (Seq.mem z (successors g2 y));
      successors_mem_edge g2 y z;
      assert (live z);
      assert (mem_graph_vertex g2 z);
      let step (wit2: reach g2 r y) : Lemma (reachable g2 r z)
      = let wit3: reach g2 r z = ReachTrans r y z wit2 in
        FStar.Classical.exists_intro (fun (_: reach g2 r z) -> True) wit3
      in
      FStar.Classical.forall_intro step

let reachable_transfer g1 g2 live r w =
  let aux (wit: reach g1 r w) : Lemma
    (live w /\ mem_graph_vertex g2 w /\ reachable g2 r w)
  = reachable_transfer_aux g1 g2 live r w wit
  in
  FStar.Classical.forall_intro aux

#pop-options

/// ---------------------------------------------------------------------------
/// Heap-level instance: the major collection
/// ---------------------------------------------------------------------------

open GC.Spec.Base
module HM = GC.Spec.HeapModel
module HG = GC.Spec.HeapGraph
module MS = GC.Spec.Correctness
module MCFH = GC.Gen.MinorCollectForwarding.Helpers

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

/// Every vertex of a heap graph is an object address.
let vertex_is_val_addr (h: heap) (x: vertex_id)
  : Lemma (requires mem_graph_vertex (HM.create_graph h) x)
          (ensures is_val_addr x)
  = let g = HM.create_graph h in
    FStar.Classical.exists_intro
      (fun (x': vertex_id{mem_graph_vertex g x'}) -> x' == x) x;
    assert (MCFH.mem_graph_vertex_at g x);
    MCFH.mem_graph_vertex_at_is_obj_addr h x

let major_graphs_agree h1 h2 droots =
  let g1 = HM.create_graph h1 in
  let g2 = HM.create_graph h2 in
  let droots' = HG.coerce_to_vertex_list droots in
  let agree (x: vertex_id) : Lemma
    (major_live h1 droots x ==>
       mem_graph_vertex g1 x /\ mem_graph_vertex g2 x /\
       successors g1 x == successors g2 x)
  = () in
  FStar.Classical.forall_intro agree;
  let closed (x y: vertex_id) : Lemma
    (major_live h1 droots x /\ mem_graph_edge g1 x y ==> major_live h1 droots y)
  = if major_live h1 droots x && mem_graph_edge g1 x y then begin
      assert (Seq.mem (x, y) g1.edges);
      assert (mem_graph_vertex g1 y);
      vertex_is_val_addr h1 y;
      GC.Spec.DFS.reachable_successor_closed g1 droots' x y
    end
  in
  FStar.Classical.forall_intro_2 closed

/// A root is reachable from itself, hence live.
let root_is_live (h1: heap) (droots: Seq.seq obj_addr) (r: vertex_id)
  : Lemma
      (requires
        graph_wf (HM.create_graph h1) /\
        (let droots' = HG.coerce_to_vertex_list droots in
         is_vertex_set droots' /\
         subset_vertices droots' (HM.create_graph h1).vertices /\
         Seq.mem r droots'))
      (ensures major_live h1 droots r)
  = let g1 = HM.create_graph h1 in
    let droots' = HG.coerce_to_vertex_list droots in
    assert (mem_graph_vertex g1 r);
    vertex_is_val_addr h1 r;
    reach_refl g1 r;
    GC.Spec.DFS.reachable_set_correct g1 droots'

#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 40"

/// Move one reachability fact across a pair of agreeing heaps.
let result_post_reachable_swap
  (ha hb: heap) (live: vertex_id -> prop) (rts: Seq.seq U64.t) (w: U64.t)
  : Lemma
      (requires
        graphs_agree_on (HM.create_graph ha) (HM.create_graph hb) live /\
        (forall (r: vertex_id). Seq.mem (r <: U64.t) rts ==> live r) /\
        MCFH.result_post_reachable ha rts w)
      (ensures live w /\ MCFH.result_post_reachable hb rts w)
  = let ga = HM.create_graph ha in
    let gb = HM.create_graph hb in
    eliminate exists (rr: U64.t)
                     (r: vertex_id{mem_graph_vertex ga r})
                     (x: vertex_id{mem_graph_vertex ga x}).
      Seq.mem rr rts /\ r == rr /\ x == w /\ reachable ga r x
    with (reachable_transfer ga gb live r x;
          assert (MCFH.result_post_reachable hb rts w))

let major_result_post_transfer h1 h2 droots rts =
  let g1 = HM.create_graph h1 in
  let g2 = HM.create_graph h2 in
  let droots' = HG.coerce_to_vertex_list droots in
  let live : vertex_id -> prop = major_live h1 droots in
  major_graphs_agree h1 h2 droots;
  graphs_agree_on_sym g1 g2 live;
  let roots_live (r: vertex_id) : Lemma (Seq.mem (r <: U64.t) rts ==> live r)
  = if Seq.mem (r <: U64.t) rts then begin
      HG.coerce_mem_lemma droots (r <: obj_addr);
      root_is_live h1 droots r
    end
  in
  FStar.Classical.forall_intro roots_live;
  let fwd (w: U64.t) : Lemma
    (MCFH.result_post_reachable h1 rts w ==> MCFH.result_post_reachable h2 rts w)
  = if MCFH.result_post_reachable h1 rts w
    then result_post_reachable_swap h1 h2 live rts w
  in
  FStar.Classical.forall_intro fwd;
  let bwd (w: U64.t) : Lemma
    (MCFH.result_post_reachable h2 rts w ==> MCFH.result_post_reachable h1 rts w)
  = if MCFH.result_post_reachable h2 rts w
    then result_post_reachable_swap h2 h1 live rts w
  in
  FStar.Classical.forall_intro bwd;
  let edges (w1 w2: U64.t) : Lemma
    (MCFH.result_post_reachable h1 rts w1 /\ MCFH.result_post_reachable h1 rts w2 ==>
     (MCFH.result_post_edge h1 w1 w2 <==> MCFH.result_post_edge h2 w1 w2))
  = if MCFH.result_post_reachable h1 rts w1 && MCFH.result_post_reachable h1 rts w2
    then begin
      result_post_reachable_swap h1 h2 live rts w1;
      assert (live w1);
      if MCFH.result_post_edge h1 w1 w2 then
        eliminate exists (s: hp_addr) (d: hp_addr).
          s == w1 /\ d == w2 /\ mem_graph_edge g1 s d
        with (edge_transfer g1 g2 live s d;
              assert (MCFH.result_post_edge h2 w1 w2));
      if MCFH.result_post_edge h2 w1 w2 then
        eliminate exists (s: hp_addr) (d: hp_addr).
          s == w1 /\ d == w2 /\ mem_graph_edge g2 s d
        with (edge_transfer g1 g2 live s d;
              assert (MCFH.result_post_edge h1 w1 w2))
    end
  in
  FStar.Classical.forall_intro_2 edges

#pop-options
