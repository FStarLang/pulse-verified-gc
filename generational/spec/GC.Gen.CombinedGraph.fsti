/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph -- Combined minor+major heap graph
/// ---------------------------------------------------------------------------
///
/// Reusable graph vocabulary for minor-collection correctness.  Vertices are
/// tagged so overlapping minor and major address spaces remain distinct.

module GC.Gen.CombinedGraph

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Reachability
open GC.Gen.Promote

type combined_vertex =
  | MinorV : addr:U64.t -> combined_vertex
  | MajorV : addr:U64.t -> combined_vertex

type combined_edge = combined_vertex & combined_vertex

noeq
type combined_graph = {
  cg_vertices : seq combined_vertex;
  cg_edges    : seq combined_edge;
}

let mem_cv (v: combined_vertex) (g: combined_graph) : GTot bool =
  Seq.mem v g.cg_vertices

let mem_ce (e: combined_edge) (g: combined_graph) : GTot bool =
  Seq.mem e g.cg_edges

let combined_graph_wf (g: combined_graph) : prop =
  forall (e: combined_edge). mem_ce e g ==> mem_cv (fst e) g /\ mem_cv (snd e) g

val classify_minor_field (ms: minor_state) (major: heap) (v: U64.t)
  : GTot (option combined_vertex)

val classify_major_field (ms: minor_state) (major: heap) (v: U64.t)
  : GTot (option combined_vertex)

val build_combined_graph (ms: minor_state) (major: heap) : GTot combined_graph

let fwd_morphism (fwd: forwarding_map) (v: combined_vertex) : GTot U64.t =
  match v with
  | MinorV addr -> fwd addr
  | MajorV addr -> addr

val combined_reachable (g: combined_graph) (roots: seq combined_vertex)
                       (v: combined_vertex)
  : GTot prop

val combined_reachable_root (g: combined_graph) (roots: seq combined_vertex)
                            (v: combined_vertex)
  : Lemma (requires Seq.mem v roots /\ mem_cv v g)
          (ensures combined_reachable g roots v)

val combined_reachable_step (g: combined_graph) (roots: seq combined_vertex)
                            (u v: combined_vertex)
  : Lemma (requires combined_reachable g roots u /\ mem_ce (u, v) g)
          (ensures combined_reachable g roots v)

val combined_reachable_ind (g: combined_graph) (roots: seq combined_vertex)
                           (p: combined_vertex -> prop) (v: combined_vertex)
  : Lemma
    (requires combined_reachable g roots v /\
              (forall r. Seq.mem r roots /\ mem_cv r g ==> p r) /\
              (forall u w. p u /\ mem_ce (u, w) g ==> p w))
    (ensures p v)

let classify_root (r: U64.t) : GTot combined_vertex =
  if is_minor_pointer r then MinorV r else MajorV r

val classify_roots (roots: seq U64.t) : GTot (seq combined_vertex)

/// Generic shape of a true reachable-subgraph graph isomorphism.
let reachable_subgraph_isomorphism
  (src_reachable: combined_vertex -> prop)
  (dst_reachable: U64.t -> prop)
  (src_edge: combined_vertex -> combined_vertex -> prop)
  (dst_edge: U64.t -> U64.t -> prop)
  (fwd: forwarding_map) : prop =
  (forall (u: combined_vertex). src_reachable u ==>
    dst_reachable (fwd_morphism fwd u)) /\
  (forall (u v: combined_vertex). src_reachable u /\ src_reachable v /\
    fwd_morphism fwd u == fwd_morphism fwd v ==> u == v) /\
  (forall (w: U64.t). dst_reachable w ==>
    exists (u: combined_vertex). src_reachable u /\ fwd_morphism fwd u == w) /\
  (forall (u v: combined_vertex). src_reachable u /\ src_reachable v ==>
    (src_edge u v <==>
     dst_edge (fwd_morphism fwd u) (fwd_morphism fwd v)))
