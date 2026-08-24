module GC.Gen.MajorReachabilityTransfer

/// Transferring reachability across the major collection.
///
/// The major collector's caller-facing contract
/// (`GC.Spec.Correctness.major_gc_live_subgraph_isomorphism`) relates the heap
/// before marking to the heap after coalescing.  Composing it with the minor
/// collector's isomorphism requires moving reachability *in both directions*
/// between the two heaps, which the edge clause alone cannot do: it is guarded
/// on both endpoints already being live, so the natural path induction is
/// circular.  The successor clause is what breaks the circularity, and this
/// module turns it into the two transfer lemmas the composition needs.
///
/// The graph-level statements are generic: two graphs that agree on the
/// successor lists of a successor-closed vertex set have the same reachability
/// and the same edges inside that set.

open FStar.Seq
open GC.Spec.Graph
module U64 = FStar.UInt64
module Seq = FStar.Seq

/// `g1` and `g2` agree on `live`, and `live` is closed under `g1`-successors.
let graphs_agree_on (g1 g2: graph_state) (live: vertex_id -> prop) : prop =
  (forall (x: vertex_id). live x ==>
     mem_graph_vertex g1 x /\ mem_graph_vertex g2 x /\
     successors g1 x == successors g2 x) /\
  (forall (x y: vertex_id). live x /\ mem_graph_edge g1 x y ==> live y)

/// Agreement is symmetric: successor equality carries the closure property over.
val graphs_agree_on_sym (g1 g2: graph_state) (live: vertex_id -> prop)
  : Lemma (requires graphs_agree_on g1 g2 live)
          (ensures graphs_agree_on g2 g1 live)

/// Edges out of a live vertex are the same in both graphs.
val edge_transfer (g1 g2: graph_state) (live: vertex_id -> prop) (x y: vertex_id)
  : Lemma (requires graphs_agree_on g1 g2 live /\ live x)
          (ensures mem_graph_edge g1 x y <==> mem_graph_edge g2 x y)

/// Reachability from a live vertex transfers, and stays inside `live`.
val reachable_transfer (g1 g2: graph_state) (live: vertex_id -> prop)
                       (r w: vertex_id)
  : Lemma (requires graphs_agree_on g1 g2 live /\ live r /\
                    mem_graph_vertex g1 w /\ reachable g1 r w)
          (ensures live w /\ mem_graph_vertex g2 w /\ reachable g2 r w)

/// ---------------------------------------------------------------------------
/// Heap-level instance: the major collection
/// ---------------------------------------------------------------------------

open GC.Spec.Base
module HM = GC.Spec.HeapModel
module HG = GC.Spec.HeapGraph
module MS = GC.Spec.Correctness
module MCFH = GC.Gen.MinorCollectForwarding.Helpers

/// The live set of the major collection, as a predicate on graph vertices.
let major_live (h: heap) (droots: Seq.seq obj_addr) (x: vertex_id) : prop =
  is_val_addr x /\ MS.heap_reachable h droots x

/// What the major collection gives us about the heaps it relates, plus the
/// graph-shape side conditions its own entry condition already carries.
let major_transfer_hyp (h1 h2: heap) (droots: Seq.seq obj_addr) : prop =
  MS.major_gc_live_subgraph_isomorphism h1 h2 droots /\
  graph_wf (HM.create_graph h1) /\
  graph_wf (HM.create_graph h2) /\
  (let droots' = HG.coerce_to_vertex_list droots in
   is_vertex_set droots' /\
   subset_vertices droots' (HM.create_graph h1).vertices)

val major_graphs_agree (h1 h2: heap) (droots: Seq.seq obj_addr)
  : Lemma (requires major_transfer_hyp h1 h2 droots)
          (ensures graphs_agree_on (HM.create_graph h1) (HM.create_graph h2)
                                   (major_live h1 droots))

/// The reachable subgraph seen through the generational vocabulary is the same
/// before and after the major collection.  This is the missing step that used
/// to force `gen_gc`'s caller to compose the minor and major isomorphisms.
val major_result_post_transfer
  (h1 h2: heap) (droots: Seq.seq obj_addr) (rts: Seq.seq U64.t)
  : Lemma
      (requires
        major_transfer_hyp h1 h2 droots /\
        (forall (r: U64.t). Seq.mem r rts ==>
           is_val_addr r /\ Seq.mem (r <: obj_addr) droots))
      (ensures
        (forall (w: U64.t).
           MCFH.result_post_reachable h1 rts w <==>
           MCFH.result_post_reachable h2 rts w) /\
        (forall (w1 w2: U64.t).
           MCFH.result_post_reachable h1 rts w1 /\
           MCFH.result_post_reachable h1 rts w2 ==>
           (MCFH.result_post_edge h1 w1 w2 <==> MCFH.result_post_edge h2 w1 w2)))
