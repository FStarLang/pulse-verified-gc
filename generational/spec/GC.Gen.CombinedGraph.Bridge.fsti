/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph.Bridge — Bridge between minor/major reachability
/// and combined-graph reachability
/// ---------------------------------------------------------------------------
///
/// Proves that reachability in the individual heaps implies reachability
/// in the combined graph. This connects the existing proof infrastructure
/// (minor_reachable, DFS-based major reachability) to the isomorphism proof.

module GC.Gen.CombinedGraph.Bridge

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Reachability
open GC.Gen.Remembered
open GC.Gen.Promote
open GC.Gen.CombinedGraph

/// ---------------------------------------------------------------------------
/// Minor → Combined Bridge
/// ---------------------------------------------------------------------------

/// If y is a minor successor of x, then there is a combined-graph edge
/// from (MinorV x) to (MinorV y).
val minor_successor_edge (ms: minor_state) (major: heap) (x y: U64.t)
  : Lemma (requires Seq.mem y (minor_successors ms x) /\
                    Seq.mem x (minor_objects ms))
          (ensures mem_ce (MinorV x, MinorV y) (build_combined_graph ms major))

/// Every minor-reachable object is combined-reachable.
val minor_reachable_implies_combined
  (ms: minor_state) (major: heap) (roots: seq U64.t) (x: U64.t)
  : Lemma (requires minor_wf ms /\ well_formed_heap major /\
                    Seq.mem x (minor_reachable ms roots))
          (ensures combined_reachable
                     (build_combined_graph ms major)
                     (classify_roots roots)
                     (MinorV x))
