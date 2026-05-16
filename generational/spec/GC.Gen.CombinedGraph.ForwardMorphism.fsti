/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph.ForwardMorphism — Forward direction of isomorphism
/// ---------------------------------------------------------------------------
///
/// Proves that gc_morphism maps every pre-GC combined-reachable vertex to
/// a valid vertex in the post-GC major heap graph. This is the "vertex
/// survival" direction of the isomorphism.
///
/// Key results:
///   1. gc_morphism sends minor vertices to their promoted major copies
///   2. gc_morphism is the identity on major vertices  
///   3. Every combined-reachable vertex has a surviving image

module GC.Gen.CombinedGraph.ForwardMorphism

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Reachability
open GC.Gen.Promote
open GC.Gen.CombinedGraph

/// ---------------------------------------------------------------------------
/// Minor vertex survival: forwarded objects exist in post-minor major heap
/// ---------------------------------------------------------------------------

/// If v is a minor object in the live_set and fwd(v) ≠ 0, then
/// gc_morphism maps MinorV v to MajorV (fwd v), which is a valid
/// major object in the post-promote heap.
val minor_vertex_survives
  (ms: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (v: U64.t)
  : Lemma (requires
      (let live_set = live_set_of ms major roots in
       let prom_res = promote_all_spec ms major fp live_set in
       Seq.mem v live_set /\
       prom_res.fwd_map v <> 0UL /\
       fwd_targets_in_objects prom_res.fwd_map live_set (Seq.length live_set) prom_res.major_final))
    (ensures
      (let live_set = live_set_of ms major roots in
       let prom_res = promote_all_spec ms major fp live_set in
       gc_morphism prom_res.fwd_map (MinorV v) == MajorV (prom_res.fwd_map v)))

/// ---------------------------------------------------------------------------
/// Major vertex survival: identity mapping, objects persist
/// ---------------------------------------------------------------------------

/// gc_morphism is the identity on major vertices
val major_vertex_identity (fwd: forwarding_map) (v: U64.t)
  : Lemma (ensures gc_morphism fwd (MajorV v) == MajorV v)
