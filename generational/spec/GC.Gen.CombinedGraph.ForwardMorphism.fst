/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph.ForwardMorphism — Implementation
/// ---------------------------------------------------------------------------

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
/// Minor vertex survival
/// ---------------------------------------------------------------------------

let minor_vertex_survives
  (ms: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (v: U64.t)
  = let live_set = live_set_of ms major roots in
    let prom_res = promote_all_spec ms major fp live_set in
    let fwd = prom_res.fwd_map in
    // gc_morphism fwd (MinorV v) == MajorV (fwd v) because fwd v ≠ 0UL
    gc_morphism_minor_fwd fwd v;
    // fwd v ∈ objects(0, prom_res.major_final) from fwd_targets_in_objects
    // We need to find the index of v in live_set
    Classical.move_requires (Seq.mem_index v) live_set;
    ()

/// ---------------------------------------------------------------------------
/// Major vertex identity
/// ---------------------------------------------------------------------------

let major_vertex_identity (fwd: forwarding_map) (v: U64.t)
  = gc_morphism_major fwd v
