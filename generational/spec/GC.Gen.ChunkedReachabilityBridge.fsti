module GC.Gen.ChunkedReachabilityBridge

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote

module MH = GC.Spec.MajorHeap
module GenInv = GC.Gen.HeapInvariant
module CG = GC.Gen.CombinedGraph

/// Major roots must be valid active non-blue chunked-major objects when they
/// classify as `MajorV`.
let chunked_roots_valid_nonblue (roots: seq U64.t) (major: MH.major_heap) : prop =
  forall (r: U64.t).
    Seq.mem r roots /\ ~(is_minor_pointer r) /\
    is_val_addr r /\ Seq.mem (r <: obj_addr) (MH.major_objects major) ==>
    ~(GenInv.chunked_is_blue major (r <: obj_addr))

/// Chunked active-major object addresses are valid legacy pointer field values.
/// This is intentionally local to avoid a dependency cycle with
/// `GC.Gen.CheneyGraphReadiness`, which provides construction lemmas for the
/// same predicate.
let chunked_major_objects_are_pointer_fields (major: MH.major_heap) : prop =
  forall (obj: obj_addr).
    Seq.mem obj (MH.major_objects major) ==> is_pointer_field obj

/// Every reachable major vertex in the chunked combined graph is an active
/// non-blue major object.
val chunked_reachable_major_valid_nonblue
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.chunked_collection_heap_shape minor major fp fuel /\
      chunked_roots_valid_nonblue roots major /\
      chunked_major_objects_are_pointer_fields major)
    (ensures (
      let cg = CG.build_chunked_combined_graph minor major in
      let combined_roots = CG.classify_roots roots in
      forall (v: U64.t).
        CG.combined_reachable cg combined_roots (CG.MajorV v) ==>
        U64.v v >= U64.v mword /\
        U64.v v < heap_size /\
        U64.v v % U64.v mword == 0 /\
        Seq.mem (v <: obj_addr) (MH.major_objects major) /\
        ~(GenInv.chunked_is_blue major (v <: obj_addr)))
    )
