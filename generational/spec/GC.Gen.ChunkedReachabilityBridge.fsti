module GC.Gen.ChunkedReachabilityBridge

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Reachability

module MH = GC.Spec.MajorHeap
module GenInv = GC.Gen.HeapInvariant
module CG = GC.Gen.CombinedGraph
module RBridge = GC.Gen.ReachabilityBridge
module SpecMajorAlloc = GC.Spec.MajorAllocator

/// Major roots must be valid active non-blue chunked-major objects when they
/// classify as `MajorV`.
let chunked_roots_valid_nonblue (roots: seq U64.t) (major: MH.major_heap) : prop =
  forall (r: U64.t).
    Seq.mem r roots /\ ~(is_minor_pointer r) /\
    is_val_addr r /\ Seq.mem (r <: obj_addr) (MH.major_objects major) ==>
    ~(GenInv.chunked_is_blue major (r <: obj_addr))

/// Roots collected before registering a fresh chunk must not name the fresh
/// chunk.  This is the root-side analogue of field expansion safety.
let chunked_roots_disjoint_from_chunk
  (roots: seq U64.t) (fresh: MH.heap_chunk) : prop =
  forall (r: U64.t).
    Seq.mem r roots ==> ~(MH.pointer_in_chunk fresh r)

val chunked_roots_valid_nonblue_single_chunk_compat
  (roots: seq U64.t) (major: heap)
  : Lemma
    (requires RBridge.roots_valid_nonblue roots major)
    (ensures
      chunked_roots_valid_nonblue roots (MH.single_chunk_major_heap major))

val chunked_roots_valid_nonblue_preserved_by_expansion
  (roots: seq U64.t) (major: MH.major_heap)
  (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
    (requires
      chunked_roots_valid_nonblue roots major /\
      chunked_roots_disjoint_from_chunk roots fresh /\
      MH.chunk_disjoint_from_all fresh major)
    (ensures
      chunked_roots_valid_nonblue
        roots (SpecMajorAlloc.expand_major_heap major fresh fp).major_out)

val chunked_roots_valid_nonblue_ensure_head_capacity
  (roots: seq U64.t) (major: MH.major_heap)
  (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk)
  : Lemma
    (requires
      chunked_roots_valid_nonblue roots major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp < needed ==>
       chunked_roots_disjoint_from_chunk roots fresh /\
       MH.chunk_disjoint_from_all fresh major))
    (ensures
      chunked_roots_valid_nonblue
        roots
        (SpecMajorAlloc.ensure_major_head_capacity_spec
          major fp fuel needed fresh).capacity_major_out)

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

/// Field 0 is not scanned by the remembered-root model.  Callers must rule out
/// live minor pointers there when proving combined-reachable minor vertices are
/// covered by the Cheney roots.
let chunked_major_field_zero_no_minor
  (minor: minor_state) (major: MH.major_heap) : prop =
  forall (src: obj_addr) (field_addr: hp_addr) (raw: U64.t).
    Seq.mem src (MH.major_objects major) /\
    ~(GenInv.chunked_is_blue major src) /\
    CG.chunked_is_no_scan major src == false /\
    CG.chunked_major_field_slot src 0 == Some field_addr /\
    MH.read_word_in_major major field_addr == Some raw ==>
    ~(is_minor_pointer (to_minor_offset raw) /\
      Seq.mem (to_minor_offset raw) (minor_objects minor))

val chunked_major_field_zero_no_minor_single_chunk_compat
  (minor: minor_state) (major: heap)
  : Lemma
    (requires RBridge.major_field_zero_no_minor minor major)
    (ensures
      chunked_major_field_zero_no_minor
        minor (MH.single_chunk_major_heap major))

val chunked_major_field_zero_no_minor_preserved_by_expansion
  (minor: minor_state) (major: MH.major_heap)
  (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
    (requires
      chunked_major_field_zero_no_minor minor major /\
      MH.chunk_disjoint_from_all fresh major /\
      CG.chunked_all_major_object_expansion_safe
        major fresh (MH.major_objects major) 0)
    (ensures
      chunked_major_field_zero_no_minor
        minor (SpecMajorAlloc.expand_major_heap major fresh fp).major_out)

val chunked_major_field_zero_no_minor_ensure_head_capacity
  (minor: minor_state) (major: MH.major_heap)
  (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk)
  : Lemma
    (requires
      chunked_major_field_zero_no_minor minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp < needed ==>
       MH.chunk_disjoint_from_all fresh major /\
       CG.chunked_all_major_object_expansion_safe
         major fresh (MH.major_objects major) 0))
    (ensures
      chunked_major_field_zero_no_minor
        minor
        (SpecMajorAlloc.ensure_major_head_capacity_spec
          major fp fuel needed fresh).capacity_major_out)

/// Provisional direct remembered-root coverage: every non-field-0 active
/// non-blue major edge to a minor vertex has that minor target in `roots`.
/// A later chunked remembered-scan module should discharge this from a
/// dense-compatible `chunked_minor_roots_from_major ⊆ roots` predicate.
let chunked_remembered_minor_edges_in_roots
  (minor: minor_state) (major: MH.major_heap) (roots: seq U64.t) : prop =
  forall (src: obj_addr) (i: nat) (field_addr: hp_addr) (raw v: U64.t).
    Seq.mem src (MH.major_objects major) /\
    ~(GenInv.chunked_is_blue major src) /\
    CG.chunked_is_no_scan major src == false /\
    i <> 0 /\
    i < CG.chunked_wosize_nat_of_object major src /\
    CG.chunked_major_field_slot src i == Some field_addr /\
    MH.read_word_in_major major field_addr == Some raw /\
    CG.chunked_classify_major_field minor major raw == Some (CG.MinorV v) ==>
    Seq.mem v roots

/// Combined-reachable minor vertices are reachable by Cheney from `roots` once
/// roots cover the chunked remembered major-to-minor edges.
val chunked_combined_minor_reachable_in_minor_reachable
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.chunked_collection_heap_shape minor major fp fuel /\
      chunked_roots_valid_nonblue roots major /\
      chunked_major_objects_are_pointer_fields major /\
      chunked_major_field_zero_no_minor minor major /\
      chunked_remembered_minor_edges_in_roots minor major roots)
    (ensures (
      let cg = CG.build_chunked_combined_graph minor major in
      let combined_roots = CG.classify_roots roots in
      forall (v: U64.t).
        CG.combined_reachable cg combined_roots (CG.MinorV v) ==>
        Seq.mem v (minor_reachable minor roots))
    )
