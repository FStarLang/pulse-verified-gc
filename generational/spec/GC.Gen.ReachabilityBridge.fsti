/// ---------------------------------------------------------------------------
/// GC.Gen.ReachabilityBridge -- Combined-graph reachability bridge
/// ---------------------------------------------------------------------------
///
/// Proves reusable facts connecting `CombinedGraph.combined_reachable` to the
/// existing minor-reachability and major no-blue invariants.

module GC.Gen.ReachabilityBridge

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Spec.HeapModel
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Reachability
open GC.Gen.Remembered
open GC.Gen.CombinedGraph

module Mark = GC.Spec.Mark

/// If a minor object has a field pointing to the major heap, the target is a
/// non-blue allocated object.
let minor_no_pointer_to_blue (minor: minor_state) (major: heap) : prop =
  forall (obj: U64.t) (j: nat).
    Seq.mem obj (minor_objects minor) /\ j < minor_wosize minor obj ==>
    (let v = minor_read_field minor obj j in
     is_val_addr v /\ Seq.mem (v <: obj_addr) (objects zero_addr major) ==>
     ~(is_blue (v <: obj_addr) major))

/// Major roots must be valid non-blue objects when they classify as `MajorV`.
let roots_valid_nonblue (roots: seq U64.t) (major: heap) : prop =
  forall (r: U64.t).
    Seq.mem r roots /\ ~(is_minor_pointer r) /\
    is_val_addr r /\ Seq.mem (r <: obj_addr) (objects zero_addr major) ==>
    ~(is_blue (r <: obj_addr) major)

/// Every reachable major vertex is a valid non-blue major object.
val reachable_major_valid_nonblue
  (minor: minor_state) (major: heap) (roots: seq U64.t)
  : Lemma
    (requires
      well_formed_heap major /\
      minor_wf minor /\
      Mark.no_pointer_to_blue major /\
      minor_no_pointer_to_blue minor major /\
      roots_valid_nonblue roots major)
    (ensures (
      let cg = build_combined_graph minor major in
      let combined_roots = classify_roots roots in
      forall (v: U64.t).
        combined_reachable cg combined_roots (MajorV v) ==>
        U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
        Seq.mem (v <: obj_addr) (objects zero_addr major) /\
        ~(is_blue (v <: obj_addr) major)))

/// Major fields with index >= 1 that point into the minor heap are accounted
/// for by `minor_roots_from_major`.
let major_field_one_plus_in_remembered (ms: minor_state) (major: heap) : prop =
  forall (src: obj_addr) (v: U64.t).
    Seq.mem src (objects zero_addr major) /\ ~(is_no_scan src major) /\
    (exists (i: nat). i >= 1 /\ i < U64.v (wosize_of_object src major) /\
      U64.v src + i * 8 + 8 <= heap_size /\
      (U64.v src + i * 8) % 8 == 0 /\
      read_word major (U64.uint_to_t (U64.v src + i * 8)) == v) /\
    is_minor_pointer v /\ Seq.mem v (minor_objects ms) ==>
    Seq.mem v (minor_roots_from_major major)

/// Field 0 is not scanned by the remembered-set model, so callers must rule out
/// minor pointers there when using the generic bridge.
let major_field_zero_no_minor (ms: minor_state) (major: heap) : prop =
  forall (src: obj_addr).
    Seq.mem src (objects zero_addr major) /\ ~(is_no_scan src major) /\
    U64.v src + 8 <= heap_size ==>
    (let v = read_word major (U64.uint_to_t (U64.v src)) in
     ~(is_minor_pointer v /\ Seq.mem v (minor_objects ms)))

/// Any minor vertex reachable in the combined graph is in the minor live set
/// computed from program roots plus remembered-set roots.
val reachability_bridge
  (minor: minor_state) (major: heap) (roots: seq U64.t)
  : Lemma
    (requires
      well_formed_heap major /\
      minor_wf minor /\
      major_field_one_plus_in_remembered minor major /\
      major_field_zero_no_minor minor major)
    (ensures (
      let cg = build_combined_graph minor major in
      let combined_roots = classify_roots roots in
      forall (v: U64.t).
        combined_reachable cg combined_roots (MinorV v) ==>
        Seq.mem v (live_set_of minor major roots)))
