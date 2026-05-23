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

/// Convert a `MajorV -> MajorV` combined-graph edge witness into the concrete
/// `points_to` relation used by `Mark.no_pointer_to_blue`.
val major_edge_points_to
  (minor: minor_state) (major: heap) (src: obj_addr) (dst: U64.t) (i: nat)
  : Lemma
    (requires
      well_formed_heap major /\
      Seq.mem src (objects zero_addr major) /\
      i < U64.v (wosize_of_object src major) /\
      U64.v src + i * 8 + 8 <= heap_size /\
      (U64.v src + i * 8) % 8 == 0 /\
      classify_major_field minor major
        (read_word major (U64.uint_to_t (U64.v src + i * 8))) == Some (MajorV dst))
    (ensures is_val_addr dst /\ points_to major src dst)

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

/// Every reachable major vertex is a valid major object.  This weaker form is
/// enough for image-validity proofs and does not require root color facts.
val reachable_major_valid
  (minor: minor_state) (major: heap) (roots: seq U64.t)
  : Lemma
    (requires well_formed_heap major /\ minor_wf minor)
    (ensures (
      let cg = build_combined_graph minor major in
      let combined_roots = classify_roots roots in
      forall (v: U64.t).
        combined_reachable cg combined_roots (MajorV v) ==>
        U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
        Seq.mem (v <: obj_addr) (objects zero_addr major)))

/// Major fields with index >= 1 that point into the minor heap are accounted
/// for by `minor_roots_from_major`.
let major_field_one_plus_in_remembered (ms: minor_state) (major: heap) : prop =
  forall (src: obj_addr) (v: U64.t).
    Seq.mem src (objects zero_addr major) /\ is_blue src major = false /\
    ~(is_no_scan src major) /\
    (exists (i: nat). i >= 1 /\ i < U64.v (wosize_of_object src major) /\
      U64.v src + i * 8 + 8 <= heap_size /\
      (U64.v src + i * 8) % 8 == 0 /\
      read_word major (U64.uint_to_t (U64.v src + i * 8)) == v) /\
    is_minor_pointer v /\ Seq.mem v (minor_objects ms) ==>
    Seq.mem v (minor_roots_from_major major)

/// The pure remembered-set scan records every non-field-0 minor pointer in a
/// scannable major object.
val major_field_one_plus_in_remembered_intro
  (minor: minor_state) (major: heap)
  : Lemma (requires well_formed_heap major)
          (ensures major_field_one_plus_in_remembered minor major)

/// Field 0 is not scanned by the remembered-set model, so callers must rule out
/// minor pointers there when using the generic bridge.
let major_field_zero_no_minor (ms: minor_state) (major: heap) : prop =
  forall (src: obj_addr).
    Seq.mem src (objects zero_addr major) /\ ~(is_no_scan src major) /\
    U64.v src + 8 <= heap_size ==>
    (let v = read_word major (U64.uint_to_t (U64.v src)) in
     ~(is_minor_pointer v /\ Seq.mem v (minor_objects ms)))

/// The scan-derived remembered roots are already included in the Cheney root
/// sequence.  This is the pure scan analogue of the slot-table coverage
/// condition used by `minor_collect_full`.
let remembered_roots_in_roots (major: heap) (roots: seq U64.t) : prop =
  forall (r: U64.t).
    Seq.mem r (minor_roots_from_major major) ==> Seq.mem r roots

/// If remembered roots are included in `roots`, then the existing live-set
/// definition (roots ++ remembered) is a subset of `minor_reachable roots`.
val live_set_in_minor_reachable
  (minor: minor_state) (major: heap) (roots: seq U64.t)
  : Lemma
    (requires remembered_roots_in_roots major roots)
    (ensures forall (v: U64.t).
      Seq.mem v (live_set_of minor major roots) ==>
      Seq.mem v (minor_reachable minor roots))

/// Any minor vertex reachable in the combined graph is in the minor live set
/// computed from program roots plus remembered-set roots.
val reachability_bridge
  (minor: minor_state) (major: heap) (roots: seq U64.t)
  : Lemma
    (requires
      well_formed_heap major /\
      minor_wf minor /\
      Mark.no_pointer_to_blue major /\
      minor_no_pointer_to_blue minor major /\
      roots_valid_nonblue roots major /\
      major_field_zero_no_minor minor major)
    (ensures (
      let cg = build_combined_graph minor major in
      let combined_roots = classify_roots roots in
      forall (v: U64.t).
        combined_reachable cg combined_roots (MinorV v) ==>
        Seq.mem v (live_set_of minor major roots)))

/// Combined-reachable minor vertices are reachable by Cheney from `roots` once
/// the scan-derived remembered roots are included in `roots`.
val combined_minor_reachable_in_minor_reachable
  (minor: minor_state) (major: heap) (roots: seq U64.t)
  : Lemma
    (requires
      well_formed_heap major /\
      minor_wf minor /\
      Mark.no_pointer_to_blue major /\
      minor_no_pointer_to_blue minor major /\
      roots_valid_nonblue roots major /\
      major_field_zero_no_minor minor major /\
      remembered_roots_in_roots major roots)
    (ensures (
      let cg = build_combined_graph minor major in
      let combined_roots = classify_roots roots in
      forall (v: U64.t).
        combined_reachable cg combined_roots (MinorV v) ==>
        Seq.mem v (minor_reachable minor roots)))
