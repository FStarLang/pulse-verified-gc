/// ---------------------------------------------------------------------------
/// GC.Gen.ReachabilityBridge — Prove reachability-based conjuncts
/// ---------------------------------------------------------------------------
///
/// Proves two conjuncts of iso_structural_preconditions internally:
///   (5) Reachability bridge: combined_reachable(MinorV v) ==> v ∈ live_set
///   (7) Reachable major valid/non-blue
///
/// The proofs use combined_reachable_ind with appropriate predicates:
///   - For (5): p(MinorV v) = mem v live_set, p(MajorV _) = True
///   - For (7): p(MajorV v) = valid /\ non-blue, p(MinorV _) = True
///
/// Required preconditions beyond standard GC assumptions:
///   - no_pointer_to_blue major (standard GC invariant: non-blue→non-blue)
///   - minor_fields_wf_nonblue: minor fields targeting major are non-blue
///   - combined_roots = classify_roots (Seq.append roots remembered)

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
open GC.Gen.Cheney
open GC.Gen.Correctness

module Mark = GC.Spec.Mark

/// ---------------------------------------------------------------------------
/// Minor fields don't point to blue major objects
/// ---------------------------------------------------------------------------

/// Standard GC invariant: if a minor object has a field pointing to the major
/// heap, the target is a non-blue (allocated) object. Blue objects are on the
/// free list and should never be referenced by live objects.
let minor_no_pointer_to_blue (minor: minor_state) (major: heap) : prop =
  forall (obj: U64.t) (j: nat).
    Seq.mem obj (minor_objects minor) /\ j < minor_wosize minor obj ==>
    (let v = minor_read_field minor obj j in
     is_val_addr v /\ Seq.mem (v <: obj_addr) (objects zero_addr major) ==>
     ~(is_blue (v <: obj_addr) major))

/// ---------------------------------------------------------------------------
/// Roots are valid non-blue major objects
/// ---------------------------------------------------------------------------

/// The roots that classify as MajorV must be valid non-blue objects.
let roots_valid_nonblue (roots: seq U64.t) (major: heap) : prop =
  forall (r: U64.t).
    Seq.mem r roots /\ ~(is_minor_pointer r) /\
    is_val_addr r /\ Seq.mem (r <: obj_addr) (objects zero_addr major) ==>
    ~(is_blue (r <: obj_addr) major)

/// ---------------------------------------------------------------------------
/// Conjunct (7): Reachable major vertices are valid and non-blue
/// ---------------------------------------------------------------------------

/// If MajorV v is reachable in the combined graph from combined_roots, then
/// v is a valid obj_addr in major and is non-blue.
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

/// ---------------------------------------------------------------------------
/// Conjunct (5): Reachability bridge — combined-reachable MinorV → live_set
/// ---------------------------------------------------------------------------

/// If a minor field (at index i >= 1) of a major object points to the minor heap,
/// that target is in minor_roots_from_major. This is the key bridge for MajorV→MinorV edges.
/// Note: field index 0 is handled separately (see major_field_zero_constraint).
let major_field_one_plus_in_remembered (ms: minor_state) (major: heap) : prop =
  forall (src: obj_addr) (v: U64.t).
    Seq.mem src (objects zero_addr major) /\ ~(is_no_scan src major) /\
    (exists (i: nat). i >= 1 /\ i < U64.v (wosize_of_object src major) /\
      U64.v src + i * 8 + 8 <= heap_size /\
      (U64.v src + i * 8) % 8 == 0 /\
      read_word major (U64.uint_to_t (U64.v src + i * 8)) == v) /\
    is_minor_pointer v /\ Seq.mem v (minor_objects ms) ==>
    Seq.mem v (minor_roots_from_major major)

/// Field 0 of non-closure major objects doesn't contain minor heap pointers.
/// This holds in OCaml-like runtimes where field 0 is typically a code pointer
/// (for closures) or a non-pointer value. For generality, we state it as a
/// constraint that the caller must establish.
let major_field_zero_no_minor (ms: minor_state) (major: heap) : prop =
  forall (src: obj_addr).
    Seq.mem src (objects zero_addr major) /\ ~(is_no_scan src major) /\
    U64.v src + 8 <= heap_size ==>
    (let v = read_word major (U64.uint_to_t (U64.v src)) in
     ~(is_minor_pointer v /\ Seq.mem v (minor_objects ms)))

/// Combined-reachable MinorV → live_set_of.
/// Under the given preconditions, any minor vertex reachable in the combined
/// graph is in the live set (= minor_reachable from roots ∪ remembered).
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
