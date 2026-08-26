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
module GenInv = GC.Gen.HeapInvariant

/// If a minor object has a field pointing to the major heap, the target is a
/// non-blue allocated object.
let minor_no_pointer_to_blue (minor: minor_state) (major: heap) : prop =
  forall (obj: U64.t) (j: nat).
    Seq.mem obj (minor_objects minor) /\ j < minor_wosize minor obj ==>
    (let v = minor_read_field minor obj j in
     is_val_addr v /\ Seq.mem (v <: obj_addr) (objects zero_addr major) ==>
     ~(is_blue (v <: obj_addr) major))

/// Two distinct `mword`-aligned addresses differ by at least one word.  Used to
/// turn `addr > zero_addr` (which enumeration gives) into the `is_pointer_field`
/// lower bound `addr >= zero_addr + mword`.
val aligned_gt_ge_plus_mword (x z: nat)
  : Lemma (requires x > z /\ x % U64.v mword == 0 /\ z % U64.v mword == 0)
          (ensures x >= z + U64.v mword)

/// The central collection heap shape already contains the stronger
/// `GenInv.minor_major_fields_no_blue` condition; expose this bridge predicate
/// as a derived fact so clients do not need to carry it as an extra assumption.
val minor_no_pointer_to_blue_from_collection_shape
  (minor: minor_state) (major: heap) (fp: U64.t)
  : Lemma (requires GenInv.collection_heap_shape minor major fp)
          (ensures minor_no_pointer_to_blue minor major)

/// Major roots must be valid non-blue objects when they classify as `MajorV`.
let roots_valid_nonblue (roots: seq U64.t) (major: heap) : prop =
  forall (r: U64.t).
    Seq.mem r roots /\ ~(is_minor_pointer r) /\
    is_val_addr r /\ Seq.mem (r <: obj_addr) (objects zero_addr major) ==>
    ~(is_blue (r <: obj_addr) major)

/// Convert a `MajorV -> MajorV` combined-graph edge witness into the concrete
/// `points_to` relation used by `Mark.no_pointer_to_blue`.
///
/// The field value is exposed *raw*: `points_to` holds of it, and `dst` is its
/// resolution.  The two coincide unless the field holds an interior (infix)
/// pointer, in which case `dst` is the enclosing closure --- which is exactly
/// the vertex the combined graph carries.  Stating it this way lets callers
/// feed the raw target to `Mark.no_pointer_to_blue`, whose conclusion is
/// already about the resolved target, and so obtain `~(is_blue dst major)`
/// without any no-infix side condition.
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
    (ensures (
      let raw = read_word major (U64.uint_to_t (U64.v src + i * 8)) in
      is_val_addr dst /\ is_val_addr raw /\ is_pointer_field raw /\
      points_to major src (raw <: obj_addr) /\
      dst == resolve_object (raw <: obj_addr) major))

/// Major-heap objects live above the nursery range, so pointer-update logic
/// cannot mistake an existing major object address for a minor pointer.
val major_object_not_minor_pointer
  (major: heap) (obj: obj_addr)
  : Lemma (requires Seq.mem obj (objects zero_addr major))
          (ensures ~(is_minor_pointer obj) /\ to_minor_offset obj == obj)

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

/// Field 0 is not scanned by the remembered-set model (`scan_object_fields`
/// starts at field index 1), so the generic bridge needs a separate hypothesis
/// covering the word at `obj + 0`.
///
/// `major_field_zero_covered` is the right one: it requires only that a
/// live-minor pointer stored in a scannable non-blue object's first field
/// already appears in the Cheney root sequence.  The liveness test is applied
/// to the *resolution* of the stored word, so an interior pointer into a live
/// nursery closure counts as live and must be covered.  That is exactly what the
/// slot-table preconditions of `minor_collect_full` supply, since
/// `ref_table_covers_minor_ptrs` quantifies over `j < wosize` and so does
/// cover `j = 0` (see `major_field_zero_covered_from_slots`).
let major_field_zero_covered
  (ms: minor_state) (major: heap) (roots: seq U64.t) : prop =
  forall (src: obj_addr).
    Seq.mem src (objects zero_addr major) /\
    ~(is_blue src major) /\ ~(is_no_scan src major) /\
    0 < U64.v (wosize_of_object src major) /\
    U64.v src + 8 <= heap_size ==>
    (let v = to_minor_offset (read_word major (U64.uint_to_t (U64.v src))) in
     is_minor_pointer v /\ Seq.mem (resolve_minor ms v) (minor_objects ms) ==>
     Seq.mem v roots)


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
      major_field_zero_covered minor major roots)
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
      major_field_zero_covered minor major roots /\
      remembered_roots_in_roots major roots)
    (ensures (
      let cg = build_combined_graph minor major in
      let combined_roots = classify_roots roots in
      forall (v: U64.t).
        combined_reachable cg combined_roots (MinorV v) ==>
        Seq.mem v (minor_reachable minor roots)))
