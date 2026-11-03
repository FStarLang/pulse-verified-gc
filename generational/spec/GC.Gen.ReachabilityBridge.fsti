/// ---------------------------------------------------------------------------
/// GC.Gen.ReachabilityBridge -- Combined-graph reachability bridge
/// ---------------------------------------------------------------------------
///
/// Proves reusable facts connecting `CombinedGraph.combined_reachable` to the
/// existing minor-reachability and the major heap's well-formedness on a
/// view.

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
open GC.Gen.CombinedGraph

module Mark = GC.Spec.Mark
module GenInv = GC.Gen.HeapInvariant

/// Two distinct `mword`-aligned addresses differ by at least one word.  Used to
/// turn `addr > zero_addr` (which enumeration gives) into the `is_pointer_field`
/// lower bound `addr >= zero_addr + mword`.
val aligned_gt_ge_plus_mword (x z: nat)
  : Lemma (requires x > z /\ x % U64.v mword == 0 /\ z % U64.v mword == 0)
          (ensures x >= z + U64.v mword)

/// Major roots are in the view when they classify as `MajorV`.
let roots_in_view (v: view) (roots: seq U64.t) (major: heap) : prop =
  forall (r: U64.t).
    Seq.mem r roots /\ ~(is_minor_pointer r) /\
    is_val_addr r /\ Seq.mem (r <: obj_addr) (objects zero_addr major) ==>
    v major (r <: obj_addr)

/// Convert a `MajorV -> MajorV` combined-graph edge witness into the concrete
/// `points_to` relation used by `GC.Spec.Fields.points_to_target_in_view`.
///
/// The field value is exposed *raw*: `points_to` holds of it, and `dst` is its
/// resolution.  The two coincide unless the field holds an interior (infix)
/// pointer, in which case `dst` is the enclosing closure --- which is exactly
/// the vertex the combined graph carries.  Stating it this way lets callers
/// feed the raw target to `points_to_target_in_view`, whose conclusion is
/// already about the resolved target, and so obtain `v major dst`
/// without any no-infix side condition.
val major_edge_points_to
  (minor: minor_state) (major: heap) (src: obj_addr) (dst: U64.t) (i: nat)
  : Lemma
    (requires
      blocks_fit major /\
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

/// Every reachable major vertex is a block of the view: the roots are, a
/// nursery field into the major heap targets one
/// (`minor_major_fields_in_view`), and so does a field of a block of the view
/// (`well_formed_view`).  So a block outside the view is never reachable.
/// (Its fields are never read either way: in the graph it has no edges.)
val reachable_in_view
  (v: view) (minor: minor_state) (major: heap) (roots: seq U64.t)
  : Lemma
    (requires
      well_formed_view v major /\
      minor_wf minor /\
      GenInv.minor_major_fields_in_view v minor major /\
      roots_in_view v roots major)
    (ensures (
      let cg = build_combined_graph minor major v in
      let combined_roots = classify_roots minor roots in
      forall (a: U64.t).
        combined_reachable cg combined_roots (MajorV a) ==>
        U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword == 0 /\
        Seq.mem (a <: obj_addr) (objects zero_addr major) /\
        v major (a <: obj_addr)))

/// Every reachable major vertex is a valid major object.  This weaker form is
/// enough for image-validity proofs and does not require root color facts.
val reachable_major_valid
  (minor: minor_state) (major: heap) (v: view) (roots: seq U64.t)
  : Lemma
    (requires minor_wf minor)
    (ensures (
      let cg = build_combined_graph minor major v in
      let combined_roots = classify_roots minor roots in
      forall (a: U64.t).
        combined_reachable cg combined_roots (MajorV a) ==>
        U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword == 0 /\
        Seq.mem (a <: obj_addr) (objects zero_addr major)))

/// The remembered-set coverage the bridge needs: a live-minor pointer stored
/// in any field of a scannable major block of the view already appears in the
/// Cheney root sequence.  The liveness test is applied to the *resolution* of
/// the stored word, so an interior pointer into a live nursery closure counts
/// as live and must be covered.
///
/// This is exactly what the slot-table preconditions of `minor_collect_full`
/// supply: `ref_table_covers_view` puts the address of every such field
/// (field 0 included) into `slots[0..n)`, and `remembered_targets_in_roots`
/// puts every recorded slot's minor target into `roots` (see
/// `major_fields_covered_from_slots`).  The bridge therefore never needs a
/// whole-heap scan of its own.
let major_fields_covered
  (ms: minor_state) (major: heap) (v: view) (roots: seq U64.t) : prop =
  forall (src: obj_addr) (j: nat).
    v major src /\ ~(is_no_scan src major) /\
    j < U64.v (wosize_of_object src major) /\
    U64.v src + j * 8 + 8 <= heap_size ==>
    (let w = to_minor_offset (read_word major (U64.uint_to_t (U64.v src + j * 8))) in
     is_minor_pointer w /\ Seq.mem (resolve_minor ms w) (minor_objects ms) ==>
     Seq.mem w roots)

/// Any minor vertex reachable in the combined graph is reachable by Cheney
/// from `roots`.  Only a major block of the view has edges, so the remembered
/// set's coverage of those objects is all the major heap must supply.
val reachability_bridge
  (minor: minor_state) (major: heap) (v: view) (roots: seq U64.t)
  : Lemma
    (requires minor_wf minor /\ major_fields_covered minor major v roots)
    (ensures (
      let cg = build_combined_graph minor major v in
      let combined_roots = classify_roots minor roots in
      forall (a: U64.t).
        combined_reachable cg combined_roots (MinorV a) ==>
        Seq.mem a (minor_reachable minor roots)))
