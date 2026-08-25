/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectForwarding -- Minor-collection forwarding kernel
/// ---------------------------------------------------------------------------
///
/// This module captures the reusable forwarding kernel of the upstream
/// minor-collection isomorphism proof, specialized to the current
/// `minor_collect_full` path.
///
/// The property is intentionally stated over `cheney_collect_spec`, since the
/// Pulse implementation proves its concrete two-pass update equals that spec.
/// The source roots are the program roots plus the remembered-set slot targets;
/// when those remembered targets are represented in the root array and the
/// collector returns `ok`, the forwarding map is an injective morphism for
/// reachable minor objects and all images are valid post-minor addresses
/// (ordinary objects or infix interior pointers).  This is NOT, by itself, a
/// graph isomorphism: the full reachable-subgraph isomorphism additionally
/// proves surjectivity onto the post-minor reachable subgraph and edge
/// preservation/reflection.  The result-indexed wrapper states that theorem
/// directly over the heap and roots returned by `minor_collect_full`.

module GC.Gen.MinorCollectForwarding.Helpers

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Remembered
open GC.Gen.Reachability
open GC.Gen.Cheney

module AllocLemmas = GC.Spec.Allocator.Lemmas
module Mark = GC.Spec.Mark
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module PromUpdate = GC.Gen.PromoteUpdate
module CheneyBFS = GC.Gen.CheneyBFS
module CheneyCorr = GC.Gen.CheneyCorrectness
module CheneyPres = GC.Gen.CheneyPreservation
module CG = GC.Gen.CombinedGraph
module RBridge = GC.Gen.ReachabilityBridge
module GenInv = GC.Gen.HeapInvariant
module HeapGraph = GC.Spec.HeapGraph
module HeapModel = GC.Spec.HeapModel

/// Read the remembered-set slot targets from the pre-collection major heap.
/// Only valid slots containing minor pointers contribute roots.
val remembered_slot_targets_from
  (major: heap) (slots: seq U64.t) (n idx: nat) : GTot (seq U64.t)

let remembered_slot_targets (major: heap) (slots: seq U64.t) (n: nat)
  : GTot (seq U64.t) =
  remembered_slot_targets_from major slots n 0

let remembered_targets_in_roots
  (major: heap) (roots slots: seq U64.t) (n: nat) : prop =
  forall (r: U64.t).
    Seq.mem r (remembered_slot_targets major slots n) ==> Seq.mem r roots

val remembered_targets_in_roots_intro_by_slots:
  major:heap ->
  roots:seq U64.t ->
  slots:seq U64.t ->
  n:nat ->
  Lemma
    (requires n <= Seq.length slots /\
      (forall (i:nat). i < n ==>
        U64.v (Seq.index slots i) < heap_size /\
        U64.v (Seq.index slots i) % U64.v mword == 0 /\
        (let slot = (Seq.index slots i <: hp_addr) in
         let v = to_minor_offset (read_word major slot) in
         is_minor_pointer v ==> Seq.mem v roots)))
    (ensures remembered_targets_in_roots major roots slots n)

#push-options "--z3rlimit 10"
/// Root validity needed to make the target be all concrete post-reachable
/// vertices: a minor-shaped root must be a real live minor object, while a
/// non-minor root must be an allocated major object.
let roots_valid_for_minor_collection
  (minor: minor_state) (major: heap) (roots: seq U64.t) : prop =
  forall (r: U64.t).
    Seq.mem r roots ==>
    ((is_minor_pointer r ==>
      Seq.mem r (minor_objects minor) /\ minor_wosize minor r > 0) /\
     (~(is_minor_pointer r) ==>
     is_val_addr r /\ Seq.mem (r <: obj_addr) (objects zero_addr major) /\
     ~(is_blue (r <: obj_addr) major)))
#pop-options

/// `roots_valid_for_minor_collection` subsumes `RBridge.roots_valid_nonblue`:
/// the non-minor branch of the former already establishes exactly the
/// non-blueness that the latter asserts, under strictly weaker hypotheses
/// (the latter additionally guards on `is_val_addr` and object membership,
/// both of which the former supplies outright).  Callers that already have
/// the former therefore need not carry the latter as a separate assumption.
val roots_valid_for_minor_collection_nonblue
  (minor: minor_state) (major: heap) (roots: seq U64.t)
  : Lemma
    (requires roots_valid_for_minor_collection minor major roots)
    (ensures RBridge.roots_valid_nonblue roots major)

/// The slot table already covers field 0.
///
/// `ref_table_covers_minor_ptrs` quantifies over `j < wosize` at address
/// `obj + j*8`, so `j = 0` -- the word at `obj + 0` -- is included; the write
/// barrier records that field like any other.  Combined with
/// `remembered_targets_in_roots`, which puts every recorded slot's minor target
/// into the Cheney root sequence, the two preconditions that
/// `minor_collect_full` already demands are together enough to discharge
/// `RBridge.major_field_zero_covered` outright.
///
/// Callers therefore do not need to supply a separate field-0 hypothesis at
/// all: it is discharged inside `minor_collect_full` from preconditions the
/// caller was already required to establish.
val major_field_zero_covered_from_slots
  (minor: minor_state) (major: heap) (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n)
    (ensures RBridge.major_field_zero_covered minor major roots)

/// Raw-address view of graph-edge membership, useful when the endpoint is a
/// forwarding-map image whose `hp_addr` refinement is proved by preconditions.
let mem_graph_edge_at (g: graph_state) (src dst: U64.t) : prop =
  exists (s: hp_addr) (d: hp_addr).
    s == src /\ d == dst /\ mem_graph_edge g s d

let mem_graph_vertex_at (g: graph_state) (w: U64.t) : prop =
  exists (x: vertex_id{mem_graph_vertex g x}). x == w

let post_minor_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (w: U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  let res = cheney_collect_spec minor major fp roots in
  let post_g = HeapModel.create_graph res.mc_major in
  exists (rr: U64.t)
         (r: vertex_id{mem_graph_vertex post_g r})
         (x: vertex_id{mem_graph_vertex post_g x}).
    Seq.mem rr (rewrite_roots roots prom.fwd_map) /\
    r == rr /\ x == w /\ reachable post_g r x

let post_minor_edge
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (x y: U64.t) : prop =
  let res = cheney_collect_spec minor major fp roots in
  mem_graph_edge_at (HeapModel.create_graph res.mc_major) x y

/// Result-indexed post-minor reachability: unlike `post_minor_reachable`, this
/// names the concrete heap and rewritten roots exposed by an implementation
/// postcondition.
let result_post_reachable
  (post_major: heap) (post_roots: seq U64.t) (w: U64.t) : prop =
  let post_g = HeapModel.create_graph post_major in
  exists (rr: U64.t)
         (r: vertex_id{mem_graph_vertex post_g r})
         (x: vertex_id{mem_graph_vertex post_g x}).
    Seq.mem rr post_roots /\
    r == rr /\ x == w /\ reachable post_g r x

let result_post_edge (post_major: heap) (x y: U64.t) : prop =
  mem_graph_edge_at (HeapModel.create_graph post_major) x y

val post_minor_reachable_refl_from_root
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (w: U64.t)
  : Lemma
    (requires (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec minor major fp roots in
      Seq.mem w (rewrite_roots roots prom.fwd_map) /\
      mem_graph_vertex_at (HeapModel.create_graph res.mc_major) w))
    (ensures post_minor_reachable minor major fp roots w)

/// Bridge the implementation-facing ref-table coverage predicate to the
/// scan-root coverage predicate used by the combined-graph reachability bridge.
val remembered_roots_in_roots_from_slots
  (major: heap) (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n)
    (ensures RBridge.remembered_roots_in_roots major roots)

/// A major-to-major field is not affected by `update_major_pointers`: existing
/// major object addresses are outside the nursery range.
val update_preserves_major_target_field
  (major: heap) (fwd: forwarding_map) (src dst: obj_addr) (j: nat)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      Seq.mem src (objects zero_addr major) /\
      Seq.mem dst (objects zero_addr major) /\
      j < U64.v (wosize_of_object src major) /\
      U64.v src + j * 8 + 8 <= heap_size /\
      (U64.v src + j * 8) % 8 == 0 /\
      is_blue src major = false /\
      is_no_scan src major = false /\
      read_word major (U64.uint_to_t (U64.v src + j * 8)) == dst)
    (ensures
      read_word (update_major_pointers major fwd)
        (U64.uint_to_t (U64.v src + j * 8)) == dst)

/// Turn a concrete field value in a heap object into a graph edge in
/// `HeapModel.create_graph`.
val heap_field_points_to_graph_edge
  (g: heap) (src: obj_addr) (dst: U64.t) (j: nat)
  : Lemma
    (requires
      well_formed_heap g /\
      no_infix_field_targets g /\
      Seq.mem src (objects zero_addr g) /\
      ~(is_no_scan src g) /\
      j < U64.v (wosize_of_object src g) /\
      U64.v src + j * 8 + 8 <= heap_size /\
      (U64.v src + j * 8) % 8 == 0 /\
      read_word g (U64.uint_to_t (U64.v src + j * 8)) == dst /\
      HeapGraph.is_pointer_field dst)
    (ensures mem_graph_edge (HeapModel.create_graph g) src dst)

val heap_graph_edge_to_pointer_field
  (g: heap) (src dst: obj_addr)
  : Lemma
    (requires mem_graph_edge (HeapModel.create_graph g) src dst /\
              well_formed_heap g /\ no_infix_field_targets g)
    (ensures
      Seq.mem src (objects zero_addr g) /\
      HeapGraph.object_fits_in_heap src g /\
      is_no_scan src g = false /\
      HeapGraph.is_pointer_field dst /\
      (exists (j: U64.t{U64.v j >= 1}).
        U64.v j <= U64.v (wosize_of_object src g) /\
        HeapGraph.get_field g src j == dst))

val heap_graph_edge_to_field_read
  (g: heap) (src dst: obj_addr)
  : Lemma
    (requires mem_graph_edge (HeapModel.create_graph g) src dst /\
              well_formed_heap g /\ no_infix_field_targets g)
    (ensures
      Seq.mem src (objects zero_addr g) /\
      is_no_scan src g = false /\
      HeapGraph.is_pointer_field dst /\
      (exists (j: nat).
        j < U64.v (wosize_of_object src g) /\
        U64.v src + j * 8 + 8 <= heap_size /\
        (U64.v src + j * 8) % 8 == 0 /\
        read_word g (U64.uint_to_t (U64.v src + j * 8)) == dst))

/// Internal helper exposed to later forwarding proof slices.
val mem_graph_vertex_at_is_obj_addr
  (g: heap) (w: U64.t)
  : Lemma
    (requires mem_graph_vertex_at (HeapModel.create_graph g) w)
    (ensures is_val_addr w /\ Seq.mem (w <: obj_addr) (objects zero_addr g))

/// Cheney promotion preserves the header-derived facts and body field of a
/// pre-existing non-blue major object.
val cheney_promote_preserves_old_major_field_context
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: obj_addr) (j: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Seq.mem src (objects zero_addr major) /\
      is_blue src major = false /\
      j < U64.v (wosize_of_object src major) /\
      U64.v src + j * 8 + 8 <= heap_size /\
      (U64.v src + j * 8) % 8 == 0)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      Seq.mem src (objects zero_addr prom.major_final) /\
      is_blue src prom.major_final = false /\
      is_no_scan src prom.major_final == is_no_scan src major /\
      wosize_of_object src prom.major_final == wosize_of_object src major /\
      read_word prom.major_final (U64.uint_to_t (U64.v src + j * 8)) ==
      read_word major (U64.uint_to_t (U64.v src + j * 8))))


/// Internal helper exposed to later forwarding proof slices.
val header_eq_preserves_wosize_no_scan
  (g1 g2: heap) (src: obj_addr)
  : Lemma
    (requires read_word g1 (hd_address src) == read_word g2 (hd_address src))
    (ensures wosize_of_object src g1 == wosize_of_object src g2 /\
             is_no_scan src g1 == is_no_scan src g2)
