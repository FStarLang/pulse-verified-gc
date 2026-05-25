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
/// graph isomorphism: a real reachable-subgraph isomorphism must also prove
/// surjectivity onto the post-minor reachable subgraph and edge preservation
/// and reflection.  The current proof also keeps the existing pure
/// `cheney_no_oom` condition explicit; connecting the runtime `ok` flag to
/// that pure predicate is the next strengthening step.

module GC.Gen.MinorCollectForwarding

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

let roots_with_remembered (major: heap) (roots slots: seq U64.t) (n: nat)
  : GTot (seq U64.t) =
  Seq.append roots (remembered_slot_targets major slots n)

let remembered_targets_in_roots
  (major: heap) (roots slots: seq U64.t) (n: nat) : prop =
  forall (r: U64.t).
    Seq.mem r (remembered_slot_targets major slots n) ==> Seq.mem r roots

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
    (requires mem_graph_edge (HeapModel.create_graph g) src dst)
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
    (requires mem_graph_edge (HeapModel.create_graph g) src dst)
    (ensures
      Seq.mem src (objects zero_addr g) /\
      is_no_scan src g = false /\
      HeapGraph.is_pointer_field dst /\
      (exists (j: nat).
        j < U64.v (wosize_of_object src g) /\
        U64.v src + j * 8 + 8 <= heap_size /\
        (U64.v src + j * 8) % 8 == 0 /\
        read_word g (U64.uint_to_t (U64.v src + j * 8)) == dst))

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

/// Generic shape of a true reachable-subgraph graph isomorphism.  Re-exported
/// from `CombinedGraph` so callers of this module can name the desired target
/// predicate directly.
let reachable_subgraph_isomorphism = CG.reachable_subgraph_isomorphism

/// Re-export the first concrete bridge needed by the eventual isomorphism:
/// combined-reachable minor vertices correspond to the existing minor live-set
/// notion, under the remembered-set coverage hypotheses named by
/// `ReachabilityBridge`.
let combined_minor_reachable_in_live_set = RBridge.reachability_bridge

/// Stronger root-coverage form: when the scan-derived remembered roots are
/// already included in the Cheney roots, combined-reachable minor vertices are
/// reachable by the actual Cheney promotion.
let combined_minor_reachable_in_minor_reachable =
  RBridge.combined_minor_reachable_in_minor_reachable

/// Combined-reachable minor vertices have forwarding images when promotion does
/// not run out of space and scan-derived remembered roots are included in the
/// Cheney roots.
val combined_reachable_minor_has_fwd
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      RBridge.major_field_zero_no_minor minor major /\
      RBridge.remembered_roots_in_roots major roots /\
      well_formed_heap major /\
      minor_wf minor /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures (
      let cg = CG.build_combined_graph minor major in
      let combined_roots = CG.classify_roots roots in
      let fwd = (cheney_promote minor major fp roots).fwd_map in
      forall (v: U64.t).
        CG.combined_reachable cg combined_roots (CG.MinorV v) /\
        minor_wosize minor v > 0 ==> fwd v <> 0UL))

/// Slot-table-facing form of `combined_reachable_minor_has_fwd`.
val combined_reachable_minor_has_fwd_from_slots
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      RBridge.major_field_zero_no_minor minor major /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      well_formed_heap major /\
      minor_wf minor /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures (
      let cg = CG.build_combined_graph minor major in
      let combined_roots = CG.classify_roots roots in
      let fwd = (cheney_promote minor major fp roots).fwd_map in
      forall (v: U64.t).
        CG.combined_reachable cg combined_roots (CG.MinorV v) /\
        minor_wosize minor v > 0 ==> fwd v <> 0UL))

let combined_reachable_images_valid_or_infix_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  let cg = CG.build_combined_graph minor major in
  let combined_roots = CG.classify_roots roots in
  let prom = cheney_promote minor major fp roots in
  let res = cheney_collect_spec minor major fp roots in
  let fwd = prom.fwd_map in
  (forall (v: U64.t).
    CG.combined_reachable cg combined_roots (CG.MajorV v) ==>
    U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
    Seq.mem (v <: obj_addr) (objects zero_addr res.mc_major)) /\
  (forall (v: U64.t).
    CG.combined_reachable cg combined_roots (CG.MinorV v) /\
    minor_wosize minor v > 0 ==>
    fwd v <> 0UL /\
    U64.v (fwd v) >= U64.v mword /\
    U64.v (fwd v) < heap_size /\
    U64.v (fwd v) % U64.v mword == 0 /\
    (Seq.mem ((fwd v) <: obj_addr) (objects zero_addr prom.major_final) \/
     is_infix (fwd v) prom.major_final))

/// First image-validity conjunct for the eventual isomorphism:
/// - reachable major vertices survive in the post-minor heap;
/// - reachable positive-size minor vertices have valid-or-infix forwarding
///   images in the post-promotion heap.
val combined_reachable_images_valid_or_infix
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
      RBridge.remembered_roots_in_roots major roots /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures combined_reachable_images_valid_or_infix_prop minor major fp roots)

/// Slot-table-facing form of `combined_reachable_images_valid_or_infix`.
val combined_reachable_images_valid_or_infix_from_slots
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures combined_reachable_images_valid_or_infix_prop minor major fp roots)

/// Concrete MajorV -> MajorV edge-forwarding lemma for the eventual
/// isomorphism: if a reachable pre-collection major object has a combined-graph
/// edge to another major object, the post-minor major heap graph still contains
/// the same concrete edge.
val combined_reachable_major_edge_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src dst: obj_addr)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      (let cg = CG.build_combined_graph minor major in
       let combined_roots = CG.classify_roots roots in
       CG.combined_reachable cg combined_roots (CG.MajorV src) /\
       CG.mem_ce (CG.MajorV src, CG.MajorV dst) cg))
    (ensures
      (let res = cheney_collect_spec minor major fp roots in
       mem_graph_edge (HeapModel.create_graph res.mc_major) src dst))

/// Field-level MajorV -> MinorV edge-forwarding lemma: if an old major field
/// points to a reachable positive-size minor object, the post-minor heap stores
/// the target's forwarding address in that field.
val combined_major_minor_field_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (src: obj_addr) (dst: U64.t) (i: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      (let cg = CG.build_combined_graph minor major in
       let combined_roots = CG.classify_roots roots in
       CG.combined_reachable cg combined_roots (CG.MajorV src) /\
       CG.combined_reachable cg combined_roots (CG.MinorV dst)) /\
      ~(is_no_scan src major) /\
      i < U64.v (wosize_of_object src major) /\
      U64.v src + i * 8 + 8 <= heap_size /\
      (U64.v src + i * 8) % 8 == 0 /\
      CG.classify_major_field minor major
        (read_word major (U64.uint_to_t (U64.v src + i * 8))) == Some (CG.MinorV dst) /\
      minor_wosize minor dst > 0)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec minor major fp roots in
      prom.fwd_map dst <> 0UL /\
      read_word res.mc_major (U64.uint_to_t (U64.v src + i * 8)) == prom.fwd_map dst))

val combined_major_minor_edge_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (src: obj_addr) (dst: U64.t) (i: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      (let prom = cheney_promote minor major fp roots in
       HeapGraph.is_pointer_field (prom.fwd_map dst)) /\
      (let cg = CG.build_combined_graph minor major in
       let combined_roots = CG.classify_roots roots in
       CG.combined_reachable cg combined_roots (CG.MajorV src) /\
       CG.combined_reachable cg combined_roots (CG.MinorV dst)) /\
      ~(is_no_scan src major) /\
      i < U64.v (wosize_of_object src major) /\
      U64.v src + i * 8 + 8 <= heap_size /\
      (U64.v src + i * 8) % 8 == 0 /\
      CG.classify_major_field minor major
        (read_word major (U64.uint_to_t (U64.v src + i * 8))) == Some (CG.MinorV dst) /\
      minor_wosize minor dst > 0)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec minor major fp roots in
      mem_graph_edge (HeapModel.create_graph res.mc_major) src (prom.fwd_map dst)))

/// Field-level MinorV -> MajorV edge-forwarding slice: for a promoted normal
/// minor source, a field that points to an old major object remains that major
/// object in the post-minor heap.
val promoted_minor_major_field_preserved
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src dst: U64.t) (j: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      (let prom = cheney_promote minor major fp roots in
       let fwd_src = prom.fwd_map src in
       fwd_src <> 0UL /\
       Seq.mem src (minor_objects minor) /\
       is_val_addr fwd_src /\
       is_infix fwd_src prom.major_final = false /\
       Seq.mem (fwd_src <: obj_addr) (objects zero_addr prom.major_final) /\
       is_blue (fwd_src <: obj_addr) prom.major_final = false /\
       is_no_scan (fwd_src <: obj_addr) prom.major_final = false /\
       is_val_addr dst /\
       j < minor_wosize minor src /\
       j < U64.v (wosize_of_object (fwd_src <: obj_addr) prom.major_final) /\
       U64.v fwd_src + j * 8 + 8 <= heap_size /\
       (U64.v fwd_src + j * 8) % 8 == 0 /\
       CG.classify_minor_field minor major (minor_read_field minor src j) ==
       Some (CG.MajorV dst)))
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec minor major fp roots in
      read_word res.mc_major (U64.uint_to_t (U64.v (prom.fwd_map src) + j * 8)) == dst))

val promoted_minor_major_edge_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src dst: U64.t) (j: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      (let prom = cheney_promote minor major fp roots in
       let fwd_src = prom.fwd_map src in
       fwd_src <> 0UL /\
       Seq.mem src (minor_objects minor) /\
       is_val_addr fwd_src /\
       is_infix fwd_src prom.major_final = false /\
       Seq.mem (fwd_src <: obj_addr) (objects zero_addr prom.major_final) /\
       is_blue (fwd_src <: obj_addr) prom.major_final = false /\
       is_no_scan (fwd_src <: obj_addr) prom.major_final = false /\
       is_val_addr dst /\
       j < minor_wosize minor src /\
       j < U64.v (wosize_of_object (fwd_src <: obj_addr) prom.major_final) /\
       U64.v fwd_src + j * 8 + 8 <= heap_size /\
       (U64.v fwd_src + j * 8) % 8 == 0 /\
       CG.classify_minor_field minor major (minor_read_field minor src j) ==
       Some (CG.MajorV dst)))
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec minor major fp roots in
      mem_graph_edge_at (HeapModel.create_graph res.mc_major) (prom.fwd_map src) dst))

/// Field-level MinorV -> MinorV edge-forwarding slice: for a promoted normal
/// minor source, a copied field that points to another forwarded minor object
/// is rewritten to the target's forwarding address in the post-minor heap.
val promoted_minor_minor_field_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src dst: U64.t) (j: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      (let prom = cheney_promote minor major fp roots in
       let fwd_src = prom.fwd_map src in
       fwd_src <> 0UL /\
       prom.fwd_map dst <> 0UL /\
       Seq.mem src (minor_objects minor) /\
       is_val_addr fwd_src /\
       is_infix fwd_src prom.major_final = false /\
       Seq.mem (fwd_src <: obj_addr) (objects zero_addr prom.major_final) /\
       is_blue (fwd_src <: obj_addr) prom.major_final = false /\
       is_no_scan (fwd_src <: obj_addr) prom.major_final = false /\
       j < minor_wosize minor src /\
       j < U64.v (wosize_of_object (fwd_src <: obj_addr) prom.major_final) /\
       U64.v fwd_src + j * 8 + 8 <= heap_size /\
       (U64.v fwd_src + j * 8) % 8 == 0 /\
       is_minor_pointer dst /\
       CG.classify_minor_field minor major (minor_read_field minor src j) ==
       Some (CG.MinorV dst)))
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec minor major fp roots in
      read_word res.mc_major (U64.uint_to_t (U64.v (prom.fwd_map src) + j * 8)) ==
      prom.fwd_map dst))

val promoted_minor_minor_edge_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src dst: U64.t) (j: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      (let prom = cheney_promote minor major fp roots in
       let fwd_src = prom.fwd_map src in
       fwd_src <> 0UL /\
       prom.fwd_map dst <> 0UL /\
       HeapGraph.is_pointer_field (prom.fwd_map dst) /\
       Seq.mem src (minor_objects minor) /\
       is_val_addr fwd_src /\
       is_infix fwd_src prom.major_final = false /\
       Seq.mem (fwd_src <: obj_addr) (objects zero_addr prom.major_final) /\
       is_blue (fwd_src <: obj_addr) prom.major_final = false /\
       is_no_scan (fwd_src <: obj_addr) prom.major_final = false /\
       j < minor_wosize minor src /\
       j < U64.v (wosize_of_object (fwd_src <: obj_addr) prom.major_final) /\
       U64.v fwd_src + j * 8 + 8 <= heap_size /\
       (U64.v fwd_src + j * 8) % 8 == 0 /\
       is_minor_pointer dst /\
       CG.classify_minor_field minor major (minor_read_field minor src j) ==
       Some (CG.MinorV dst)))
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec minor major fp roots in
      mem_graph_edge_at (HeapModel.create_graph res.mc_major)
        (prom.fwd_map src) (prom.fwd_map dst)))

/// Side condition for the normal-object edge-forwarding theorem.  Minor-source
/// cases require the source image to be a normal promoted object; minor-target
/// cases require the target image to be pointer-shaped.
let normal_edge_forward_ready
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (u v: CG.combined_vertex) : prop =
  let prom = cheney_promote minor major fp roots in
  let normal_minor_source (src: U64.t) =
    let fwd_src = prom.fwd_map src in
    fwd_src <> 0UL /\
    Seq.mem src (minor_objects minor) /\
    is_val_addr fwd_src /\
    is_infix fwd_src prom.major_final = false /\
    Seq.mem (fwd_src <: obj_addr) (objects zero_addr prom.major_final) /\
    is_blue (fwd_src <: obj_addr) prom.major_final = false /\
    is_no_scan (fwd_src <: obj_addr) prom.major_final = false /\
    U64.v (wosize_of_object (fwd_src <: obj_addr) prom.major_final) >=
      minor_wosize minor src /\
    (forall (i:nat). i < minor_wosize minor src ==>
      i < U64.v (wosize_of_object (fwd_src <: obj_addr) prom.major_final) /\
      U64.v fwd_src + i * 8 + 8 <= heap_size /\
      (U64.v fwd_src + i * 8) % 8 == 0)
  in
  match u, v with
  | CG.MajorV _, CG.MajorV _ -> True
  | CG.MajorV _, CG.MinorV dst ->
    minor_wosize minor dst > 0 /\
    HeapGraph.is_pointer_field (prom.fwd_map dst)
  | CG.MinorV src, CG.MajorV dst ->
    normal_minor_source src /\ is_val_addr dst
  | CG.MinorV src, CG.MinorV dst ->
    normal_minor_source src /\
    prom.fwd_map dst <> 0UL /\
    HeapGraph.is_pointer_field (prom.fwd_map dst) /\
    is_minor_pointer dst

/// Composed forward-edge theorem for the normal reachable subgraph: any
/// reachable combined edge satisfying `normal_edge_forward_ready` maps to a
/// concrete edge in the post-minor major heap graph.
val combined_reachable_edge_forwarded_normal
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      (let cg = CG.build_combined_graph minor major in
       let combined_roots = CG.classify_roots roots in
       CG.combined_reachable cg combined_roots u /\
       CG.combined_reachable cg combined_roots v /\
       CG.mem_ce (u, v) cg) /\
      normal_edge_forward_ready minor major fp roots u v)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec minor major fp roots in
      mem_graph_edge_at (HeapModel.create_graph res.mc_major)
        (CG.fwd_morphism prom.fwd_map u)
        (CG.fwd_morphism prom.fwd_map v)))

let combined_reachable_normal_edges_forwarded_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  let cg = CG.build_combined_graph minor major in
  let combined_roots = CG.classify_roots roots in
  let prom = cheney_promote minor major fp roots in
  let res = cheney_collect_spec minor major fp roots in
  forall (u v: CG.combined_vertex).
    CG.combined_reachable cg combined_roots u /\
    CG.combined_reachable cg combined_roots v /\
    CG.mem_ce (u, v) cg /\
    normal_edge_forward_ready minor major fp roots u v ==>
    mem_graph_edge_at (HeapModel.create_graph res.mc_major)
      (CG.fwd_morphism prom.fwd_map u)
      (CG.fwd_morphism prom.fwd_map v)

/// Disjointness assumption needed for cross-generation injectivity: normal
/// forwarding targets are not old non-blue major objects.
let fwd_disjoint_reachable_major
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  let cg = CG.build_combined_graph minor major in
  let combined_roots = CG.classify_roots roots in
  let prom = cheney_promote minor major fp roots in
  forall (x y: U64.t).
    CG.combined_reachable cg combined_roots (CG.MinorV x) /\
    CG.combined_reachable cg combined_roots (CG.MajorV y) /\
    prom.fwd_map x <> 0UL /\
    is_val_addr (prom.fwd_map x) /\
    is_infix (prom.fwd_map x) prom.major_final = false ==>
    prom.fwd_map x <> y

val fwd_disjoint_reachable_major_intro
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major)
    (ensures fwd_disjoint_reachable_major minor major fp roots)

val minor_source_edge_not_no_scan
  (minor: minor_state) (major: heap) (fp: U64.t)
  (src: U64.t) (dst: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      CG.mem_ce (CG.MinorV src, dst) (CG.build_combined_graph minor major))
    (ensures minor_tag minor src < 251)

let combined_reachable_normal_injective_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  let cg = CG.build_combined_graph minor major in
  let combined_roots = CG.classify_roots roots in
  let prom = cheney_promote minor major fp roots in
  forall (u v: CG.combined_vertex).
    CG.combined_reachable cg combined_roots u /\
    CG.combined_reachable cg combined_roots v /\
    (match u with
     | CG.MinorV x ->
       prom.fwd_map x <> 0UL /\
       is_val_addr (prom.fwd_map x) /\
       is_infix (prom.fwd_map x) prom.major_final = false
     | CG.MajorV _ -> True) /\
    (match v with
     | CG.MinorV x ->
       prom.fwd_map x <> 0UL /\
       is_val_addr (prom.fwd_map x) /\
       is_infix (prom.fwd_map x) prom.major_final = false
     | CG.MajorV _ -> True) /\
    CG.fwd_morphism prom.fwd_map u == CG.fwd_morphism prom.fwd_map v ==> u == v

let normal_vertex_ready
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (u: CG.combined_vertex) : prop =
  let prom = cheney_promote minor major fp roots in
  match u with
  | CG.MajorV _ -> True
  | CG.MinorV x ->
    prom.fwd_map x <> 0UL /\
    is_val_addr (prom.fwd_map x) /\
    is_infix (prom.fwd_map x) prom.major_final = false

let normal_src_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (u: CG.combined_vertex) : prop =
  let cg = CG.build_combined_graph minor major in
  let combined_roots = CG.classify_roots roots in
  CG.combined_reachable cg combined_roots u /\
  normal_vertex_ready minor major fp roots u

val normal_edge_forward_ready_intro
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      normal_src_reachable minor major fp roots u /\
      normal_src_reachable minor major fp roots v /\
      CG.mem_ce (u, v) (CG.build_combined_graph minor major))
    (ensures normal_edge_forward_ready minor major fp roots u v)

val normal_classified_root_image_in_rewrite_roots
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (u: CG.combined_vertex)
  : Lemma
    (requires
      Seq.mem u (CG.classify_roots roots) /\
      normal_vertex_ready minor major fp roots u)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      Seq.mem (CG.fwd_morphism prom.fwd_map u)
        (rewrite_roots roots prom.fwd_map)))

let normal_src_edge
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (u v: CG.combined_vertex) : prop =
  let cg = CG.build_combined_graph minor major in
  normal_src_reachable minor major fp roots u /\
  normal_src_reachable minor major fp roots v /\
  CG.mem_ce (u, v) cg /\
  normal_edge_forward_ready minor major fp roots u v

noeq type ready_src_reach
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : CG.combined_vertex -> Type =
  | ReadyRoot :
      u:CG.combined_vertex ->
      (Seq.mem u (CG.classify_roots roots) /\
       CG.mem_cv u (CG.build_combined_graph minor major) /\
       normal_vertex_ready minor major fp roots u) ->
      ready_src_reach minor major fp roots u
  | ReadyStep :
      u:CG.combined_vertex ->
      v:CG.combined_vertex ->
      ready_src_reach minor major fp roots u ->
      normal_src_edge minor major fp roots u v ->
      ready_src_reach minor major fp roots v

let ready_src_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (u: CG.combined_vertex) : prop =
  exists (_: ready_src_reach minor major fp roots u). True

let ready_image_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (w: U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  exists (u: CG.combined_vertex).
    ready_src_reachable minor major fp roots u /\
    CG.fwd_morphism prom.fwd_map u == w

let ready_src_edge
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (u v: CG.combined_vertex) : prop =
  ready_src_reachable minor major fp roots u /\
  ready_src_reachable minor major fp roots v /\
  normal_src_edge minor major fp roots u v

let ready_image_edge
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (x y: U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  exists (u v: CG.combined_vertex).
    ready_src_edge minor major fp roots u v /\
    CG.fwd_morphism prom.fwd_map u == x /\
    CG.fwd_morphism prom.fwd_map v == y

let ready_image_reachable_subgraph_isomorphism_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  CG.reachable_subgraph_isomorphism
    (ready_src_reachable minor major fp roots)
    (ready_image_reachable minor major fp roots)
    (ready_src_edge minor major fp roots)
    (ready_image_edge minor major fp roots)
    prom.fwd_map

let normal_image_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (w: U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  exists (u: CG.combined_vertex).
    normal_src_reachable minor major fp roots u /\
    CG.fwd_morphism prom.fwd_map u == w

let normal_image_edge
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (x y: U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  exists (u v: CG.combined_vertex).
    normal_src_edge minor major fp roots u v /\
    CG.fwd_morphism prom.fwd_map u == x /\
    CG.fwd_morphism prom.fwd_map v == y

val normal_image_vertex_is_post_vertex
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (w: U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      normal_image_reachable minor major fp roots w)
    (ensures (
      let res = cheney_collect_spec minor major fp roots in
      mem_graph_vertex_at (HeapModel.create_graph res.mc_major) w))

let normal_image_vertices_are_post_vertices_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  let res = cheney_collect_spec minor major fp roots in
  forall (w: U64.t).
    normal_image_reachable minor major fp roots w ==>
    mem_graph_vertex_at (HeapModel.create_graph res.mc_major) w

val normal_image_vertices_are_post_vertices
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires GenInv.collection_heap_shape minor major fp)
    (ensures normal_image_vertices_are_post_vertices_prop minor major fp roots)

val normal_classified_root_image_post_reachable
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (u: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Seq.mem u (CG.classify_roots roots) /\
      normal_src_reachable minor major fp roots u)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      post_minor_reachable minor major fp roots
        (CG.fwd_morphism prom.fwd_map u)))

let normal_image_reachable_subgraph_isomorphism_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  CG.reachable_subgraph_isomorphism
    (normal_src_reachable minor major fp roots)
    (normal_image_reachable minor major fp roots)
    (normal_src_edge minor major fp roots)
    (normal_image_edge minor major fp roots)
    prom.fwd_map

val combined_reachable_normal_injective
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      fwd_disjoint_reachable_major minor major fp roots)
    (ensures combined_reachable_normal_injective_prop minor major fp roots)

val normal_image_reachable_subgraph_isomorphism
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      fwd_disjoint_reachable_major minor major fp roots)
    (ensures normal_image_reachable_subgraph_isomorphism_prop minor major fp roots)

let normal_image_edges_are_post_edges_prop
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat) : prop =
  let prom = cheney_promote minor major fp roots in
  let res = cheney_collect_spec minor major fp roots in
  forall (u v: CG.combined_vertex).
    normal_src_edge minor major fp roots u v ==>
    mem_graph_edge_at (HeapModel.create_graph res.mc_major)
      (CG.fwd_morphism prom.fwd_map u)
      (CG.fwd_morphism prom.fwd_map v)

val normal_image_edges_are_post_edges
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures normal_image_edges_are_post_edges_prop minor major fp roots slots n)

val normal_src_edge_preserves_post_minor_reachable
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      normal_src_edge minor major fp roots u v /\
      (let prom = cheney_promote minor major fp roots in
       post_minor_reachable minor major fp roots
         (CG.fwd_morphism prom.fwd_map u)))
    (ensures (
      let prom = cheney_promote minor major fp roots in
      post_minor_reachable minor major fp roots
        (CG.fwd_morphism prom.fwd_map v)))

val ready_src_reach_image_post_reachable
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (u: CG.combined_vertex)
  (r: ready_src_reach minor major fp roots u)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      post_minor_reachable minor major fp roots
        (CG.fwd_morphism prom.fwd_map u)))

val ready_image_reachable_is_post_reachable
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (w: U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      ready_image_reachable minor major fp roots w)
    (ensures post_minor_reachable minor major fp roots w)

let ready_image_reachable_is_post_reachable_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  forall (w: U64.t).
    ready_image_reachable minor major fp roots w ==>
    post_minor_reachable minor major fp roots w

val ready_image_reachable_is_post_reachable_all
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures ready_image_reachable_is_post_reachable_prop minor major fp roots)

val ready_image_reachable_subgraph_isomorphism
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major)
    (ensures ready_image_reachable_subgraph_isomorphism_prop minor major fp roots)

val normal_src_reachable_is_ready_src_reachable
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (u: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      normal_src_reachable minor major fp roots u)
    (ensures ready_src_reachable minor major fp roots u)

let normal_image_reachable_is_post_reachable_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  forall (w: U64.t).
    normal_image_reachable minor major fp roots w ==>
    post_minor_reachable minor major fp roots w

val normal_image_reachable_is_post_reachable
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (w: U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      normal_image_reachable minor major fp roots w)
    (ensures post_minor_reachable minor major fp roots w)

val normal_image_reachable_is_post_reachable_all
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures normal_image_reachable_is_post_reachable_prop minor major fp roots)

let normal_post_image_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (w: U64.t) : prop =
  post_minor_reachable minor major fp roots w /\
  normal_image_reachable minor major fp roots w

let normal_post_image_reachable_subgraph_isomorphism_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  CG.reachable_subgraph_isomorphism
    (normal_src_reachable minor major fp roots)
    (normal_post_image_reachable minor major fp roots)
    (normal_src_edge minor major fp roots)
    (post_minor_edge minor major fp roots)
    prom.fwd_map

val post_normal_image_edges_reflect_src
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      normal_src_reachable minor major fp roots u /\
      normal_src_reachable minor major fp roots v /\
      (let prom = cheney_promote minor major fp roots in
       post_minor_edge minor major fp roots
         (CG.fwd_morphism prom.fwd_map u)
         (CG.fwd_morphism prom.fwd_map v)))
    (ensures normal_src_edge minor major fp roots u v)

val normal_post_image_reachable_subgraph_isomorphism
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures normal_post_image_reachable_subgraph_isomorphism_prop minor major fp roots)

let post_minor_reachable_is_normal_image_reachable_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  forall (w: U64.t).
    post_minor_reachable minor major fp roots w ==>
    normal_image_reachable minor major fp roots w

let normal_post_reachable_subgraph_isomorphism_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  CG.reachable_subgraph_isomorphism
    (normal_src_reachable minor major fp roots)
    (post_minor_reachable minor major fp roots)
    (normal_src_edge minor major fp roots)
    (post_minor_edge minor major fp roots)
    prom.fwd_map

/// The post-minor forwarding kernel established by `minor_collect_full`.
[@@"opaque_to_smt"]
let minor_collect_full_forwarding_kernel
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat) (ok: bool)
  (post_major: heap) (post_roots: seq U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  let res = cheney_collect_spec minor major fp roots in
  let fwd = prom.fwd_map in
  post_major == res.mc_major /\
  post_roots == rewrite_roots roots fwd /\
  (forall (obj: obj_addr). Seq.mem obj (objects zero_addr major) ==>
    Seq.mem obj (objects zero_addr post_major)) /\
  // Conditional isomorphism kernel.  Full graph isomorphism only makes sense
  // when all remembered targets are part of the root set and promotion succeeds.
  (remembered_targets_in_roots major roots slots n /\
   ok /\
   CheneyBFS.cheney_no_oom minor major fp roots ==>
    // Reachable minor vertices have images.
    (forall (x: U64.t). Seq.mem x (minor_reachable minor roots) /\
      minor_wosize minor x > 0 ==> fwd x <> 0UL) /\
    // Images are valid post-promotion major addresses, allowing infix interior
    // pointers for minor infix vertices.
    CheneyPres.fwd_valid_or_infix fwd prom.major_final /\
    // Normal images are injective and non-blue.
    CheneyPres.fwd_normal_injective fwd prom.major_final /\
    CheneyPres.fwd_targets_not_blue fwd prom.major_final /\
    (RBridge.major_field_zero_no_minor minor major /\
     RBridge.remembered_roots_in_roots major roots /\
     Mark.no_pointer_to_blue major /\
     RBridge.minor_no_pointer_to_blue minor major /\
     RBridge.roots_valid_nonblue roots major ==>
     combined_reachable_images_valid_or_infix_prop minor major fp roots) /\
    (UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
     RBridge.major_field_zero_no_minor minor major /\
     Mark.no_pointer_to_blue major /\
     RBridge.minor_no_pointer_to_blue minor major /\
     RBridge.roots_valid_nonblue roots major ==>
     combined_reachable_images_valid_or_infix_prop minor major fp roots /\
     combined_reachable_normal_edges_forwarded_prop minor major fp roots)
    /\
    (UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
     RBridge.major_field_zero_no_minor minor major /\
     Mark.no_pointer_to_blue major /\
     RBridge.minor_no_pointer_to_blue minor major /\
     RBridge.roots_valid_nonblue roots major ==>
     combined_reachable_normal_injective_prop minor major fp roots /\
     normal_image_vertices_are_post_vertices_prop minor major fp roots /\
     normal_image_reachable_subgraph_isomorphism_prop minor major fp roots /\
     normal_image_edges_are_post_edges_prop minor major fp roots slots n /\
     ready_image_reachable_subgraph_isomorphism_prop minor major fp roots /\
     ready_image_reachable_is_post_reachable_prop minor major fp roots /\
     normal_image_reachable_is_post_reachable_prop minor major fp roots /\
     normal_post_image_reachable_subgraph_isomorphism_prop minor major fp roots))

val post_minor_reachable_is_normal_image_reachable_all
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      roots_valid_for_minor_collection minor major roots /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures post_minor_reachable_is_normal_image_reachable_prop minor major fp roots)

val normal_post_reachable_subgraph_isomorphism
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      roots_valid_for_minor_collection minor major roots /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures normal_post_reachable_subgraph_isomorphism_prop minor major fp roots)

val minor_collect_full_forwarding_kernel_intro
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat) (ok: bool)
  : Lemma
    (requires GenInv.collection_heap_shape minor major fp)
    (ensures (
      let res = cheney_collect_spec minor major fp roots in
      minor_collect_full_forwarding_kernel minor major fp roots slots n ok
        res.mc_major (rewrite_roots roots (cheney_promote minor major fp roots).fwd_map)))
