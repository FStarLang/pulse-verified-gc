/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectForwarding -- Minor-collection forwarding kernel
/// ---------------------------------------------------------------------------
///
/// This module captures the reusable forwarding kernel of the upstream
/// minor-collection isomorphism proof, specialized to the current
/// `minor_collect_full` path.
///
/// The property is stated over `cheney_collect_spec_except` for a set `pf` of
/// major objects pending free (`no_pending` is the stop-the-world
/// `cheney_collect_spec`), since the Pulse implementation proves its concrete
/// two-pass update equals that spec.  The graphs skip the pending objects as
/// they skip free blocks (vertices with no outgoing edges), and no pending
/// object is reachable: the roots are not pending and a not-freed object points
/// only at not-freed ones.
/// The source roots are the program roots plus the remembered-set slot targets;
/// when those remembered targets are represented in the root array and the
/// collector returns `ok`, the forwarding map is an injective morphism for
/// reachable minor objects and all images are valid post-minor addresses
/// (ordinary objects or infix interior pointers).  This is NOT, by itself, a
/// graph isomorphism: the full reachable-subgraph isomorphism additionally
/// proves surjectivity onto the post-minor reachable subgraph and edge
/// preservation/reflection.  The result-indexed wrapper states that theorem
/// directly over the heap and roots returned by `minor_collect_full`.

module GC.Gen.MinorCollectForwarding.Edges

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
open GC.Gen.Reachability
open GC.Gen.Cheney

module AllocLemmas = GC.Spec.Allocator.Lemmas
module Mark = GC.Spec.Mark
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module PromUpdate = GC.Gen.PromoteUpdate
module Cheney = GC.Gen.Cheney
module CheneyBFS = GC.Gen.CheneyBFS
module CheneyCorr = GC.Gen.CheneyCorrectness
module CheneyPres = GC.Gen.CheneyPreservation
module CG = GC.Gen.CombinedGraph
module RBridge = GC.Gen.ReachabilityBridge
module GenInv = GC.Gen.HeapInvariant
module HeapGraph = GC.Spec.HeapGraph
module HeapModel = GC.Spec.HeapModel

module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module TPC = GC.Gen.TwoPassEquiv.Collect
module CE = GC.Gen.CheneyExcept
open GC.Gen.MinorCollectForwarding.Helpers

/// Statement well-formedness here involves `U64.uint_to_t (v x + j * 8)`
/// side conditions (`FStar.UInt.size ... 64`); with fuel, Z3 5.x unrolls the
/// `FStar.UInt.to_vec` definitions reachable from the context and times out.
/// None of the statements below need recursive unfolding.
#push-options "--fuel 0 --ifuel 0"
val combined_reachable_minor_has_fwd
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t)
  : Lemma
    (requires
      RBridge.major_fields_covered minor major pf roots /\
      well_formed_heap_except major pf /\
      minor_wf minor /\
      GenInv.minor_major_fields_not_freed minor major pf /\
      RBridge.roots_not_freed roots major pf /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures (
      let cg = CG.build_combined_graph minor major pf in
      let combined_roots = CG.classify_roots minor roots in
      let fwd = (cheney_promote minor major fp roots).fwd_map in
      forall (v: U64.t).
        CG.combined_reachable cg combined_roots (CG.MinorV v) /\
        minor_wosize minor v > 0 ==> fwd v <> 0UL))

let combined_reachable_images_valid_or_infix_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t) : prop =
  let cg = CG.build_combined_graph minor major pf in
  let combined_roots = CG.classify_roots minor roots in
  let prom = cheney_promote minor major fp roots in
  let res = cheney_collect_spec_except minor major fp roots pf in
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
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_shape_except minor major fp pf /\
      RBridge.major_fields_covered minor major pf roots /\
      RBridge.roots_not_freed roots major pf /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures combined_reachable_images_valid_or_infix_prop minor major fp pf roots)


/// A live major object's field target keeps its header word --- and therefore
/// its resolution --- across a whole minor collection.  This is what lets a
/// `MajorV src -> MajorV dst` combined-graph edge survive into the
/// post-collection heap graph when the field holds an interior pointer.
val cheney_collect_frame_target_header
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t)
  (h: obj_addr)
  : Lemma
    (requires well_formed_heap_except major pf /\
              AllocLemmas.fl_valid major fp heap_words /\
              AllocLemmas.fl_chain_terminates major fp heap_words /\
              chain_objects_blue major fp /\
              minor_infix_wf minor /\
              GC.Spec.Object.infix_addr_wf major (objects zero_addr major) h /\
              Seq.mem (GC.Spec.Object.resolve_object h major) (objects zero_addr major) /\
              is_blue (GC.Spec.Object.resolve_object h major) major = false)
    (ensures (let res = cheney_collect_spec_except minor major fp roots pf in
              read_word res.mc_major (hd_address h) == read_word major (hd_address h) /\
              GC.Spec.Object.resolve_object h res.mc_major ==
                GC.Spec.Object.resolve_object h major))

/// Concrete MajorV -> MajorV edge-forwarding lemma for the eventual
/// isomorphism: a combined-graph edge between two major objects is still an
/// edge of the post-minor major heap graph.  Only a not-freed object has edges,
/// so the source need not be known reachable.
val combined_major_edge_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t)
  (src dst: obj_addr)
  : Lemma
    (requires
      GenInv.collection_shape_except minor major fp pf /\
      CG.mem_ce (CG.MajorV src, CG.MajorV dst) (CG.build_combined_graph minor major pf))
    (ensures
      (let res = cheney_collect_spec_except minor major fp roots pf in
       mem_graph_edge (HeapModel.create_graph_except res.mc_major pf) src dst))

/// `U64.uint_to_t (v src + i * 8)` side condition, discharged in an empty
/// context: under the full hypotheses of the lemma below Z3 5.x needs more than
/// the default rlimit for this linear fact.
let field_addr_fits (src: U64.t) (i: nat)
  : Lemma (requires U64.v src + i * 8 + 8 <= heap_size)
          (ensures FStar.UInt.size (U64.v src + i * 8) 64)
  = ()

/// Field-level MajorV -> MinorV edge-forwarding lemma: if an old major field
/// points to a reachable positive-size minor object, the post-minor heap stores
/// the target's forwarding address in that field.
val combined_major_minor_field_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop)
  (roots slots: seq U64.t) (n: nat)
  (src: obj_addr) (dst: U64.t) (i: nat)
  : Lemma
    (requires
      GenInv.collection_shape_except minor major fp pf /\
      RBridge.major_fields_covered minor major pf roots /\
      TPC.ref_table_covers_except major pf slots n /\
      remembered_targets_in_roots major roots slots n /\
      RBridge.roots_not_freed roots major pf /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      (let cg = CG.build_combined_graph minor major pf in
       let combined_roots = CG.classify_roots minor roots in
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
      let fa = (field_addr_fits src i; U64.uint_to_t (U64.v src + i * 8)) in
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec_except minor major fp roots pf in
      let ov = to_minor_offset (read_word major fa) in
      prom.fwd_map dst <> 0UL /\
      prom.fwd_map ov <> 0UL /\
      resolve_minor minor ov == dst /\
      read_word res.mc_major fa == prom.fwd_map ov))

val combined_major_minor_edge_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop)
  (roots slots: seq U64.t) (n: nat)
  (src: obj_addr) (dst: U64.t) (i: nat)
  : Lemma
    (requires
      GenInv.collection_shape_except minor major fp pf /\
      RBridge.major_fields_covered minor major pf roots /\
      TPC.ref_table_covers_except major pf slots n /\
      remembered_targets_in_roots major roots slots n /\
      RBridge.roots_not_freed roots major pf /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      (let prom = cheney_promote minor major fp roots in
       HeapGraph.is_pointer_field (prom.fwd_map dst)) /\
      (let cg = CG.build_combined_graph minor major pf in
       let combined_roots = CG.classify_roots minor roots in
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
      let res = cheney_collect_spec_except minor major fp roots pf in
      mem_graph_edge (HeapModel.create_graph_except res.mc_major pf) src (prom.fwd_map dst)))

/// Field-level MinorV -> MajorV edge-forwarding slice: for a promoted normal
/// minor source, a field that points to an old major object remains that major
/// object in the post-minor heap.
val promoted_minor_major_field_preserved
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t)
  (src dst: U64.t) (j: nat)
  : Lemma
    (requires
      GenInv.collection_shape_except minor major fp pf /\
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
      let res = cheney_collect_spec_except minor major fp roots pf in
      read_word res.mc_major (U64.uint_to_t (U64.v (prom.fwd_map src) + j * 8)) == dst))

val promoted_minor_major_edge_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t)
  (src dst: U64.t) (j: nat)
  : Lemma
    (requires
      GenInv.collection_shape_except minor major fp pf /\
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
      let res = cheney_collect_spec_except minor major fp roots pf in
      mem_graph_edge_at (HeapModel.create_graph_except res.mc_major pf) (prom.fwd_map src) dst))

/// Field-level MinorV -> MinorV edge-forwarding slice: for a promoted normal
/// minor source, a copied field that points to another forwarded minor object
/// is rewritten to the target's forwarding address in the post-minor heap.
// the `U64.uint_to_t` in the conclusion needs more than the default budget
#push-options "--z3rlimit 40"
val promoted_minor_minor_field_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t)
  (src dst: U64.t) (j: nat)
  : Lemma
    (requires
      GenInv.collection_shape_except minor major fp pf /\
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
       Some (CG.MinorV dst)) /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec_except minor major fp roots pf in
      let ov = to_minor_offset (minor_read_field minor src j) in
      read_word res.mc_major (U64.uint_to_t (U64.v (prom.fwd_map src) + j * 8)) ==
      prom.fwd_map ov /\
      prom.fwd_map ov <> 0UL /\
      resolve_minor minor ov == dst))
#pop-options

val promoted_minor_minor_edge_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t)
  (src dst: U64.t) (j: nat)
  : Lemma
    (requires
      GenInv.collection_shape_except minor major fp pf /\
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
       Some (CG.MinorV dst)) /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec_except minor major fp roots pf in
      mem_graph_edge_at (HeapModel.create_graph_except res.mc_major pf)
        (prom.fwd_map src) (prom.fwd_map dst)))

/// Side condition for the normal-object edge-forwarding theorem.  Minor-source
/// cases require the source image to be a normal promoted object; minor-target
/// cases require the target image to be pointer-shaped.
#pop-options
