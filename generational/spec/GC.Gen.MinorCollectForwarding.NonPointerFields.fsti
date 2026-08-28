/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectForwarding.NonPointerFields
/// ---------------------------------------------------------------------------
///
/// Preservation of non-pointer field contents across a normal minor collection.

module GC.Gen.MinorCollectForwarding.NonPointerFields

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

module Mark = GC.Spec.Mark
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module CheneyBFS = GC.Gen.CheneyBFS
module CG = GC.Gen.CombinedGraph
module RBridge = GC.Gen.ReachabilityBridge
module GenInv = GC.Gen.HeapInvariant

module MCFH = GC.Gen.MinorCollectForwarding.Helpers
open GC.Gen.MinorCollectForwarding.Helpers

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
  let combined_roots = CG.classify_roots minor roots in
  CG.combined_reachable cg combined_roots u /\
  normal_vertex_ready minor major fp roots u

let normal_post_non_pointer_fields_preserved_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  let res = cheney_collect_spec minor major fp roots in
  forall (u: CG.combined_vertex).
    normal_src_reachable minor major fp roots u ==>
    (match u with
    | CG.MajorV src ->
      is_val_addr src ==>
      forall (j:nat).
        j < U64.v (wosize_of_object (src <: obj_addr) major) /\
        U64.v src + j * 8 + 8 <= heap_size /\
        (U64.v src + j * 8) % 8 == 0 /\
        CG.classify_major_field minor major
          (read_word major (U64.uint_to_t (U64.v src + j * 8))) == None ==>
        read_word res.mc_major (U64.uint_to_t (U64.v src + j * 8)) ==
        read_word major (U64.uint_to_t (U64.v src + j * 8))
    | CG.MinorV src ->
      let img = prom.fwd_map src in
      is_val_addr img ==>
      forall (j:nat).
        j < minor_wosize minor src /\
        j < U64.v (wosize_of_object (img <: obj_addr) prom.major_final) /\
        U64.v img + j * 8 + 8 <= heap_size /\
        (U64.v img + j * 8) % 8 == 0 /\
        CG.classify_minor_field minor major (minor_read_field minor src j) == None ==>
        read_word res.mc_major (U64.uint_to_t (U64.v img + j * 8)) ==
        minor_read_field minor src j
    | _ -> True)

let normal_result_non_pointer_fields_preserved_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (post_major: heap) : prop =
  let prom = cheney_promote minor major fp roots in
  forall (u: CG.combined_vertex).
    normal_src_reachable minor major fp roots u ==>
    (match u with
    | CG.MajorV src ->
      is_val_addr src ==>
      forall (j:nat).
        j < U64.v (wosize_of_object (src <: obj_addr) major) /\
        U64.v src + j * 8 + 8 <= heap_size /\
        (U64.v src + j * 8) % 8 == 0 /\
        CG.classify_major_field minor major
          (read_word major (U64.uint_to_t (U64.v src + j * 8))) == None ==>
        read_word post_major (U64.uint_to_t (U64.v src + j * 8)) ==
        read_word major (U64.uint_to_t (U64.v src + j * 8))
    | CG.MinorV src ->
      let img = prom.fwd_map src in
      is_val_addr img ==>
      forall (j:nat).
        j < minor_wosize minor src /\
        j < U64.v (wosize_of_object (img <: obj_addr) prom.major_final) /\
        U64.v img + j * 8 + 8 <= heap_size /\
        (U64.v img + j * 8) % 8 == 0 /\
        CG.classify_minor_field minor major (minor_read_field minor src j) == None ==>
        read_word post_major (U64.uint_to_t (U64.v img + j * 8)) ==
        minor_read_field minor src j
    | _ -> True)

val normal_post_non_pointer_fields_preserved
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_covered minor major roots /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      roots_valid_for_minor_collection minor major roots /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures normal_post_non_pointer_fields_preserved_prop minor major fp roots)

val normal_post_non_pointer_fields_preserved_to_result
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (post_major: heap)
  : Lemma
    (requires
      post_major == (cheney_collect_spec minor major fp roots).mc_major /\
      normal_post_non_pointer_fields_preserved_prop minor major fp roots)
    (ensures
      normal_result_non_pointer_fields_preserved_prop
        minor major fp roots post_major)
