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
open GC.Gen.Reachability
open GC.Gen.Cheney

module Mark = GC.Spec.Mark
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module CheneyBFS = GC.Gen.CheneyBFS
module CG = GC.Gen.CombinedGraph
module RBridge = GC.Gen.ReachabilityBridge
module GenInv = GC.Gen.HeapInvariant

module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module TPC = GC.Gen.TwoPassEquiv.Collect
module CE = GC.Gen.CheneyExcept
open GC.Gen.MinorCollectForwarding.Helpers

/// Statement well-formedness here involves `U64.uint_to_t (v x + j * 8)`
/// side conditions (`FStar.UInt.size ... 64`); with fuel, Z3 5.x unrolls the
/// `FStar.UInt.to_vec` definitions reachable from the context and times out.
/// None of the statements below need recursive unfolding.
#push-options "--fuel 0 --ifuel 1"
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
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  let res = cheney_collect_spec_except minor major fp roots pf in
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
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop)
  (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      GenInv.collection_shape_except minor major fp pf /\
      RBridge.major_fields_covered minor major pf roots /\
      TPC.ref_table_covers_except major pf slots n /\
      remembered_targets_in_roots major roots slots n /\
      RBridge.roots_not_freed roots major pf /\
      roots_valid_except minor major pf roots /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures normal_post_non_pointer_fields_preserved_prop minor major fp pf roots)

val normal_post_non_pointer_fields_preserved_to_result
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t)
  (post_major: heap)
  : Lemma
    (requires
      post_major == (cheney_collect_spec_except minor major fp roots pf).mc_major /\
      normal_post_non_pointer_fields_preserved_prop minor major fp pf roots)
    (ensures
      normal_result_non_pointer_fields_preserved_prop
        minor major fp roots post_major)
#pop-options
