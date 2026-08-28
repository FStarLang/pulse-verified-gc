module GC.SPOT.MinorInfix

module U64 = FStar.UInt64
module Seq = FStar.Seq

open FStar.Seq
open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

module SpecObj = GC.Spec.Object
module SpecMark = GC.Spec.Mark
module SpecHeap = GC.Spec.Heap
module HeapGraph = GC.Spec.HeapGraph
module HeapModel = GC.Spec.HeapModel
module GenInv = GC.Gen.HeapInvariant
module Cheney = GC.Gen.Cheney
module CheneyBFS = GC.Gen.CheneyBFS
module CG = GC.Gen.CombinedGraph
module MinorFwd = GC.Gen.MinorCollectForwarding
module MCFE = GC.Gen.MinorCollectForwarding.Edges
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module RBridge = GC.Gen.ReachabilityBridge
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs

#set-options "--fuel 0 --ifuel 1 --z3rlimit 30"

let spot_minor_infix_admissible
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (c: obj_addr) (i: nat)
  =
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.minor_heap_shape_elim minor;
  infix_parent_in_minor_objects minor (stored_target major c i)

/// The classification of the field is the *resolved* one: a field holding an
/// interior nursery pointer is a combined-graph edge to the enclosing closure.
private let scenario_classifies
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (c: obj_addr) (i: nat)
  : Lemma
    (requires minor_infix_scenario minor major fp roots slots n c i)
    (ensures
      CG.classify_major_field minor major
        (SpecHeap.read_word major (field_slot c i)) ==
      Some (CG.MinorV (infix_parent minor (stored_target major c i))))
  =
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.minor_heap_shape_elim minor;
  let ov = stored_target major c i in
  infix_parent_in_minor_objects minor ov;
  assert (resolve_minor minor ov == infix_parent minor ov);
  assert (Seq.mem (resolve_minor minor ov) (minor_objects minor));
  CG.classify_major_field_is_minor minor major
    (SpecHeap.read_word major (field_slot c i))

#push-options "--z3rlimit 60"
let spot_minor_infix_promoted
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (c: obj_addr) (i: nat)
  =
  let ov = stored_target major c i in
  let par = infix_parent minor ov in
  scenario_classifies minor major fp roots slots n c i;
  // the field is rewritten to the image of the word *as stored*
  MCFE.combined_major_minor_field_forwarded
    minor major fp roots slots n c par i;
  // that image is an interior pointer of the post heap resolving to `fwd par`
  MCFH.fwd_image_resolves minor major fp roots ov;
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.minor_heap_shape_elim minor;
  infix_parent_in_minor_objects minor ov;
  assert (resolve_minor minor ov == par);
  // and the graph edge still names the promoted closure
  MCFE.combined_major_minor_edge_forwarded
    minor major fp roots slots n c par i
#pop-options

let spot_minor_infix_was_forbidden
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (c: obj_addr) (i: nat)
  =
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.minor_heap_shape_elim minor;
  GenInv.major_heap_shape_elim major fp;
  RBridge.reachable_major_valid_nonblue minor major roots;
  assert (Seq.mem c (GC.Spec.Fields.objects zero_addr major));
  assert (~(SpecObj.is_blue c major));
  assert (deleted_major_minor_fields_no_infix_targets minor major);
  assert (~(is_infix_in_minor minor (stored_target major c i)))
