module GC.Gen.ChunkedMajorGCBridge

module Seq = FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap

module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module ChunkedMark = GC.Spec.ChunkedMarkBounded.Defs
module ChunkedMarkPres = GC.Spec.ChunkedMarkBounded.Preservation
module ChunkedMarkReadiness = GC.Spec.ChunkedMarkBounded.Readiness
module ChunkedMarkTargetMembership = GC.Spec.ChunkedMarkBounded.TargetMembership
module ChunkedMarkTargetReady = GC.Spec.ChunkedMarkBounded.TargetReady
module ChunkedMarkLive = GC.Spec.ChunkedMajorGC.MarkLiveness
module ChunkedMajorGCRoots = GC.Spec.ChunkedMajorGC.Roots
module ChunkedMarkEdge = GC.Spec.ChunkedMarkBounded.EdgeInvariant
module ChunkedMajorGraph = GC.Spec.ChunkedMajorGC.Graph
module ChunkedMajorGC = GC.Spec.ChunkedMajorGC.Defs
module ChunkedMajorGCCorr = GC.Spec.ChunkedMajorGC.Correctness
module ChunkedMajorReach = GC.Spec.ChunkedMajorGC.Reachability
module ChunkedMarkNoBlack = GC.Spec.ChunkedMarkBounded.NoBlackToWhite
module GenInv = GC.Gen.HeapInvariant
module CG = GC.Gen.CombinedGraph

val chunked_major_roots_nonblue
  : mh:MH.major_heap -> roots:Seq.seq obj_addr -> Tot prop

val chunked_sweep_black_implies_gen_black
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires SweepDefs.chunked_is_black mh obj)
      (ensures GenInv.chunked_is_black mh obj)

val chunked_no_black_objects_implies_no_black_to_white_vertex_targets
  (mh: MH.major_heap)
  : Lemma
      (requires GenInv.chunked_no_black_objects mh)
      (ensures
        ChunkedMarkNoBlack.chunked_no_black_to_white_vertex_targets mh)

val chunked_collection_heap_shape_implies_no_black_to_white_vertex_targets
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (fuel: nat)
  : Lemma
      (requires GenInv.chunked_collection_heap_shape minor mh fp fuel)
      (ensures
        ChunkedMarkNoBlack.chunked_no_black_to_white_vertex_targets mh)

val chunked_major_edge_gen_field_witness
  (mh: MH.major_heap)
  : prop

val chunked_major_edge_gen_field_witness_intro
  (mh: MH.major_heap)
  : Lemma
      (requires
        forall (src dst: obj_addr).
          ChunkedMajorGraph.chunked_major_edge mh src dst /\
          ChunkedMajorGraph.chunked_major_vertex mh dst ==>
          exists (idx: nat) (field_addr: hp_addr) (raw: U64.t).
            Seq.mem src (MH.major_objects mh) /\
            idx < CG.chunked_wosize_nat_of_object mh src /\
            CG.chunked_major_field_slot src idx == Some field_addr /\
            MH.read_word_in_major mh field_addr == Some raw /\
            Seq.mem dst (MH.major_objects mh) /\
            is_pointer_to raw dst)
      (ensures chunked_major_edge_gen_field_witness mh)

val chunked_major_edge_gen_field_witness_elim
  (mh: MH.major_heap)
  (src dst: obj_addr)
  : Lemma
      (requires
        chunked_major_edge_gen_field_witness mh /\
        ChunkedMajorGraph.chunked_major_edge mh src dst /\
        ChunkedMajorGraph.chunked_major_vertex mh dst)
      (ensures
        exists (idx: nat) (field_addr: hp_addr) (raw: U64.t).
          Seq.mem src (MH.major_objects mh) /\
          idx < CG.chunked_wosize_nat_of_object mh src /\
          CG.chunked_major_field_slot src idx == Some field_addr /\
          MH.read_word_in_major mh field_addr == Some raw /\
          Seq.mem dst (MH.major_objects mh) /\
          is_pointer_to raw dst)

val chunked_major_edge_gen_field_witness_from_pointer_fields
  (mh: MH.major_heap)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        (forall (obj: obj_addr).
          Seq.mem obj (MH.major_objects mh) ==> is_pointer_field obj))
      (ensures chunked_major_edge_gen_field_witness mh)

val chunked_major_edge_gen_field_witness_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_major_edge_gen_field_witness mh)
      (ensures
        chunked_major_edge_gen_field_witness
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots))

val chunked_major_field_targets_non_infix
  (mh: MH.major_heap)
  : prop

val chunked_major_field_targets_non_infix_intro
  (mh: MH.major_heap)
  : Lemma
      (requires
        forall (src dst: obj_addr) (idx: nat)
               (field_addr: hp_addr) (raw: U64.t).
          Seq.mem src (MH.major_objects mh) /\
          idx < CG.chunked_wosize_nat_of_object mh src /\
          CG.chunked_major_field_slot src idx == Some field_addr /\
          MH.read_word_in_major mh field_addr == Some raw /\
          Seq.mem dst (MH.major_objects mh) /\
          is_pointer_to raw dst ==>
          ~(SweepDefs.chunked_is_infix mh dst))
      (ensures chunked_major_field_targets_non_infix mh)

val chunked_major_field_targets_non_infix_elim
  (mh: MH.major_heap)
  (src dst: obj_addr)
  (idx: nat)
  (field_addr: hp_addr)
  (raw: U64.t)
  : Lemma
      (requires
        chunked_major_field_targets_non_infix mh /\
        Seq.mem src (MH.major_objects mh) /\
        idx < CG.chunked_wosize_nat_of_object mh src /\
        CG.chunked_major_field_slot src idx == Some field_addr /\
        MH.read_word_in_major mh field_addr == Some raw /\
        Seq.mem dst (MH.major_objects mh) /\
        is_pointer_to raw dst)
      (ensures ~(SweepDefs.chunked_is_infix mh dst))

val chunked_major_field_targets_non_infix_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_major_field_targets_non_infix mh)
      (ensures
        chunked_major_field_targets_non_infix
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots))

val chunked_major_field_targets_non_infix_implies_vertex_edge_targets_non_infix
  (mh: MH.major_heap)
  : Lemma
      (requires
        chunked_major_edge_gen_field_witness mh /\
        chunked_major_field_targets_non_infix mh)
      (ensures ChunkedMarkEdge.chunked_vertex_edge_targets_non_infix mh)

val chunked_major_gc_bounded_liveness_policy
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : prop

val chunked_major_gc_bounded_liveness_policy_intro
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        mark_fuel > 0 /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready
          mh cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= ChunkedMark.chunked_count_non_black mh /\
        ChunkedMarkLive.chunked_roots_gray_or_black mh roots)
      (ensures
        chunked_major_gc_bounded_liveness_policy
          mh roots cap mark_fuel)

val chunked_major_gc_bounded_liveness_policy_elim
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        chunked_major_gc_bounded_liveness_policy
          mh roots cap mark_fuel)
      (ensures
        mark_fuel > 0 /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready
          mh cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= ChunkedMark.chunked_count_non_black mh /\
        ChunkedMarkLive.chunked_roots_gray_or_black mh roots)

val chunked_major_gc_bounded_liveness_policy_after_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        mark_fuel > 0 /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        chunked_major_gc_bounded_liveness_policy
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          roots cap mark_fuel)

val chunked_major_gc_bounded_after_gray_roots_policy
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : prop

val chunked_major_gc_bounded_after_gray_roots_policy_intro
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        mark_fuel > 0 /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        chunked_major_gc_bounded_after_gray_roots_policy
          mh roots cap mark_fuel)

val chunked_major_gc_bounded_after_gray_roots_policy_elim
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        chunked_major_gc_bounded_after_gray_roots_policy
          mh roots cap mark_fuel)
      (ensures
        MH.well_formed_major_heap mh /\
        mark_fuel > 0 /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= Seq.length (MH.major_objects mh))

val chunked_major_gc_bounded_after_gray_roots_target_membership_policy
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : prop

val chunked_major_gc_bounded_after_gray_roots_target_membership_policy_intro
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        mark_fuel > 0 /\
        ChunkedMarkReadiness.chunked_mark_bounded_target_membership_policy
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        chunked_major_gc_bounded_after_gray_roots_target_membership_policy
          mh roots cap mark_fuel)

val chunked_major_gc_bounded_after_gray_roots_policy_from_target_membership
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        chunked_major_gc_bounded_after_gray_roots_target_membership_policy
          mh roots cap mark_fuel)
      (ensures
        chunked_major_gc_bounded_after_gray_roots_policy
          mh roots cap mark_fuel)

val chunked_major_gc_bounded_after_gray_roots_raw_target_policy
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : prop

val chunked_major_gc_bounded_after_gray_roots_raw_target_policy_intro
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        mark_fuel > 0 /\
        ChunkedMarkTargetMembership.chunked_mark_bounded_raw_targets_policy
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        chunked_major_gc_bounded_after_gray_roots_raw_target_policy
          mh roots cap mark_fuel)

val chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : prop

val chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy_intro
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        mark_fuel > 0 /\
        ChunkedMarkTargetMembership.chunked_scanned_raw_targets_in_major
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy
          mh roots cap mark_fuel)

val chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy_from_pre_gray
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        mark_fuel > 0 /\
        ChunkedMarkTargetMembership.chunked_scanned_raw_targets_in_major mh /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy
          mh roots cap mark_fuel)

val chunked_major_gc_bounded_after_gray_roots_raw_target_policy_from_static
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy
          mh roots cap mark_fuel)
      (ensures
        chunked_major_gc_bounded_after_gray_roots_raw_target_policy
          mh roots cap mark_fuel)

val chunked_major_gc_bounded_after_gray_roots_target_membership_policy_from_raw_targets
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        chunked_major_gc_bounded_after_gray_roots_raw_target_policy
          mh roots cap mark_fuel)
      (ensures
        chunked_major_gc_bounded_after_gray_roots_target_membership_policy
          mh roots cap mark_fuel)

val chunked_major_gc_bounded_after_gray_roots_policy_from_raw_targets
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        chunked_major_gc_bounded_after_gray_roots_raw_target_policy
          mh roots cap mark_fuel)
      (ensures
        chunked_major_gc_bounded_after_gray_roots_policy
          mh roots cap mark_fuel)

val chunked_major_gc_bounded_after_gray_roots_target_membership_policy_from_static_raw_targets
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy
          mh roots cap mark_fuel)
      (ensures
        chunked_major_gc_bounded_after_gray_roots_target_membership_policy
          mh roots cap mark_fuel)

val chunked_major_gc_bounded_after_gray_roots_policy_from_static_raw_targets
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy
          mh roots cap mark_fuel)
      (ensures
        chunked_major_gc_bounded_after_gray_roots_policy
          mh roots cap mark_fuel)

val chunked_major_gc_bounded_liveness_policy_after_gray_roots_from_policy
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        chunked_major_gc_bounded_after_gray_roots_policy
          mh roots cap mark_fuel)
      (ensures
        chunked_major_gc_bounded_liveness_policy
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          roots cap mark_fuel)

val chunked_no_black_objects_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        GenInv.chunked_no_black_objects mh)
      (ensures
        GenInv.chunked_no_black_objects
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots))

val chunked_blue_status_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh) /\
        chunked_major_roots_nonblue mh roots)
      (ensures
        GenInv.chunked_is_blue
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) target ==
        GenInv.chunked_is_blue mh target)

val chunked_minor_major_fields_no_blue_preserved_by_gray_roots
  (minor: minor_state)
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_major_roots_nonblue mh roots /\
        GenInv.chunked_minor_major_fields_no_blue minor mh)
      (ensures
        GenInv.chunked_minor_major_fields_no_blue minor
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots))

val chunked_no_scan_invariant_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_major_roots_nonblue mh roots /\
        GenInv.chunked_no_scan_invariant mh)
      (ensures
        GenInv.chunked_no_scan_invariant
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots))

val chunked_no_pointer_to_blue_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_major_roots_nonblue mh roots /\
        GenInv.chunked_no_pointer_to_blue mh)
      (ensures
        GenInv.chunked_no_pointer_to_blue
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots))

val chunked_major_minor_fields_no_infix_targets_preserved_by_gray_roots
  (minor: minor_state)
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_major_roots_nonblue mh roots /\
        GenInv.chunked_major_minor_fields_no_infix_targets minor mh)
      (ensures
        GenInv.chunked_major_minor_fields_no_infix_targets minor
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots))

val chunked_major_alloc_shape_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (fp: U64.t)
  (fuel: nat)
  : Lemma
      (requires GenInv.chunked_major_alloc_shape mh fp fuel)
      (ensures
        GenInv.chunked_major_alloc_shape
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          fp fuel)

val chunked_collection_heap_shape_preserved_by_gray_roots
  (minor: minor_state)
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (fp: U64.t)
  (fuel: nat)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor mh fp fuel /\
        chunked_major_roots_nonblue mh roots)
      (ensures
        GenInv.chunked_collection_heap_shape minor
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          fp fuel)

val chunked_sweep_not_blue_vertex_implies_gen_not_blue
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMajorGraph.chunked_major_vertex mh obj /\
        ~(SweepDefs.chunked_is_blue mh obj))
      (ensures ~(GenInv.chunked_is_blue mh obj))

val chunked_gen_not_blue_vertex_implies_sweep_not_blue
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMajorGraph.chunked_major_vertex mh obj /\
        ~(GenInv.chunked_is_blue mh obj))
      (ensures ~(SweepDefs.chunked_is_blue mh obj))

val chunked_no_pointer_to_blue_implies_mark_vertex_targets
  (mh: MH.major_heap)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        GenInv.chunked_no_pointer_to_blue mh /\
        chunked_major_edge_gen_field_witness mh)
      (ensures
        ChunkedMarkLive.chunked_no_pointer_to_blue_vertex_targets mh)

val chunked_collection_heap_shape_implies_mark_vertex_targets_no_pointer_to_blue
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (fuel: nat)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor mh fp fuel /\
        chunked_major_edge_gen_field_witness mh)
      (ensures
        ChunkedMarkLive.chunked_no_pointer_to_blue_vertex_targets mh)

val chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_from_collection_shape
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (shape_fuel: nat)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        mark_fuel > 0 /\
        GenInv.chunked_collection_heap_shape minor mh fp shape_fuel /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready
          mh cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= ChunkedMark.chunked_count_non_black mh /\
        ChunkedMarkLive.chunked_roots_gray_or_black mh roots /\
        ChunkedMarkLive.chunked_no_pointer_to_blue mh /\
        ChunkedMarkEdge.chunked_vertex_edge_targets_non_infix mh)
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded mh cap mark_fuel in
        ChunkedMajorGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))

val chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_from_collection_shape_vertex_targets
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (shape_fuel: nat)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        mark_fuel > 0 /\
        GenInv.chunked_collection_heap_shape minor mh fp shape_fuel /\
        chunked_major_edge_gen_field_witness mh /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready
          mh cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= ChunkedMark.chunked_count_non_black mh /\
        ChunkedMarkLive.chunked_roots_gray_or_black mh roots /\
        ChunkedMarkEdge.chunked_vertex_edge_targets_non_infix mh)
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded mh cap mark_fuel in
        ChunkedMajorGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))

val chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_from_collection_shape_field_policies
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (shape_fuel: nat)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        mark_fuel > 0 /\
        GenInv.chunked_collection_heap_shape minor mh fp shape_fuel /\
        chunked_major_edge_gen_field_witness mh /\
        chunked_major_field_targets_non_infix mh /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready
          mh cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= ChunkedMark.chunked_count_non_black mh /\
        ChunkedMarkLive.chunked_roots_gray_or_black mh roots)
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded mh cap mark_fuel in
        ChunkedMajorGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))

val chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_from_collection_shape_policy
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (shape_fuel: nat)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor mh fp shape_fuel /\
        chunked_major_edge_gen_field_witness mh /\
        chunked_major_field_targets_non_infix mh /\
        chunked_major_gc_bounded_liveness_policy
          mh roots cap mark_fuel)
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded mh cap mark_fuel in
        ChunkedMajorGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))

val chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_after_gray_roots_from_grayed_collection_shape_policy
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (shape_fuel: nat)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        GenInv.chunked_collection_heap_shape minor
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          fp shape_fuel /\
        chunked_major_edge_gen_field_witness
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) /\
        chunked_major_field_targets_non_infix
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel > 0 /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded
            (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
            cap mark_fuel in
        ChunkedMajorGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))

val chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_after_gray_roots_from_original_field_policies
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (shape_fuel: nat)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        GenInv.chunked_collection_heap_shape minor
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          fp shape_fuel /\
        chunked_major_edge_gen_field_witness mh /\
        chunked_major_field_targets_non_infix mh /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel > 0 /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded
            (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
            cap mark_fuel in
        ChunkedMajorGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))

val chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_after_gray_roots_from_original_shape
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (shape_fuel: nat)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor mh fp shape_fuel /\
        chunked_major_roots_nonblue mh roots /\
        chunked_major_edge_gen_field_witness mh /\
        chunked_major_field_targets_non_infix mh /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel > 0 /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded
            (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
            cap mark_fuel in
        ChunkedMajorGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))

val chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_after_gray_roots_from_original_shape_policy
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (shape_fuel: nat)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor mh fp shape_fuel /\
        chunked_major_roots_nonblue mh roots /\
        chunked_major_edge_gen_field_witness mh /\
        chunked_major_field_targets_non_infix mh /\
        chunked_major_gc_bounded_after_gray_roots_policy
          mh roots cap mark_fuel)
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded
            (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
            cap mark_fuel in
        ChunkedMajorGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))
