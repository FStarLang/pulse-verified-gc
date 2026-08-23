module GC.SPOT.ThreeObjects

open FStar.Seq
module Seq = FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

module Layout = GC.SPOT.Layout
module Preconditions = GC.SPOT.Preconditions
module Postconditions = GC.SPOT.Postconditions
module SpecHeap = GC.Spec.Heap
module SpecObj = GC.Spec.Object
module SpecFields = GC.Spec.Fields
module SpecMark = GC.Spec.Mark
module GenInv = GC.Gen.HeapInvariant
module Promote = GC.Gen.Promote
module Cheney = GC.Gen.Cheney
module CheneyBFS = GC.Gen.CheneyBFS
module CG = GC.Gen.CombinedGraph
module MinorFwd = GC.Gen.MinorCollectForwarding
module RBridge = GC.Gen.ReachabilityBridge
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs

let spot_roots (c: obj_addr) : seq U64.t =
  Seq.cons (c <: U64.t)
    (Seq.cons Layout.a_minor Seq.empty)

let spot_c_to_a_slot
  (c: obj_addr{U64.v c + Layout.c_to_a_field_index * 8 + 8 <= heap_size})
  : hp_addr =
  assert (heap_size < pow2 57);
  assert (U64.v c + 8 < pow2 64);
  U64.add c 8UL

let spot_c_to_a_slot_spec
  (c: obj_addr{U64.v c + Layout.c_to_a_field_index * 8 + 8 <= heap_size})
  =
  assert (Layout.c_to_a_field_index == 1);
  assert (heap_size < pow2 57);
  assert (U64.v c + 8 < pow2 64)

let spot_slots
  (c: obj_addr{U64.v c + Layout.c_to_a_field_index * 8 + 8 <= heap_size})
  : seq U64.t =
  Seq.cons (spot_c_to_a_slot c) Seq.empty

let spot_slots_len
  (c: obj_addr{U64.v c + Layout.c_to_a_field_index * 8 + 8 <= heap_size})
  = ()

let spot_slots_index
  (c: obj_addr{U64.v c + Layout.c_to_a_field_index * 8 + 8 <= heap_size})
  (i: nat{i < Seq.length (spot_slots c)})
  =
  assert (i == 0)

let spot_roots_mem_c (c: obj_addr)
  = ()

let spot_roots_mem_a (c: obj_addr)
  = ()

let spot_roots_len (c: obj_addr)
  = ()

let spot_roots_index_c (c: obj_addr)
  = ()

let spot_roots_index_a (c: obj_addr)
  = ()

let spot_roots_cases (c: obj_addr) (root: U64.t)
  =
  SpecFields.mem_cons_lemma root (c <: U64.t) (Seq.cons Layout.a_minor Seq.empty);
  SpecFields.mem_cons_lemma root Layout.a_minor Seq.empty;
  if root = (c <: U64.t) then ()
  else if root = Layout.a_minor then ()
  else begin
    assert_norm (~(Seq.mem root (Seq.empty #U64.t)));
    assert False
  end

let spot_slots_singleton_distinct
  (c: obj_addr{U64.v c + Layout.c_to_a_field_index * 8 + 8 <= heap_size})
  = Preconditions.singleton_slots_pairwise_distinct (spot_slots c) 1

let spot_minor_scenario_pre
  (minor: minor_state) (major: heap) (fp: U64.t)
  (c: obj_addr{U64.v c + Layout.c_to_a_field_index * 8 + 8 <= heap_size})
  (farr: seq U64.t) : prop =
  Preconditions.minor_collect_full_pre
    minor major fp (spot_roots c) farr (spot_slots c) 1 /\
  ~(Promote.is_minor_pointer (c <: U64.t)) /\
  Seq.mem c (SpecFields.objects zero_addr major) /\
  ~(SpecObj.is_no_scan c major) /\
  U64.v (SpecObj.wosize_of_object c major) > Layout.c_to_a_field_index /\
  U64.v c + Layout.c_to_a_field_index * 8 + 8 <= heap_size /\
  CG.classify_major_field minor major
    (SpecHeap.read_word major (spot_c_to_a_slot c)) == Some (CG.MinorV Layout.a_minor) /\
  Seq.mem Layout.a_minor (minor_objects minor) /\
  Seq.mem Layout.b_minor (minor_objects minor) /\
  minor_wosize minor Layout.a_minor > 0 /\
  minor_wosize minor Layout.b_minor > 0 /\
  CheneyBFS.cheney_no_oom minor major fp (spot_roots c)

let spot_minor_scenario_pre_intro_from_c_to_a
  (minor: minor_state) (major: heap) (fp: U64.t)
  (c: obj_addr{U64.v c + Layout.c_to_a_field_index * 8 + 8 <= heap_size})
  (farr: seq U64.t)
  =
  let slot_v = SpecHeap.read_word major (spot_c_to_a_slot c) in
  assert (slot_v == Layout.a_minor);
  Layout.a_minor_is_minor_pointer ();
  assert (U64.v slot_v == U64.v Layout.a_minor);
  assert (U64.v slot_v < minor_heap_size);
  assert (U64.v slot_v % 8 == 0);
  to_minor_offset_in_minor_range slot_v;
  assert (to_minor_offset slot_v == Layout.a_minor);
  assert (Promote.is_minor_pointer (to_minor_offset slot_v));
  assert (Seq.mem (to_minor_offset slot_v) (minor_objects minor));
  CG.classify_major_field_is_minor minor major slot_v;
  assert (CG.classify_major_field minor major slot_v ==
          Some (CG.MinorV (to_minor_offset slot_v)));
  assert (Some (CG.MinorV (to_minor_offset slot_v)) ==
          Some (CG.MinorV Layout.a_minor));
  assert (CG.classify_major_field minor major slot_v ==
          Some (CG.MinorV Layout.a_minor))

let spot_full_scenario_pre
  (minor: minor_state) (major: heap) (fp: U64.t)
  (c: obj_addr{U64.v c + Layout.c_to_a_field_index * 8 + 8 <= heap_size})
  (farr: seq U64.t) (st: seq obj_addr) (cap: nat) : prop =
  spot_minor_scenario_pre minor major fp c farr /\
  Preconditions.gen_gc_pre
    minor major fp (spot_roots c) farr (spot_slots c) 1 st cap

let expose_spot_collection_facts
  (minor: minor_state) (major: heap) (fp: U64.t)
  (c: obj_addr{U64.v c + Layout.c_to_a_field_index * 8 + 8 <= heap_size})
  (farr: seq U64.t)
  : Lemma
      (requires spot_minor_scenario_pre minor major fp c farr)
      (ensures
        GC.Gen.HeapInvariant.collection_heap_shape minor major fp /\
        SpecFields.well_formed_heap major /\
        minor_wf minor /\
        SpecMark.no_pointer_to_blue major /\
        RBridge.minor_no_pointer_to_blue minor major /\
        UpdatePtrs.ref_table_covers_minor_ptrs major (spot_slots c) 1 /\
        MinorFwd.remembered_targets_in_roots major (spot_roots c) (spot_slots c) 1 /\
        RBridge.major_field_zero_no_minor minor major /\
        RBridge.roots_valid_nonblue (spot_roots c) major)
  =
  Preconditions.minor_collect_full_pre_elim
    minor major fp (spot_roots c) farr (spot_slots c) 1;
  MCFH.roots_valid_for_minor_collection_nonblue minor major (spot_roots c);
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.major_heap_shape_elim major fp;
  GenInv.minor_heap_shape_elim minor;
  RBridge.minor_no_pointer_to_blue_from_collection_shape minor major fp

let spot_c_reachable_root
  (minor: minor_state) (major: heap) (fp: U64.t)
  (c: obj_addr{U64.v c + Layout.c_to_a_field_index * 8 + 8 <= heap_size})
  (farr: seq U64.t)
  =
  spot_roots_mem_c c;
  CG.classify_roots_major_mem (spot_roots c) (c <: U64.t);
  CG.major_vertex_char minor major c;
  assert (CG.mem_cv (CG.MajorV c) (CG.build_combined_graph minor major));
  CG.combined_reachable_root
    (CG.build_combined_graph minor major)
    (CG.classify_roots (spot_roots c))
    (CG.MajorV c)

let spot_a_reachable_root
  (minor: minor_state) (major: heap) (fp: U64.t)
  (c: obj_addr{U64.v c + Layout.c_to_a_field_index * 8 + 8 <= heap_size})
  (farr: seq U64.t)
  =
  spot_roots_mem_a c;
  Layout.a_minor_is_minor_pointer ();
  CG.classify_roots_minor_mem (spot_roots c) Layout.a_minor;
  CG.minor_vertex_char minor major Layout.a_minor;
  assert (CG.mem_cv (CG.MinorV Layout.a_minor) (CG.build_combined_graph minor major));
  CG.combined_reachable_root
    (CG.build_combined_graph minor major)
    (CG.classify_roots (spot_roots c))
    (CG.MinorV Layout.a_minor)

let spot_a_promoted
  (minor: minor_state) (major: heap) (fp: U64.t)
  (c: obj_addr{U64.v c + Layout.c_to_a_field_index * 8 + 8 <= heap_size})
  (farr: seq U64.t)
  =
  expose_spot_collection_facts minor major fp c farr;
  spot_a_reachable_root minor major fp c farr;
  MinorFwd.combined_reachable_minor_has_fwd_from_slots
    minor major fp (spot_roots c) (spot_slots c) 1;
  assert ((Cheney.cheney_promote minor major fp (spot_roots c)).fwd_map
    Layout.a_minor <> 0UL);
  Postconditions.promoted_image_from_forwarding
    minor major fp (spot_roots c) Layout.a_minor
    ((Cheney.cheney_promote minor major fp (spot_roots c)).fwd_map Layout.a_minor)

let spot_c_field_rewritten_to_a_prime
  (minor: minor_state) (major: heap) (fp: U64.t)
  (c: obj_addr{U64.v c + Layout.c_to_a_field_index * 8 + 8 <= heap_size})
  (farr: seq U64.t)
  =
  expose_spot_collection_facts minor major fp c farr;
  spot_c_reachable_root minor major fp c farr;
  spot_a_reachable_root minor major fp c farr;
  Postconditions.major_minor_field_rewritten
    minor major fp (spot_roots c) (spot_slots c) 1 c Layout.a_minor
    Layout.c_to_a_field_index

let spot_b_not_promoted_from_forwarding_zero
  (minor: minor_state) (major: heap) (fp: U64.t) (c: obj_addr)
  = Postconditions.not_promoted_from_zero_forwarding
      minor major fp (spot_roots c) Layout.b_minor

let spot_final_survives_from_gen_gc_post
  (minor: minor_state) (major: heap) (fp: U64.t)
  (c: obj_addr{U64.v c + Layout.c_to_a_field_index * 8 + 8 <= heap_size})
  (roots_out: seq U64.t) (ok: bool) (final_major: heap)
  (st: seq obj_addr) (cap: nat) (x: obj_addr)
  = Postconditions.final_major_survives_from_gen_gc_post
      minor major fp (spot_roots c) roots_out ok final_major st cap x
