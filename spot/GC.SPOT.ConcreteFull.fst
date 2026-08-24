module GC.SPOT.ConcreteFull

module U64 = FStar.UInt64
module Seq = FStar.Seq

open FStar.Seq
open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

module Layout = GC.SPOT.Layout
module ThreeObjects = GC.SPOT.ThreeObjects
module ConcreteMinor = GC.SPOT.ConcreteMinor
module ConcreteMajor = GC.SPOT.ConcreteMajor
module ConcreteScenarios = GC.SPOT.ConcreteScenarios
module ConcreteForwarding = GC.SPOT.ConcreteForwarding
module Postconditions = GC.SPOT.Postconditions
module Preconditions = GC.SPOT.Preconditions
module SpecHeap = GC.Spec.Heap
module SpecObj = GC.Spec.Object
module SpecFields = GC.Spec.Fields
module SpecMark = GC.Spec.Mark
module SpecMarkBoundedInv = GC.Spec.MarkBoundedInv
module SpecCorrectness = GC.Spec.Correctness
module HeapGraph = GC.Spec.HeapGraph
module HeapModel = GC.Spec.HeapModel
module SpecGraph = GC.Spec.Graph
module SpecDFS = GC.Spec.DFS
module GenInv = GC.Gen.HeapInvariant
module Promote = GC.Gen.Promote
module PromoteUpdate = GC.Gen.PromoteUpdate
module Cheney = GC.Gen.Cheney
module CheneyBFS = GC.Gen.CheneyBFS
module GenImpl = GC.Gen.Impl
module MinorFwd = GC.Gen.MinorCollectForwarding
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module MajorGC = GC.Impl
module MarkBoundedImpl = GC.Impl.MarkBounded

let roots_match_u64_mem_in_stack
  (roots: seq U64.t) (st: seq obj_addr) (r: U64.t)
  : Lemma
      (requires GenImpl.roots_match_stack roots st /\ Seq.mem r roots)
      (ensures is_val_addr r /\ Seq.mem (r <: obj_addr) st)
  =
  GenImpl.roots_match_stack_root_is_val_addr roots st r;
  GC.Spec.Base.is_val_addr_spec r;
  let r_obj = (r <: obj_addr) in
  assert ((r_obj <: U64.t) == r);
  GenImpl.roots_match_stack_root_in_stack roots st r_obj

let post_roots_mem_c
  (r: unit{ConcreteMajor.spot_major_room})
  (roots_out: seq U64.t) (st: seq obj_addr) (cap: nat)
  : Lemma
      (requires
        GenImpl.gen_gc_roots_post
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
          roots_out true st cap)
      (ensures
        Seq.mem (ConcreteMajor.spot_c r <: U64.t) roots_out /\
        Seq.mem (ConcreteMajor.spot_c r)
          (GenImpl.gen_gc_prepared_roots
            ConcreteMinor.spot_minor2
            (ConcreteMajor.spot_major_heap r)
            (ConcreteMajor.spot_major_fp r)
            (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
            st cap))
  =
  let c = ConcreteMajor.spot_c r in
  let roots = ThreeObjects.spot_roots c in
  let prom = Cheney.cheney_promote
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    roots in
  let res = Cheney.cheney_collect_spec
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    roots in
  assert (roots_out == res.mc_roots);
  ThreeObjects.spot_roots_len c;
  ThreeObjects.spot_roots_index_c c;
  Promote.rewrite_roots_length roots prom.fwd_map;
  Promote.rewrite_roots_index roots prom.fwd_map 0;
  ConcreteMajor.spot_major_layout_facts r;
  zero_addr_above_minor ();
  assert (~(Promote.is_minor_pointer (c <: U64.t)));
  assert (Promote.rewrite_root (c <: U64.t) prom.fwd_map == (c <: U64.t));
  assert (Seq.length roots_out > 0);
  assert (Seq.index roots_out 0 == (c <: U64.t));
  FStar.Seq.Properties.seq_mem_k roots_out 0;
  assert (Seq.mem (c <: U64.t) roots_out);
  let prepared_roots = GenImpl.gen_gc_prepared_roots
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    roots st cap in
  assert (GenImpl.roots_match_stack roots_out prepared_roots);
  roots_match_u64_mem_in_stack roots_out prepared_roots (c <: U64.t)

let post_roots_mem_a_prime
  (r: unit{ConcreteMajor.spot_major_room})
  (roots_out: seq U64.t) (st: seq obj_addr) (cap: nat)
  : Lemma
      (requires
        CheneyBFS.cheney_no_oom
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) /\
        GenImpl.gen_gc_roots_post
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
          roots_out true st cap)
      (ensures (
        let prom = Cheney.cheney_promote
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) in
        let img = prom.fwd_map Layout.a_minor in
        let prepared_roots = GenImpl.gen_gc_prepared_roots
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
          st cap in
        Seq.mem img roots_out /\
        is_val_addr img /\
        Seq.mem (img <: obj_addr) prepared_roots)
      )
  =
  let c = ConcreteMajor.spot_c r in
  let roots = ThreeObjects.spot_roots c in
  let prom = Cheney.cheney_promote
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    roots in
  let img = prom.fwd_map Layout.a_minor in
  let res = Cheney.cheney_collect_spec
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    roots in
  ConcreteScenarios.spot_concrete_a_promoted_from_no_oom r;
  assert (Postconditions.promoted_image
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    roots Layout.a_minor img);
  Postconditions.promoted_image_elim
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    roots Layout.a_minor img;
  assert (img <> 0UL);
  assert (roots_out == res.mc_roots);
  ThreeObjects.spot_roots_len c;
  ThreeObjects.spot_roots_index_a c;
  Promote.rewrite_roots_length roots prom.fwd_map;
  Promote.rewrite_roots_index roots prom.fwd_map 1;
  Layout.a_minor_is_minor_pointer ();
  assert (Promote.rewrite_root Layout.a_minor prom.fwd_map == img);
  assert (Seq.length roots_out > 1);
  assert (Seq.index roots_out 1 == img);
  FStar.Seq.Properties.seq_mem_k roots_out 1;
  assert (Seq.mem img roots_out);
  let prepared_roots = GenImpl.gen_gc_prepared_roots
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    roots st cap in
  assert (GenImpl.roots_match_stack roots_out prepared_roots);
  roots_match_u64_mem_in_stack roots_out prepared_roots img

let root_heap_reachable_from_major_gc_pre
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (st: seq obj_addr) (cap: nat) (r: obj_addr)
  : Lemma
      (requires
        GenInv.collection_heap_shape minor major fp /\
        MinorFwd.roots_valid_for_minor_collection minor major roots /\
        CheneyBFS.cheney_no_oom minor major fp roots /\
        GenImpl.gen_gc_stack_budget roots st cap /\
        Seq.mem r (GenImpl.gen_gc_prepared_roots minor major fp roots st cap))
      (ensures
        SpecCorrectness.heap_reachable
          (GenImpl.gen_gc_prepared_major minor major fp roots st cap)
          (GenImpl.gen_gc_prepared_roots minor major fp roots st cap)
          r)
  =
  let prepared_major = GenImpl.gen_gc_prepared_major minor major fp roots st cap in
  let prepared_roots = GenImpl.gen_gc_prepared_roots minor major fp roots st cap in
  let graph = HeapModel.create_graph prepared_major in
  let roots' = HeapGraph.coerce_to_vertex_list prepared_roots in
  GenImpl.gen_gc_major_precondition_elim minor major fp roots st cap;
  assert (MajorGC.gc_precondition_with_roots
    prepared_major prepared_roots prepared_roots
    (Cheney.cheney_collect_spec minor major fp roots).mc_fp cap);
  HeapGraph.coerce_mem_lemma prepared_roots r;
  assert (Seq.mem r roots');
  assert (SpecGraph.mem_graph_vertex graph r);
  assert (Seq.mem r (SpecDFS.reachable_set graph roots'));
  assert (SpecCorrectness.heap_reachable prepared_major prepared_roots r)

/// The concrete instance, so that the scenario proofs do not have to re-supply
/// the pre-minor shape facts at every use.
let spot_root_heap_reachable_from_major_gc_pre
  (r: unit{ConcreteMajor.spot_major_room})
  (st: seq obj_addr) (cap: nat) (v: obj_addr)
  : Lemma
      (requires (
        let roots = ThreeObjects.spot_roots (ConcreteMajor.spot_c r) in
        GenImpl.gen_gc_stack_budget roots st cap /\
        Seq.mem v (GenImpl.gen_gc_prepared_roots
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r) roots st cap)))
      (ensures (
        let roots = ThreeObjects.spot_roots (ConcreteMajor.spot_c r) in
        SpecCorrectness.heap_reachable
          (GenImpl.gen_gc_prepared_major
            ConcreteMinor.spot_minor2
            (ConcreteMajor.spot_major_heap r)
            (ConcreteMajor.spot_major_fp r) roots st cap)
          (GenImpl.gen_gc_prepared_roots
            ConcreteMinor.spot_minor2
            (ConcreteMajor.spot_major_heap r)
            (ConcreteMajor.spot_major_fp r) roots st cap)
          v))
  =
  ConcreteScenarios.spot_collection_heap_shape r;
  ConcreteScenarios.spot_roots_valid_for_minor_collection r;
  ConcreteForwarding.spot_concrete_no_oom r;
  root_heap_reachable_from_major_gc_pre
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
    st cap v

let spot_concrete_c_final_survives
  (r: unit{ConcreteMajor.spot_major_room})
  (d2: minor_heap) (b2: U64.t)
  (roots_out: seq U64.t) (ok: bool) (final_major: heap)
  (st: seq obj_addr) (cap: nat)
  =
  let result =
    Cheney.cheney_collect_spec
      ConcreteMinor.spot_minor2
      (ConcreteMajor.spot_major_heap r)
      (ConcreteMajor.spot_major_fp r)
      (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) in
  let c = ConcreteMajor.spot_c r in
  post_roots_mem_c r roots_out st cap;
  assert (Seq.mem (c <: U64.t) roots_out);
  assert (Seq.mem c
    (GenImpl.gen_gc_prepared_roots
      ConcreteMinor.spot_minor2
      (ConcreteMajor.spot_major_heap r)
      (ConcreteMajor.spot_major_fp r)
      (ThreeObjects.spot_roots c)
      st cap));
  assert (GenImpl.gen_gc_stack_budget (ThreeObjects.spot_roots c) st cap);
  spot_root_heap_reachable_from_major_gc_pre r st cap c;
  ThreeObjects.spot_final_survives_from_gen_gc_post
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    c roots_out ok final_major st cap c

let spot_concrete_a_prime_final_survives
  (r: unit{ConcreteMajor.spot_major_room})
  (d2: minor_heap) (b2: U64.t)
  (roots_out: seq U64.t) (ok: bool) (final_major: heap)
  (st: seq obj_addr) (cap: nat)
  =
  let result =
    Cheney.cheney_collect_spec
      ConcreteMinor.spot_minor2
      (ConcreteMajor.spot_major_heap r)
      (ConcreteMajor.spot_major_fp r)
      (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) in
  let c = ConcreteMajor.spot_c r in
  let prom =
    Cheney.cheney_promote
      ConcreteMinor.spot_minor2
      (ConcreteMajor.spot_major_heap r)
      (ConcreteMajor.spot_major_fp r)
      (ThreeObjects.spot_roots c) in
  let img = prom.fwd_map Layout.a_minor in
  ConcreteForwarding.spot_concrete_no_oom r;
  post_roots_mem_a_prime r roots_out st cap;
  let a_prime = (img <: obj_addr) in
  assert (Seq.mem a_prime
    (GenImpl.gen_gc_prepared_roots
      ConcreteMinor.spot_minor2
      (ConcreteMajor.spot_major_heap r)
      (ConcreteMajor.spot_major_fp r)
      (ThreeObjects.spot_roots c)
      st cap));
  assert (GenImpl.gen_gc_stack_budget (ThreeObjects.spot_roots c) st cap);
  spot_root_heap_reachable_from_major_gc_pre r st cap a_prime;
  ThreeObjects.spot_final_survives_from_gen_gc_post
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    c roots_out ok final_major st cap a_prime;
  assert (a_prime == img);
  assert (exists (a_prime: obj_addr).
    a_prime == img /\ Seq.mem a_prime (SpecFields.objects zero_addr final_major))

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let post_minor_c_wosize
  (r: unit{ConcreteMajor.spot_major_room})
  : Lemma
      (ensures (
        let result =
          Cheney.cheney_collect_spec
            ConcreteMinor.spot_minor2
            (ConcreteMajor.spot_major_heap r)
            (ConcreteMajor.spot_major_fp r)
            (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) in
        SpecObj.wosize_of_object (ConcreteMajor.spot_c r) result.mc_major ==
          U64.uint_to_t Layout.c_wosize))
  =
  let minor = ConcreteMinor.spot_minor2 in
  let major = ConcreteMajor.spot_major_heap r in
  let fp = ConcreteMajor.spot_major_fp r in
  let c = ConcreteMajor.spot_c r in
  let roots = ThreeObjects.spot_roots c in
  let prom = Cheney.cheney_promote minor major fp roots in
  let result = Cheney.cheney_collect_spec minor major fp roots in
  ConcreteScenarios.spot_concrete_minor_collect_full_pre r;
  Preconditions.minor_collect_full_pre_elim
    minor major fp roots ConcreteScenarios.spot_fwd_array
    (ThreeObjects.spot_slots c) 1;
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.major_heap_shape_elim major fp;
  ConcreteMajor.spot_major_layout_facts r;
  ConcreteMajor.spot_major_c_mem r;
  ConcreteMajor.spot_major_c_reads r;
  assert (SpecObj.is_blue c major = false);
  assert (Layout.c_to_a_field_index < U64.v (SpecObj.wosize_of_object c major));
  MinorFwd.cheney_promote_preserves_old_major_field_context
    minor major fp roots c Layout.c_to_a_field_index;
  Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
  PromoteUpdate.update_major_pointers_preserves_header prom.major_final prom.fwd_map c;
  MCFH.header_eq_preserves_wosize_no_scan result.mc_major prom.major_final c;
  assert (SpecObj.wosize_of_object c prom.major_final ==
          SpecObj.wosize_of_object c major);
  assert (SpecObj.wosize_of_object c result.mc_major ==
          SpecObj.wosize_of_object c prom.major_final)

let c_field1_get_field
  (r: unit{ConcreteMajor.spot_major_room}) (g: heap)
  : Lemma
      (ensures
        HeapGraph.get_field g (ConcreteMajor.spot_c r) 2UL ==
        SpecHeap.read_word g (ConcreteMajor.spot_c_field1 r))
  =
  let c = ConcreteMajor.spot_c r in
  let slot = ConcreteMajor.spot_c_field1 r in
  let one = U64.sub 2UL 1UL in
  let raw_slot = U64.add_mod c (U64.mul_mod one mword) in
  ConcreteMajor.spot_major_layout_facts r;
  SpecHeap.hd_address_spec c;
  assert (Layout.c_to_a_field_index == 1);
  assert (U64.v (SpecHeap.hd_address c) + U64.v mword * 2 + U64.v mword ==
          U64.v c + Layout.c_to_a_field_index * 8 + 8);
  assert (U64.v (SpecHeap.hd_address c) + U64.v mword * 2 + U64.v mword <=
          heap_size);
  FStar.Math.Lemmas.pow2_lt_compat 54 1;
  assert (pow2 1 == 2);
  assert (2 < pow2 54);
  HeapGraph.get_field_addr_eq g c 2UL;
  assert (U64.v one == 1);
  assert (U64.v raw_slot == U64.v c + 8);
  assert (U64.v raw_slot == U64.v slot);
  assert (raw_slot == slot)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let post_roots_shape
  (r: unit{ConcreteMajor.spot_major_room})
  (roots_out: seq U64.t) (st: seq obj_addr) (cap: nat)
  : Lemma
      (requires
        CheneyBFS.cheney_no_oom
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) /\
        GenImpl.gen_gc_roots_post
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
          roots_out true st cap)
      (ensures (
        let c = ConcreteMajor.spot_c r in
        let prom = Cheney.cheney_promote
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots c) in
        Seq.length roots_out == 2 /\
        Seq.index roots_out 0 == (c <: U64.t) /\
        Seq.index roots_out 1 == prom.fwd_map Layout.a_minor))
  =
  let c = ConcreteMajor.spot_c r in
  let roots = ThreeObjects.spot_roots c in
  let prom = Cheney.cheney_promote
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    roots in
  let result = Cheney.cheney_collect_spec
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    roots in
  assert (roots_out == result.mc_roots);
  ThreeObjects.spot_roots_len c;
  Promote.rewrite_roots_length roots prom.fwd_map;
  assert (Seq.length roots_out == 2);
  ThreeObjects.spot_roots_index_c c;
  Promote.rewrite_roots_index roots prom.fwd_map 0;
  ConcreteMajor.spot_major_layout_facts r;
  zero_addr_above_minor ();
  assert (~(Promote.is_minor_pointer (c <: U64.t)));
  assert (Promote.rewrite_root (c <: U64.t) prom.fwd_map == (c <: U64.t));
  assert (Seq.index roots_out 0 == (c <: U64.t));
  ThreeObjects.spot_roots_index_a c;
  Promote.rewrite_roots_index roots prom.fwd_map 1;
  Layout.a_minor_is_minor_pointer ();
  ConcreteScenarios.spot_concrete_a_promoted_from_no_oom r;
  Postconditions.promoted_image_elim
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    roots Layout.a_minor (prom.fwd_map Layout.a_minor);
  assert (prom.fwd_map Layout.a_minor <> 0UL);
  assert (Promote.rewrite_root Layout.a_minor prom.fwd_map ==
          prom.fwd_map Layout.a_minor);
  assert (Seq.index roots_out 1 == prom.fwd_map Layout.a_minor)

let nat_lt_two_cases (i: nat)
  : Lemma (requires i < 2) (ensures i == 0 \/ i == 1)
  = ()

let object_header_not_c_field1
  (r: unit{ConcreteMajor.spot_major_room}) (g: heap) (target: obj_addr)
  : Lemma
      (requires
        SpecFields.well_formed_heap g /\
        Seq.mem (ConcreteMajor.spot_c r) (SpecFields.objects zero_addr g) /\
        Seq.mem target (SpecFields.objects zero_addr g) /\
        U64.v (SpecObj.wosize_of_object (ConcreteMajor.spot_c r) g) >= 2)
      (ensures SpecHeap.hd_address target <> ConcreteMajor.spot_c_field1 r)
  =
  let c = ConcreteMajor.spot_c r in
  let slot = ConcreteMajor.spot_c_field1 r in
  ConcreteMajor.spot_major_layout_facts r;
  SpecHeap.hd_address_spec c;
  SpecHeap.hd_address_spec target;
  assert (U64.v slot == U64.v c + 8);
  if target = c then
    assert (U64.v (SpecHeap.hd_address target) < U64.v slot)
  else if U64.v target < U64.v c then
    assert (U64.v (SpecHeap.hd_address target) < U64.v slot)
  else begin
    assert (U64.v c < U64.v target);
    SpecObj.wosize_of_object_bound c g;
    assert (SpecFields.wosize_of_object_as_wosize c g ==
            SpecObj.wosize_of_object c g);
    SpecFields.objects_separated zero_addr g c target;
    assert (U64.v target > U64.v c + 16);
    assert (U64.v (SpecHeap.hd_address target) > U64.v slot)
  end

let prepared_roots_preserve_c_field1
  (r: unit{ConcreteMajor.spot_major_room})
  (roots_out: seq U64.t) (st: seq obj_addr) (cap: nat)
  : Lemma
      (requires
        CheneyBFS.cheney_no_oom
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) /\
        GenImpl.gen_gc_roots_post
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
          roots_out true st cap /\
        GenImpl.gen_gc_stack_budget
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
          st cap)
      (ensures (
        let result = Cheney.cheney_collect_spec
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) in
        let prepared_major = GenImpl.gen_gc_prepared_major
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
          st cap in
        SpecHeap.read_word prepared_major (ConcreteMajor.spot_c_field1 r) ==
        SpecHeap.read_word result.mc_major (ConcreteMajor.spot_c_field1 r) /\
        SpecObj.wosize_of_object (ConcreteMajor.spot_c r) prepared_major ==
        SpecObj.wosize_of_object (ConcreteMajor.spot_c r) result.mc_major))
  =
  let c = ConcreteMajor.spot_c r in
  let roots = ThreeObjects.spot_roots c in
  let result = Cheney.cheney_collect_spec
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    roots in
  let prepared_major = GenImpl.gen_gc_prepared_major
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    roots st cap in
  let prepared_roots = GenImpl.gen_gc_prepared_roots
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    roots st cap in
  post_roots_shape r roots_out st cap;
  post_roots_mem_c r roots_out st cap;
  post_roots_mem_a_prime r roots_out st cap;
  post_minor_c_wosize r;
  assert (roots_out == result.mc_roots);
  assert (prepared_major ==
          fst (MarkBoundedImpl.darken_roots_bounded_spec
            result.mc_major st roots_out cap));
  MarkBoundedImpl.darken_roots_bounded_spec_preserves_wosize
    result.mc_major st roots_out cap c;
  assert (SpecObj.wosize_of_object c prepared_major ==
          SpecObj.wosize_of_object c result.mc_major);
  assert (U64.v (SpecObj.wosize_of_object c prepared_major) >= 2);
  ConcreteScenarios.spot_collection_heap_shape r;
  ConcreteScenarios.spot_roots_valid_for_minor_collection r;
  ConcreteForwarding.spot_concrete_no_oom r;
  GenImpl.gen_gc_major_precondition_elim
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    roots st cap;
  assert (MajorGC.gc_precondition_with_roots
    prepared_major prepared_roots prepared_roots result.mc_fp cap);
  assert (SpecMarkBoundedInv.bounded_mark_inv prepared_major prepared_roots cap);
  SpecMarkBoundedInv.bounded_mark_inv_elim_wfh prepared_major prepared_roots cap;
  assert (SpecMark.root_props prepared_major prepared_roots);
  assert (Seq.mem c prepared_roots);
  assert (Seq.mem c (SpecFields.objects zero_addr prepared_major));
  let prom = Cheney.cheney_promote
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    roots in
  let img = prom.fwd_map Layout.a_minor in
  let a_prime = (img <: obj_addr) in
  assert (Seq.mem a_prime prepared_roots);
  assert (Seq.mem a_prime (SpecFields.objects zero_addr prepared_major));
  let slot = ConcreteMajor.spot_c_field1 r in
  let no_root_header (i: nat)
    : Lemma
        (ensures
          i < Seq.length roots_out ==>
          (U64.v (Seq.index roots_out i) >= U64.v zero_addr + U64.v mword /\
           U64.v (Seq.index roots_out i) < heap_size /\
           U64.v (Seq.index roots_out i) % U64.v mword == 0 ==>
           U64.sub (Seq.index roots_out i) mword <> slot))
    =
    if i < Seq.length roots_out then begin
      assert (Seq.length roots_out == 2);
      match i with
      | 0 ->
        assert (Seq.index roots_out i == (c <: U64.t));
        object_header_not_c_field1 r prepared_major c;
        SpecHeap.hd_address_spec c;
        assert (U64.v (U64.sub (Seq.index roots_out i) mword) ==
                U64.v (SpecHeap.hd_address c));
        U64.v_inj (U64.sub (Seq.index roots_out i) mword) (SpecHeap.hd_address c);
        assert (U64.sub (Seq.index roots_out i) mword == SpecHeap.hd_address c)
      | 1 ->
        assert (Seq.index roots_out i == img);
        object_header_not_c_field1 r prepared_major a_prime;
        assert (Seq.index roots_out i == (a_prime <: U64.t));
        SpecHeap.hd_address_spec a_prime;
        assert (U64.v (U64.sub (Seq.index roots_out i) mword) ==
                U64.v (SpecHeap.hd_address a_prime));
        U64.v_inj (U64.sub (Seq.index roots_out i) mword) (SpecHeap.hd_address a_prime);
        assert (U64.sub (Seq.index roots_out i) mword ==
                SpecHeap.hd_address a_prime)
      | _ ->
        nat_lt_two_cases i;
        assert False
    end
  in
  FStar.Classical.forall_intro no_root_header;
  MarkBoundedImpl.darken_roots_bounded_spec_preserves_read_word
    result.mc_major st roots_out cap slot
#pop-options

let spot_concrete_c_field_final_points_to_a_prime
  (r: unit{ConcreteMajor.spot_major_room})
  (d2: minor_heap) (b2: U64.t)
  (roots_out: seq U64.t) (ok: bool) (final_major: heap)
  (st: seq obj_addr) (cap: nat)
  =
  let result =
    Cheney.cheney_collect_spec
      ConcreteMinor.spot_minor2
      (ConcreteMajor.spot_major_heap r)
      (ConcreteMajor.spot_major_fp r)
      (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) in
  let c = ConcreteMajor.spot_c r in
  let prom =
    Cheney.cheney_promote
      ConcreteMinor.spot_minor2
      (ConcreteMajor.spot_major_heap r)
      (ConcreteMajor.spot_major_fp r)
      (ThreeObjects.spot_roots c) in
  let img = prom.fwd_map Layout.a_minor in
  ConcreteForwarding.spot_concrete_no_oom r;
  ConcreteScenarios.spot_concrete_c_field_rewritten_from_no_oom r;
  post_minor_c_wosize r;
  post_roots_mem_c r roots_out st cap;
  post_roots_mem_a_prime r roots_out st cap;
  let a_prime = (img <: obj_addr) in
  let prepared_major = GenImpl.gen_gc_prepared_major
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    (ThreeObjects.spot_roots c)
    st cap in
  let prepared_roots = GenImpl.gen_gc_prepared_roots
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    (ThreeObjects.spot_roots c)
    st cap in
  assert (Seq.mem c prepared_roots);
  assert (Seq.mem a_prime prepared_roots);
  assert (GenImpl.gen_gc_stack_budget (ThreeObjects.spot_roots c) st cap);
  spot_root_heap_reachable_from_major_gc_pre r st cap c;
  spot_root_heap_reachable_from_major_gc_pre r st cap a_prime;
  assert (SpecCorrectness.major_gc_live_subgraph_isomorphism
    prepared_major final_major prepared_roots);
  prepared_roots_preserve_c_field1 r roots_out st cap;
  c_field1_get_field r prepared_major;
  c_field1_get_field r final_major;
  assert (U64.v 2UL <= U64.v (SpecObj.wosize_of_object c prepared_major));
  assert (HeapGraph.get_field prepared_major c 2UL ==
          HeapGraph.get_field final_major c 2UL);
  spot_concrete_c_final_survives r d2 b2 roots_out ok final_major st cap;
  spot_concrete_a_prime_final_survives r d2 b2 roots_out ok final_major st cap;
  assert (SpecHeap.read_word result.mc_major (ConcreteMajor.spot_c_field1 r) ==
          img);
  assert (SpecHeap.read_word prepared_major (ConcreteMajor.spot_c_field1 r) ==
          SpecHeap.read_word result.mc_major (ConcreteMajor.spot_c_field1 r));
  assert (SpecHeap.read_word prepared_major (ConcreteMajor.spot_c_field1 r) ==
          img);
  assert (SpecHeap.read_word final_major (ConcreteMajor.spot_c_field1 r) ==
          img);
  assert (a_prime == img);
  assert (exists (a_prime: obj_addr).
    a_prime == img /\
    Seq.mem a_prime (SpecFields.objects zero_addr final_major) /\
    SpecHeap.read_word final_major (ConcreteMajor.spot_c_field1 r) == a_prime)
