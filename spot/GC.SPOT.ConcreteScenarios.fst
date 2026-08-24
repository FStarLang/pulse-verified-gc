module GC.SPOT.ConcreteScenarios

module U64 = FStar.UInt64
module Seq = FStar.Seq

open FStar.Seq
open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

module Layout = GC.SPOT.Layout
module Preconditions = GC.SPOT.Preconditions
module ThreeObjects = GC.SPOT.ThreeObjects
module ConcreteMinor = GC.SPOT.ConcreteMinor
module ConcreteMajor = GC.SPOT.ConcreteMajor
module Postconditions = GC.SPOT.Postconditions
module SpecHeap = GC.Spec.Heap
module SpecObj = GC.Spec.Object
module SpecFields = GC.Spec.Fields
module GenInv = GC.Gen.HeapInvariant
module Promote = GC.Gen.Promote
module Cheney = GC.Gen.Cheney
module CheneyBFS = GC.Gen.CheneyBFS
module CheneyCorr = GC.Gen.CheneyCorrectness
module ConcreteForwarding = GC.SPOT.ConcreteForwarding
module MinorFwd = GC.Gen.MinorCollectForwarding
module MinorFwdHelpers = GC.Gen.MinorCollectForwarding.Helpers
module RBridge = GC.Gen.ReachabilityBridge
module PromoteUpdate = GC.Gen.PromoteUpdate
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module GenImpl = GC.Gen.Impl
module CheneyPres = GC.Gen.CheneyPreservation
module MajorGC = GC.Impl
module MarkBoundedImpl = GC.Impl.MarkBounded
module MarkBoundedRootLemmas = GC.Impl.MarkBoundedRootLemmas
module SpecMarkBounded = GC.Spec.MarkBounded
module SpecMarkBoundedInv = GC.Spec.MarkBoundedInv
module SpecMark = GC.Spec.Mark
module SpecSweep = GC.Spec.Sweep
module SpecHeapModel = GC.Spec.HeapModel
module SpecHeapGraph = GC.Spec.HeapGraph
module SpecGraph = GC.Spec.Graph
module MBP = GC.Impl.MarkBoundedPrecondition
module GMP = GC.Gen.MajorPrecondition

let spot_fwd_array : seq U64.t =
  Seq.create UpdatePtrs.fwd_array_size 0UL

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let zero_not_minor_pointer ()
  : Lemma (ensures ~(Promote.is_minor_pointer 0UL))
  = assert_norm (Promote.is_minor_pointer 0UL == false)

let zero_not_major_pointer ()
  : Lemma (ensures ~(SpecFields.is_pointer_field 0UL))
  =
  zero_addr_above_2048 ();
  assert (U64.v 0UL < U64.v zero_addr + U64.v mword)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let spot_fwd_array_zero ()
  =
  FStar.Seq.Base.lemma_create_len UpdatePtrs.fwd_array_size 0UL;
  assert (Seq.length spot_fwd_array == UpdatePtrs.fwd_array_size);
  let aux (i: nat)
    : Lemma (ensures i < Seq.length spot_fwd_array ==> Seq.index spot_fwd_array i == 0UL)
    =
    if i < Seq.length spot_fwd_array then begin
      assert (i < UpdatePtrs.fwd_array_size);
      FStar.Seq.Base.lemma_index_create UpdatePtrs.fwd_array_size 0UL i
    end
  in
  FStar.Classical.forall_intro aux;
  Preconditions.zero_forwarding_array_intro spot_fwd_array
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let spot_c_slot_is_field1 (r: unit{ConcreteMajor.spot_major_room})
  =
  ConcreteMajor.spot_major_layout_facts r;
  ThreeObjects.spot_c_to_a_slot_spec (ConcreteMajor.spot_c r);
  assert (U64.v (ThreeObjects.spot_c_to_a_slot (ConcreteMajor.spot_c r)) ==
          U64.v (ConcreteMajor.spot_c r) + 8);
  assert (U64.v (ConcreteMajor.spot_c_field1 r) ==
          U64.v (ConcreteMajor.spot_c r) + 8)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let spot_minor_major_fields_no_blue (r: unit{ConcreteMajor.spot_major_room})
  : Lemma (GenInv.minor_major_fields_no_blue
             ConcreteMinor.spot_minor2 (ConcreteMajor.spot_major_heap r))
  =
  let aux (obj: U64.t) (j: nat)
    : Lemma
        (requires
          Seq.mem obj (minor_objects ConcreteMinor.spot_minor2) /\
          j < minor_wosize ConcreteMinor.spot_minor2 obj)
        (ensures
          ~(SpecFields.is_pointer_field
            (minor_read_field ConcreteMinor.spot_minor2 obj j)))
    =
    ConcreteMinor.spot_minor2_field_zero obj j;
    zero_not_major_pointer ();
    assert (minor_read_field ConcreteMinor.spot_minor2 obj j == 0UL)
  in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 aux);
  GenInv.minor_major_fields_no_blue_no_pointer_fields
    ConcreteMinor.spot_minor2 (ConcreteMajor.spot_major_heap r)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let spot_major_minor_fields_no_infix_targets (r: unit{ConcreteMajor.spot_major_room})
  : Lemma (GenInv.major_minor_fields_no_infix_targets
             ConcreteMinor.spot_minor2 (ConcreteMajor.spot_major_heap r))
  =
  let major = ConcreteMajor.spot_major_heap r in
  let aux (obj: obj_addr) (j: nat)
    : Lemma
        (ensures
          Seq.mem obj (SpecFields.objects zero_addr major) /\
          ~(SpecObj.is_blue obj major) /\
          ~(SpecObj.is_no_scan obj major) /\
          j < U64.v (SpecObj.wosize_of_object obj major) /\
          U64.v obj + j * 8 + 8 <= heap_size /\
          (U64.v obj + j * 8) % 8 == 0 ==>
          (let v = to_minor_offset
             (SpecHeap.read_word major (U64.uint_to_t (U64.v obj + j * 8))) in
           Promote.is_minor_pointer v ==> ~(is_infix_in_minor ConcreteMinor.spot_minor2 v)))
    =
    if Seq.mem obj (SpecFields.objects zero_addr major) /\
       ~(SpecObj.is_blue obj major) /\
       ~(SpecObj.is_no_scan obj major) /\
       j < U64.v (SpecObj.wosize_of_object obj major) /\
       U64.v obj + j * 8 + 8 <= heap_size /\
       (U64.v obj + j * 8) % 8 == 0
    then begin
      ConcreteMajor.spot_major_object_cases r obj;
      ConcreteMajor.spot_major_c_reads r;
      ConcreteMajor.spot_major_free_reads r;
      if obj = ConcreteMajor.spot_c r then begin
        assert (U64.v (SpecObj.wosize_of_object obj major) == Layout.c_wosize);
        assert (j < 2);
        if j = 0 then begin
          ConcreteMajor.spot_major_layout_facts r;
          assert (U64.v obj == U64.v (ConcreteMajor.spot_c r));
          assert (U64.v obj + j * 8 == U64.v (ConcreteMajor.spot_c r));
          assert (U64.uint_to_t (U64.v obj + j * 8) == ConcreteMajor.spot_c_field0 r);
          assert (SpecHeap.read_word major (U64.uint_to_t (U64.v obj + j * 8)) == 0UL);
          zero_not_minor_pointer ()
        end else begin
          assert (j == Layout.c_to_a_field_index);
          ConcreteMajor.spot_major_layout_facts r;
          assert (U64.uint_to_t (U64.v obj + j * 8) == ConcreteMajor.spot_c_field1 r);
          assert (SpecHeap.read_word major (U64.uint_to_t (U64.v obj + j * 8)) ==
                  Layout.a_minor);
          to_minor_offset_in_minor_range Layout.a_minor;
          ConcreteMinor.spot_minor_a_not_infix ()
        end
      end else begin
        assert (obj == ConcreteMajor.spot_free_obj r);
        assert (SpecObj.is_blue obj major);
        assert False
      end
    end
  in
  FStar.Classical.forall_intro_2 aux;
  GenInv.major_minor_fields_no_infix_targets_intro
    ConcreteMinor.spot_minor2 major
#pop-options

let spot_collection_heap_shape (r: unit{ConcreteMajor.spot_major_room})
  : Lemma (GenInv.collection_heap_shape
             ConcreteMinor.spot_minor2
             (ConcreteMajor.spot_major_heap r)
             (ConcreteMajor.spot_major_fp r))
  =
  ConcreteMajor.spot_major_heap_shape r;
  ConcreteMinor.spot_minor_heap_shape ();
  spot_minor_major_fields_no_blue r;
  spot_major_minor_fields_no_infix_targets r;
  GenInv.collection_heap_shape_intro
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let spot_ref_table_sound (r: unit{ConcreteMajor.spot_major_room})
  : Lemma (UpdatePtrs.ref_table_sound
             (ConcreteMajor.spot_major_heap r)
             (ThreeObjects.spot_slots (ConcreteMajor.spot_c r)) 1)
  =
  let major = ConcreteMajor.spot_major_heap r in
  spot_c_slot_is_field1 r;
  ThreeObjects.spot_slots_len (ConcreteMajor.spot_c r);
  assert (1 <= Seq.length (ThreeObjects.spot_slots (ConcreteMajor.spot_c r)));
  ConcreteMajor.spot_major_objects r;
  ConcreteMajor.spot_major_c_reads r;
  ConcreteMajor.spot_major_layout_facts r;
  let aux (i: nat)
    : Lemma (ensures
              i < 1 ==>
              (let addr = U64.v (Seq.index (ThreeObjects.spot_slots (ConcreteMajor.spot_c r)) i) in
               addr < heap_size /\ addr % 8 == 0 /\
               (exists (obj: obj_addr) (j: nat).
                 Seq.mem obj (SpecFields.objects zero_addr major) /\
                 SpecObj.is_blue obj major = false /\
                 SpecObj.is_no_scan obj major = false /\
                 j < U64.v (SpecObj.wosize_of_object obj major) /\
                 addr == U64.v obj + j * 8)))
    =
    if i < 1 then begin
      assert (i == 0);
      assert (i < Seq.length (ThreeObjects.spot_slots (ConcreteMajor.spot_c r)));
      ThreeObjects.spot_slots_index (ConcreteMajor.spot_c r) i;
      assert (Seq.index (ThreeObjects.spot_slots (ConcreteMajor.spot_c r)) i ==
              ConcreteMajor.spot_c_field1 r);
      assert (U64.v (ConcreteMajor.spot_c_field1 r) ==
              U64.v (ConcreteMajor.spot_c r) + Layout.c_to_a_field_index * 8);
      ThreeObjects.spot_roots_mem_c (ConcreteMajor.spot_c r);
      ConcreteMajor.spot_major_c_mem r;
      assert (Seq.mem (ConcreteMajor.spot_c r)
        (SpecFields.objects zero_addr major));
      assert (Layout.c_to_a_field_index < U64.v (SpecObj.wosize_of_object
        (ConcreteMajor.spot_c r) major));
      assert (exists (obj: obj_addr) (j: nat).
        Seq.mem obj (SpecFields.objects zero_addr major) /\
        SpecObj.is_blue obj major = false /\
        SpecObj.is_no_scan obj major = false /\
        j < U64.v (SpecObj.wosize_of_object obj major) /\
        U64.v (ConcreteMajor.spot_c_field1 r) == U64.v obj + j * 8)
    end
  in
  FStar.Classical.forall_intro aux
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let spot_ref_table_covers_minor_ptrs (r: unit{ConcreteMajor.spot_major_room})
  : Lemma (UpdatePtrs.ref_table_covers_minor_ptrs
             (ConcreteMajor.spot_major_heap r)
             (ThreeObjects.spot_slots (ConcreteMajor.spot_c r)) 1)
  =
  let major = ConcreteMajor.spot_major_heap r in
  spot_c_slot_is_field1 r;
  ThreeObjects.spot_slots_len (ConcreteMajor.spot_c r);
  assert (1 <= Seq.length (ThreeObjects.spot_slots (ConcreteMajor.spot_c r)));
  ConcreteMajor.spot_major_objects r;
  ConcreteMajor.spot_major_c_reads r;
  ConcreteMajor.spot_major_free_reads r;
  let aux (obj: obj_addr) (j: nat)
    : Lemma
        (ensures
          Seq.mem obj (SpecFields.objects zero_addr major) /\
          SpecObj.is_blue obj major = false /\
          SpecObj.is_no_scan obj major = false /\
          j < U64.v (SpecObj.wosize_of_object obj major) /\
          U64.v obj + j * 8 + 8 <= heap_size /\
          (let field_val =
            to_minor_offset
              (SpecHeap.read_word major (U64.uint_to_t (U64.v obj + j * 8))) in
           Promote.is_minor_pointer field_val) ==>
          (exists (i: nat).
            i < 1 /\
            U64.v (Seq.index (ThreeObjects.spot_slots (ConcreteMajor.spot_c r)) i) ==
              U64.v obj + j * 8))
    =
    if Seq.mem obj (SpecFields.objects zero_addr major) /\
       SpecObj.is_blue obj major = false /\
       SpecObj.is_no_scan obj major = false /\
       j < U64.v (SpecObj.wosize_of_object obj major) /\
       U64.v obj + j * 8 + 8 <= heap_size /\
       (let field_val =
          to_minor_offset
            (SpecHeap.read_word major (U64.uint_to_t (U64.v obj + j * 8))) in
        Promote.is_minor_pointer field_val)
    then begin
      ConcreteMajor.spot_major_object_cases r obj;
      if obj = ConcreteMajor.spot_c r then begin
        ConcreteMajor.spot_major_layout_facts r;
        assert (obj == ConcreteMajor.spot_c r);
        assert (U64.v (SpecObj.wosize_of_object obj major) == Layout.c_wosize);
        assert (j < 2);
        if j = 0 then begin
          assert (j == 0);
          assert (U64.v (ConcreteMajor.spot_c_field0 r) == U64.v obj + j * 8);
          assert (U64.uint_to_t (U64.v obj + j * 8) == ConcreteMajor.spot_c_field0 r);
          assert (SpecHeap.read_word major (U64.uint_to_t (U64.v obj + j * 8)) == 0UL);
          zero_not_minor_pointer ();
          assert False
        end else begin
          assert (j <> 0);
          assert (j == Layout.c_to_a_field_index);
          assert (U64.v (ConcreteMajor.spot_c_field1 r) == U64.v obj + j * 8);
          assert (U64.uint_to_t (U64.v obj + j * 8) == ConcreteMajor.spot_c_field1 r);
          ThreeObjects.spot_slots_index (ConcreteMajor.spot_c r) 0;
          assert (Seq.index (ThreeObjects.spot_slots (ConcreteMajor.spot_c r)) 0 ==
                  ConcreteMajor.spot_c_field1 r);
          assert (U64.v (Seq.index (ThreeObjects.spot_slots (ConcreteMajor.spot_c r)) 0) ==
                  U64.v obj + j * 8);
          assert (exists (i: nat).
            i < 1 /\
            U64.v (Seq.index (ThreeObjects.spot_slots (ConcreteMajor.spot_c r)) i) ==
              U64.v obj + j * 8)
        end
      end else begin
        assert (obj == ConcreteMajor.spot_free_obj r);
        ConcreteMajor.spot_major_free_reads r;
        assert (SpecObj.is_blue obj major);
        assert False
      end
    end
  in
  FStar.Classical.forall_intro_2 aux
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let spot_remembered_targets_in_roots (r: unit{ConcreteMajor.spot_major_room})
  : Lemma (MinorFwd.remembered_targets_in_roots
             (ConcreteMajor.spot_major_heap r)
             (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
             (ThreeObjects.spot_slots (ConcreteMajor.spot_c r)) 1)
  =
  let major = ConcreteMajor.spot_major_heap r in
  spot_c_slot_is_field1 r;
  ThreeObjects.spot_slots_len (ConcreteMajor.spot_c r);
  assert (1 <= Seq.length (ThreeObjects.spot_slots (ConcreteMajor.spot_c r)));
  ConcreteMajor.spot_major_c_reads r;
  let aux (i: nat)
    : Lemma (ensures
              i < 1 ==>
              U64.v (Seq.index (ThreeObjects.spot_slots (ConcreteMajor.spot_c r)) i) < heap_size /\
              U64.v (Seq.index (ThreeObjects.spot_slots (ConcreteMajor.spot_c r)) i) % U64.v mword == 0 /\
              (let slot = (Seq.index (ThreeObjects.spot_slots (ConcreteMajor.spot_c r)) i <: hp_addr) in
               let v = to_minor_offset (SpecHeap.read_word major slot) in
               Promote.is_minor_pointer v ==> Seq.mem v (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))))
    =
    if i < 1 then begin
      assert (i == 0);
      assert (i < Seq.length (ThreeObjects.spot_slots (ConcreteMajor.spot_c r)));
      ThreeObjects.spot_slots_index (ConcreteMajor.spot_c r) i;
      assert (Seq.index (ThreeObjects.spot_slots (ConcreteMajor.spot_c r)) i ==
              ConcreteMajor.spot_c_field1 r);
      assert (SpecHeap.read_word major (ConcreteMajor.spot_c_field1 r) == Layout.a_minor);
      to_minor_offset_in_minor_range Layout.a_minor;
      ThreeObjects.spot_roots_mem_a (ConcreteMajor.spot_c r)
    end
  in
  FStar.Classical.forall_intro aux;
  MinorFwdHelpers.remembered_targets_in_roots_intro_by_slots
    major (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
    (ThreeObjects.spot_slots (ConcreteMajor.spot_c r)) 1
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let spot_roots_valid_for_minor_collection (r: unit{ConcreteMajor.spot_major_room})
  : Lemma (MinorFwd.roots_valid_for_minor_collection
             ConcreteMinor.spot_minor2
             (ConcreteMajor.spot_major_heap r)
             (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)))
  =
  let major = ConcreteMajor.spot_major_heap r in
  let aux (root: U64.t)
    : Lemma
        (requires Seq.mem root (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)))
        (ensures
          ((Promote.is_minor_pointer root ==>
            Seq.mem root (minor_objects ConcreteMinor.spot_minor2) /\
            minor_wosize ConcreteMinor.spot_minor2 root > 0) /\
           (~(Promote.is_minor_pointer root) ==>
            is_val_addr root /\
            Seq.mem (root <: obj_addr) (SpecFields.objects zero_addr major) /\
            ~(SpecObj.is_blue (root <: obj_addr) major))))
    =
    ThreeObjects.spot_roots_cases (ConcreteMajor.spot_c r) root;
    if root = (ConcreteMajor.spot_c r <: U64.t) then begin
      ConcreteMajor.spot_major_c_reads r;
      ConcreteMajor.spot_major_c_mem r;
      assert ((root <: obj_addr) == ConcreteMajor.spot_c r);
      assert (Seq.mem (ConcreteMajor.spot_c r) (SpecFields.objects zero_addr major));
      RBridge.major_object_not_minor_pointer major (ConcreteMajor.spot_c r)
    end else begin
      assert (root == Layout.a_minor);
      if root = Layout.a_minor then begin
        Layout.a_minor_is_minor_pointer ();
        ConcreteMinor.spot_minor_two_object_layout ()
      end else begin
        assert False
      end
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

let spot_concrete_minor_collect_full_pre (r: unit{ConcreteMajor.spot_major_room})
  =
  spot_collection_heap_shape r;
  spot_fwd_array_zero ();
  spot_ref_table_sound r;
  spot_ref_table_covers_minor_ptrs r;
  ThreeObjects.spot_slots_singleton_distinct (ConcreteMajor.spot_c r);
  spot_remembered_targets_in_roots r;
  spot_roots_valid_for_minor_collection r;
  Preconditions.minor_collect_full_pre_intro
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
    spot_fwd_array
    (ThreeObjects.spot_slots (ConcreteMajor.spot_c r))
    1

let spot_concrete_minor_scenario_pre_from_no_oom
  (r: unit{ConcreteMajor.spot_major_room})
  =
  ConcreteForwarding.spot_concrete_no_oom r;
  spot_concrete_minor_collect_full_pre r;
  ConcreteMajor.spot_major_objects r;
  ConcreteMajor.spot_major_c_mem r;
  ConcreteMajor.spot_major_c_reads r;
  ConcreteMinor.spot_minor_two_object_layout ();
  spot_c_slot_is_field1 r;
  RBridge.major_object_not_minor_pointer
    (ConcreteMajor.spot_major_heap r) (ConcreteMajor.spot_c r);
  assert (U64.v (SpecObj.wosize_of_object (ConcreteMajor.spot_c r)
                   (ConcreteMajor.spot_major_heap r)) == Layout.c_wosize);
  assert (U64.v (SpecObj.wosize_of_object (ConcreteMajor.spot_c r)
                   (ConcreteMajor.spot_major_heap r)) >
          Layout.c_to_a_field_index);
  assert (SpecHeap.read_word (ConcreteMajor.spot_major_heap r)
    (ThreeObjects.spot_c_to_a_slot (ConcreteMajor.spot_c r)) ==
    Layout.a_minor);
  assert (minor_wosize ConcreteMinor.spot_minor2 Layout.a_minor > 0);
  assert (minor_wosize ConcreteMinor.spot_minor2 Layout.b_minor > 0);
  ThreeObjects.spot_minor_scenario_pre_intro_from_c_to_a
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    (ConcreteMajor.spot_c r)
    spot_fwd_array

let spot_concrete_gen_gc_pre_from_stack
  (r: unit{ConcreteMajor.spot_major_room}) (st: seq obj_addr) (cap: nat)
  =
  spot_concrete_minor_collect_full_pre r;
  Preconditions.gen_gc_pre_intro
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
    spot_fwd_array
    (ThreeObjects.spot_slots (ConcreteMajor.spot_c r))
    1 st cap

let spot_concrete_gen_gc_major_pre_empty_stack
  (r: unit{ConcreteMajor.spot_major_room}) (cap: nat{cap >= 2})
  : Lemma
      (ensures
        GenImpl.gen_gc_major_precondition
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
          Seq.empty cap)
  =
  ConcreteForwarding.spot_concrete_no_oom r;
  ThreeObjects.spot_roots_len (ConcreteMajor.spot_c r);
  assert_norm (Seq.length (Seq.empty #obj_addr) == 0)

let spot_concrete_gen_gc_pre_empty_stack
  (r: unit{ConcreteMajor.spot_major_room}) (cap: nat{cap >= 2})
  =
  spot_concrete_gen_gc_major_pre_empty_stack r cap;
  spot_concrete_gen_gc_pre_from_stack r Seq.empty cap

let spot_concrete_a_promoted_from_no_oom (r: unit{ConcreteMajor.spot_major_room})
  =
  spot_concrete_minor_scenario_pre_from_no_oom r;
  ThreeObjects.spot_a_promoted
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    (ConcreteMajor.spot_c r)
    spot_fwd_array

let spot_concrete_c_field_rewritten_from_no_oom
  (r: unit{ConcreteMajor.spot_major_room})
  =
  spot_concrete_minor_scenario_pre_from_no_oom r;
  ThreeObjects.spot_c_field_rewritten_to_a_prime
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    (ConcreteMajor.spot_c r)
    spot_fwd_array;
  spot_c_slot_is_field1 r

let spot_concrete_b_not_promoted (r: unit{ConcreteMajor.spot_major_room})
  =
  ConcreteForwarding.spot_concrete_b_forwarding_zero r;
  ThreeObjects.spot_b_not_promoted_from_forwarding_zero
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    (ConcreteMajor.spot_c r)
