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

let nat_lt_two_cases (i: nat)
  : Lemma
      (requires i < 2)
      (ensures i == 0 \/ i == 1)
  =
  if i = 0 then ()
  else if i = 1 then ()
  else begin
    assert (i >= 2);
    assert False
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let fp_in_heap_transfer (fp: U64.t) (g1 g2: heap)
  : Lemma
      (requires
        SpecSweep.fp_in_heap fp g1 /\
        SpecFields.objects zero_addr g2 == SpecFields.objects zero_addr g1)
      (ensures SpecSweep.fp_in_heap fp g2)
  =
  if fp = 0UL then ()
  else begin
    SpecSweep.fp_in_heap_elim fp g1;
    assert (Seq.mem (fp <: obj_addr) (SpecFields.objects zero_addr g1));
    assert (Seq.mem (fp <: obj_addr) (SpecFields.objects zero_addr g2))
  end

let root_points_to_object_from_mem (g: heap) (obj: obj_addr)
  : Lemma
      (requires
        U64.v obj >= U64.v zero_addr + U64.v mword /\
        Seq.mem obj (SpecFields.objects zero_addr g))
      (ensures MarkBoundedImpl.root_points_to_object g (obj <: U64.t))
  =
  let h = U64.sub (obj <: U64.t) mword in
  SpecHeap.hd_address_spec obj;
  assert (U64.v h == U64.v (SpecHeap.hd_address obj));
  U64.v_inj h (SpecHeap.hd_address obj);
  assert (h == SpecHeap.hd_address obj);
  SpecHeap.f_hd_roundtrip obj;
  assert (SpecHeap.f_address h == obj)

let bounded_stack_props_root_props (g: heap) (st: seq obj_addr)
  : Lemma
      (requires SpecMarkBounded.bounded_stack_props g st)
      (ensures SpecMark.root_props g st)
  =
  let aux (r: obj_addr)
    : Lemma
        (requires Seq.mem r st)
        (ensures
          Seq.mem r (SpecFields.objects zero_addr g) /\
          (SpecObj.is_gray r g \/ SpecObj.is_black r g))
    =
    SpecMark.sev_mem_objects g st r;
    assert (SpecMark.stack_points_to_gray g st);
    assert (SpecObj.is_gray r g)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

#push-options "--fuel 1 --ifuel 0"
let rec stack_no_dups_coerce_is_vertex_set (st: seq obj_addr)
  : Lemma
      (requires SpecMark.stack_no_dups st)
      (ensures SpecGraph.is_vertex_set (SpecHeapGraph.coerce_to_vertex_list st))
      (decreases Seq.length st)
  =
  if Seq.length st = 0 then ()
  else begin
    let hd = Seq.head st in
    let tl = Seq.tail st in
    Seq.cons_head_tail st;
    assert (st == Seq.cons hd tl);
    assert (SpecMark.stack_no_dups (Seq.cons hd tl));
    assert (~(Seq.mem hd tl));
    assert (SpecMark.stack_no_dups tl);
    stack_no_dups_coerce_is_vertex_set tl;
    SpecHeapGraph.coerce_cons_lemma hd tl;
    SpecHeapGraph.coerce_mem_lemma tl hd;
    assert (~(Seq.mem hd (SpecHeapGraph.coerce_to_vertex_list tl)));
    SpecGraph.is_vertex_set_cons hd (SpecHeapGraph.coerce_to_vertex_list tl)
  end
#pop-options

let bounded_mark_inv_graph_facts (g: heap) (st: seq obj_addr) (cap: nat)
  : Lemma
      (requires
        SpecMarkBoundedInv.bounded_mark_inv g st cap /\
        SpecMark.root_props g st)
      (ensures (
        let graph = SpecHeapModel.create_graph g in
        let roots' = SpecHeapGraph.coerce_to_vertex_list st in
        SpecGraph.graph_wf graph /\
        SpecGraph.is_vertex_set roots' /\
        SpecGraph.subset_vertices roots' graph.vertices))
  =
  SpecMarkBoundedInv.bounded_mark_inv_elim_wfh g st cap;
  SpecMarkBoundedInv.bounded_mark_inv_elim_bsp g st cap;
  assert (SpecMark.stack_no_dups st);
  stack_no_dups_coerce_is_vertex_set st;
  SpecMark.root_graph_precondition g st

let cheney_gray_black_stack_to_gray_stack (g: heap) (st: seq obj_addr)
  : Lemma
      (requires CheneyPres.gray_black_objects_on_stack g st)
      (ensures SpecMark.gray_objects_on_stack g st)
  =
  let aux (obj: obj_addr)
    : Lemma
        (requires
          Seq.mem obj (SpecFields.objects zero_addr g) /\
          SpecObj.is_gray obj g)
        (ensures Seq.mem obj st)
    =
    assert (SpecObj.is_gray obj g \/ SpecObj.is_black obj g);
    assert (Seq.mem obj st)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let gray_objects_no_black_to_gray_black_stack (g: heap) (st: seq obj_addr)
  : Lemma
      (requires SpecMark.gray_objects_on_stack g st /\
                SpecMark.no_black_objects g)
      (ensures GenInv.gray_black_objects_on_stack g st)
  =
  let aux (obj: obj_addr)
    : Lemma
        (requires
          Seq.mem obj (SpecFields.objects zero_addr g) /\
          (SpecObj.is_gray obj g \/ SpecObj.is_black obj g))
        (ensures Seq.mem obj st)
    =
    if SpecObj.is_gray obj g then
      assert (Seq.mem obj st)
    else begin
      assert (SpecObj.is_black obj g);
      assert False
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let spot_major_gray_black_empty (r: unit{ConcreteMajor.spot_major_room})
  : Lemma
      (ensures
        CheneyPres.gray_black_objects_on_stack
          (ConcreteMajor.spot_major_heap r) (Seq.empty #obj_addr))
  =
  let major = ConcreteMajor.spot_major_heap r in
  let c = ConcreteMajor.spot_c r in
  let free = ConcreteMajor.spot_free_obj r in
  ConcreteMajor.spot_major_objects r;
  let aux (obj: obj_addr)
    : Lemma
        (requires
          Seq.mem obj (SpecFields.objects zero_addr major) /\
          (SpecObj.is_gray obj major \/ SpecObj.is_black obj major))
        (ensures Seq.mem obj (Seq.empty #obj_addr))
    =
    ConcreteMajor.spot_major_object_cases r obj;
    if obj = c then begin
      ConcreteMajor.spot_major_c_reads r;
      if SpecObj.is_gray obj major then assert False
      else begin
        assert (SpecObj.is_black obj major);
        assert False
      end
    end
    else begin
      assert (obj == free);
      ConcreteMajor.spot_major_free_reads r;
      if SpecObj.is_gray obj major then assert False
      else begin
        assert (SpecObj.is_black obj major);
        assert False
      end
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
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

let spot_post_minor_roots_shape (r: unit{ConcreteMajor.spot_major_room})
  : Lemma
      (ensures (
        let c = ConcreteMajor.spot_c r in
        let prom = Cheney.cheney_promote
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots c) in
        let result = Cheney.cheney_collect_spec
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots c) in
        Seq.length result.mc_roots == 2 /\
        Seq.index result.mc_roots 0 == (c <: U64.t) /\
        Seq.index result.mc_roots 1 == prom.fwd_map Layout.a_minor))
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
  ThreeObjects.spot_roots_len c;
  Promote.rewrite_roots_length roots prom.fwd_map;
  assert (Seq.length result.mc_roots == 2);
  ThreeObjects.spot_roots_index_c c;
  Promote.rewrite_roots_index roots prom.fwd_map 0;
  ConcreteMajor.spot_major_layout_facts r;
  zero_addr_above_minor ();
  assert (~(Promote.is_minor_pointer (c <: U64.t)));
  assert (Promote.rewrite_root (c <: U64.t) prom.fwd_map == (c <: U64.t));
  assert (Seq.index result.mc_roots 0 == (c <: U64.t));
  ThreeObjects.spot_roots_index_a c;
  Promote.rewrite_roots_index roots prom.fwd_map 1;
  Layout.a_minor_is_minor_pointer ();
  ConcreteForwarding.spot_concrete_a_forwarding_free_obj r;
  ConcreteMajor.spot_major_layout_facts r;
  assert (prom.fwd_map Layout.a_minor <> 0UL);
  assert (Promote.rewrite_root Layout.a_minor prom.fwd_map ==
          prom.fwd_map Layout.a_minor);
  assert (Seq.index result.mc_roots 1 == prom.fwd_map Layout.a_minor)

let spot_post_minor_roots_point_to_objects
  (r: unit{ConcreteMajor.spot_major_room})
  : Lemma
      (ensures (
        let result = Cheney.cheney_collect_spec
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) in
        forall (i:nat). i < Seq.length result.mc_roots ==>
          MarkBoundedImpl.root_points_to_object result.mc_major
            (Seq.index result.mc_roots i)))
  =
  let minor = ConcreteMinor.spot_minor2 in
  let major = ConcreteMajor.spot_major_heap r in
  let fp = ConcreteMajor.spot_major_fp r in
  let c = ConcreteMajor.spot_c r in
  let free = ConcreteMajor.spot_free_obj r in
  let roots = ThreeObjects.spot_roots c in
  let prom = Cheney.cheney_promote minor major fp roots in
  let result = Cheney.cheney_collect_spec minor major fp roots in
  spot_collection_heap_shape r;
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.major_heap_shape_elim major fp;
  ConcreteMajor.spot_major_objects r;
  ConcreteMajor.spot_major_c_mem r;
  ConcreteMajor.spot_major_free_mem r;
  CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
  assert (Seq.mem c (SpecFields.objects zero_addr result.mc_major));
  assert (Seq.mem free (SpecFields.objects zero_addr result.mc_major));
  spot_post_minor_roots_shape r;
  ConcreteForwarding.spot_concrete_a_forwarding_free_obj r;
  assert (prom.fwd_map Layout.a_minor == (free <: U64.t));
  ConcreteMajor.spot_major_layout_facts r;
  let aux (i:nat)
    : Lemma
        (ensures
          i < Seq.length result.mc_roots ==>
            MarkBoundedImpl.root_points_to_object result.mc_major
              (Seq.index result.mc_roots i))
    =
    if i < Seq.length result.mc_roots then
      match i with
      | 0 ->
        assert (Seq.index result.mc_roots i == (c <: U64.t));
        root_points_to_object_from_mem result.mc_major c
      | 1 ->
        assert (Seq.index result.mc_roots i == (free <: U64.t));
        root_points_to_object_from_mem result.mc_major free
      | _ ->
        assert (Seq.length result.mc_roots == 2);
        nat_lt_two_cases i;
        assert False
  in
  FStar.Classical.forall_intro aux

let spot_post_minor_roots_mem_cases
  (r: unit{ConcreteMajor.spot_major_room}) (v: U64.t)
  : Lemma
      (requires (
        let result = Cheney.cheney_collect_spec
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) in
        Seq.mem v result.mc_roots))
      (ensures (
        let c = ConcreteMajor.spot_c r in
        let free = ConcreteMajor.spot_free_obj r in
        v == (c <: U64.t) \/ v == (free <: U64.t)))
  =
  let minor = ConcreteMinor.spot_minor2 in
  let major = ConcreteMajor.spot_major_heap r in
  let fp = ConcreteMajor.spot_major_fp r in
  let c = ConcreteMajor.spot_c r in
  let free = ConcreteMajor.spot_free_obj r in
  let roots = ThreeObjects.spot_roots c in
  let prom = Cheney.cheney_promote minor major fp roots in
  let result = Cheney.cheney_collect_spec minor major fp roots in
  spot_post_minor_roots_shape r;
  ConcreteForwarding.spot_concrete_a_forwarding_free_obj r;
  let i = Seq.index_mem v result.mc_roots in
  assert (Seq.index result.mc_roots i == v);
  nat_lt_two_cases i;
  if i = 0 then
    assert (v == (c <: U64.t))
  else begin
    assert (i == 1);
    assert (Seq.index result.mc_roots 1 == prom.fwd_map Layout.a_minor);
    assert (prom.fwd_map Layout.a_minor == (free <: U64.t));
    assert (v == (free <: U64.t))
  end

let spot_post_minor_c_header_context
  (r: unit{ConcreteMajor.spot_major_room})
  : Lemma
      (ensures (
        let minor = ConcreteMinor.spot_minor2 in
        let major = ConcreteMajor.spot_major_heap r in
        let fp = ConcreteMajor.spot_major_fp r in
        let c = ConcreteMajor.spot_c r in
        let result = Cheney.cheney_collect_spec minor major fp (ThreeObjects.spot_roots c) in
        Seq.mem c (SpecFields.objects zero_addr result.mc_major) /\
        ~(SpecObj.is_blue c result.mc_major) /\
        SpecObj.wosize_of_object c result.mc_major == U64.uint_to_t Layout.c_wosize /\
        ~(SpecObj.is_no_scan c result.mc_major)))
  =
  let minor = ConcreteMinor.spot_minor2 in
  let major = ConcreteMajor.spot_major_heap r in
  let fp = ConcreteMajor.spot_major_fp r in
  let c = ConcreteMajor.spot_c r in
  let roots = ThreeObjects.spot_roots c in
  let prom = Cheney.cheney_promote minor major fp roots in
  let result = Cheney.cheney_collect_spec minor major fp roots in
  spot_collection_heap_shape r;
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.major_heap_shape_elim major fp;
  ConcreteMajor.spot_major_objects r;
  ConcreteMajor.spot_major_c_mem r;
  ConcreteMajor.spot_major_c_reads r;
  assert (SpecObj.is_blue c major = false);
  MinorFwd.cheney_promote_preserves_old_major_field_context
    minor major fp roots c Layout.c_to_a_field_index;
  assert (Seq.mem c (SpecFields.objects zero_addr prom.major_final));
  assert (SpecObj.is_blue c prom.major_final = false);
  Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
  PromoteUpdate.update_major_pointers_preserves_header
    prom.major_final prom.fwd_map c;
  assert (result.mc_major == Promote.update_major_pointers prom.major_final prom.fwd_map);
  SpecObj.color_of_header_eq c prom.major_final result.mc_major;
  assert (~(SpecObj.is_blue c result.mc_major));
  SpecObj.wosize_of_object_spec c prom.major_final;
  SpecObj.wosize_of_object_spec c result.mc_major;
  assert (SpecObj.wosize_of_object c result.mc_major ==
          SpecObj.wosize_of_object c prom.major_final);
  assert (SpecObj.wosize_of_object c result.mc_major ==
          U64.uint_to_t Layout.c_wosize);
  SpecObj.tag_of_object_spec c prom.major_final;
  SpecObj.tag_of_object_spec c result.mc_major;
  SpecObj.is_no_scan_spec c prom.major_final;
  SpecObj.is_no_scan_spec c result.mc_major;
  assert (SpecObj.is_no_scan c result.mc_major ==
          SpecObj.is_no_scan c prom.major_final);
  assert (~(SpecObj.is_no_scan c result.mc_major));
  PromoteUpdate.update_major_pointers_preserves_objects
    prom.major_final prom.fwd_map;
  assert (Seq.mem c (SpecFields.objects zero_addr result.mc_major))

let spot_post_minor_c_points_to_free
  (r: unit{ConcreteMajor.spot_major_room})
  : Lemma
      (ensures (
        let result = Cheney.cheney_collect_spec
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) in
        SpecFields.points_to result.mc_major
          (ConcreteMajor.spot_c r) (ConcreteMajor.spot_free_obj r)))
  =
  let minor = ConcreteMinor.spot_minor2 in
  let major = ConcreteMajor.spot_major_heap r in
  let fp = ConcreteMajor.spot_major_fp r in
  let c = ConcreteMajor.spot_c r in
  let free = ConcreteMajor.spot_free_obj r in
  let roots = ThreeObjects.spot_roots c in
  let prom = Cheney.cheney_promote minor major fp roots in
  let result = Cheney.cheney_collect_spec minor major fp roots in
  spot_post_minor_c_header_context r;
  spot_concrete_minor_scenario_pre_from_no_oom r;
  ThreeObjects.spot_c_field_rewritten_to_a_prime
    minor major fp c spot_fwd_array;
  spot_c_slot_is_field1 r;
  ConcreteForwarding.spot_concrete_a_forwarding_free_obj r;
  assert (prom.fwd_map Layout.a_minor == (free <: U64.t));
  ConcreteMajor.spot_major_layout_facts r;
  assert (SpecObj.wosize_of_object c result.mc_major == U64.uint_to_t Layout.c_wosize);
  assert (Layout.c_wosize == 2);
  assert (Layout.c_to_a_field_index == 1);
  let field = ConcreteMajor.spot_c_field1 r in
  assert (field ==
    U64.add_mod c
      (U64.mul_mod (U64.sub (SpecObj.wosize_of_object c result.mc_major) 1UL) mword));
  assert (SpecHeap.read_word result.mc_major field == (free <: U64.t));
  assert (SpecFields.is_pointer_field (free <: U64.t));
  assert (SpecFields.is_pointer_to (SpecHeap.read_word result.mc_major field) free);
  let wz = SpecObj.wosize_of_object c result.mc_major in
  assert (U64.v wz == Layout.c_wosize);
  assert (U64.v wz == 2);
  FStar.Math.Lemmas.pow2_lt_compat 54 1;
  assert (pow2 1 == 2);
  assert (2 < pow2 54);
  assert (U64.v wz < pow2 54);
  assert (U64.v 0UL == 0);
  assert (wz <> 0UL);
  SpecFields.efptu_match result.mc_major c
    wz free field
    (SpecHeap.read_word result.mc_major field);
  assert (SpecFields.points_to result.mc_major c free)

let spot_post_minor_free_not_blue
  (r: unit{ConcreteMajor.spot_major_room})
  : Lemma
      (requires (
        let result = Cheney.cheney_collect_spec
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) in
        SpecMark.no_pointer_to_blue result.mc_major))
      (ensures (
        let result = Cheney.cheney_collect_spec
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) in
        ~(SpecObj.is_blue (ConcreteMajor.spot_free_obj r) result.mc_major)))
  =
  let minor = ConcreteMinor.spot_minor2 in
  let major = ConcreteMajor.spot_major_heap r in
  let fp = ConcreteMajor.spot_major_fp r in
  let c = ConcreteMajor.spot_c r in
  let free = ConcreteMajor.spot_free_obj r in
  let roots = ThreeObjects.spot_roots c in
  let result = Cheney.cheney_collect_spec minor major fp roots in
  spot_post_minor_c_header_context r;
  spot_post_minor_c_points_to_free r;
  assert (Seq.mem c (SpecFields.objects zero_addr result.mc_major));
  assert (~(SpecObj.is_blue c result.mc_major));
  assert (SpecFields.points_to result.mc_major c free);
  assert (~(SpecObj.is_blue free result.mc_major))

let empty_stack_roots_subset (roots: seq U64.t)
  : Lemma
      (ensures (forall (x: obj_addr). Seq.mem x (Seq.empty #obj_addr) ==>
        Seq.mem (x <: U64.t) roots))
  =
  let aux (x: obj_addr)
    : Lemma (ensures Seq.mem x (Seq.empty #obj_addr) ==> Seq.mem (x <: U64.t) roots)
    =
    if Seq.mem x (Seq.empty #obj_addr) then begin
      let i = Seq.index_mem x (Seq.empty #obj_addr) in
      assert_norm (Seq.length (Seq.empty #obj_addr) == 0);
      assert (i < Seq.length (Seq.empty #obj_addr));
      assert False
    end
  in
  FStar.Classical.forall_intro aux

let spot_post_minor_roots_match_prepared_empty_stack
  (r: unit{ConcreteMajor.spot_major_room}) (cap: nat{cap >= 2})
  : Lemma
      (requires (
        let result = Cheney.cheney_collect_spec
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) in
        SpecMark.gray_objects_on_stack result.mc_major (Seq.empty #obj_addr) /\
        SpecMark.no_black_objects result.mc_major /\
        SpecMark.no_pointer_to_blue result.mc_major))
      (ensures (
        let result = Cheney.cheney_collect_spec
          ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_major_heap r)
          (ConcreteMajor.spot_major_fp r)
          (ThreeObjects.spot_roots (ConcreteMajor.spot_c r)) in
        GenImpl.roots_match_stack result.mc_roots
          (snd (MarkBoundedImpl.darken_roots_bounded_spec
            result.mc_major (Seq.empty #obj_addr) result.mc_roots cap))))
  =
  let minor = ConcreteMinor.spot_minor2 in
  let major = ConcreteMajor.spot_major_heap r in
  let fp = ConcreteMajor.spot_major_fp r in
  let c = ConcreteMajor.spot_c r in
  let free = ConcreteMajor.spot_free_obj r in
  let roots = ThreeObjects.spot_roots c in
  let result = Cheney.cheney_collect_spec minor major fp roots in
  let roots2 = result.mc_roots in
  let st0 = Seq.empty #obj_addr in
  spot_post_minor_roots_shape r;
  spot_post_minor_roots_point_to_objects r;
  spot_post_minor_c_header_context r;
  spot_post_minor_c_points_to_free r;
  spot_post_minor_free_not_blue r;
  spot_collection_heap_shape r;
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.major_heap_shape_elim major fp;
  ConcreteForwarding.spot_concrete_a_forwarding_free_obj r;
  assert (Seq.length roots2 == 2);
  let p0 = MarkBoundedImpl.darken_roots_bounded_prefix_spec
    result.mc_major st0 roots2 0 cap in
  MarkBoundedRootLemmas.darken_roots_bounded_prefix_base
    result.mc_major st0 roots2 cap;
  assert (p0 == (result.mc_major, st0));
  let g0 = fst p0 in
  let s0 = snd p0 in
  let r0 = Seq.index roots2 0 in
  assert (g0 == result.mc_major);
  assert (s0 == st0);
  assert (r0 == (c <: U64.t));
  assert (Seq.mem r0 roots2);
  assert (GC.Spec.Base.is_val_addr r0);
  ConcreteMajor.spot_major_layout_facts r;
  assert (U64.v c == U64.v zero_addr + U64.v mword);
  assert (U64.v c >= U64.v zero_addr + U64.v mword);
  assert (U64.v c < heap_size);
  assert (U64.v c % U64.v mword == 0);
  assert (MarkBoundedImpl.root_points_to_object result.mc_major r0);
  assert (~(SpecObj.is_black c result.mc_major));
  assert (~(SpecObj.is_blue c result.mc_major));
  MarkBoundedRootLemmas.check_and_darken_bounded_spec_pushes_valid_nonblack_nonblue_root
    result.mc_major st0 c cap;
  let p1 = MarkBoundedImpl.darken_roots_bounded_prefix_spec
    result.mc_major st0 roots2 1 cap in
  MarkBoundedImpl.darken_roots_bounded_prefix_step
    result.mc_major st0 roots2 0 cap;
  assert (p1 == MarkBoundedImpl.check_and_darken_bounded_spec
    result.mc_major st0 c cap);
  let g1 = fst p1 in
  let s1 = snd p1 in
  assert (Seq.mem c s1);
  MarkBoundedRootLemmas.check_and_darken_bounded_spec_preserves_gray_objects_on_stack
    result.mc_major st0 c cap;
  assert (SpecMark.gray_objects_on_stack g1 s1);
  MarkBoundedImpl.check_and_darken_bounded_spec_preserves_objects
    result.mc_major st0 c cap;
  MarkBoundedRootLemmas.check_and_darken_bounded_spec_length_increases_at_most_one
    result.mc_major st0 c cap;
  assert (Seq.length s1 <= 1);
  assert (Seq.length s1 < cap);
  let r1 = Seq.index roots2 1 in
  assert (r1 == (free <: U64.t));
  assert (Seq.mem r1 roots2);
  assert (GC.Spec.Base.is_val_addr r1);
  assert (U64.v free == U64.v zero_addr + 32);
  assert (U64.v free >= U64.v zero_addr + U64.v mword);
  assert (U64.v free < heap_size);
  assert (U64.v free % U64.v mword == 0);
  assert (MarkBoundedImpl.root_points_to_object result.mc_major r1);
  assert (MarkBoundedImpl.root_points_to_object g1 r1);
  ConcreteMajor.spot_major_free_mem r;
  CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
  assert (Seq.mem free (SpecFields.objects zero_addr result.mc_major));
  assert (~(SpecObj.is_black free result.mc_major));
  assert (~(SpecObj.is_blue free result.mc_major));
  MarkBoundedRootLemmas.check_and_darken_bounded_spec_preserves_not_black
    result.mc_major st0 c cap free;
  MarkBoundedRootLemmas.check_and_darken_bounded_spec_preserves_not_blue
    result.mc_major st0 c cap free;
  assert (~(SpecObj.is_black free g1));
  assert (~(SpecObj.is_blue free g1));
  MarkBoundedRootLemmas.check_and_darken_bounded_spec_pushes_valid_nonblack_nonblue_root
    g1 s1 free cap;
  let p2 = MarkBoundedImpl.darken_roots_bounded_prefix_spec
    result.mc_major st0 roots2 2 cap in
  MarkBoundedImpl.darken_roots_bounded_prefix_step
    result.mc_major st0 roots2 1 cap;
  assert (p2 == MarkBoundedImpl.check_and_darken_bounded_spec g1 s1 free cap);
  let g2 = fst p2 in
  let s2 = snd p2 in
  assert (Seq.mem free s2);
  MarkBoundedRootLemmas.check_and_darken_bounded_spec_preserves_stack_mem
    g1 s1 free cap c;
  assert (Seq.mem c s2);
  empty_stack_roots_subset roots2;
  FStar.Seq.Properties.seq_mem_k roots2 0;
  FStar.Seq.Properties.seq_mem_k roots2 1;
  MarkBoundedRootLemmas.check_and_darken_bounded_spec_preserves_stack_roots
    result.mc_major st0 roots2 c cap;
  assert (forall (x: obj_addr). Seq.mem x s1 ==> Seq.mem (x <: U64.t) roots2);
  MarkBoundedRootLemmas.check_and_darken_bounded_spec_preserves_stack_roots
    g1 s1 roots2 free cap;
  assert (forall (x: obj_addr). Seq.mem x s2 ==> Seq.mem (x <: U64.t) roots2);
  assert (MarkBoundedImpl.darken_roots_bounded_spec
    result.mc_major st0 roots2 cap == p2);
  let prepared_st = snd (MarkBoundedImpl.darken_roots_bounded_spec
    result.mc_major st0 roots2 cap) in
  assert (prepared_st == s2);
  let roots_val (rv: U64.t)
    : Lemma (ensures Seq.mem rv roots2 ==> GC.Spec.Base.is_val_addr rv)
    =
    if Seq.mem rv roots2 then begin
      spot_post_minor_roots_mem_cases r rv;
      if rv == (c <: U64.t) then
        assert (GC.Spec.Base.is_val_addr rv)
      else begin
        assert (rv == (free <: U64.t));
        assert (GC.Spec.Base.is_val_addr rv)
      end
    end
  in
  let roots_in_stack (x: obj_addr)
    : Lemma (ensures Seq.mem (x <: U64.t) roots2 ==> Seq.mem x prepared_st)
    =
    if Seq.mem (x <: U64.t) roots2 then begin
      spot_post_minor_roots_mem_cases r (x <: U64.t);
      if (x <: U64.t) == (c <: U64.t) then begin
        U64.v_inj x c;
        assert (x == c);
        assert (Seq.mem x prepared_st)
      end else begin
        assert ((x <: U64.t) == (free <: U64.t));
        U64.v_inj x free;
        assert (x == free);
        assert (Seq.mem x prepared_st)
      end
    end
  in
  FStar.Classical.forall_intro roots_val;
  FStar.Classical.forall_intro roots_in_stack;
  assert (GenImpl.roots_match_stack roots2 prepared_st)

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
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
  let minor = ConcreteMinor.spot_minor2 in
  let major = ConcreteMajor.spot_major_heap r in
  let fp = ConcreteMajor.spot_major_fp r in
  let c = ConcreteMajor.spot_c r in
  let roots = ThreeObjects.spot_roots c in
  let result = Cheney.cheney_collect_spec minor major fp roots in
  let prepared = GenImpl.gen_gc_prepared_state minor major fp roots Seq.empty cap in
  let prepared_major = fst prepared in
  let prepared_st = snd prepared in
  spot_collection_heap_shape r;
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.major_heap_shape_elim major fp;
  GenInv.minor_heap_shape_elim minor;
  ConcreteForwarding.spot_concrete_no_oom r;
  CheneyPres.cheney_collect_preserves_collection_heap_shape minor major fp roots;
  GenInv.collection_heap_shape_elim result.mc_minor result.mc_major result.mc_fp;
  GenInv.major_heap_shape_elim result.mc_major result.mc_fp;
  CheneyPres.cheney_collect_preserves_wfh_from_shape minor major fp roots;
  CheneyPres.cheney_collect_preserves_no_black minor major fp roots;
  CheneyPres.cheney_collect_preserves_no_pointer_to_blue minor major fp roots;
  CheneyPres.cheney_collect_preserves_no_scan_invariant minor major fp roots;
  SpecMarkBounded.empty_bounded_stack_props major;
  SpecMarkBounded.empty_bounded_stack_props result.mc_major;
  CheneyPres.cheney_collect_preserves_bounded_stack_props minor major fp roots Seq.empty;
  spot_post_minor_roots_shape r;
  assert (Seq.length result.mc_roots == 2);
  assert (Seq.length (Seq.empty #obj_addr) + Seq.length result.mc_roots <= cap);
  spot_major_gray_black_empty r;
  CheneyPres.cheney_collect_preserves_gray_black_objects_on_stack
    minor major fp roots (Seq.empty #obj_addr);
  cheney_gray_black_stack_to_gray_stack result.mc_major (Seq.empty #obj_addr);
  MarkBoundedImpl.darken_roots_bounded_prefix_length_le_cap
    result.mc_major Seq.empty result.mc_roots (Seq.length result.mc_roots) cap;
  assert (Seq.length prepared_st <= cap);
  assert (SpecMarkBounded.bounded_stack_props result.mc_major Seq.empty);
  assert (SpecMarkBounded.bounded_stack_props result.mc_major Seq.empty);
  assert (SpecMark.no_black_objects result.mc_major);
  assert (SpecMark.no_pointer_to_blue result.mc_major);
  assert (SpecFields.no_scan_invariant result.mc_major);
  assert (SpecFields.well_formed_heap result.mc_major);
  assert (Promote.heap_objects_dense result.mc_major);
  GC.Spec.SweepInv.heap_objects_dense_intro result.mc_major;
  assert (GC.Spec.SweepInv.heap_objects_dense result.mc_major);
  assert (Seq.length (SpecFields.objects zero_addr result.mc_major) > 0);
  assert (GC.Spec.SweepInv.fp_valid result.mc_fp result.mc_major);
  assert (GC.Spec.Sweep.fp_in_heap result.mc_fp result.mc_major);
  assert (Seq.length (Seq.empty #obj_addr) <= cap);
  SpecMarkBoundedInv.bounded_mark_inv_intro result.mc_major Seq.empty cap;
  assert (SpecMarkBoundedInv.bounded_mark_inv result.mc_major Seq.empty cap);
  spot_post_minor_roots_point_to_objects r;
  assert (prepared == MarkBoundedImpl.darken_roots_bounded_spec result.mc_major Seq.empty result.mc_roots cap);
  assert (prepared_major == fst (MarkBoundedImpl.darken_roots_bounded_spec result.mc_major Seq.empty result.mc_roots cap));
  assert (prepared_st == snd (MarkBoundedImpl.darken_roots_bounded_spec result.mc_major Seq.empty result.mc_roots cap));
  spot_post_minor_roots_match_prepared_empty_stack r cap;
  MarkBoundedImpl.darken_roots_bounded_spec_preserves_bounded_mark_inv
    result.mc_major Seq.empty result.mc_roots cap;
  MarkBoundedImpl.darken_roots_bounded_spec_preserves_no_black
    result.mc_major Seq.empty result.mc_roots cap;
  MarkBoundedImpl.darken_roots_bounded_spec_preserves_no_pointer_to_blue
    result.mc_major Seq.empty result.mc_roots cap;
  MarkBoundedImpl.darken_roots_bounded_spec_preserves_no_scan_invariant
    result.mc_major Seq.empty result.mc_roots cap;
  MarkBoundedImpl.darken_roots_bounded_spec_preserves_objects
    result.mc_major Seq.empty result.mc_roots cap;
  MarkBoundedRootLemmas.darken_roots_bounded_spec_preserves_gray_objects_on_stack
    result.mc_major Seq.empty result.mc_roots cap;
  assert (SpecFields.objects zero_addr prepared_major ==
          SpecFields.objects zero_addr result.mc_major);
  assert (SpecMarkBoundedInv.bounded_mark_inv prepared_major prepared_st cap);
  GC.Spec.SweepInv.fp_valid_transfer result.mc_fp result.mc_major prepared_major;
  assert (GC.Spec.SweepInv.fp_valid result.mc_fp prepared_major);
  fp_in_heap_transfer result.mc_fp result.mc_major prepared_major;
  SpecMarkBoundedInv.bounded_mark_inv_elim_bsp prepared_major prepared_st cap;
  bounded_stack_props_root_props prepared_major prepared_st;
  assert (SpecMark.root_props prepared_major prepared_st);
  assert (GC.Spec.Sweep.fp_in_heap result.mc_fp prepared_major);
  assert (SpecMark.no_black_objects prepared_major);
  assert (SpecMark.no_pointer_to_blue prepared_major);
  assert (SpecFields.no_scan_invariant prepared_major);
  gray_objects_no_black_to_gray_black_stack prepared_major prepared_st;
  assert (forall (x: obj_addr). Seq.mem x (SpecFields.objects zero_addr prepared_major) /\
    (SpecObj.is_gray x prepared_major \/ SpecObj.is_black x prepared_major) ==> Seq.mem x prepared_st);
  bounded_mark_inv_graph_facts prepared_major prepared_st cap;
  assert (GenImpl.roots_match_stack result.mc_roots prepared_st);
  assert (GenImpl.gen_gc_major_precondition minor major fp roots Seq.empty cap)
#pop-options

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
