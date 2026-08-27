module GC.SPOT.MinorInfixPre

module U64 = FStar.UInt64
module Seq = FStar.Seq

open FStar.Seq
open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

module SpecHeap = GC.Spec.Heap
module SpecObj = GC.Spec.Object
module SpecFields = GC.Spec.Fields
module GenInv = GC.Gen.HeapInvariant
module Promote = GC.Gen.Promote
module MinorFwd = GC.Gen.MinorCollectForwarding
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module RBridge = GC.Gen.ReachabilityBridge
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module GenImpl = GC.Gen.Impl
module Preconditions = GC.SPOT.Preconditions
module Layout = GC.SPOT.Layout
module Major = GC.SPOT.ConcreteMajorInfix
module Nursery = GC.SPOT.MinorInfixHeap
module MinorInfix = GC.SPOT.MinorInfix

#set-options "--fuel 1 --ifuel 1 --z3rlimit 30"

let spot_mi_roots (r: unit{Major.spot_major_room})
  : (s:seq U64.t{Seq.length s == 2}) =
  Seq.cons (Major.spot_c r <: U64.t)
    (Seq.cons (Layout.b_minor <: U64.t) Seq.empty)

let spot_mi_roots_mem r =
  SpecFields.mem_cons_lemma (Major.spot_c r <: U64.t) (Major.spot_c r <: U64.t)
    (Seq.cons (Layout.b_minor <: U64.t) Seq.empty);
  SpecFields.mem_cons_lemma (Layout.b_minor <: U64.t) (Major.spot_c r <: U64.t)
    (Seq.cons (Layout.b_minor <: U64.t) Seq.empty);
  SpecFields.mem_cons_lemma (Layout.b_minor <: U64.t) (Layout.b_minor <: U64.t)
    (Seq.empty #U64.t)

let spot_mi_slots (r: unit{Major.spot_major_room})
  : (s:seq U64.t{Seq.length s == 1}) =
  Seq.cons (Major.spot_c_field1 r) Seq.empty

let spot_mi_slots_index r = ()

let spot_mi_fwd_array : seq U64.t =
  Seq.create UpdatePtrs.fwd_array_size 0UL

/// Case analysis on the two roots.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
private let spot_mi_roots_cases (r: unit{Major.spot_major_room}) (root: U64.t)
  : Lemma (requires Seq.mem root (spot_mi_roots r))
          (ensures root == (Major.spot_c r <: U64.t) \/
                   root == (Layout.b_minor <: U64.t))
  =
  SpecFields.mem_cons_lemma root (Major.spot_c r <: U64.t)
    (Seq.cons (Layout.b_minor <: U64.t) Seq.empty);
  SpecFields.mem_cons_lemma root (Layout.b_minor <: U64.t) Seq.empty;
  if root = (Major.spot_c r <: U64.t) then ()
  else if root = (Layout.b_minor <: U64.t) then ()
  else begin
    assert_norm (~(Seq.mem root (Seq.empty #U64.t)));
    assert False
  end
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
private let zero_not_minor_pointer ()
  : Lemma (ensures ~(Promote.is_minor_pointer 0UL))
  = assert_norm (Promote.is_minor_pointer 0UL == false)

private let spot_mi_fwd_array_zero ()
  : Lemma (ensures Preconditions.zero_forwarding_array spot_mi_fwd_array)
  =
  FStar.Seq.Base.lemma_create_len UpdatePtrs.fwd_array_size 0UL;
  let aux (i: nat)
    : Lemma (ensures i < Seq.length spot_mi_fwd_array ==>
                     Seq.index spot_mi_fwd_array i == 0UL)
    =
    if i < Seq.length spot_mi_fwd_array then
      FStar.Seq.Base.lemma_index_create UpdatePtrs.fwd_array_size 0UL i
  in
  FStar.Classical.forall_intro aux;
  Preconditions.zero_forwarding_array_intro spot_mi_fwd_array
#pop-options

/// ---------------------------------------------------------------------------
/// It really is an interior pointer
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let spot_mi_field_is_interior r =
  Major.spot_major_layout_facts r;
  Major.spot_major_c_reads r;
  Nursery.spot_infix_nursery_infix ();
  Nursery.spot_infix_nursery_objects ();
  let major = Major.spot_major_heap r in
  let c = Major.spot_c r in
  assert (U64.v c + Layout.c_to_a_field_index * 8 + 8 <= heap_size);
  assert (MinorInfix.field_slot c Layout.c_to_a_field_index == Major.spot_c_field1 r);
  assert (SpecHeap.read_word major (Major.spot_c_field1 r) == (Layout.b_minor <: U64.t));
  to_minor_offset_in_minor_range (Layout.b_minor <: U64.t);
  assert (MinorInfix.stored_target major c Layout.c_to_a_field_index ==
          (Layout.b_minor <: U64.t));
  // an infix address is never itself an enumerated nursery object
  let not_mem ()
    : Lemma (ensures ~(Seq.mem (Layout.b_minor <: U64.t) (minor_objects spot_mi_minor)))
    =
    if Seq.mem (Layout.b_minor <: U64.t) (minor_objects spot_mi_minor) then begin
      Nursery.spot_infix_nursery_object_cases (Layout.b_minor <: U64.t);
      assert False
    end
  in
  not_mem ()
#pop-options

/// ---------------------------------------------------------------------------
/// The entry invariant
/// ---------------------------------------------------------------------------

/// No nursery field holds a major pointer: the closure's three fields are
/// `0`, the infix header (an unaligned immediate) and `0`.
#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
private let spot_mi_minor_major_fields_no_blue (r: unit{Major.spot_major_room})
  : Lemma (GenInv.minor_major_fields_no_blue spot_mi_minor (Major.spot_major_heap r))
  =
  Nursery.spot_infix_nursery_closure ();
  let aux (obj: U64.t) (j: nat)
    : Lemma
        (requires Seq.mem obj (minor_objects spot_mi_minor) /\
                  j < minor_wosize spot_mi_minor obj)
        (ensures ~(SpecFields.is_pointer_field (minor_read_field spot_mi_minor obj j)))
    =
    Nursery.spot_infix_nursery_object_cases obj;
    assert (obj == (Layout.a_minor <: U64.t));
    assert (minor_wosize spot_mi_minor Layout.a_minor == 3);
    Nursery.spot_infix_nursery_fields j
  in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 aux);
  GenInv.minor_major_fields_no_blue_no_pointer_fields
    spot_mi_minor (Major.spot_major_heap r)
#pop-options

let spot_mi_collection_heap_shape r =
  Major.spot_major_heap_shape r;
  Nursery.spot_infix_nursery_heap_shape ();
  spot_mi_minor_major_fields_no_blue r;
  GenInv.collection_heap_shape_intro
    spot_mi_minor (Major.spot_major_heap r) (Major.spot_major_fp r)

/// ---------------------------------------------------------------------------
/// The remembered set
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
private let spot_mi_ref_table_sound (r: unit{Major.spot_major_room})
  : Lemma (UpdatePtrs.ref_table_sound (Major.spot_major_heap r) (spot_mi_slots r) 1)
  =
  let major = Major.spot_major_heap r in
  Major.spot_major_layout_facts r;
  Major.spot_major_objects r;
  Major.spot_major_c_mem r;
  Major.spot_major_c_reads r;
  let aux (i: nat)
    : Lemma (ensures
              i < 1 ==>
              (let addr = U64.v (Seq.index (spot_mi_slots r) i) in
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
      assert (Seq.index (spot_mi_slots r) i == Major.spot_c_field1 r);
      assert (U64.v (Major.spot_c_field1 r) ==
              U64.v (Major.spot_c r) + Layout.c_to_a_field_index * 8);
      assert (Layout.c_to_a_field_index <
              U64.v (SpecObj.wosize_of_object (Major.spot_c r) major));
      assert (exists (obj: obj_addr) (j: nat).
        Seq.mem obj (SpecFields.objects zero_addr major) /\
        SpecObj.is_blue obj major = false /\
        SpecObj.is_no_scan obj major = false /\
        j < U64.v (SpecObj.wosize_of_object obj major) /\
        U64.v (Major.spot_c_field1 r) == U64.v obj + j * 8)
    end
  in
  FStar.Classical.forall_intro aux
#pop-options

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let spot_mi_ref_table_covers (r: unit{Major.spot_major_room})
  : Lemma (UpdatePtrs.ref_table_covers_minor_ptrs
             (Major.spot_major_heap r) (spot_mi_slots r) 1)
  =
  let major = Major.spot_major_heap r in
  Major.spot_major_layout_facts r;
  Major.spot_major_objects r;
  Major.spot_major_c_reads r;
  Major.spot_major_free_reads r;
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
            i < 1 /\ U64.v (Seq.index (spot_mi_slots r) i) == U64.v obj + j * 8))
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
      Major.spot_major_object_cases r obj;
      if obj = Major.spot_c r then begin
        assert (U64.v (SpecObj.wosize_of_object obj major) == Layout.c_wosize);
        assert (j < 2);
        if j = 0 then begin
          assert (U64.uint_to_t (U64.v obj + j * 8) == Major.spot_c_field0 r);
          assert (SpecHeap.read_word major (U64.uint_to_t (U64.v obj + j * 8)) == 0UL);
          to_minor_offset_in_minor_range 0UL;
          zero_not_minor_pointer ();
          assert False
        end else begin
          assert (j == Layout.c_to_a_field_index);
          assert (U64.v (Major.spot_c_field1 r) == U64.v obj + j * 8);
          assert (Seq.index (spot_mi_slots r) 0 == Major.spot_c_field1 r);
          assert (exists (i: nat).
            i < 1 /\ U64.v (Seq.index (spot_mi_slots r) i) == U64.v obj + j * 8)
        end
      end else begin
        assert (obj == Major.spot_free_obj r);
        assert (SpecObj.is_blue obj major);
        assert False
      end
    end
  in
  FStar.Classical.forall_intro_2 aux
#pop-options

/// The remembered slot's target --- the interior pointer `24` --- is a root.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
private let spot_mi_remembered_targets (r: unit{Major.spot_major_room})
  : Lemma (MinorFwd.remembered_targets_in_roots
             (Major.spot_major_heap r) (spot_mi_roots r) (spot_mi_slots r) 1)
  =
  let major = Major.spot_major_heap r in
  Major.spot_major_layout_facts r;
  Major.spot_major_c_reads r;
  let aux (i: nat)
    : Lemma (ensures
              i < 1 ==>
              U64.v (Seq.index (spot_mi_slots r) i) < heap_size /\
              U64.v (Seq.index (spot_mi_slots r) i) % U64.v mword == 0 /\
              (let slot = (Seq.index (spot_mi_slots r) i <: hp_addr) in
               let v = to_minor_offset (SpecHeap.read_word major slot) in
               Promote.is_minor_pointer v ==> Seq.mem v (spot_mi_roots r)))
    =
    if i < 1 then begin
      assert (i == 0);
      assert (Seq.index (spot_mi_slots r) i == Major.spot_c_field1 r);
      assert (SpecHeap.read_word major (Major.spot_c_field1 r) ==
              (Layout.b_minor <: U64.t));
      to_minor_offset_in_minor_range (Layout.b_minor <: U64.t);
      spot_mi_roots_mem r
    end
  in
  FStar.Classical.forall_intro aux;
  MCFH.remembered_targets_in_roots_intro_by_slots
    major (spot_mi_roots r) (spot_mi_slots r) 1
#pop-options

/// ---------------------------------------------------------------------------
/// Roots
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let spot_mi_roots_valid r =
  let major = Major.spot_major_heap r in
  let aux (root: U64.t)
    : Lemma
        (requires Seq.mem root (spot_mi_roots r))
        (ensures
          ((Promote.is_minor_pointer root ==>
            Seq.mem (resolve_minor spot_mi_minor root) (minor_objects spot_mi_minor) /\
            minor_wosize spot_mi_minor (resolve_minor spot_mi_minor root) > 0) /\
           (~(Promote.is_minor_pointer root) ==>
            is_val_addr root /\
            Seq.mem (root <: obj_addr) (SpecFields.objects zero_addr major) /\
            ~(SpecObj.is_blue (root <: obj_addr) major))))
    =
    spot_mi_roots_cases r root;
    if root = (Major.spot_c r <: U64.t) then begin
      Major.spot_major_c_reads r;
      Major.spot_major_c_mem r;
      RBridge.major_object_not_minor_pointer major (Major.spot_c r)
    end else begin
      assert (root == (Layout.b_minor <: U64.t));
      Layout.b_minor_is_minor_pointer ();
      // The Phase H.2 clause: an interior root resolves to its closure.
      Nursery.spot_infix_nursery_infix ();
      Nursery.spot_infix_nursery_closure ();
      assert (resolve_minor spot_mi_minor root == (Layout.a_minor <: U64.t));
      assert (Seq.mem (Layout.a_minor <: U64.t) (minor_objects spot_mi_minor));
      assert (minor_wosize spot_mi_minor Layout.a_minor == 3)
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

let spot_mi_minor_collect_full_pre r =
  spot_mi_collection_heap_shape r;
  spot_mi_fwd_array_zero ();
  spot_mi_ref_table_sound r;
  spot_mi_ref_table_covers r;
  Preconditions.singleton_slots_pairwise_distinct (spot_mi_slots r) 1;
  spot_mi_remembered_targets r;
  spot_mi_roots_valid r;
  Preconditions.minor_collect_full_pre_intro
    spot_mi_minor (Major.spot_major_heap r) (Major.spot_major_fp r)
    (spot_mi_roots r) spot_mi_fwd_array (spot_mi_slots r) 1

let spot_mi_gen_gc_pre r cap =
  spot_mi_minor_collect_full_pre r;
  assert_norm (Seq.length (Seq.empty #obj_addr) == 0);
  Preconditions.gen_gc_pre_intro
    spot_mi_minor (Major.spot_major_heap r) (Major.spot_major_fp r)
    (spot_mi_roots r) spot_mi_fwd_array (spot_mi_slots r) 1
    Seq.empty cap

/// ---------------------------------------------------------------------------
/// Non-vacuity
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let spot_mi_was_forbidden r =
  let major = Major.spot_major_heap r in
  let c = Major.spot_c r in
  Major.spot_major_layout_facts r;
  Major.spot_major_objects r;
  Major.spot_major_c_mem r;
  Major.spot_major_c_reads r;
  spot_mi_field_is_interior r;
  assert (Seq.mem c (SpecFields.objects zero_addr major));
  assert (~(SpecObj.is_blue c major));
  assert (~(SpecObj.is_no_scan c major));
  assert (Layout.c_to_a_field_index < U64.v (SpecObj.wosize_of_object c major));
  assert (U64.v c + Layout.c_to_a_field_index * 8 + 8 <= heap_size);
  assert ((U64.v c + Layout.c_to_a_field_index * 8) % 8 == 0);
  assert (is_infix_in_minor spot_mi_minor
            (to_minor_offset (SpecHeap.read_word major
              (U64.uint_to_t (U64.v c + Layout.c_to_a_field_index * 8)))))
#pop-options
