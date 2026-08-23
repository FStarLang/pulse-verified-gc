/// ---------------------------------------------------------------------------
/// GC.Gen.HeapInvariant -- Central generational heap-shape invariant
/// ---------------------------------------------------------------------------

module GC.Gen.HeapInvariant

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote

module AllocLemmas = GC.Spec.Allocator.Lemmas
module Mark = GC.Spec.Mark
module MarkBoundedInv = GC.Spec.MarkBoundedInv
module Sweep = GC.Spec.Sweep
module SweepInv = GC.Spec.SweepInv
module HeapModel = GC.Spec.HeapModel
module HeapGraph = GC.Spec.HeapGraph
module Graph = GC.Spec.Graph
module FreeListShape = GC.Gen.FreeListShape

[@@"opaque_to_smt"]
let major_heap_shape (major: heap) (fp: U64.t) : prop =
  well_formed_heap major /\
  AllocLemmas.fl_valid major fp heap_words /\
  AllocLemmas.fl_chain_terminates major fp heap_words /\
  FreeListShape.fp_pointer_or_zero fp /\
  FreeListShape.blue_link_fields_valid major /\
  heap_objects_dense major /\
  chain_objects_blue major fp /\
  Seq.length (objects zero_addr major) > 0 /\
  SweepInv.fp_valid fp major /\
  Sweep.fp_in_heap fp major /\
  Mark.no_black_objects major /\
  Mark.no_pointer_to_blue major /\
  no_scan_invariant major

[@@"opaque_to_smt"]
let minor_major_fields_no_blue (minor: minor_state) (major: heap) : prop =
  forall (obj: U64.t) (j: nat).
    Seq.mem obj (minor_objects minor) /\
    j < minor_wosize minor obj /\
    is_pointer_field (minor_read_field minor obj j) ==>
    Seq.mem ((minor_read_field minor obj j) <: obj_addr)
            (objects zero_addr major) /\
    ~(is_blue ((minor_read_field minor obj j) <: obj_addr) major)

[@@"opaque_to_smt"]
let minor_fields_no_infix_targets (minor: minor_state) : prop =
  forall (obj: U64.t) (j: nat).
    Seq.mem obj (minor_objects minor) /\
    j < minor_wosize minor obj /\
    is_minor_pointer (to_minor_offset (minor_read_field minor obj j)) ==>
    ~(is_infix_in_minor minor (to_minor_offset (minor_read_field minor obj j)))

[@@"opaque_to_smt"]
let major_minor_fields_no_infix_targets (minor: minor_state) (major: heap) : prop =
  forall (obj: obj_addr) (j: nat).
    Seq.mem obj (objects zero_addr major) /\
    ~(is_blue obj major) /\
    ~(is_no_scan obj major) /\
    j < U64.v (wosize_of_object obj major) /\
    U64.v obj + j * 8 + 8 <= heap_size /\
    (U64.v obj + j * 8) % 8 == 0 ==>
    (let v = to_minor_offset
       (read_word major (U64.uint_to_t (U64.v obj + j * 8))) in
     is_minor_pointer v ==> ~(is_infix_in_minor minor v))

[@@"opaque_to_smt"]
let minor_heap_shape (minor: minor_state) : prop =
  minor_wf minor /\
  minor_guards_complete minor /\
  minor_infix_wf minor /\
  minor_no_scan_invariant minor /\
  minor_fields_no_infix_targets minor
[@@"opaque_to_smt"]
let collection_heap_shape (minor: minor_state) (major: heap) (fp: U64.t) : prop =
  major_heap_shape major fp /\
  minor_heap_shape minor /\
  minor_major_fields_no_blue minor major /\
  major_minor_fields_no_infix_targets minor major
let major_heap_shape_intro (major: heap) (fp: U64.t)
  = reveal_opaque (`%major_heap_shape) (major_heap_shape major fp)

let major_heap_shape_elim (major: heap) (fp: U64.t)
  = reveal_opaque (`%major_heap_shape) (major_heap_shape major fp)

let minor_heap_shape_elim (minor: minor_state)
  = reveal_opaque (`%minor_heap_shape) (minor_heap_shape minor)

let minor_fields_no_infix_targets_intro (minor: minor_state)
  = reveal_opaque (`%minor_fields_no_infix_targets)
      (minor_fields_no_infix_targets minor)

let minor_heap_shape_intro (minor: minor_state)
  = reveal_opaque (`%minor_heap_shape) (minor_heap_shape minor)

let minor_major_fields_no_blue_no_pointer_fields
  (minor: minor_state) (major: heap)
  =
  reveal_opaque (`%minor_major_fields_no_blue)
    (minor_major_fields_no_blue minor major)

let minor_major_fields_no_blue_elim (minor: minor_state) (major: heap)
  (obj: U64.t) (j: nat)
  = reveal_opaque (`%minor_major_fields_no_blue)
      (minor_major_fields_no_blue minor major)

let minor_fields_no_infix_targets_elim (minor: minor_state)
  (obj: U64.t) (j: nat)
  = reveal_opaque (`%minor_fields_no_infix_targets)
      (minor_fields_no_infix_targets minor)

let major_minor_fields_no_infix_targets_elim
  (minor: minor_state) (major: heap) (obj: obj_addr) (j: nat)
  = reveal_opaque (`%major_minor_fields_no_infix_targets)
      (major_minor_fields_no_infix_targets minor major)

let major_minor_fields_no_infix_targets_intro
  (minor: minor_state) (major: heap)
  = reveal_opaque (`%major_minor_fields_no_infix_targets)
      (major_minor_fields_no_infix_targets minor major)

let collection_heap_shape_elim (minor: minor_state) (major: heap) (fp: U64.t)
  = reveal_opaque (`%collection_heap_shape)
      (collection_heap_shape minor major fp)

let collection_heap_shape_intro (minor: minor_state) (major: heap) (fp: U64.t)
  = reveal_opaque (`%collection_heap_shape)
      (collection_heap_shape minor major fp)

/// ---------------------------------------------------------------------------
/// Minor reset shape
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
private let minor_reset_guards_complete (minor: minor_state)
  : Lemma (ensures minor_guards_complete (minor_reset minor))
  =
  let reset = minor_reset minor in
  let aux (addr: U64.t)
    : Lemma (requires U64.v addr >= 8 /\ U64.v addr < minor_heap_size /\
                      U64.v addr % 8 == 0 /\
                      minor_wosize reset addr > 0 /\
                      U64.v addr + minor_wosize reset addr * 8 <= minor_heap_size /\
                      minor_tag reset addr <> 249)
            (ensures Seq.mem addr (minor_objects reset))
    =
    minor_reset_wosize_zero minor addr;
    assert False
  in
  reveal_opaque (`%minor_guards_complete) (minor_guards_complete reset);
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

private let minor_reset_infix_wf (minor: minor_state)
  : Lemma (ensures minor_infix_wf (minor_reset minor))
  =
  let reset = minor_reset minor in
  let aux (addr: U64.t)
    : Lemma (requires is_infix_in_minor reset addr)
            (ensures (let wz = minor_wosize reset addr in
                      let parent = infix_parent reset addr in
                      wz > 0 /\
                      wz * 8 <= U64.v addr - 8 /\
                      U64.v parent >= 8 /\
                      U64.v parent % 8 == 0 /\
                      Seq.mem parent (minor_objects reset) /\
                      U64.v addr - U64.v parent < minor_wosize reset parent * 8))
    =
    minor_reset_no_infix minor addr;
    assert False
  in
  reveal_opaque (`%minor_infix_wf) (minor_infix_wf reset);
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

private let minor_reset_no_scan_invariant (minor: minor_state)
  : Lemma (ensures minor_no_scan_invariant (minor_reset minor))
  =
  let reset = minor_reset minor in
  minor_reset_objects_empty minor;
  assert (minor_objects reset == Seq.empty);
  let aux (obj: U64.t) (j: nat)
    : Lemma (ensures (Seq.mem obj (minor_objects reset) /\
                      minor_tag reset obj >= 251 /\
                      j < minor_wosize reset obj ==>
                      ~(is_pointer_field (minor_read_field reset obj j)) /\
                      ~(is_minor_pointer (to_minor_offset (minor_read_field reset obj j)))))
    =
    minor_reset_objects_not_mem minor obj
  in
  FStar.Classical.forall_intro_2 aux

private let minor_reset_fields_no_infix_targets (minor: minor_state)
  : Lemma (ensures minor_fields_no_infix_targets (minor_reset minor))
  =
  let reset = minor_reset minor in
  minor_reset_objects_empty minor;
  assert (minor_objects reset == Seq.empty);
  let aux (obj: U64.t) (j: nat)
    : Lemma (ensures (Seq.mem obj (minor_objects reset) /\
                      j < minor_wosize reset obj /\
                      is_minor_pointer (to_minor_offset (minor_read_field reset obj j)) ==>
                      ~(is_infix_in_minor reset
                        (to_minor_offset (minor_read_field reset obj j)))))
    =
    minor_reset_objects_not_mem minor obj
  in
  reveal_opaque (`%minor_fields_no_infix_targets)
    (minor_fields_no_infix_targets reset);
  FStar.Classical.forall_intro_2 aux

let minor_reset_heap_shape (minor: minor_state)
  =
  let reset = minor_reset minor in
  minor_reset_guards_complete minor;
  minor_reset_infix_wf minor;
  minor_reset_no_scan_invariant minor;
  minor_reset_fields_no_infix_targets minor;
  reveal_opaque (`%minor_heap_shape) (minor_heap_shape reset)

let minor_reset_minor_major_fields_no_blue (minor: minor_state) (major: heap)
  =
  let reset = minor_reset minor in
  minor_reset_objects_empty minor;
  assert (minor_objects reset == Seq.empty);
  let aux (obj: U64.t) (j: nat)
    : Lemma (ensures (Seq.mem obj (minor_objects reset) /\
                      j < minor_wosize reset obj /\
                      is_pointer_field (minor_read_field reset obj j) ==>
                      Seq.mem ((minor_read_field reset obj j) <: obj_addr)
                              (objects zero_addr major) /\
                      ~(is_blue ((minor_read_field reset obj j) <: obj_addr) major)))
    =
    minor_reset_objects_not_mem minor obj
  in
  reveal_opaque (`%minor_major_fields_no_blue)
    (minor_major_fields_no_blue reset major);
  FStar.Classical.forall_intro_2 aux

let minor_reset_major_minor_fields_no_infix_targets
  (minor: minor_state) (major: heap)
  =
  let reset = minor_reset minor in
  let aux (obj: obj_addr) (j: nat)
    : Lemma (ensures (Seq.mem obj (objects zero_addr major) /\
                      ~(is_blue obj major) /\
                      ~(is_no_scan obj major) /\
                      j < U64.v (wosize_of_object obj major) /\
                      U64.v obj + j * 8 + 8 <= heap_size /\
                      (U64.v obj + j * 8) % 8 == 0 ==>
                      (let v = to_minor_offset
                         (read_word major (U64.uint_to_t (U64.v obj + j * 8))) in
                       is_minor_pointer v ==> ~(is_infix_in_minor reset v))))
    =
    if Seq.mem obj (objects zero_addr major) &&
       not (is_blue obj major) &&
       not (is_no_scan obj major) &&
       j < U64.v (wosize_of_object obj major) &&
       U64.v obj + j * 8 + 8 <= heap_size &&
       (U64.v obj + j * 8) % 8 = 0 then begin
      let field_nat = U64.v obj + j * 8 in
      assert_norm (pow2 57 < pow2 64);
      assert (field_nat < heap_size);
      assert (field_nat < pow2 64);
      let field_addr : hp_addr = U64.uint_to_t field_nat in
      assert (U64.v field_addr == field_nat);
      let v = to_minor_offset (read_word major field_addr) in
      minor_reset_no_infix minor v
    end
  in
  reveal_opaque (`%major_minor_fields_no_infix_targets)
    (major_minor_fields_no_infix_targets reset major);
  FStar.Classical.forall_intro_2 aux

let collection_heap_shape_after_minor_reset
  (minor: minor_state) (major: heap) (fp: U64.t)
  =
  let reset = minor_reset minor in
  minor_reset_heap_shape minor;
  minor_reset_minor_major_fields_no_blue minor major;
  minor_reset_major_minor_fields_no_infix_targets minor major;
  reveal_opaque (`%collection_heap_shape)
    (collection_heap_shape reset major fp)
#pop-options

/// ---------------------------------------------------------------------------
/// Helper Lemmas for SPOT (Empty Minor Heap)
/// ---------------------------------------------------------------------------
