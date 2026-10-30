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
module FL = GC.Spec.FreeList
module Mark = GC.Spec.Mark
module MarkBoundedInv = GC.Spec.MarkBoundedInv
module SweepInv = GC.Spec.SweepInv
module HeapModel = GC.Spec.HeapModel
module HeapGraph = GC.Spec.HeapGraph
module Graph = GC.Spec.Graph
module FreeListShape = GC.Gen.FreeListShape
module FLA = GC.Spec.FreeList.Ascending

let free_list_exact (major: heap) (fp: U64.t) : prop = FL.fl_exact major fp

let free_list_exact_iff (major: heap) (fp: U64.t) = ()

[@@"opaque_to_smt"]
let major_heap_shape (major: heap) (fp: U64.t) : prop =
  well_formed_heap major /\
  AllocLemmas.fl_valid major fp heap_words /\
  AllocLemmas.fl_chain_terminates major fp heap_words /\
  // The free list is exactly the blue blocks that can hold a link -- so an
  // allocation fails only when no free block is big enough
  // (GC.Gen.AllocExact.alloc_succeeds_when_a_block_fits).
  free_list_exact major fp /\
  // ... and in address order: the next fused sweep edits it in place
  // (GC.Spec.FreeList.Ascending, GC.Spec.FusedSweep).
  FLA.fl_ascending major fp /\
  FreeListShape.fp_pointer_or_zero fp /\
  FreeListShape.blue_link_fields_valid major /\
  heap_objects_dense major /\
  chain_objects_blue major fp /\
  Seq.length (objects zero_addr major) > 0 /\
  SweepInv.fp_valid fp major /\
  GC.Spec.FreeList.fp_in_heap fp major /\
  Mark.no_black_objects major /\
  SweepInv.no_gray_objects major /\
  Mark.no_pointer_to_blue major

[@@"opaque_to_smt"]
let minor_major_fields_no_blue (minor: minor_state) (major: heap) : prop =
  forall (obj: U64.t) (j: nat).
    Seq.mem obj (minor_objects minor) /\
    j < minor_scan_wosize minor obj /\
    is_pointer_field (minor_read_field minor obj j) ==>
    Seq.mem ((minor_read_field minor obj j) <: obj_addr)
            (objects zero_addr major) /\
    ~(is_blue ((minor_read_field minor obj j) <: obj_addr) major)

[@@"opaque_to_smt"]
let minor_heap_shape (minor: minor_state) : prop =
  minor_wf minor /\
  minor_guards_complete minor /\
  minor_infix_wf minor
[@@"opaque_to_smt"]
let collection_heap_shape (minor: minor_state) (major: heap) (fp: U64.t) : prop =
  major_heap_shape major fp /\
  minor_heap_shape minor /\
  minor_major_fields_no_blue minor major
let major_heap_shape_intro (major: heap) (fp: U64.t)
  = reveal_opaque (`%major_heap_shape) (major_heap_shape major fp)

let major_heap_shape_elim (major: heap) (fp: U64.t)
  = reveal_opaque (`%major_heap_shape) (major_heap_shape major fp)

let major_heap_shape_walk (major: heap) (fp: U64.t)
  = reveal_opaque (`%major_heap_shape) (major_heap_shape major fp);
    wf_parts ()

let minor_heap_shape_elim (minor: minor_state)
  = reveal_opaque (`%minor_heap_shape) (minor_heap_shape minor)

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

let minor_reset_heap_shape (minor: minor_state)
  =
  let reset = minor_reset minor in
  minor_reset_guards_complete minor;
  minor_reset_infix_wf minor;
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

let collection_heap_shape_after_minor_reset
  (minor: minor_state) (major: heap) (fp: U64.t)
  =
  let reset = minor_reset minor in
  minor_reset_heap_shape minor;
  minor_reset_minor_major_fields_no_blue minor major;
  reveal_opaque (`%collection_heap_shape)
    (collection_heap_shape reset major fp)
#pop-options

/// ---------------------------------------------------------------------------
/// Helper Lemmas for SPOT (Empty Minor Heap)
/// ---------------------------------------------------------------------------

/// ---------------------------------------------------------------------------
/// The collection's shape over a live set
/// ---------------------------------------------------------------------------

module IdleLive = GC.Spec.IdleLive

[@@"opaque_to_smt"]
let major_shape_over (major: heap) (fp: U64.t) (live: obj_addr -> prop) : prop =
  live_ok major live /\
  well_formed_heap_over major live /\
  AllocLemmas.fl_valid major fp heap_words /\
  AllocLemmas.fl_chain_terminates major fp heap_words /\
  free_list_exact major fp /\
  FLA.fl_ascending major fp /\
  FreeListShape.fp_pointer_or_zero fp /\
  FreeListShape.blue_link_fields_valid major /\
  heap_objects_dense major /\
  chain_objects_blue major fp /\
  Seq.length (objects zero_addr major) > 0 /\
  SweepInv.fp_valid fp major /\
  GC.Spec.FreeList.fp_in_heap fp major

let major_shape_over_intro major fp live =
  reveal_opaque (`%major_shape_over) (major_shape_over major fp live)

let major_shape_over_elim major fp live =
  reveal_opaque (`%major_shape_over) (major_shape_over major fp live);
  wf_over_parts ()

let major_shape_over_congr major fp live live' =
  reveal_opaque (`%major_shape_over) (major_shape_over major fp live);
  reveal_opaque (`%major_shape_over) (major_shape_over major fp live');
  wf_over_parts ();
  well_formed_heap_part2_over_congr major live live';
  well_formed_heap_part3_over_weaken major live live'

#push-options "--fuel 0 --ifuel 0"
[@@"opaque_to_smt"]
let minor_major_fields_live (minor: minor_state) (live: obj_addr -> prop) : prop =
  forall (obj: U64.t) (j: nat).
    Seq.mem obj (minor_objects minor) /\
    j < minor_scan_wosize minor obj /\
    is_pointer_field (minor_read_field minor obj j) ==>
    live ((minor_read_field minor obj j) <: obj_addr)
#pop-options

let minor_major_fields_live_intro minor live pf =
  reveal_opaque (`%minor_major_fields_live) (minor_major_fields_live minor live);
  let aux (obj: U64.t) (j: nat) : Lemma
    (Seq.mem obj (minor_objects minor) /\
     j < minor_scan_wosize minor obj /\
     is_pointer_field (minor_read_field minor obj j) ==>
     live ((minor_read_field minor obj j) <: obj_addr))
    = if Seq.mem obj (minor_objects minor) &&
         j < minor_scan_wosize minor obj &&
         is_pointer_field (minor_read_field minor obj j)
      then pf obj j
  in
  FStar.Classical.forall_intro_2 aux

let minor_major_fields_live_elim minor live obj j =
  reveal_opaque (`%minor_major_fields_live) (minor_major_fields_live minor live)

let minor_major_fields_live_idle minor major =
  reveal_opaque (`%minor_major_fields_live) (minor_major_fields_live minor (idle_live major));
  reveal_opaque (`%minor_major_fields_no_blue) (minor_major_fields_no_blue minor major)

[@@"opaque_to_smt"]
let collection_shape_over (minor: minor_state) (major: heap) (fp: U64.t)
  (live: obj_addr -> prop) : prop =
  major_shape_over major fp live /\
  minor_heap_shape minor /\
  minor_major_fields_live minor live

let collection_shape_over_intro minor major fp live =
  reveal_opaque (`%collection_shape_over) (collection_shape_over minor major fp live)

let collection_shape_over_elim minor major fp live =
  reveal_opaque (`%collection_shape_over) (collection_shape_over minor major fp live)

let collection_shape_over_congr minor major fp live live' =
  reveal_opaque (`%collection_shape_over) (collection_shape_over minor major fp live);
  reveal_opaque (`%collection_shape_over) (collection_shape_over minor major fp live');
  major_shape_over_congr major fp live live';
  reveal_opaque (`%minor_major_fields_live) (minor_major_fields_live minor live);
  reveal_opaque (`%minor_major_fields_live) (minor_major_fields_live minor live')

let major_heap_shape_over_idle major fp =
  major_heap_shape_elim major fp;
  idle_live_ok major;
  IdleLive.wf_over_idle_intro major;
  major_shape_over_intro major fp (idle_live major)

let major_heap_shape_of_over_idle major fp =
  major_shape_over_elim major fp (idle_live major);
  IdleLive.wf_over_idle_elim major;
  major_heap_shape_intro major fp

let collection_heap_shape_over_idle minor major fp =
  collection_heap_shape_elim minor major fp;
  major_heap_shape_over_idle major fp;
  minor_major_fields_live_idle minor major;
  collection_shape_over_intro minor major fp (idle_live major)

let collection_heap_shape_of_over_idle minor major fp =
  collection_shape_over_elim minor major fp (idle_live major);
  major_heap_shape_of_over_idle major fp;
  minor_major_fields_live_idle minor major;
  collection_heap_shape_intro minor major fp

let collection_shape_over_after_minor_reset minor major fp live =
  let reset = minor_reset minor in
  minor_reset_heap_shape minor;
  minor_reset_objects_empty minor;
  let pf (obj: U64.t) (j: nat) : Lemma
    (requires Seq.mem obj (minor_objects reset) /\
              j < minor_scan_wosize reset obj /\
              is_pointer_field (minor_read_field reset obj j))
    (ensures live ((minor_read_field reset obj j) <: obj_addr))
    = minor_reset_objects_not_mem minor obj
  in
  minor_major_fields_live_intro reset live pf;
  collection_shape_over_intro reset major fp live
