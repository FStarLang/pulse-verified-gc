module GC.Gen.MarkPhase.Alloc

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module GenInv = GC.Gen.HeapInvariant
module GI = GC.Gen.Incremental
module GMM = GC.Gen.MarkPhase.Minor
module MS = GC.Gen.MarkState
module MPA = GC.Spec.MarkPhase.Alloc
module MP = GC.Spec.MarkPhase
module MM = GC.Spec.MarkPhase.Mutator
module SPM = GC.Spec.SweepPhase.Mutator
module SPI = GC.Spec.SweepPhase.Intrinsic
module AC = GC.Spec.Allocator.Cursor
module AP = GC.Spec.Allocator.Phase
module SA = GC.Spec.Allocator
module FLA = GC.Spec.FreeList.Ascending
module PCS = GC.Gen.PostCollectionShape
module Promote = GC.Gen.Promote
module Mark = GC.Spec.Mark
module W = GC.Spec.Walk

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// The cross-generation condition depends only on the non-free blocks: it
/// survives a change that keeps every one non-free.
let mmf_keep (minor: minor_state) (g g': heap)
  : Lemma (requires GenInv.minor_major_fields_not_free free_stw minor g /\
                    (forall (y: obj_addr). in_use free_stw g y ==> in_use free_stw g' y))
          (ensures GenInv.minor_major_fields_not_free free_stw minor g')
  = GenInv.minor_major_fields_not_free_intro free_stw minor g'
      (fun obj j -> GenInv.minor_major_fields_not_free_elim free_stw minor g obj j)

/// The collector's state at `Marking`, taken apart.
let marking_parts (minor: minor_state) (g: heap) (fp: U64.t)
  : Lemma (requires GI.phase_shape minor g fp Ph.Marking)
          (ensures MP.marking_inv g (GMM.nursery_held minor) /\
                   GenInv.minor_heap_shape minor /\
                   GenInv.minor_major_fields_not_free free_stw minor g /\
                   AP.alloc_ok g fp /\ no_infix_block g /\
                   heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
                   FLA.fl_ascending g fp)
  = GI.phase_shape_marking minor g fp;
    GenInv.collection_shape_with_elim Ph.Marking free_stw minor g fp;
    GenInv.major_shape_with_elim Ph.Marking free_stw g fp

/// ---------------------------------------------------------------------------
/// Allocation
/// ---------------------------------------------------------------------------

let marking_alloc_shape minor g fp wz tag =
  let ph = Ph.Marking in
  let held = GMM.nursery_held minor in
  marking_parts minor g fp;
  MPA.marking_alloc g held fp wz tag;
  let r = AC.alloc_phase g fp ph wz tag in
  if r.SA.obj_out <> 0UL then begin
    let g' = r.SA.heap_out in
    // the walk stays dense
    AP.alloc_at_recoloured ph g fp wz tag;
    GC.Spec.Allocator.Dense.alloc_spec_preserves_dense_part1 g fp wz tag;
    AP.recoloured_facts (SA.alloc_spec g fp wz tag).SA.heap_out g';
    FStar.Seq.Properties.mem_index (r.SA.obj_out <: obj_addr) (objects zero_addr g');
    assert (heap_objects_dense g' /\ Seq.length (objects zero_addr g') > 0);
    // what the nursery points at stays non-free
    free_stw_ok ();
    free_def_ok_elim free_stw;
    let keep (y: obj_addr) : Lemma (requires in_use free_stw g y) (ensures in_use free_stw g' y)
      = MM.header_kept_facts g g' y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires keep);
    mmf_keep minor g g';
    assert (fresh_shape minor g' r.SA.fp_out r.SA.obj_out)
  end

/// ---------------------------------------------------------------------------
/// Initialising
/// ---------------------------------------------------------------------------

/// The walk is a function of the positions: the same positions, the same
/// density.
let dense_transport (g g': heap)
  : Lemma (requires heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\ SPI.same_heads g g')
          (ensures heap_objects_dense g' /\ Seq.length (objects zero_addr g') > 0)
  = SPI.same_heads_facts g g';
    W.reaches_end_of_dense g;
    W.reaches_refl g zero_addr;
    W.dense_of_reaches_end g' (W.walk_end g zero_addr)

let fresh_shape_write minor g fp obj a v =
  let g' = write_word g a v in
  MPA.marking_fresh_write g (GMM.nursery_held minor) obj a v;
  SPI.same_heads_facts g g';
  Mark.colors_exclusive obj g;
  SPM.in_body_block g obj a;
  SPI.colour_of g obj;
  SPI.body_write g fp (hd_address obj) a v;
  dense_transport g g';
  mmf_keep minor g g'

/// ---------------------------------------------------------------------------
/// Closing
/// ---------------------------------------------------------------------------

let fresh_shape_close minor g fp obj =
  MPA.marking_fresh_close g (GMM.nursery_held minor) obj;
  free_stw_ok ();
  Promote.free_stw_allocations_not_free Ph.Marking;
  PCS.free_list_shape_of_ascending g fp;
  GenInv.major_shape_with_intro Ph.Marking free_stw g fp;
  GenInv.collection_shape_with_intro Ph.Marking free_stw minor g fp;
  GI.phase_shape_marking minor g fp

/// ---------------------------------------------------------------------------
/// The mark cache
/// ---------------------------------------------------------------------------

/// A grey object after the allocation was a grey object before: it is not
/// the new block (black), so it was a non-free block, kept with its header.
let alloc_grey (g: heap) (fp: U64.t) (wz: nat) (tag: SPM.tag_t) (obj y: obj_addr)
  : Lemma (requires well_formed_heap g /\ FLA.fl_ascending g fp /\ wz >= 1 /\
                    (AC.alloc_phase g fp Ph.Marking wz tag).SA.obj_out == obj /\
                    is_black obj (AC.alloc_phase g fp Ph.Marking wz tag).SA.heap_out /\
                    MPA.keeps_blocks free_stw g (AC.alloc_phase g fp Ph.Marking wz tag).SA.heap_out /\
                    MS.grey_obj (AC.alloc_phase g fp Ph.Marking wz tag).SA.heap_out y)
          (ensures MS.grey_obj g y)
  = let g' = (AC.alloc_phase g fp Ph.Marking wz tag).SA.heap_out in
    Mark.colors_exclusive y g';
    Mark.colors_exclusive obj g';
    MPA.alloc_in_use g fp wz tag obj y;
    assert (in_use (MPA.free_or_new obj) g' y);
    MM.header_kept_facts g g' y

let alloc_mark_cache minor g fp wz tag st ov p =
  let held = GMM.nursery_held minor in
  marking_parts minor g fp;
  MPA.marking_alloc g held fp wz tag;
  let r = AC.alloc_phase g fp Ph.Marking wz tag in
  if r.SA.obj_out <> 0UL then begin
    let obj : obj_addr = r.SA.obj_out in
    FStar.Classical.forall_intro (FStar.Classical.move_requires (alloc_grey g fp wz tag obj));
    MS.mark_cache_keeps_blocks g r.SA.heap_out st ov p
  end

let fresh_mark_cache_write minor g fp obj a v st ov p =
  Mark.colors_exclusive obj g;
  MS.mark_cache_write g Ph.Marking st ov p obj a v
