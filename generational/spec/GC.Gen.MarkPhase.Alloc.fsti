/// ---------------------------------------------------------------------------
/// GC.Gen.MarkPhase.Alloc - a major allocation while marking, at the
/// collector's state
/// ---------------------------------------------------------------------------
///
/// The program allocates a major block directly while the collector is
/// marking (`GC.Impl.Allocator.allocate` computes `AC.alloc_phase g fp
/// Marking wz tag`), then the runtime initialises its fields.  The block is
/// black (`GC.Spec.Phase.allocation_color Marking`), and until its fields are
/// written it is *fresh* (`GC.Spec.MarkPhase.Alloc.marking_fresh`): its
/// fields hold whatever the free block held, so they are exempt from
/// well-formedness and the weak tri-colour clause.  This module lifts the
/// three steps of `GC.Spec.MarkPhase.Alloc` to the collector's state at
/// `Marking` (`GC.Gen.Incremental.phase_shape minor g fp Marking`):
///
///   * **The state with a fresh block** (`fresh_shape minor g fp obj`): the
///     nursery's shape and the cross-generation condition at `free_stw`, the
///     walk dense, the free list ascending, and the marking invariant with
///     `obj` fresh and what the nursery points at held.
///   * **Allocation** (`marking_alloc_shape`): from the collector's state at
///     `Marking`, the allocation either fails and changes nothing, or hands
///     out a block of the requested size and tag, fresh.  Nothing the
///     nursery points at moves or changes colour (allocation keeps every
///     non-free block, `MPA.keeps_blocks`).
///   * **Initialising** (`fresh_shape_write`): a write into the new block's
///     body keeps it fresh.  The write keeps the walk and every header, so
///     the list and the cross-generation condition.
///   * **Closing** (`fresh_shape_close`): once every field of the block is
///     storable and fine for a black block to point at (`MPA.fields_ok`, e.g.
///     a value the program holds), the collector's state at `Marking` holds
///     again.  The free-list half of the shape follows from the list being
///     ascending (`GC.Gen.PostCollectionShape.free_list_shape_of_ascending`).
///
/// The mark cache (`GC.Gen.MarkState.mark_cache_ok`) survives both: the
/// allocation keeps every non-free block with its header and fields and
/// makes no grey object (`alloc_mark_cache`), and an initialising write
/// touches only the body of a black block (`fresh_mark_cache_write`).

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
module SPM = GC.Spec.SweepPhase.Mutator
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator
module FLA = GC.Spec.FreeList.Ascending

/// **The collector's state at `Marking` with `obj` just allocated** and not
/// yet initialised.
let fresh_shape (minor: minor_state) (g: heap) (fp: U64.t) (obj: obj_addr) : prop =
  GenInv.minor_heap_shape minor /\
  GenInv.minor_major_fields_not_free free_stw minor g /\
  heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
  FLA.fl_ascending g fp /\
  MPA.marking_fresh g (GMM.nursery_held minor) obj

/// **Allocation while marking**: nothing changes if nothing fits; otherwise
/// the new block has the requested size and tag and is fresh.
val marking_alloc_shape (minor: minor_state) (g: heap) (fp: U64.t) (wz: nat) (tag: SPM.tag_t)
  : Lemma (requires GI.phase_shape minor g fp Ph.Marking /\ wz >= 1 /\ tag <> infix_tag)
          (ensures (let r = AC.alloc_phase g fp Ph.Marking wz tag in
                    (r.SA.obj_out == 0UL ==> r.SA.heap_out == g /\ r.SA.fp_out == fp) /\
                    (r.SA.obj_out <> 0UL ==>
                       GC.Spec.FusedSweep.is_obj r.SA.obj_out /\
                       (let obj : obj_addr = r.SA.obj_out in
                        U64.v (wosize_of_object obj r.SA.heap_out) == wz /\
                        tag_of_object obj r.SA.heap_out == tag /\
                        fresh_shape minor r.SA.heap_out r.SA.fp_out obj))))

/// **Initialising**: a write into the body of the fresh block keeps it
/// fresh.
val fresh_shape_write (minor: minor_state) (g: heap) (fp: U64.t) (obj: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires fresh_shape minor g fp obj /\ SPM.in_body g obj a)
          (ensures fresh_shape minor (write_word g a v) fp obj)

/// **Closing**: with every field storable and fine for a black block to
/// point at, the collector's state at `Marking`.
val fresh_shape_close (minor: minor_state) (g: heap) (fp: U64.t) (obj: obj_addr)
  : Lemma (requires fresh_shape minor g fp obj /\ SPM.fields_storable free_stw g obj /\
                    MPA.fields_ok g (GMM.nursery_held minor) obj)
          (ensures GI.phase_shape minor g fp Ph.Marking)

/// ---------------------------------------------------------------------------
/// The mark cache
/// ---------------------------------------------------------------------------

/// **The allocation keeps the mark cache**: it keeps every non-free block
/// with its header and fields, and the only block it colours other than
/// blue is the new one, black.
val alloc_mark_cache (minor: minor_state) (g: heap) (fp: U64.t) (wz: nat) (tag: SPM.tag_t)
  (st: seq obj_addr) (ov: bool) (p: MS.mark_pos)
  : Lemma (requires GI.phase_shape minor g fp Ph.Marking /\ wz >= 1 /\ tag <> infix_tag /\
                    MS.mark_cache_ok g Ph.Marking st ov p)
          (ensures MS.mark_cache_ok (AC.alloc_phase g fp Ph.Marking wz tag).SA.heap_out Ph.Marking st ov p)

/// **An initialising write keeps the mark cache** (`MS.mark_cache_write`).
val fresh_mark_cache_write (minor: minor_state) (g: heap) (fp: U64.t) (obj: obj_addr)
  (a: hp_addr) (v: U64.t) (st: seq obj_addr) (ov: bool) (p: MS.mark_pos)
  : Lemma (requires fresh_shape minor g fp obj /\ MS.mark_cache_ok g Ph.Marking st ov p /\
                    SPM.in_body g obj a)
          (ensures MS.mark_cache_ok (write_word g a v) Ph.Marking st ov p)
