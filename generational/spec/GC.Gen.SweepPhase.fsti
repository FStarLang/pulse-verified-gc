/// ---------------------------------------------------------------------------
/// GC.Gen.SweepPhase - promotion during the sweep phase
/// ---------------------------------------------------------------------------
///
/// A minor collection mid-sweep promotes into the major heap.  Promotion
/// (`promote_sweep_phase`) is `GC.Gen.Promote.promote_object` at the sweep's
/// phase: the allocation with the nursery object's tag
/// (`GC.Spec.SweepPhase.Mutator.alloc_sweep_phase`), the copy of its fields
/// into it, and the close (`GC.Spec.SweepPhase.Mutator.fresh_close`).  It keeps
/// the sweep phase (`GC.Spec.SweepPhase.Intrinsic.sweep_inv_incremental`) and
/// the pending-free set.
///
/// The `_shape` form is the same statement about `sweep_shape` alone (the
/// walk, headers and free list, without well-formedness): a minor collection
/// mid-sweep gets well-formedness from the generic theorem and its shape from
/// it.

module GC.Gen.SweepPhase

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.SweepPhase.Util
open GC.Spec.SweepPhase.Intrinsic
open GC.Spec.SweepPhase.Mutator
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator
module Promote = GC.Gen.Promote
module WB = GC.Gen.WriteBodyLemmas
module FLA = GC.Spec.FreeList.Ascending

/// ---------------------------------------------------------------------------
/// Promotion
/// ---------------------------------------------------------------------------

/// The nursery object `obj`'s fields, where the collector scans them, are not
/// major pointers or point at non-free blocks.
let minor_fields_ok (free: free_def) (minor: minor_state) (obj: U64.t) (g: heap) : prop =
  forall (j: nat). j < minor_scan_wosize minor obj ==> storable free g (minor_read_field minor obj j)

/// The cross-generation condition gives it, for every nursery object.
val minor_fields_ok_of (free: free_def) (minor: minor_state) (obj: U64.t) (g: heap)
  : Lemma (requires GC.Gen.HeapInvariant.minor_major_fields_not_free free minor g /\ free_def_ok free /\
                    Seq.mem obj (minor_objects minor) /\ no_infix_block g)
          (ensures minor_fields_ok free minor obj g)

/// Promotion keeps the sweep shape, and the pending-free set.
val promote_sweep_shape (g: heap) (fp: U64.t) (c: U64.t)
                        (minor: minor_state) (obj: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires sweep_shape g fp c)
          (ensures (let r = Promote.promote_object minor g obj fp wosize (SA.Sweeping c) in
                    sweep_shape r.Promote.major_out r.Promote.fp_out c /\
                    (forall (x: obj_addr). pending_free c r.Promote.major_out x == pending_free c g x)))

/// Promotion keeps where the walk ends: an allocation, then writes into the
/// body of the new object.
val promote_walk_end (g: heap) (fp: U64.t) (c: U64.t)
                     (minor: minor_state) (obj: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires sweep_shape g fp c)
          (ensures W.walk_end (Promote.promote_object minor g obj fp wosize (SA.Sweeping c)).Promote.major_out
                     zero_addr == W.walk_end g zero_addr)

/// **Promotion keeps the sweep phase**, and the pending-free set.
val promote_sweep_phase (g: heap) (fp: U64.t) (c: U64.t)
                        (minor: minor_state) (obj: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires sweep_inv_incremental g fp c /\
                    Promote.promoted_tag minor obj <> infix_tag /\
                    wosize == minor_wosize minor obj /\
                    minor_fields_ok (free_incremental c) minor obj g)
          (ensures (let r = Promote.promote_object minor g obj fp wosize (SA.Sweeping c) in
                    sweep_inv_incremental r.Promote.major_out r.Promote.fp_out c /\
                    (forall (x: obj_addr). pending_free c r.Promote.major_out x == pending_free c g x)))
