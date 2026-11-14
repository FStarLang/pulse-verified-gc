/// ---------------------------------------------------------------------------
/// GC.Gen.SweepPhase.Completeness - a minor collection mid-sweep, for completeness
/// ---------------------------------------------------------------------------
///
/// The sweep phase's completeness (`GC.Spec.SweepPhase.Completeness`) is
/// carried by an account of the non-free blocks: each is a survivor of
/// marking or was allocated since.  A minor collection in the middle of the
/// sweep keeps the account with its promoted copies among the new addresses
/// (`survivor_or_new_minor`): every non-free block of the heap before is one
/// after, with the same header, and the only other non-free blocks after are
/// promoted copies (`GC.Gen.SweepPhase.Minor.minor_keeps_blocks`); and the
/// walk ends where it did (`GC.Gen.SweepPhase.Minor.minor_keeps_walk_end`).  An empty nursery promotes
/// nothing (`nothing_promoted_after_reset`).

module GC.Gen.SweepPhase.Completeness

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.SweepPhase.Intrinsic
open GC.Spec.SweepPhase.Completeness
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module GenInv = GC.Gen.HeapInvariant
module Ph = GC.Spec.Phase
module Cheney = GC.Gen.Cheney
module Promote = GC.Gen.Promote
module SPM = GC.Gen.SweepPhase.Minor
module LL = GC.Spec.FusedSweep.Lossless

/// The addresses of the copies a minor collection at the sweep's phase
/// promotes into the major heap.
let promoted_copy (c: U64.t) (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t)
                  (x: obj_addr) : prop =
  exists (m: U64.t). Seq.mem m (minor_objects minor) /\
    (Cheney.cheney_promote (Ph.Sweeping c) minor g fp roots).Promote.fwd_map m == x

/// `since`, and the collection's promoted copies.
let with_promoted (since: obj_addr -> prop) (c: U64.t) (minor: minor_state) (g: heap) (fp: U64.t)
                  (roots: seq U64.t) : obj_addr -> prop =
  fun x -> since x \/ promoted_copy c minor g fp roots x

/// **A minor collection mid-sweep keeps the account**, with its promoted
/// copies among the new addresses.
val survivor_or_new_minor (g0: heap) (since: obj_addr -> prop)
                          (minor: minor_state) (g: heap) (fp: U64.t) (c: U64.t) (roots: seq U64.t)
  : Lemma (requires sweep_inv_incremental g fp c /\
                    GenInv.minor_heap_shape minor /\
                    GenInv.minor_major_fields_not_free (free_incremental c) minor g /\
                    survivor_or_new g0 since g c)
          (ensures (let res = SPM.collect_at c minor g fp roots in
                    survivor_or_new g0 (with_promoted since c minor g fp roots) res.Promote.mc_major c))

/// An empty nursery promotes nothing.
val nothing_promoted_after_reset (c: U64.t) (m: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t)
                                 (x: obj_addr)
  : Lemma (~(promoted_copy c (minor_reset m) g fp roots x))

/// ---------------------------------------------------------------------------
/// The blocks a collection made, and the converse
/// ---------------------------------------------------------------------------

/// The blocks a change from `g` to `g'` made non-free: non-free after, and
/// not before.
let made_by (c: U64.t) (g g': heap) (x: obj_addr) : prop =
  in_use (free_incremental c) g' x /\ ~(in_use (free_incremental c) g x)

/// `since`, and the blocks a change from `g` to `g'` made non-free.
let with_made (since: obj_addr -> prop) (c: U64.t) (g g': heap) : obj_addr -> prop =
  fun x -> since x \/ made_by c g g' x

/// **The blocks a minor collection makes are its promoted copies.**
val made_by_minor_promoted (minor: minor_state) (g: heap) (fp: U64.t) (c: U64.t) (roots: seq U64.t)
                           (x: obj_addr)
  : Lemma (requires sweep_inv_incremental g fp c /\
                    GenInv.minor_heap_shape minor /\
                    GenInv.minor_major_fields_not_free (free_incremental c) minor g /\
                    made_by c g (SPM.collect_at c minor g fp roots).Promote.mc_major x)
          (ensures promoted_copy c minor g fp roots x)

/// **A minor collection mid-sweep keeps the account**, with the blocks it
/// made (its promoted copies) among the new addresses.
val survivor_or_new_minor_made (g0: heap) (since: obj_addr -> prop)
                               (minor: minor_state) (g: heap) (fp: U64.t) (c: U64.t) (roots: seq U64.t)
  : Lemma (requires sweep_inv_incremental g fp c /\
                    GenInv.minor_heap_shape minor /\
                    GenInv.minor_major_fields_not_free (free_incremental c) minor g /\
                    survivor_or_new g0 since g c)
          (ensures (let g' = (SPM.collect_at c minor g fp roots).Promote.mc_major in
                    survivor_or_new g0 (with_made since c g g') g' c))

/// **A minor collection mid-sweep keeps the converse**, with the blocks it
/// made among the new addresses: it keeps every non-free block, and its
/// copies are carved out of free space.
val reclaimed_was_dead_minor (g0: heap) (since: obj_addr -> prop)
                             (minor: minor_state) (g: heap) (fp: U64.t) (c: U64.t) (roots: seq U64.t)
  : Lemma (requires sweep_inv_incremental g fp c /\
                    GenInv.minor_heap_shape minor /\
                    GenInv.minor_major_fields_not_free (free_incremental c) minor g /\
                    reclaimed_was_dead g0 since (free_incremental c) g)
          (ensures (let g' = (SPM.collect_at c minor g fp roots).Promote.mc_major in
                    reclaimed_was_dead g0 (with_made since c g g') (free_incremental c) g'))
