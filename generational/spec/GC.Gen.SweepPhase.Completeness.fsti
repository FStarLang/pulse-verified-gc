/// ---------------------------------------------------------------------------
/// GC.Gen.SweepPhase.Completeness - a minor collection mid-sweep, for completeness
/// ---------------------------------------------------------------------------
///
/// The sweep phase's completeness (`GC.Spec.SweepPhase.Completeness`) is
/// carried by an account of the non-free blocks: each is a survivor of
/// marking or was allocated since.  A minor collection in the middle of the
/// sweep keeps the account with its promoted copies among the new addresses
/// (`survivor_or_new_minor`): every non-free block of the heap before is one
/// after, and the only other non-free blocks after are promoted copies
/// (`GC.Gen.SweepPhase.Minor.minor_keeps_blocks`).  An empty nursery promotes
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
