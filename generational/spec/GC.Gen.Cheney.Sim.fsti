/// ---------------------------------------------------------------------------
/// GC.Gen.Cheney.Sim — Simulation lemmas connecting Cheney impl to spec
/// ---------------------------------------------------------------------------
///
/// Pure F* lemmas used to eliminate the assume_ in GC.Gen.Impl.Cheney.fst.
/// Proves that the imperative BFS implementation faithfully simulates the
/// functional spec (cheney_forward_one, cheney_forward_roots, etc.).

module GC.Gen.Cheney.Sim

open FStar.Seq
module U64 = FStar.UInt64
module SZ = FStar.SizeT

open GC.Spec.Base
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Impl.UpdatePtrs

module CheneySpec = GC.Gen.Cheney
module AllocLemmas = GC.Spec.Allocator.Lemmas
module SimOne = GC.Gen.Cheney.SimOne

/// ---------------------------------------------------------------------------
/// Connection predicate: relates impl state to spec cheney_state
/// ---------------------------------------------------------------------------

/// Queue capacity = fwd_array_size = minor_heap_size / 8
let queue_size : pos = fwd_array_size

/// The impl state (heap, fp, fwd_arr, queue, back) corresponds to the spec
/// cheney_state when:
/// - heap = cs.cs_major
/// - fp = cs.cs_fp
/// - fwd_arr represents cs.cs_fwd
/// - queue[0..back) = cs.cs_queue
let impl_matches_spec
  (ms: heap) (fp: U64.t)
  (farr: seq U64.t) (q: seq U64.t) (bk: nat)
  (cs: CheneySpec.cheney_state) : prop =
  ms == cs.cs_major /\
  fp == cs.cs_fp /\
  represents_fwd farr cs.cs_fwd /\
  bk == Seq.length cs.cs_queue /\
  bk <= queue_size /\
  Seq.length q == queue_size /\
  Seq.length farr == fwd_array_size /\
  (forall (j:nat). j < bk ==> Seq.index q j == Seq.index cs.cs_queue j)

/// ---------------------------------------------------------------------------
/// Initial state: zeroed fwd_arr ↔ empty_forwarding
/// ---------------------------------------------------------------------------

val represents_fwd_initial (farr: seq U64.t)
  : Lemma (requires Seq.length farr == fwd_array_size /\
                    (forall (i:nat). i < fwd_array_size ==> Seq.index farr i == 0UL))
          (ensures represents_fwd farr empty_forwarding)

/// ---------------------------------------------------------------------------
/// Forwarding array update ↔ extend_forwarding
/// ---------------------------------------------------------------------------

val represents_fwd_update
  (farr: seq U64.t) (fwd: forwarding_map)
  (addr: U64.t) (new_addr: U64.t)
  : Lemma (requires represents_fwd farr fwd /\
                    U64.v addr >= 8 /\ U64.v addr < minor_heap_size /\
                    U64.v addr % 8 == 0)
          (ensures (let idx = U64.v addr / 8 in
                    idx < fwd_array_size /\
                    represents_fwd (Seq.upd farr idx new_addr)
                                   (extend_forwarding fwd addr new_addr)))

/// ---------------------------------------------------------------------------
/// Non-minor addresses: impl guards ↔ spec noop
/// ---------------------------------------------------------------------------

/// If addr fails the impl's range/alignment checks, it's not a minor object
val not_minor_if_guards_fail (minor: minor_state) (addr: U64.t)
  : Lemma (requires U64.v addr < 8 \/ U64.v addr >= minor_heap_size \/ U64.v addr % 8 <> 0)
          (ensures ~(Seq.mem addr (minor_objects minor)))

/// Minor objects always pass the wosize/bounds guards
val minor_object_passes_guards (minor: minor_state) (obj: U64.t)
  : Lemma (requires minor_wf minor /\ Seq.mem obj (minor_objects minor))
          (ensures minor_wosize minor obj < minor_heap_size /\
                   U64.v obj + minor_wosize minor obj * 8 <= minor_heap_size)

/// ---------------------------------------------------------------------------
/// Queue length bounds: bounded by |minor_objects| via BFS invariant
/// ---------------------------------------------------------------------------

/// Forward_one preserves queue entry validity
val cheney_forward_one_queue_valid
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (requires (forall (j:nat). j < Seq.length cs.cs_queue ==>
                      Seq.mem (Seq.index cs.cs_queue j) (minor_objects minor)))
          (ensures (let cs' = CheneySpec.cheney_forward_one minor cs addr in
                    forall (j:nat). j < Seq.length cs'.cs_queue ==>
                      Seq.mem (Seq.index cs'.cs_queue j) (minor_objects minor)))

/// Forward_one adds at most 1 to the queue
val cheney_forward_one_queue_bound
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (ensures (let cs' = CheneySpec.cheney_forward_one minor cs addr in
                    Seq.length cs'.cs_queue <= Seq.length cs.cs_queue + 1))

/// ---------------------------------------------------------------------------
/// Queue entries are minor objects (maintained through BFS)
/// ---------------------------------------------------------------------------

/// After cheney_forward_fields, all queue entries are minor objects
val cheney_forward_fields_queue_valid
  (minor: minor_state) (cs: CheneySpec.cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires (forall (j:nat). j < Seq.length cs.cs_queue ==>
                      Seq.mem (Seq.index cs.cs_queue j) (minor_objects minor)))
          (ensures (let cs' = CheneySpec.cheney_forward_fields minor cs parent idx wosize in
                    forall (j:nat). j < Seq.length cs'.cs_queue ==>
                      Seq.mem (Seq.index cs'.cs_queue j) (minor_objects minor)))

/// After cheney_forward_roots, all queue entries are minor objects
val cheney_forward_roots_queue_valid
  (minor: minor_state) (cs: CheneySpec.cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires (forall (j:nat). j < Seq.length cs.cs_queue ==>
                      Seq.mem (Seq.index cs.cs_queue j) (minor_objects minor)))
          (ensures (let cs' = CheneySpec.cheney_forward_roots minor cs roots idx in
                    forall (j:nat). j < Seq.length cs'.cs_queue ==>
                      Seq.mem (Seq.index cs'.cs_queue j) (minor_objects minor)))

/// After cheney_scan, all queue entries are minor objects
val cheney_scan_queue_valid
  (minor: minor_state) (cs: CheneySpec.cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires (forall (j:nat). j < Seq.length cs.cs_queue ==>
                      Seq.mem (Seq.index cs.cs_queue j) (minor_objects minor)))
          (ensures (let cs' = CheneySpec.cheney_scan minor cs scan fuel in
                    forall (j:nat). j < Seq.length cs'.cs_queue ==>
                      Seq.mem (Seq.index cs'.cs_queue j) (minor_objects minor)))

/// ---------------------------------------------------------------------------
/// BFS invariant: compound predicate for queue length bound
///
/// The BFS invariant tracks:
///   - queue_valid (all entries are minor objects)
///   - queue_fwd_consistent (all entries have fwd set)
///   - potential function (|queue| + unforwarded_count <= |minor_objects|)
/// This is maintained through all BFS operations and implies |queue| <= |minor_objects|.
/// ---------------------------------------------------------------------------

/// Re-export: BFS invariant from SimOne for queue bounds

/// The queue length never exceeds |minor_objects|, which is <= queue_size.
/// Requires the BFS invariant (established at initialization and maintained throughout).
val cheney_forward_roots_queue_bound
  (minor: minor_state) (cs: CheneySpec.cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires SimOne.cheney_bfs_inv minor cs /\
                    Seq.length (minor_objects minor) <= queue_size)
          (ensures (let cs' = CheneySpec.cheney_forward_roots minor cs roots idx in
                    SimOne.cheney_bfs_inv minor cs' /\
                    Seq.length cs'.cs_queue <= Seq.length (minor_objects minor) /\
                    Seq.length cs'.cs_queue <= queue_size))

val cheney_scan_queue_bound
  (minor: minor_state) (cs: CheneySpec.cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires SimOne.cheney_bfs_inv minor cs /\
                    Seq.length (minor_objects minor) <= queue_size)
          (ensures (let cs' = CheneySpec.cheney_scan minor cs scan fuel in
                    SimOne.cheney_bfs_inv minor cs' /\
                    Seq.length cs'.cs_queue <= Seq.length (minor_objects minor) /\
                    Seq.length cs'.cs_queue <= queue_size))

/// ---------------------------------------------------------------------------
/// Scan fuel sufficiency
/// ---------------------------------------------------------------------------

/// When the scan processes all queue entries, extra fuel doesn't change the result.
val cheney_scan_fuel_sufficient
  (minor: minor_state) (cs: CheneySpec.cheney_state) (scan: nat) (fuel1 fuel2: nat)
  : Lemma (requires fuel1 >= fuel2 /\
                    fuel2 >= Seq.length cs.cs_queue - scan /\
                    Seq.length cs.cs_queue <= Seq.length (minor_objects minor) /\
                    Seq.length (minor_objects minor) <= queue_size /\
                    (forall (j:nat). j < Seq.length cs.cs_queue ==>
                      Seq.mem (Seq.index cs.cs_queue j) (minor_objects minor)))
          (ensures CheneySpec.cheney_scan minor cs scan fuel1 ==
                   CheneySpec.cheney_scan minor cs scan fuel2)
