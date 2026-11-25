/// ---------------------------------------------------------------------------
/// GC.Gen.MarkPhase.RunStart - the cycle's snapshot, and the start of marking
/// ---------------------------------------------------------------------------
///
/// The completeness of marking (`GC.Spec.MarkPhase.Completeness`,
/// `GC.Gen.MarkPhase.Completeness`) is stated of a ghost set `snapshot`
/// given as an argument.  The run invariant (`GC.Gen.Run.Invariant`) fixes it
/// by the run: the cycle's **snapshot** is `snapshot g0 rs since`, what the
/// roots `rs` reached in the heap `g0` the cycle started from
/// (`GMC.reachable_at_start`), and the addresses `since` handed out since.
///
/// While marking, the collector keeps two invariants (`mark_run_inv`):
///
///   * **what is dark is in the snapshot, and the snapshot is closed under
///     the heap's edges** (`MPC.within_snapshot`): nothing outside the
///     snapshot is ever greyed;
///   * **snapshot-at-the-beginning** (`satb`): every object reachable when
///     the cycle started is still a block that is not free, and if it is
///     white, the marker will reach it (`MP.marker_will_reach`: along
///     unscanned edges from a grey object).
///
/// It also carries that the blocks handed out are black blocks, and that the
/// walk still reaches where the start heap's walk ended
/// (`GC.Gen.MarkPhase.Walk`).  This module proves that root darkening
/// (`start_cycle`, from the idle heap with the nursery empty) establishes
/// them (`start_inv`); the run invariant's collector step
/// (`GC.Gen.Run.Invariant.Collector`) uses it.

module GC.Gen.MarkPhase.RunStart

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module MP = GC.Spec.MarkPhase
module MStart = GC.Gen.MarkPhase.Start
module MBP = GC.Impl.MarkBoundedPrecondition
module MPC = GC.Spec.MarkPhase.Completeness
module GMC = GC.Gen.MarkPhase.Completeness
module SPC = GC.Spec.SweepPhase.Completeness
module GenInv = GC.Gen.HeapInvariant
module W = GC.Spec.Walk

/// ---------------------------------------------------------------------------
/// The snapshot
/// ---------------------------------------------------------------------------

/// **The cycle's snapshot**: the objects reachable from the roots `rs` in the
/// heap `g0` the cycle started from, and the addresses `since` handed out
/// during it.
let snapshot (g0: heap) (rs: seq U64.t) (since: obj_addr -> prop) (x: obj_addr) : prop =
  GMC.reachable_at_start g0 rs x \/ since x

/// **Snapshot-at-the-beginning**: every object reachable when the cycle
/// started is a block that is not free, and one the marker will reach if it
/// is white.
let satb (g0: heap) (rs: seq U64.t) (g: heap) (sp: MP.scan_pos) : prop =
  (forall (x: obj_addr). GMC.reachable_at_start g0 rs x ==> in_use free_stw g x) /\
  MP.outside_refs_reached g sp (GMC.reachable_at_start g0 rs)

/// What a run of the marking phase carries: the account, snapshot-at-the-beginning, and of
/// the objects reachable at the start, that they keep their size and are
/// not among the addresses handed out (those were not blocks in use); the
/// addresses handed out are black blocks (allocated and promoted black, and
/// marking whitens nothing); and the walk still reaches where the walk of
/// `g0` ended, the end of the heap or one header slot short of it.
let mark_run_inv (g0: heap) (rs: seq U64.t) (since: obj_addr -> prop) (g: heap) (sp: MP.scan_pos) : prop =
  MPC.within_snapshot (snapshot g0 rs since) g /\ satb g0 rs g sp /\
  (forall (x: obj_addr). GMC.reachable_at_start g0 rs x ==>
     Seq.mem x (objects zero_addr g0) /\ wosize_of_object x g == wosize_of_object x g0) /\
  (forall (x: obj_addr). since x ==> ~(GMC.reachable_at_start g0 rs x)) /\
  (forall (x: obj_addr). since x ==> Seq.mem x (objects zero_addr g) /\ is_black x g) /\
  W.walk_end g0 zero_addr + 8 >= heap_size /\
  W.reaches g zero_addr (W.walk_end g0 zero_addr)

/// What `start_cycle` is called on: idle, the nursery empty, every root a
/// darkenable object.
let start_pre (minor: minor_state) (g0: heap) (fp0: U64.t) (rs: seq U64.t) : prop =
  GenInv.collection_heap_shape minor g0 fp0 /\ minor == minor_reset minor /\
  (forall (i: nat). i < Seq.length rs ==> MBP.root_valid_for_darkening g0 (Seq.index rs i))

/// ---------------------------------------------------------------------------
/// The start
/// ---------------------------------------------------------------------------

/// **The start**: root darkening leaves every object reachable from the roots
/// grey or one the marker will reach (along the edges of the path that
/// reached it, which root darkening keeps), and the account of the
/// snapshot (`GMC.cycle_start`).
val start_inv (minor: minor_state) (g0: heap) (fp0: U64.t) (rs: seq U64.t)
  : Lemma (requires start_pre minor g0 fp0 rs)
          (ensures mark_run_inv g0 rs SPC.nothing_new (MStart.darkened g0 rs) MP.scan_none)
