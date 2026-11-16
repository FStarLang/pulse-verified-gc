/// ---------------------------------------------------------------------------
/// GC.Gen.MarkPhase.Completeness - the cycle's completeness at the collector's state
/// ---------------------------------------------------------------------------
///
/// The account of `GC.Spec.MarkPhase.Completeness` (`MPC.cycle_account snapshot g
/// ph`: every block that is dark, or not free, is in the ghost set `snapshot` of
/// addresses reachable when the cycle started or allocated since) at the
/// generational collector's entry points:
///
///   * **the start** (`cycle_start`): `start_cycle` runs idle right after a
///     minor collection; the heap it leaves, the roots darkened
///     (`GC.Gen.MarkPhase.Start.darkened`), has the account with `snapshot` the
///     objects reachable from the roots in the heap it started from
///     (`reachable_at_start`: the darkening only recolours);
///   * **a major slice** at any phase (`cycle_slice`, from
///     `GI.major_slice_post`): mark moves, the hand-over to the sweep, sweep
///     slices;
///   * **the barrier** (`cycle_modify`, from `GB.modify_ok` and, while
///     marking, the completeness obligation `MPC.cycle_write snapshot`);
///   * **a minor collection** while marking (`account_minor`, the promoted
///     copies -- the blocks that were not blocks before -- added to `snapshot`) and
///     mid-sweep (`sweep_minor`, with `GC.Gen.SweepPhase.Completeness.
///     with_promoted`).  While marking it needs the nursery's major pointers
///     in the snapshot (`GenInv.minor_major_fields_not_free (MPC.outside_snapshot
///     snapshot)`), the nursery half of the same trusted obligation.
///
/// Allocation while marking is `MPC.account_alloc` / `account_fresh_*` on the
/// allocator's result, and mid-sweep `MPC.cycle_sweep_alloc` /
/// `cycle_sweep_write`.
///
/// **The theorem** (`cycle_frees_unreachable`): when the cycle is idle again,
/// every object unreachable from the roots when it started is freed, unless
/// its address was allocated or promoted since.

module GC.Gen.MarkPhase.Completeness

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
module GB = GC.Gen.Barrier
module GMM = GC.Gen.MarkPhase.Minor
module MP = GC.Spec.MarkPhase
module MStart = GC.Gen.MarkPhase.Start
module MBP = GC.Impl.MarkBoundedPrecondition
module MPC = GC.Spec.MarkPhase.Completeness
module SPC = GC.Spec.SweepPhase.Completeness
module GSC = GC.Gen.SweepPhase.Completeness
module SPM = GC.Gen.SweepPhase.Minor
module Promote = GC.Gen.Promote

/// The objects reachable from the roots `rs` in the heap `g` a cycle starts
/// from.
let reachable_at_start (g: heap) (rs: seq U64.t) : obj_addr -> prop =
  MPC.reachable g (GMM.root_refs g rs)

/// As an equation (the SMT encoding does not unfold a definition whose
/// value is a function).
val reachable_at_start_eq (g: heap) (rs: seq U64.t)
  : Lemma (reachable_at_start g rs == MPC.reachable g (GMM.root_refs g rs))

/// **The start of the cycle**: idle, the nursery empty, every root a
/// darkenable object; the darkened heap has the account of what was
/// reachable.
val cycle_start (minor: minor_state) (g: heap) (fp: U64.t) (rs: seq U64.t)
  : Lemma (requires GenInv.collection_heap_shape minor g fp /\ minor == minor_reset minor /\
                    (forall (i: nat). i < Seq.length rs ==> MBP.root_valid_for_darkening g (Seq.index rs i)))
          (ensures MPC.within_snapshot (reachable_at_start g rs) (MStart.darkened g rs))

/// **A major slice keeps the account**, at whatever phase it leaves:
/// marking, mark moves; the hand-over to the sweep when nothing is grey; a
/// sweep slice.
val cycle_slice (snapshot: obj_addr -> prop) (minor: minor_state) (g: heap) (sp: MP.scan_pos) (fp: U64.t)
                (ph: Ph.gc_phase) (budget: nat) (g': heap) (sp': MP.scan_pos) (fp': U64.t) (ph': Ph.gc_phase)
  : Lemma (requires GI.phase_shape minor g fp ph sp /\ MPC.cycle_account snapshot g ph /\
                    GI.major_slice_post g sp fp ph budget g' sp' fp' ph')
          (ensures MPC.cycle_account snapshot g' ph')

/// The completeness half of the barrier's obligation: while marking, the
/// program writes into an object it can reach a value it holds.
let modify_in_snapshot (snapshot: obj_addr -> prop) (ph: Ph.gc_phase) (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : prop =
  Ph.Marking? ph ==> MPC.cycle_write snapshot g x a v

/// **The barrier keeps the account** at every phase.
val cycle_modify (snapshot: obj_addr -> prop) (ph: Ph.gc_phase) (minor: minor_state) (g: heap) (fp: U64.t)
                 (sp: MP.scan_pos) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires GI.phase_shape minor g fp ph sp /\ GB.modify_ok ph minor g sp x a v /\
                    MPC.cycle_account snapshot g ph /\ modify_in_snapshot snapshot ph g x a v)
          (ensures MPC.cycle_account snapshot (GB.modify_heap ph g a v) ph)

/// `snapshot`, and the blocks of `g'` that were not blocks of `g`: a minor
/// collection's promoted copies.
let with_new_blocks (snapshot: obj_addr -> prop) (g g': heap) (x: obj_addr) : prop =
  snapshot x \/ (in_use free_stw g' x /\ ~(in_use free_stw g x))

/// **A minor collection while marking keeps the account**, with its promoted
/// copies added, when what the nursery holds is in the snapshot.
val account_minor (snapshot: obj_addr -> prop) (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t)
    (sp: MP.scan_pos)
  : Lemma (requires GI.phase_shape minor g fp Ph.Marking sp /\ MPC.within_snapshot snapshot g /\
                    GenInv.minor_major_fields_not_free (MPC.outside_snapshot snapshot) minor g)
          (ensures (let g' = (GMM.collect_marking minor g fp roots).Promote.mc_major in
                    MPC.within_snapshot (with_new_blocks snapshot g g') g'))

/// **A minor collection mid-sweep keeps it**, with its promoted copies added.
val sweep_minor (snapshot: obj_addr -> prop) (minor: minor_state) (g: heap) (fp: U64.t) (c: U64.t)
                (roots: seq U64.t) (sp: MP.scan_pos)
  : Lemma (requires GI.phase_shape minor g fp (Ph.Sweeping c) sp /\ MPC.sweep_in_snapshot snapshot g c)
          (ensures MPC.sweep_in_snapshot (GSC.with_promoted snapshot c minor g fp roots)
                     (SPM.collect_at c minor g fp roots).Promote.mc_major c)

/// **Completeness across an incremental cycle.**  Idle again, with the
/// account of the cycle that started from `g0` and the roots `rs` -- every
/// address in `snapshot` reachable then, or in `since` (allocated or promoted
/// since) -- every object unreachable from the roots when the cycle started
/// is freed, unless its address is in `since`.
val cycle_frees_unreachable (g0: heap) (rs: seq U64.t) (since: obj_addr -> prop)
                            (snapshot: obj_addr -> prop) (g: heap)
  : Lemma (requires MPC.cycle_account snapshot g Ph.Idle /\
                    (forall (x: obj_addr). snapshot x ==> reachable_at_start g0 rs x \/ since x))
          (ensures forall (x: obj_addr). ~(reachable_at_start g0 rs x) /\ ~(since x) ==> SPC.freed g x)
