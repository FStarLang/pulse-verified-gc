/// ---------------------------------------------------------------------------
/// GC.Gen.MarkPhase.Completeness - the cycle's completeness at the collector's state
/// ---------------------------------------------------------------------------
///
/// The account of `GC.Spec.MarkPhase.Completeness` (`MPC.cycle_account s g
/// ph`: every block that is dark, or not free, is in the ghost set `s` of
/// addresses reachable when the cycle started or allocated since) at the
/// generational collector's entry points:
///
///   * **the start** (`cycle_start`): `start_cycle` runs idle right after a
///     minor collection; the heap it leaves, the roots darkened
///     (`GC.Gen.MarkPhase.Start.darkened`), has the account with `s` the
///     objects reachable from the roots in the heap it started from
///     (`reachable_at_start`: the darkening only recolours);
///   * **a major slice** at any phase (`cycle_slice`, from
///     `GI.major_slice_post`): mark moves, the hand-over to the sweep, sweep
///     slices;
///   * **the barrier** (`cycle_modify`, from `GB.modify_ok` and, while
///     marking, the completeness obligation `MPC.cycle_write s`);
///   * **a minor collection** while marking (`account_minor`, the promoted
///     copies -- the blocks that were not blocks before -- added to `s`) and
///     mid-sweep (`sweep_minor`, with `GC.Gen.SweepPhase.Completeness.
///     with_promoted`).  While marking it needs the nursery's major pointers
///     accounted for (`GenInv.minor_major_fields_not_free (MPC.unaccounted
///     s)`), the nursery half of the same trusted obligation.
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
  MPC.reachable g (GMM.roots_held g rs)

/// As an equation (the SMT encoding does not unfold a definition whose
/// value is a function).
val reachable_at_start_eq (g: heap) (rs: seq U64.t)
  : Lemma (reachable_at_start g rs == MPC.reachable g (GMM.roots_held g rs))

/// **The start of the cycle**: idle, the nursery empty, every root a
/// darkenable object; the darkened heap has the account of what was
/// reachable.
val cycle_start (minor: minor_state) (g: heap) (fp: U64.t) (rs: seq U64.t)
  : Lemma (requires GenInv.collection_heap_shape minor g fp /\ minor == minor_reset minor /\
                    (forall (i: nat). i < Seq.length rs ==> MBP.root_valid_for_darkening g (Seq.index rs i)))
          (ensures MPC.mark_account (reachable_at_start g rs) (MStart.darkened g rs))

/// **A major slice keeps the account**, at whatever phase it leaves:
/// marking, mark moves; the hand-over to the sweep when nothing is grey; a
/// sweep slice.
val cycle_slice (s: obj_addr -> prop) (minor: minor_state) (g: heap) (fp: U64.t) (ph: Ph.gc_phase)
                (budget: nat) (g': heap) (fp': U64.t) (ph': Ph.gc_phase)
  : Lemma (requires GI.phase_shape minor g fp ph /\ MPC.cycle_account s g ph /\
                    GI.major_slice_post g fp ph budget g' fp' ph')
          (ensures MPC.cycle_account s g' ph')

/// The completeness half of the barrier's obligation: while marking, the
/// program writes into an object it can reach a value it holds.
let modify_accounted (s: obj_addr -> prop) (ph: Ph.gc_phase) (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : prop =
  Ph.Marking? ph ==> MPC.cycle_write s g x a v

/// **The barrier keeps the account** at every phase.
val cycle_modify (s: obj_addr -> prop) (ph: Ph.gc_phase) (minor: minor_state) (g: heap) (fp: U64.t)
                 (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires GI.phase_shape minor g fp ph /\ GB.modify_ok ph minor g x a v /\
                    MPC.cycle_account s g ph /\ modify_accounted s ph g x a v)
          (ensures MPC.cycle_account s (GB.modify_heap ph g a v) ph)

/// `s`, and the blocks of `g'` that were not blocks of `g`: a minor
/// collection's promoted copies.
let with_new_blocks (s: obj_addr -> prop) (g g': heap) (x: obj_addr) : prop =
  s x \/ (in_use free_stw g' x /\ ~(in_use free_stw g x))

/// **A minor collection while marking keeps the account**, with its promoted
/// copies added, when what the nursery holds is accounted for.
val account_minor (s: obj_addr -> prop) (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires GI.phase_shape minor g fp Ph.Marking /\ MPC.mark_account s g /\
                    GenInv.minor_major_fields_not_free (MPC.unaccounted s) minor g)
          (ensures (let g' = (GMM.collect_marking minor g fp roots).Promote.mc_major in
                    MPC.mark_account (with_new_blocks s g g') g'))

/// **A minor collection mid-sweep keeps it**, with its promoted copies added.
val sweep_minor (s: obj_addr -> prop) (minor: minor_state) (g: heap) (fp: U64.t) (c: U64.t)
                (roots: seq U64.t)
  : Lemma (requires GI.phase_shape minor g fp (Ph.Sweeping c) /\ MPC.sweep_accounted s g c)
          (ensures MPC.sweep_accounted (GSC.with_promoted s c minor g fp roots)
                     (SPM.collect_at c minor g fp roots).Promote.mc_major c)

/// **Completeness across an incremental cycle.**  Idle again, with the
/// account of the cycle that started from `g0` and the roots `rs` -- every
/// address in `s` reachable then, or in `since` (allocated or promoted
/// since) -- every object unreachable from the roots when the cycle started
/// is freed, unless its address is in `since`.
val cycle_frees_unreachable (g0: heap) (rs: seq U64.t) (since: obj_addr -> prop)
                            (s: obj_addr -> prop) (g: heap)
  : Lemma (requires MPC.cycle_account s g Ph.Idle /\
                    (forall (x: obj_addr). s x ==> reachable_at_start g0 rs x \/ since x))
          (ensures forall (x: obj_addr). ~(reachable_at_start g0 rs x) /\ ~(since x) ==> SPC.freed g x)
