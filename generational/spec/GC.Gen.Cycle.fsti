/// ---------------------------------------------------------------------------
/// GC.Gen.Cycle - a run of the whole incremental major cycle, and what it frees
/// ---------------------------------------------------------------------------
///
/// A major cycle starts idle, with `start_cycle` darkening the roots, marks
/// in slices while the program runs, hands over to the sweep when nothing is
/// grey, sweeps in slices while the program runs, and is idle again.
/// `major_cycle g0 rs g fp ph since` is a run of it, from the heap `g0` that
/// `start_cycle` was called on with the roots `rs`, to the heap `g`,
/// free-list head `fp` and phase `ph`, with `since` the addresses its
/// allocations and promotions handed out.  It composes the two phases' runs
/// rather than repeating their events:
///
///   * `Mark`: a run of the marking phase (`GC.Gen.MarkPhase.Cycle.marking`);
///   * `Sweep`: a run of the marking phase, the slice that hands over to the
///     sweep (`GI.mark_slice_post` ending at `Sweeping zero_addr`: mark
///     moves, then nothing grey), and a run of the sweep phase
///     (`GC.Gen.SweepPhase.Cycle.cycle`) from the heap it handed over, from
///     the same free list (`sweep_start_fp`).  `since` is what both runs
///     handed out (`union`).
///
/// The sweep's run is indexed by the heap marking left (its `g0`); this run
/// by the heap the cycle started from.  So its theorems are about what was
/// reachable when the cycle started -- snapshot-at-the-beginning -- where the
/// sweep's are about what was black when marking ended.  The cycle's
/// **snapshot** (`MC.snapshot g0 rs since`) is what the roots reached in `g0`
/// and what the run handed out.
///
/// **The incremental cycle is lossless, up to what it handed out**
/// (`cycle_lossless`): once a run is idle again, an address the run did not
/// hand out holds a block that is not free exactly when it held an object
/// reachable from the roots when the cycle started.  Its two halves:
///
///   * **completeness** (`cycle_complete`, and `cycle_frees_unreachable`):
///     every address outside the snapshot is freed.  Each event keeps the
///     account of the snapshot (`MPC.cycle_account`, at every state of a run:
///     `cycle_account`): marking greys only what is in the snapshot, so what
///     marking leaves black is in it, and the sweep frees every other block
///     that it did not hand out;
///   * **its converse** (`cycle_survives`): every object reachable when the
///     cycle started survives it -- a block that is not free, at the size it
///     had, and not handed out again.  The deletion barrier keeps
///     snapshot-at-the-beginning while marking (`MC.satb`), so marking leaves
///     every such object black, and the sweep frees no black block.
///
/// Completeness alone is weak in `since` (it holds of the set of every
/// address); the run pins `since`, and the converse shows the snapshot is not
/// too large: it frees nothing that was reachable.

module GC.Gen.Cycle

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module Mark = GC.Spec.Mark
module MP = GC.Spec.MarkPhase
module GI = GC.Gen.Incremental
module MPC = GC.Spec.MarkPhase.Completeness
module GMC = GC.Gen.MarkPhase.Completeness
module SPC = GC.Spec.SweepPhase.Completeness
module FSI = GC.Spec.FusedSweep.Inv
module MC = GC.Gen.MarkPhase.Cycle
module SC = GC.Gen.SweepPhase.Cycle

/// The addresses either set holds.
let union (a b: obj_addr -> prop) (x: obj_addr) : prop = a x \/ b x

/// The free-list head a run of the sweep phase started from.
let rec sweep_start_fp (#gh #g: heap) (#fp: U64.t) (#ph: Ph.gc_phase) (#since: obj_addr -> prop)
                       (r: SC.cycle gh g fp ph since)
  : GTot U64.t (decreases r)
  = match r with
    | SC.Start fp0 _ -> fp0
    | SC.Slice r1 _ _ _ _ _ -> sweep_start_fp r1
    | SC.Alloc r1 _ _ _ _ _ _ -> sweep_start_fp r1
    | SC.Write r1 _ _ _ _ _ -> sweep_start_fp r1
    | SC.Minor r1 _ _ _ _ _ -> sweep_start_fp r1

/// **A run of the incremental major cycle** that `start_cycle` began on `g0`
/// with the roots `rs`, to the heap `g`, free-list head `fp` and phase `ph`,
/// with `since` the addresses its allocations and promotions handed out.
noeq type major_cycle (g0: heap) (rs: seq U64.t) : heap -> U64.t -> Ph.gc_phase -> (obj_addr -> prop) -> Type =
  // Marking.
  | Mark :
      #g: heap -> #fp: U64.t -> #sp: MP.scan_pos -> #since: (obj_addr -> prop) ->
      MC.marking g0 rs g fp sp since ->
      major_cycle g0 rs g fp Ph.Marking since
  // Marking, the slice that hands over to the sweep, and the sweep from the
  // heap and free list it handed over.
  | Sweep :
      #g: heap -> #fp: U64.t -> #sp: MP.scan_pos -> #sm: (obj_addr -> prop) ->
      MC.marking g0 rs g fp sp sm ->
      minor: minor_state -> budget: nat -> gh: heap -> sp': MP.scan_pos ->
      squash (GI.phase_shape minor g fp Ph.Marking sp /\
              GI.mark_slice_post g sp fp budget gh sp' fp (Ph.Sweeping zero_addr)) ->
      #g': heap -> #fp': U64.t -> #ph: Ph.gc_phase -> #ss: (obj_addr -> prop) ->
      sr: SC.cycle gh g' fp' ph ss ->
      squash (sweep_start_fp sr == fp) ->
      major_cycle g0 rs g' fp' ph (union sm ss)

/// **The hand-over starts the sweep**: the heap the hand-over slice leaves,
/// with the free list, is where a run of the sweep phase starts (`SC.Start`).
val handover_sweep_start (minor: minor_state) (g: heap) (sp: MP.scan_pos) (fp: U64.t) (budget: nat)
                         (gh: heap) (sp': MP.scan_pos)
  : Lemma (requires GI.phase_shape minor g fp Ph.Marking sp /\
                    GI.mark_slice_post g sp fp budget gh sp' fp (Ph.Sweeping zero_addr))
          (ensures FSI.sweep_pre gh fp /\ Mark.noGreyObjects gh /\ Mark.tri_color_invariant gh)

/// **Every state of a run carries the account of the snapshot**, at the
/// run's phase (`MPC.cycle_account`): while marking, what is dark is in the
/// snapshot and the snapshot is closed under the edges; mid-sweep, every
/// block that is not free (or pending free) is in it; idle again, every
/// block that is not free is in it.
val cycle_account (#g0: heap) (#rs: seq U64.t) (#g: heap) (#fp: U64.t) (#ph: Ph.gc_phase)
                  (#since: obj_addr -> prop) (r: major_cycle g0 rs g fp ph since)
  : Lemma (ensures MPC.cycle_account (MC.snapshot g0 rs since) g ph)

/// **Completeness of a run**: once it is idle again, every address outside
/// the snapshot -- unreachable when the cycle started, and not handed out
/// since -- is freed.
val cycle_complete (#g0: heap) (#rs: seq U64.t) (#g: heap) (#fp: U64.t) (#since: obj_addr -> prop)
                   (r: major_cycle g0 rs g fp Ph.Idle since)
  : Lemma (ensures forall (x: obj_addr). ~(MC.snapshot g0 rs since x) ==> SPC.freed g x)

/// The same, spelled out: an object unreachable from the roots when the
/// cycle started is freed by the end of the cycle, unless the run handed its
/// address out again.
val cycle_frees_unreachable (#g0: heap) (#rs: seq U64.t) (#g: heap) (#fp: U64.t) (#since: obj_addr -> prop)
                            (r: major_cycle g0 rs g fp Ph.Idle since)
  : Lemma (ensures forall (x: obj_addr).
                     ~(GMC.reachable_at_start g0 rs x) /\ ~(since x) ==> SPC.freed g x)

/// **The converse: what was reachable survives.**  Once a run is idle again,
/// every object reachable from the roots when the cycle started is a block
/// that is not free, at the size it had, and the run did not hand its
/// address out.
val cycle_survives (#g0: heap) (#rs: seq U64.t) (#g: heap) (#fp: U64.t) (#since: obj_addr -> prop)
                   (r: major_cycle g0 rs g fp Ph.Idle since)
  : Lemma (ensures forall (x: obj_addr). GMC.reachable_at_start g0 rs x ==>
                     Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\
                     wosize_of_object x g == wosize_of_object x g0 /\ ~(since x))

/// **The incremental cycle is lossless, up to what it handed out**: once a
/// run is idle again, an address the run did not hand out holds a block that
/// is not free exactly when it held an object reachable from the roots when
/// the cycle started.
val cycle_lossless (#g0: heap) (#rs: seq U64.t) (#g: heap) (#fp: U64.t) (#since: obj_addr -> prop)
                   (r: major_cycle g0 rs g fp Ph.Idle since)
  : Lemma (ensures forall (x: obj_addr). ~(since x) ==>
                     (GMC.reachable_at_start g0 rs x <==> ~(SPC.freed g x)))
