/// ---------------------------------------------------------------------------
/// GC.Gen.MarkPhase.Cycle - a run of the marking phase, and its snapshot
/// ---------------------------------------------------------------------------
///
/// The completeness of marking (`GC.Spec.MarkPhase.Completeness`,
/// `GC.Gen.MarkPhase.Completeness`) is stated of a ghost set `snapshot`
/// given as an argument -- the objects reachable when the cycle started and
/// those allocated or promoted since -- and the set of every address
/// satisfies it.  This module fixes the set by the run, as
/// `GC.Gen.SweepPhase.Cycle` does for the sweep.  `marking g0 rs g fp sp
/// since` is a run of the marking phase of the cycle that `start_cycle`
/// began on the heap `g0` with the roots `rs`, to the heap `g`, free-list
/// head `fp` and scan position `sp`, with `since` the addresses it handed
/// out.  Each event is a constructor, with that event's preconditions (the
/// collector's state, `GI.phase_shape`, which the entry points carry) as its
/// hypotheses and `since` after it fixed by the event:
///
///   * `Start`: root darkening (`MStart.darkened`), idle with the nursery
///     empty -- nothing new;
///   * `Slice`: a mark slice that stays marking (`GI.mark_slice_post`) --
///     `since` unchanged;
///   * `Write`: the barrier write (`GB.modify_heap`: darken the old value,
///     then write) -- unchanged;
///   * `Alloc`: an allocation and the initialisation of the new object's
///     fields (`init_writes`) -- `since` and the new object;
///   * `Minor`: a minor collection -- `since` and the blocks it made
///     (`GMC.with_new_blocks`, its promoted copies).
///
/// The cycle's **snapshot** is `snapshot g0 rs since`: what the roots reached
/// in `g0` (`GMC.reachable_at_start`), and `since`.  The program's events
/// carry the trusted obligation of completeness as a hypothesis, as the sweep
/// run's events carry theirs: the program writes, and initialises fresh
/// objects with, values in the snapshot (`MPC.cycle_write`,
/// `SPM.fields_storable` at `MPC.outside_snapshot`), and the nursery holds
/// only pointers into it (`minor_major_fields_not_free`).  OCaml's type
/// safety is what discharges it: the program obtains pointers only from its
/// roots, from fields of objects it holds (`MPC.account_load`), and by
/// allocating.
///
/// Every state of a run carries two invariants (`mark_run_inv`):
///
///   * **what is dark is in the snapshot, and the snapshot is closed under
///     the heap's edges** (`MPC.within_snapshot`): nothing outside the
///     snapshot is ever greyed;
///   * **snapshot-at-the-beginning** (`satb`): every object reachable when
///     the cycle started is still a block that is not free, and if it is
///     white, the marker will reach it (`MP.marker_will_reach`: along
///     unscanned edges from a grey object).  The deletion barrier is what
///     keeps it -- a write that cuts an edge greys the old target -- and the
///     marking invariant's lemmas keep it for a fixed set of outside
///     references, which is what the objects reachable at the start are
///     (`MP.outside_refs_reached`).
///
/// So when marking ends, with nothing grey (`handover`), **the black objects
/// are the snapshot's**: every object reachable at the start is black, and
/// every black object is in the snapshot.

module GC.Gen.MarkPhase.Cycle

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
module GB = GC.Gen.Barrier
module GMM = GC.Gen.MarkPhase.Minor
module MStart = GC.Gen.MarkPhase.Start
module MBP = GC.Impl.MarkBoundedPrecondition
module MPC = GC.Spec.MarkPhase.Completeness
module GMC = GC.Gen.MarkPhase.Completeness
module SPC = GC.Spec.SweepPhase.Completeness
module SPM = GC.Spec.SweepPhase.Mutator
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator
module GenInv = GC.Gen.HeapInvariant
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module Promote = GC.Gen.Promote

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

/// What the run carries: the account, snapshot-at-the-beginning, and of
/// the objects reachable at the start, that they keep their size and are
/// not among the addresses handed out (those were not blocks in use).
let mark_run_inv (g0: heap) (rs: seq U64.t) (since: obj_addr -> prop) (g: heap) (sp: MP.scan_pos) : prop =
  MPC.within_snapshot (snapshot g0 rs since) g /\ satb g0 rs g sp /\
  (forall (x: obj_addr). GMC.reachable_at_start g0 rs x ==> wosize_of_object x g == wosize_of_object x g0) /\
  (forall (x: obj_addr). since x ==> ~(GMC.reachable_at_start g0 rs x))

/// What `start_cycle` is called on: idle, the nursery empty, every root a
/// darkenable object.
let start_pre (minor: minor_state) (g0: heap) (fp0: U64.t) (rs: seq U64.t) : prop =
  GenInv.collection_heap_shape minor g0 fp0 /\ minor == minor_reset minor /\
  (forall (i: nat). i < Seq.length rs ==> MBP.root_valid_for_darkening g0 (Seq.index rs i))

/// ---------------------------------------------------------------------------
/// Initialising a fresh object
/// ---------------------------------------------------------------------------

/// Writes into the body of `obj`, from `g` to `g'`: how the program
/// initialises the object it was just handed.
noeq type init_writes (obj: obj_addr) : heap -> heap -> Type =
  | Init_done : g: heap -> init_writes obj g g
  | Init_write : #g: heap -> #g1: heap -> init_writes obj g g1 ->
      a: hp_addr -> v: U64.t -> g2: heap ->
      squash (SPM.in_body g1 obj a /\ g2 == write_word g1 a v) ->
      init_writes obj g g2

/// ---------------------------------------------------------------------------
/// The run
/// ---------------------------------------------------------------------------

/// **A run of the marking phase** of the cycle `start_cycle` began on `g0`
/// with the roots `rs`, to the heap `g`, free-list head `fp` and scan
/// position `sp`, with `since` the addresses its allocations and promotions
/// handed out.
noeq type marking (g0: heap) (rs: seq U64.t) : heap -> U64.t -> MP.scan_pos -> (obj_addr -> prop) -> Type =
  // Root darkening, from the idle heap with the nursery empty.
  | Start :
      minor: minor_state -> fp0: U64.t ->
      squash (start_pre minor g0 fp0 rs) ->
      marking g0 rs (MStart.darkened g0 rs) fp0 MP.scan_none SPC.nothing_new
  // A mark slice that leaves the collector marking.
  | Slice :
      #g: heap -> #fp: U64.t -> #sp: MP.scan_pos -> #since: (obj_addr -> prop) ->
      marking g0 rs g fp sp since ->
      minor: minor_state -> budget: nat -> g': heap -> sp': MP.scan_pos ->
      squash (GI.phase_shape minor g fp Ph.Marking sp /\
              GI.mark_slice_post g sp fp budget g' sp' fp Ph.Marking) ->
      marking g0 rs g' fp sp' since
  // The barrier write of `v` at `a`, a body word of `x`: the program's
  // obligation, and both ends in the snapshot.
  | Write :
      #g: heap -> #fp: U64.t -> #sp: MP.scan_pos -> #since: (obj_addr -> prop) ->
      marking g0 rs g fp sp since ->
      minor: minor_state -> x: obj_addr -> a: hp_addr -> v: U64.t ->
      squash (GI.phase_shape minor g fp Ph.Marking sp /\
              GB.modify_ok Ph.Marking minor g sp x a v /\
              MPC.cycle_write (snapshot g0 rs since) g x a v) ->
      marking g0 rs (GB.modify_heap Ph.Marking g a v) fp sp since
  // An allocation of `wz` words with tag `tag` that hands out `obj`, and the
  // writes that initialise it, with values in the snapshot; `obj` is new.
  | Alloc :
      #g: heap -> #fp: U64.t -> #sp: MP.scan_pos -> #since: (obj_addr -> prop) ->
      marking g0 rs g fp sp since ->
      minor: minor_state -> wz: nat -> tag: SPM.tag_t -> g1: heap -> fp': U64.t -> obj: obj_addr ->
      squash (GI.phase_shape minor g fp Ph.Marking sp /\ wz >= 1 /\ tag <> infix_tag /\
              (let r = AC.alloc_phase g fp Ph.Marking wz tag in
               g1 == r.SA.heap_out /\ fp' == r.SA.fp_out /\ (obj <: U64.t) == r.SA.obj_out)) ->
      g': heap -> init_writes obj g1 g' ->
      squash (SPM.fields_storable (MPC.outside_snapshot (snapshot g0 rs (SPC.with_new since obj))) g' obj) ->
      marking g0 rs g' fp' sp (SPC.with_new since obj)
  // A minor collection of the nursery `minor` from `roots`: the roots are
  // ones the marker will reach if white (`GI.minor_keeps_marking_shape`'s
  // hypothesis), and the nursery points only into the snapshot; the blocks
  // it makes are new.
  | Minor :
      #g: heap -> #fp: U64.t -> #sp: MP.scan_pos -> #since: (obj_addr -> prop) ->
      marking g0 rs g fp sp since ->
      minor: minor_state -> roots: seq U64.t ->
      squash (GI.phase_shape minor g fp Ph.Marking sp /\
              MCFH.roots_valid_for_minor_collection minor g roots /\
              MP.outside_refs_reached g sp (GMM.root_refs g roots) /\
              GenInv.minor_major_fields_not_free (MPC.outside_snapshot (snapshot g0 rs since)) minor g) ->
      marking g0 rs (GMM.collect_marking minor g fp roots).Promote.mc_major
                    (GMM.collect_marking minor g fp roots).Promote.mc_fp sp
                    (GMC.with_new_blocks since g (GMM.collect_marking minor g fp roots).Promote.mc_major)

/// ---------------------------------------------------------------------------
/// What a run carries
/// ---------------------------------------------------------------------------

/// **The start**: root darkening leaves every object reachable from the roots
/// grey or one the marker will reach (along the edges of the path that
/// reached it, which root darkening keeps), and the account of the
/// snapshot (`GMC.cycle_start`).
val start_inv (minor: minor_state) (g0: heap) (fp0: U64.t) (rs: seq U64.t)
  : Lemma (requires start_pre minor g0 fp0 rs)
          (ensures mark_run_inv g0 rs SPC.nothing_new (MStart.darkened g0 rs) MP.scan_none)

/// **Every state of a run carries both invariants.**
val mark_run_account (#g0: heap) (#rs: seq U64.t) (#g: heap) (#fp: U64.t) (#sp: MP.scan_pos)
                     (#since: obj_addr -> prop) (r: marking g0 rs g fp sp since)
  : Lemma (ensures mark_run_inv g0 rs since g sp)

/// **When marking ends, the black objects are the snapshot's**: after the
/// slice that hands over to the sweep (nothing grey left), every object
/// reachable when the cycle started is black, at the size it had, and every
/// black object is in the snapshot.
val handover (#g0: heap) (#rs: seq U64.t) (#g: heap) (#fp: U64.t) (#sp: MP.scan_pos)
             (#since: obj_addr -> prop) (r: marking g0 rs g fp sp since)
             (minor: minor_state) (budget: nat) (gh: heap) (sp': MP.scan_pos)
  : Lemma (requires GI.phase_shape minor g fp Ph.Marking sp /\
                    GI.mark_slice_post g sp fp budget gh sp' fp (Ph.Sweeping zero_addr))
          (ensures (forall (x: obj_addr). GMC.reachable_at_start g0 rs x ==>
                      SPC.survived_mark gh x /\ wosize_of_object x gh == wosize_of_object x g0) /\
                   (forall (x: obj_addr). SPC.survived_mark gh x ==> snapshot g0 rs since x) /\
                   (forall (x: obj_addr). since x ==> ~(GMC.reachable_at_start g0 rs x)))
