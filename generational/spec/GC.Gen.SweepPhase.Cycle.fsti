/// ---------------------------------------------------------------------------
/// GC.Gen.SweepPhase.Cycle - a run of the sweep phase, and what it frees
/// ---------------------------------------------------------------------------
///
/// The completeness of the sweep phase (`GC.Spec.SweepPhase.Completeness`)
/// is stated for a set of new addresses `since` given as an argument, and
/// the set of every address satisfies it.  This module fixes `since` by the
/// run.  `cycle g0 g fp ph since` is a run of the sweep phase from the marked
/// heap `g0` to the heap `g`, free-list head `fp` and phase `ph`: it starts
/// from `g0` with nothing new, and each event of the phase is a constructor,
/// with that event's preconditions as its hypotheses and the set of new
/// addresses after it fixed by the event:
///
///   * `Slice`: a slice at the sweep's phase -- `since` unchanged;
///   * `Alloc`: an allocation -- `since` and the object the allocator
///     returned (`with_new`);
///   * `Write`: a write into the body of a block that is not blue (a program
///     write, or the initialisation of a fresh object) -- `since` unchanged;
///   * `Minor`: a minor collection -- `since` and the blocks it made non-free
///     (`with_made`), which are its promoted copies
///     (`SPC.made_by_minor_promoted`).
///
/// `since` is an index of the run, so it is the addresses the run's
/// allocations and promotions handed out, and no others.  The events other
/// than a slice need the sweep's phase, so a run reaches `Idle` exactly by
/// the slice that ends the sweep and stops there.
///
/// **The sweep phase is lossless, up to what the run handed out**
/// (`cycle_lossless`): once a run is idle, a word was in a non-black block
/// of the marked heap (dead, or already free) exactly when it lies in a free
/// block, or in a block the run allocated or promoted.  With no allocation
/// and nothing promoted this is the stop-the-world clause of
/// `GC.Spec.FusedSweep.Lossless.sweep_lossless`, `blue_covered g p <==>
/// dead_covered g0 p`.  Its two halves are completeness (`cycle_covered`,
/// and `cycle_unreachable_covered` for dead read as unreachable) and its
/// converse; each alone is weak in `since` (completeness holds of every
/// address, the converse of none), and the run pins `since`.  Every state of
/// a run carries the account and its converse (`cycle_account`).
///
/// The run is here, with the generational spec, because the minor
/// collection is one of its events.

module GC.Gen.SweepPhase.Cycle

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.SweepPhase.Intrinsic
open GC.Spec.SweepPhase.Completeness
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Mark = GC.Spec.Mark
module Mut = GC.Spec.SweepPhase.Mutator
module SL = GC.Spec.SweepPhase.Slice
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator
module Corr = GC.Spec.Correctness
module Ph = GC.Spec.Phase
module LL = GC.Spec.FusedSweep.Lossless
module GenInv = GC.Gen.HeapInvariant
module Promote = GC.Gen.Promote
module SPM = GC.Gen.SweepPhase.Minor
module SPC = GC.Gen.SweepPhase.Completeness

/// **A run of the sweep phase** from the marked heap `g0`, to the heap `g`,
/// free-list head `fp` and phase `ph`, with `since` the addresses its
/// allocations and promotions handed out.
noeq type cycle (g0: heap) : heap -> U64.t -> Ph.gc_phase -> (obj_addr -> prop) -> Type =
  // The sweep starts at the marked heap: nothing grey, the tri-colour
  // invariant, and the sweep's precondition.
  | Start :
      fp0: U64.t ->
      squash (sweep_pre g0 fp0 /\ Mark.noGreyObjects g0 /\ Mark.tri_color_invariant g0) ->
      cycle g0 g0 fp0 (Ph.Sweeping sweep_start.cursor) nothing_new
  // A slice of `budget` words, on the sweep phase; idle if it ends the sweep.
  | Slice :
      #g: heap -> #fp: U64.t -> #c: U64.t -> #since: (obj_addr -> prop) ->
      cycle g0 g fp (Ph.Sweeping c) since ->
      budget: nat -> g': heap -> fp': U64.t -> ph': Ph.gc_phase ->
      squash (sweep_inv_incremental g fp c /\
              (g', fp', ph') == SL.phase_slice g fp (Ph.Sweeping c) budget) ->
      cycle g0 g' fp' ph' since
  // An allocation at the sweep's phase; the object it returns is new.
  | Alloc :
      #g: heap -> #fp: U64.t -> #c: U64.t -> #since: (obj_addr -> prop) ->
      cycle g0 g fp (Ph.Sweeping c) since ->
      wz: nat -> tag: Mut.tag_t -> g': heap -> fp': U64.t -> obj: U64.t ->
      squash (sweep_shape g fp c /\
              (let r = AC.alloc_phase g fp (SA.Sweeping c) wz tag in
               g' == r.SA.heap_out /\ fp' == r.SA.fp_out /\ obj == r.SA.obj_out)) ->
      cycle g0 g' fp' (Ph.Sweeping c) (with_new since obj)
  // A write of `v` at `a`, in the body of the block `x` that is not blue.
  | Write :
      #g: heap -> #fp: U64.t -> #c: U64.t -> #since: (obj_addr -> prop) ->
      cycle g0 g fp (Ph.Sweeping c) since ->
      x: obj_addr -> a: hp_addr -> v: U64.t -> g': heap ->
      squash (sweep_shape g fp c /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\
              Mut.in_body g x a /\ g' == write_word g a v) ->
      cycle g0 g' fp (Ph.Sweeping c) since
  // A minor collection of the nursery `minor` from `roots`, on the sweep
  // phase; its promoted copies are new.
  | Minor :
      #g: heap -> #fp: U64.t -> #c: U64.t -> #since: (obj_addr -> prop) ->
      cycle g0 g fp (Ph.Sweeping c) since ->
      minor: minor_state -> roots: seq U64.t -> g': heap -> fp': U64.t ->
      squash (sweep_inv_incremental g fp c /\
              GenInv.minor_heap_shape minor /\
              GenInv.minor_major_fields_not_free (free_incremental c) minor g /\
              (let res = SPM.collect_at c minor g fp roots in
               g' == res.Promote.mc_major /\ fp' == res.Promote.mc_fp)) ->
      cycle g0 g' fp' (Ph.Sweeping c) (SPC.with_made since c g g')

/// The account and its converse a run carries: mid-sweep, at the cursor;
/// idle, for the blue blocks.
let cycle_inv (g0: heap) (since: obj_addr -> prop) (g: heap) (ph: Ph.gc_phase) : prop =
  match ph with
  | Ph.Sweeping c -> survivor_or_new g0 since g c /\ reclaimed_was_dead g0 since (free_incremental c) g
  | Ph.Idle -> idle_account g0 since g /\ reclaimed_was_dead g0 since free_stw g

/// **Every state of a run carries the account.**
val cycle_account (#g0 #g: heap) (#fp: U64.t) (#ph: Ph.gc_phase) (#since: obj_addr -> prop)
                  (r: cycle g0 g fp ph since)
  : Lemma (ensures cycle_inv g0 since g ph)

/// **The sweep phase is lossless, up to what the run handed out**: once a
/// run is idle, a word of the heap was in a non-black block of the marked
/// heap exactly when it lies in a free block, or in a block the run
/// allocated or promoted.
val cycle_lossless (#g0 #g: heap) (#fp: U64.t) (#since: obj_addr -> prop)
                   (r: cycle g0 g fp Ph.Idle since)
  : Lemma (ensures forall (p: nat). p < heap_size ==>
                     (LL.dead_covered g0 p <==> LL.blue_covered g p \/ new_covered since g p))

/// **Completeness of a run**: once it is idle, every word of a non-black
/// block of the marked heap lies in a free block, or in a block the run
/// allocated or promoted.
val cycle_covered (#g0 #g: heap) (#fp: U64.t) (#since: obj_addr -> prop)
                  (r: cycle g0 g fp Ph.Idle since)
  : Lemma (ensures forall (p: nat). LL.dead_covered g0 p ==> free_or_new_at g since p)

/// The same with dead at mark read as unreachable from the roots when
/// marking ended.
val cycle_unreachable_covered (h_init: heap) (roots: seq obj_addr) (fp0: U64.t)
                              (#h_mark #g: heap) (#fp: U64.t) (#since: obj_addr -> prop)
                              (r: cycle h_mark g fp Ph.Idle since)
  : Lemma (requires Corr.mark_post h_init h_mark roots fp0 /\ roots_in_graph h_init roots)
          (ensures forall (x: obj_addr) (p: nat).
                     dead_at_mark h_init h_mark roots x /\ LL.in_extent h_mark x p ==>
                     free_or_new_at g since p)
