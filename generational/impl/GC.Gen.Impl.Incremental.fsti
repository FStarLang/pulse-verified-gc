(*
   Pulse GC (Generational) - the incremental sweep's entry points

   With `VERGC_SWEEP=incremental` a full collection is a minor collection and
   marking (`gen_gc_start`), after which the sweep runs in slices
   (`sweep_slice`) between program steps; a minor collection may run in
   between (`minor_collect_any_phase`), and so may major allocation
   (`gen_alloc_major`).  `finish_sweep` runs the rest of the sweep at once:
   before a full collection (a full collection requested mid-sweep finishes
   the sweep first) and on allocation failure.  The stop-the-world collector
   (`GC.Gen.Impl.gen_gc`) is unchanged.

   The collector's state is handed from one call to the next through
   `gc_state`, indexed by the phase (`GC.Gen.Incremental.phase_shape`): the
   stop-the-world shape when idle, the sweep phase mid-sweep.
*)

module GC.Gen.Impl.Incremental

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Phase
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Impl.MinorHeap
open GC.Impl.Heap
open GC.Impl.Stack
open GC.Gen.Impl
module SpecFields = GC.Spec.Fields
module CheneySpec = GC.Gen.Cheney
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module SpecGCPost = GC.Spec.Correctness
module Cheney = GC.Gen.Impl.Cheney
module GenInv = GC.Gen.HeapInvariant
module MinorFwd = GC.Gen.MinorCollectForwarding
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module CheneyBFS = GC.Gen.CheneyBFS
module RT = GC.Gen.RefTable
module Alloc = GC.Impl.Allocator
module Ph = GC.Spec.Phase
module FS = GC.Spec.FusedSweep
module SPI = GC.Spec.SweepPhase.Intrinsic
module SL = GC.Spec.SweepPhase.Slice
module GI = GC.Gen.Incremental
module GSP = GC.Gen.SweepPhase
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator

/// ---------------------------------------------------------------------------
/// The collector's state
/// ---------------------------------------------------------------------------

/// The generational heap, the collector's phase (its record's caches derived
/// from the major heap, `gen_phase`), and the collector's state at that phase
/// (`GI.phase_shape`):
///
///   * `Ph.Idle`: `GenInv.collection_heap_shape` of the nursery, the major
///     heap and the free-list head -- what `gen_gc` demands and restores;
///   * `Ph.Sweeping c`: the sweep phase at the cursor `c`
///     (`SPI.sweep_inv_incremental s fp c`), the nursery's shape, and that the
///     nursery's major pointers point at non-free objects
///     (`GenInv.minor_major_fields_not_free` for `SPI.free_incremental c`:
///     free is blue, or pending free -- white in front of the cursor).
let gc_state (gh: gen_heap_t) (d: minor_heap) (b: U64.t) (s: heap_state) (fp: U64.t)
             (ph: Ph.gc_phase) : slprop =
  is_gen_heap gh d b s fp ** gen_phase gh s ph **
  pure (GI.phase_shape ({ data = d; bump = b } <: minor_state) s fp ph)

/// ---------------------------------------------------------------------------
/// What the runtime supplies (trusted bridge obligations)
/// ---------------------------------------------------------------------------
///
/// Each entry point below is a separate call from C, and the separation-logic
/// state does not survive between calls: the bridge re-supplies `gc_state`'s
/// pure half at every call, as it supplies `collection_heap_shape` to
/// `gen_gc` today.  What justifies it is that every collector call returns
/// it, and the program's events in between keep it:
///
///   * **Allocation mid-sweep** (`gen_alloc_major`, or the allocator called
///     directly): the new object is *fresh* (`GSP.fresh_ok`: the sweep phase
///     except that its fields are uninitialised and nothing points at it).
///     The runtime initialises every field of a block it allocates with a
///     storable value (an integer, or a pointer to a non-free object --
///     reachable objects are never pending free) before the
///     next collector call; `GSP.fresh_write` and `GSP.fresh_close` then give
///     back the sweep phase.  Idle, the obligation is today's: the fields are
///     initialised before the next collection.
///   * **Field writes** (`caml_modify`, `caml_initialize`): `GSP.program_write`
///     -- a word of the body of a non-free object that is not a closure, and
///     a value that is not a pointer or points at a non-free object.
///     `GSP.write_sweep_phase` keeps the sweep phase.  The write barrier
///     records every major field that gets a nursery pointer (the remembered
///     set below).
///   * **Nursery allocation** keeps the nursery's shape and the
///     cross-generation condition (as today, mid-sweep for `free_incremental`).
///   * **The minor collection's arguments** (`minor_slots_ok`): the
///     forwarding array zeroed, the remembered set sound and covering for the
///     phase's definition of free (`RT.ref_table_sound_with`,
///     `RT.ref_table_covers_with` for `GI.phase_free`), its slots distinct,
///     the remembered targets among the roots, and the roots valid and not free (never pending free).
///   * **The phase record** (`gh.phase_ref`) is written only by the collector
///     and the allocator.

/// The minor collection's arguments, for the phase's definition of free.
let minor_slots_ok (ph: Ph.gc_phase) (minor_st: minor_state) (s: heap_state)
    (rs farr sl: Seq.seq U64.t) (nslots: nat) : prop =
  let free = GI.phase_free ph in
  Seq.length farr == GC.Gen.ForwardingArray.fwd_array_size /\
  (forall (i: nat). i < Seq.length farr ==> Seq.index farr i == 0UL) /\
  RT.ref_table_sound_with free s sl nslots /\
  RT.ref_table_covers_with free s sl nslots /\
  RT.slots_pairwise_distinct sl nslots /\
  MinorFwd.remembered_targets_in_roots s rs sl nslots /\
  MinorFwd.roots_valid_with free minor_st s rs

/// ---------------------------------------------------------------------------
/// Sweeping
/// ---------------------------------------------------------------------------

/// **One slice of the sweep**: whole sweep steps until the blocks swept add
/// up to at least `budget` words (headers included; at most one block over),
/// or the sweep is finished.  The heap, free-list head and phase are exactly
/// the spec's slice (`SL.phase_slice`: some number of sweep steps, keeping
/// the sweep phase, `SL.sweep_slice_phase`); when the sweep finishes the
/// phase is `Idle` and the state is the stop-the-world shape again
/// (`GI.sweep_end_shape`).  Idle, it does nothing.  Returns whether the
/// phase it leaves is `Idle`.
fn sweep_slice (gh: gen_heap_t) (budget: U64.t)
  requires gc_state gh 'd 'b 's 'fp 'ph
  returns fin: bool
  ensures exists* s2 fp2 ph2.
    gc_state gh 'd 'b s2 fp2 ph2 **
    pure ((s2, fp2, ph2) == SL.phase_slice 's 'fp 'ph (U64.v budget) /\
          fin == Ph.Idle? ph2)

/// **Finish the sweep**: a slice with an unbounded budget.  It leaves the
/// collector idle, in the stop-the-world shape.
fn finish_sweep (gh: gen_heap_t)
  requires gc_state gh 'd 'b 's 'fp 'ph
  ensures exists* s2 fp2.
    gc_state gh 'd 'b s2 fp2 Ph.Idle **
    pure ((s2, fp2, Ph.Idle) == SL.phase_slice 's 'fp 'ph (pow2 64 - 1) /\
          GenInv.collection_heap_shape ({ data = 'd; bump = 'b } <: minor_state) s2 fp2)

/// ---------------------------------------------------------------------------
/// A minor collection at either phase
/// ---------------------------------------------------------------------------

/// **`minor_collect_full` at the collector's phase**, for the phase's
/// definition of free (`GI.phase_free`: `free_stw` idle, `free_incremental c`
/// mid-sweep): its contract (`minor_collect_post_with`, at the phase), and
/// the collector's state at the same phase -- idle stays idle; mid-sweep the
/// sweep keeps its cursor and the objects pending free
/// (`GI.minor_keeps_phase_shape`).  The C is `minor_collect_full`'s.
fn minor_collect_any_phase (gh: gen_heap_t)
                           (roots: array U64.t) (nroots: SZ.t)
                           (fwd_arr: array U64.t)
                           (queue: larray U64.t GC.Gen.ForwardingArray.queue_size)
                           (slots: array U64.t) (nslots: SZ.t)
  requires gc_state gh 'd 'b 's 'fp 'ph **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           pts_to slots 'sl **
           pure (SZ.v nroots == Seq.length 'rs /\
                 minor_slots_ok 'ph ({ data = 'd; bump = 'b } <: minor_state) 's
                   'rs 'farr 'sl (SZ.v nslots))
  returns ok: bool
  ensures exists* d2 b2 s2 fp2 rs2 farr2 qv2.
    gc_state gh d2 b2 s2 fp2 'ph **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pts_to slots 'sl **
    pure (minor_collect_post_with 'ph (GI.phase_free 'ph) ({ data = 'd; bump = 'b } <: minor_state)
            's 'fp 'rs ok d2 b2 s2 fp2 rs2)

/// ---------------------------------------------------------------------------
/// Major allocation at either phase
/// ---------------------------------------------------------------------------

/// What a major allocation gives: the allocator's spec at the phase
/// (`AC.alloc_phase`; idle, `alloc_spec`), and mid-sweep, from the collector's
/// state: either nothing changed (no block fits) or the new object is
/// `GSP.new_block` and *fresh* (`GSP.fresh_ok`) at the same cursor: the
/// runtime initialises its fields before the next collector call (see above).
let alloc_major_post (ph: Ph.gc_phase) (minor: minor_state) (s: heap_state) (fp: U64.t)
    (wz: nat) (tag: GSP.tag_t) (obj: U64.t) (s2: heap_state) (fp2: U64.t) : prop =
  let ar = AC.alloc_phase s fp ph wz tag in
  s2 == ar.SA.heap_out /\ fp2 == ar.SA.fp_out /\ obj == ar.SA.obj_out /\
  (forall (c: U64.t).
     ph == Ph.Sweeping c /\ GI.phase_shape minor s fp ph /\ tag <> GC.Spec.Object.infix_tag ==>
     (obj == 0UL ==> s2 == s /\ fp2 == fp /\ GI.phase_shape minor s2 fp2 ph) /\
     (obj <> 0UL ==> GSP.new_block s s2 c obj wz tag /\ GSP.fresh_ok s2 fp2 c (obj <: obj_addr)))

/// **Allocate in the major heap** at the collector's phase (`caml_alloc_shr`):
/// the free-list head is updated in place, and the phase stays as it is (its
/// record's cached `swept_tail` follows the allocation).  Mid-sweep the free
/// list is exact and ascending (as `GSP.fresh_ok` and the sweep phase say).
/// Returns the object, or 0 when no free block fits.
fn gen_alloc_major (gh: gen_heap_t) (wosize: U64.t) (tag: GSP.tag_t)
  requires is_gen_heap gh 'd 'b 's 'fp ** gen_phase gh 's 'ph **
           pure (U64.v wosize >= 1 /\
                 (Ph.Sweeping? 'ph ==> GC.Spec.FreeList.Ascending.fl_ascending 's 'fp))
  returns obj: U64.t
  ensures exists* s2 fp2.
    is_gen_heap gh 'd 'b s2 fp2 ** gen_phase gh s2 'ph **
    pure (alloc_major_post 'ph ({ data = 'd; bump = 'b } <: minor_state) 's 'fp
            (U64.v wosize) tag obj s2 fp2)

/// ---------------------------------------------------------------------------
/// Starting the sweep phase
/// ---------------------------------------------------------------------------

/// What `gen_gc_start` guarantees.  On success the major heap is the marked
/// heap (`SpecGCPost.mark_post` of the heap the minor collection and root
/// darkening produced: every object reachable from the darkened roots is
/// black, everything else white or free, nothing grey, and the objects and
/// their fields are unchanged), the phase is the start of the sweep, and the
/// minor collection is a reachable-subgraph isomorphism, as in `gen_gc`.
/// When promotion runs out of memory the major phase is skipped, as in
/// `gen_gc`: the heap is the post-minor one and the phase stays idle.
let gen_gc_start_post
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  (ok: bool) (s2: heap) (fp2: U64.t) (ph2: Ph.gc_phase) (roots_out: Seq.seq U64.t)
  (st: Seq.seq obj_addr) (cap: nat) : prop =
  let result = CheneySpec.cheney_collect_spec minor major fp roots in
  let prepared = gen_gc_prepared_state minor major fp roots st cap in
  fp2 == result.mc_fp /\
  (not ok ==> CheneyBFS.cheney_oom Idle minor major fp roots /\ s2 == result.mc_major /\ ph2 == Ph.Idle) /\
  (ok ==>
   ph2 == Ph.Sweeping zero_addr /\
   SpecGCPost.mark_post (fst prepared) s2 (snd prepared) fp2 /\
   MinorFwd.normal_result_reachable_subgraph_isomorphism_prop Idle
     minor major fp SpecFields.free_stw roots result.mc_major
     (MCFH.resolve_roots result.mc_major roots_out) /\
   MinorFwd.normal_result_non_pointer_fields_preserved_prop Idle
     minor major fp SpecFields.free_stw roots result.mc_major)

/// **Start a major collection**: `gen_gc`'s minor collection, root darkening
/// and marking, and then -- instead of sweeping -- the start of the sweep
/// phase (`phase = Sweeping zero_addr`, the cursor at the first block).  The
/// arguments and their preconditions are `gen_gc`'s.
fn gen_gc_start (gh: gen_heap_t)
                (roots: array U64.t) (nroots: SZ.t)
                (fwd_arr: array U64.t)
                (queue: larray U64.t GC.Gen.ForwardingArray.queue_size)
                (slots: array U64.t) (nslots: SZ.t)
                (st: gray_stack)
  requires gc_state gh 'd 'b 's 'fp Ph.Idle **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           pts_to slots 'sl **
           is_gray_stack st 'st **
           pure (gen_gc_stack_budget 'rs 'st (stack_capacity st) /\
                 SZ.v nroots == Seq.length 'rs /\
                 Seq.length 'farr == GC.Gen.ForwardingArray.fwd_array_size /\
                 (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\
                 RT.ref_table_sound 's 'sl (SZ.v nslots) /\
                 RT.ref_table_covers_minor_ptrs 's 'sl (SZ.v nslots) /\
                 RT.slots_pairwise_distinct 'sl (SZ.v nslots) /\
                 MinorFwd.remembered_targets_in_roots 's 'rs 'sl (SZ.v nslots) /\
                 MinorFwd.roots_valid_for_minor_collection
                   ({ data = 'd; bump = 'b } <: minor_state) 's 'rs)
  returns ok: bool
  ensures exists* d2 b2 s2 fp2 ph2 rs2 farr2 qv2 st2.
    gc_state gh d2 b2 s2 fp2 ph2 **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pts_to slots 'sl **
    is_gray_stack st st2 **
    pure (let minor_st : minor_state = { data = 'd; bump = 'b } in
          ({ data = d2; bump = b2 } <: minor_state) == minor_reset minor_st /\
          gen_gc_roots_post minor_st 's 'fp 'rs rs2 ok 'st (stack_capacity st) /\
          gen_gc_start_post minor_st 's 'fp 'rs ok s2 fp2 ph2 rs2 'st (stack_capacity st))
