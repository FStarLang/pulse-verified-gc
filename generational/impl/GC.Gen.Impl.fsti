(*
   Pulse GC (Generational) - Top-Level Entry Point Interface

   Provides:
   - gc_state: the collector's state at its phase, which every entry point
     states its contract over
   - minor_collect: the minor collection, at the collector's phase (the
     generic minor_collect_with underneath, for any phase and definition of
     free)
   - start_cycle: start a major cycle (darken the roots, mark, start the
     sweep phase)
   - major_slice: one slice of the major cycle, at the collector's phase
   - full_gc: a whole collection (minor_collect, start_cycle, slices until
     idle)
*)

module GC.Gen.Impl

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Phase
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Impl.MinorHeap
open GC.Impl.Heap
open GC.Impl.Stack
module SpecFields = GC.Spec.Fields
module AllocLemmas = GC.Spec.Allocator.Lemmas
module CheneySpec = GC.Gen.Cheney
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module PromoteSpec = GC.Gen.Promote
module MajorGC = GC.Impl
module MarkBoundedImpl = GC.Impl.MarkBounded
module MBP = GC.Impl.MarkBoundedPrecondition
module SpecObject = GC.Spec.Object
module GMP = GC.Gen.MajorPrecondition
module MarkBoundedInv = GC.Spec.MarkBoundedInv
module SpecGCPost = GC.Spec.Correctness
module Mark = GC.Spec.Mark
module Cheney = GC.Gen.Impl.Cheney
module GenInv = GC.Gen.HeapInvariant
module MinorFwd = GC.Gen.MinorCollectForwarding
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module RBridge = GC.Gen.ReachabilityBridge
module CheneyBFS = GC.Gen.CheneyBFS
module SpecHeapModel = GC.Spec.HeapModel
module MRT = GC.Gen.MajorReachabilityTransfer
module RT = GC.Gen.RefTable
module CV = GC.Gen.CheneyGeneric
module Alloc = GC.Impl.Allocator
module Ph = GC.Spec.Phase
module ST = GC.Gen.SweptTail

module FA = GC.Gen.ForwardingArray
module GI = GC.Gen.Incremental

/// ---------------------------------------------------------------------------
/// Combined generational heap state
/// ---------------------------------------------------------------------------

noeq
type gen_heap_t = {
  minor : minor_heap_t;
  major : heap_t;
  fp_ref : R.ref U64.t;    // major heap free-list head
  phase_ref : R.ref Alloc.phase_state;  // the major collector's phase
}

/// The major collector's phase, held in `gh.phase_ref`, with the sweep's
/// caches beside the cursor the ones derived from the major heap `g`
/// (`Alloc.is_phase`).  It is kept apart from `is_gen_heap`: only the
/// allocator and the major collector read it.  `minor_collect` runs at any
/// phase (its promotions are allocated at it); `start_cycle` and `full_gc`
/// run outside a sweep (`Ph.Idle`).
let gen_phase (gh: gen_heap_t) (g: heap_state) (ph: Ph.gc_phase) : slprop =
  Alloc.is_phase gh.phase_ref g ph

/// Combined slprop for the generational heap:
///   is_minor — ownership of minor heap array + bump pointer
///   is_heap  — ownership of major heap array
///   R.pts_to — ownership of the free-list head reference
let is_gen_heap (gh: gen_heap_t) (d: minor_heap) (b: U64.t)
                (s: heap_state) (fp: U64.t) : slprop =
  is_minor gh.minor d b **
  is_heap gh.major s **
  R.pts_to gh.fp_ref fp

/// ---------------------------------------------------------------------------
/// The collector's state
/// ---------------------------------------------------------------------------

/// The generational heap, the collector's phase (its record's caches derived
/// from the major heap, `gen_phase`), and the collector's state at that phase
/// (`GI.phase_shape`):
///
///   * `Ph.Idle`: `GenInv.collection_heap_shape` of the nursery, the major
///     heap and the free-list head -- what a full collection demands and
///     restores;
///   * `Ph.Sweeping c`: the sweep phase at the cursor `c`
///     (`SPI.sweep_inv_incremental s fp c`), the nursery's shape, and that the
///     nursery's major pointers point at non-free objects
///     (`GenInv.minor_major_fields_not_free` for `SPI.free_incremental c`:
///     free is blue, or pending free -- white in front of the cursor).
///
/// Every entry point states its contract over it.
let gc_state (gh: gen_heap_t) (d: minor_heap) (b: U64.t) (s: heap_state) (fp: U64.t)
             (ph: Ph.gc_phase) : slprop =
  is_gen_heap gh d b s fp ** gen_phase gh s ph **
  pure (GI.phase_shape ({ data = d; bump = b } <: minor_state) s fp ph)

/// The mark stack handed to the major collector holds exactly the objects the
/// root array names in `g`.
///
/// "Names" rather than "is": a root may be an interior (infix) pointer, in
/// which case it names the closure it points into.  `SpecObject.resolve_object`
/// performs that step and is the identity on ordinary pointers, so for a root
/// set free of interior pointers this says exactly `roots == st` as sets.
let roots_match_stack (g: heap) (roots: Seq.seq U64.t) (st: Seq.seq obj_addr) : prop =
  (forall (r: U64.t). Seq.mem r roots ==> GC.Spec.Base.is_val_addr r) /\
  (forall (r: obj_addr). Seq.mem (r <: U64.t) roots ==>
     Seq.mem (SpecObject.resolve_object r g) st) /\
  (forall (r: obj_addr). Seq.mem r st ==> MBP.root_named g roots r)

let gen_gc_prepared_state
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  (st: Seq.seq obj_addr) (cap: nat) : GTot (heap & Seq.seq obj_addr) =
  let result = CheneySpec.cheney_collect_spec minor major fp roots in
  MarkBoundedImpl.darken_roots_bounded_spec result.mc_major st result.mc_roots cap

let gen_gc_prepared_major
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  (st: Seq.seq obj_addr) (cap: nat) : GTot heap =
  fst (gen_gc_prepared_state minor major fp roots st cap)

let gen_gc_prepared_roots
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  (st: Seq.seq obj_addr) (cap: nat) : GTot (Seq.seq obj_addr) =
  snd (gen_gc_prepared_state minor major fp roots st cap)

/// What the caller owes the collector about the gray stack it supplies.
///
/// This is the whole of it.  There is no heap in the statement: the major
/// phase's entry condition is derived internally by `GC.Gen.MajorPrecondition`
/// from `collection_heap_shape`, `roots_valid_for_minor_collection` and the
/// *runtime* success flag of the minor collection.
///
///  * `Seq.length st == 0` -- the gray stack starts empty.  It is collector
///    scratch space, not caller state, and both real clients pass an empty one.
///  * `Seq.length roots <= cap` -- darkening pushes every root, so the stack has
///    to be able to hold them.  This is the only sizing obligation.
///  * `cap > 0` rules out a zero-capacity stack.
///
/// In particular the caller does *not* have to establish `cheney_no_oom`.  An
/// earlier version did require it, which was indefensible: it is a statement
/// about the outcome of the entire Cheney BFS, no caller can discharge it, and
/// `full_gc` reports promotion failure through its `ok` result anyway.  `full_gc`
/// now consumes the runtime flag instead and simply skips the major phase when
/// the minor collection ran out of memory.
let gen_gc_stack_budget
  (roots: Seq.seq U64.t) (st: Seq.seq obj_addr) (cap: nat) : prop =
  Seq.length st == 0 /\
  Seq.length roots <= cap /\
  cap > 0

/// Everything the major phase needs, from pre-minor shape facts plus the
/// minor collection's own success flag.
val gen_gc_major_precondition_elim
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  (st: Seq.seq obj_addr) (cap: nat)
  : Lemma
      (requires
        GenInv.collection_heap_shape minor major fp /\
        MinorFwd.roots_valid_for_minor_collection minor major roots /\
        CheneyBFS.cheney_no_oom Idle minor major fp roots /\
        gen_gc_stack_budget roots st cap)
      (ensures
        (let result = CheneySpec.cheney_collect_spec minor major fp roots in
         let prepared = gen_gc_prepared_state minor major fp roots st cap in
         MajorGC.gc_precondition_with_roots
           (fst prepared) (snd prepared) (snd prepared) result.mc_fp cap /\
         roots_match_stack result.mc_major result.mc_roots (snd prepared) /\
         (forall (r: U64.t). Seq.mem r result.mc_roots ==>
            GC.Spec.Base.is_val_addr r /\
            U64.v r >= U64.v zero_addr + U64.v mword) /\
         /// The darkened stack holds the objects the rewritten roots *name*.
         /// For an interior root that is the closure it points into, not the
         /// root value itself, so this cannot be stated on `result.mc_roots`.
         (forall (e: U64.t).
            Seq.mem e (MCFH.resolve_roots result.mc_major result.mc_roots) ==>
            GC.Spec.Base.is_val_addr e) /\
         (forall (e: obj_addr).
            Seq.mem (e <: U64.t)
                    (MCFH.resolve_roots result.mc_major result.mc_roots) ==>
            Seq.mem e (snd prepared)) /\
         SpecHeapModel.create_graph (fst prepared) ==
           SpecHeapModel.create_graph result.mc_major))

/// The roots array contains exactly the post-minor roots used by the following
/// major collection.
/// The array is rewritten by the minor collection unconditionally; the match
/// with the darkened mark stack only holds on the path where the major phase
/// actually ran.
let gen_gc_roots_post
  (minor: minor_state) (major: heap) (fp: U64.t) (roots roots_out: Seq.seq U64.t)
  (ok: bool) (st: Seq.seq obj_addr) (cap: nat) : prop =
  let result = CheneySpec.cheney_collect_spec minor major fp roots in
  roots_out == result.mc_roots /\
  (ok ==>
   roots_match_stack (CheneySpec.cheney_collect_spec minor major fp roots).mc_major
                     roots_out (gen_gc_prepared_roots minor major fp roots st cap) /\
   (forall (r: U64.t). Seq.mem r roots_out ==>
      GC.Spec.Base.is_val_addr r /\ U64.v r >= U64.v zero_addr + U64.v mword) /\
   /// The mark stack holds the objects the roots *name*: an interior root
   /// pushes the closure it points into rather than itself.
   (forall (e: U64.t).
      Seq.mem e (MCFH.resolve_roots result.mc_major roots_out) ==>
      GC.Spec.Base.is_val_addr e) /\
   (forall (e: obj_addr).
      Seq.mem (e <: U64.t) (MCFH.resolve_roots result.mc_major roots_out) ==>
      Seq.mem e (gen_gc_prepared_roots minor major fp roots st cap)))

/// A root that names *itself* --- i.e. one that is not an interior pointer ---
/// is on the darkened mark stack literally, not merely up to resolution.
/// This is the shape most callers want: `gen_gc_roots_post` speaks about the
/// resolved sequence so that interior roots have somewhere to go, and this
/// lemma reads the ordinary case straight back out of it.
val gen_gc_named_root_in_stack
  (minor: minor_state) (major: heap) (fp: U64.t) (roots roots_out: Seq.seq U64.t)
  (st: Seq.seq obj_addr) (cap: nat) (r: obj_addr)
  : Lemma
    (requires
      gen_gc_roots_post minor major fp roots roots_out true st cap /\
      Seq.mem (r <: U64.t) roots_out /\
      SpecObject.resolve_object r
        (CheneySpec.cheney_collect_spec minor major fp roots).mc_major == r)
    (ensures Seq.mem r (gen_gc_prepared_roots minor major fp roots st cap))

/// The free-list-free projection of the shape invariant.
///
/// This is **not** an independent fact: every conjunct is a consequence of
/// `GC.Gen.HeapInvariant.collection_heap_shape`, which is what `full_gc` actually
/// promises: `gc_postcondition` -- well-formedness plus "every object is white
/// or blue" -- follows from three of `major_heap_shape`'s conjuncts
/// (`well_formed_heap`, `no_black_objects`, `no_gray_objects`) by colour
/// exhaustiveness.  `gen_gc_heap_shape_post_intro` below is that derivation.
///
/// It is kept because it mentions no free-list head, so a client that only
/// cares about object colours can state it without threading `fp` through.
/// That is exactly what the SPOT audit lemmas want.
let gen_gc_heap_shape_post
  (minor_data: minor_heap) (minor_bump: U64.t)
  (final_major: heap) : prop =
  U64.v minor_bump == 0 /\
  SpecGCPost.gc_postcondition final_major

/// Recover the projection from the invariant `full_gc` returns.
val gen_gc_heap_shape_post_intro
  (minor_data: minor_heap) (minor_bump: U64.t)
  (final_major: heap) (final_fp: U64.t)
  : Lemma
      (requires
        U64.v minor_bump == 0 /\
        GenInv.collection_heap_shape
          ({ data = minor_data; bump = minor_bump } <: minor_state)
          final_major final_fp)
      (ensures gen_gc_heap_shape_post minor_data minor_bump final_major)

/// Reachable subgraph correctness.
///
/// The headline conjunct is a *single* isomorphism between the reachable
/// subgraph of the heap `full_gc` was handed and the reachable subgraph of the
/// heap it returns, with the minor collector's forwarding map as the morphism.
/// Earlier versions exposed only the two halves -- minor collection into the
/// post-minor heap, then major collection out of the post-darkening heap --
/// and left the caller to chain them.  That was not something a caller could
/// actually do: the halves are stated in different vocabularies, root darkening
/// sits between them, and transferring reachability backwards out of the final
/// heap needs the major collector's successor-preservation clause.  All of that
/// is now discharged once, inside `GC.Gen.MajorReachabilityTransfer`.
///
/// The two intermediate facts are kept because they say things the composition
/// cannot: the minor step says *where* each non-free object went, and the
/// major step says the survivors did not move again and are white.
let gen_gc_reachable_subgraph_isomorphism_post
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  (ok: bool) (final_major: heap) (roots_out: Seq.seq U64.t)
  (st: Seq.seq obj_addr) (cap: nat) : prop =
  let result = CheneySpec.cheney_collect_spec minor major fp roots in
  let prepared = gen_gc_prepared_state minor major fp roots st cap in
  (ok ==>
   MRT.end_to_end_isomorphism minor major fp roots final_major
     (MCFH.resolve_roots result.mc_major roots_out) /\
   MinorFwd.normal_result_reachable_subgraph_isomorphism_prop Idle
     minor major fp SpecFields.free_stw roots result.mc_major
     (MCFH.resolve_roots result.mc_major roots_out) /\
   MinorFwd.normal_result_non_pointer_fields_preserved_prop Idle
     minor major fp SpecFields.free_stw roots result.mc_major /\
   SpecGCPost.major_gc_live_subgraph_isomorphism
     (fst prepared) final_major (snd prepared))

/// Collection completeness: every object that remains in the final major heap
/// but is not reachable from the final roots is blue.
/// Only the sweep makes unreachable objects blue, so this is guarded on `ok`:
/// on the out-of-memory path the returned heap is the (unswept) post-minor heap.
let gen_gc_unreachable_final_blue_post
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  (ok: bool) (final_major: heap) (st: Seq.seq obj_addr) (cap: nat) : prop =
  let prepared = gen_gc_prepared_state minor major fp roots st cap in
  ok ==>
  SpecGCPost.major_gc_unreachable_final_blue (fst prepared) final_major (snd prepared)

/// ---------------------------------------------------------------------------
/// Full minor collection with ref_table
/// ---------------------------------------------------------------------------

/// Full minor collection with a ref_table of major-heap field addresses holding
/// minor pointers.  It promotes the nursery objects reachable from `roots`
/// (Cheney BFS), rewrites the promoted objects' fields and the remembered
/// slots, rewrites the roots and resets the nursery.
///
/// The contract is stated for the collector's phase `ph` the collection runs
/// at -- its promotions are allocated there, with the colour the phase gives
/// a new object -- and a definition `free` of what counts as free in the
/// major heap (`GC.Spec.Fields.free_def`), both supplied by the caller as
/// ghost arguments.  The non-free blocks point only to non-free blocks
/// (`GenInv.collection_shape_with`); a free block is garbage left in place,
/// never read or written.  The shape includes that the blocks the allocator
/// creates at `ph` do not count as free (`allocations_not_free ph free`), so no
/// promoted copy is free.  The stop-the-world collector runs at `Idle` with
/// `free_stw`; `minor_collect_pre_idle` / `minor_collect_post_idle` below are
/// that instance, with the colour facts of `collection_heap_shape` added.
/// The incremental sweep's minor collection runs at `Sweeping c` with
/// `free_incremental c` (`minor_collect`, below).
///
/// The ref_table comes from the write barrier: it records addresses of
/// existing major-heap fields that were assigned minor-heap pointers.  The
/// caller states it as a pre-promotion property given what counts as free
/// (`RT.ref_table_covers_with`: every nursery pointer held by a non-free
/// block is at a recorded slot; `RT.ref_table_sound_with`: slots are fields of
/// scannable non-free blocks).  A slot may be recorded more than once
/// (`caml_modify` after young -> immediate -> young); the second rewrite of
/// it is a no-op, so the bridge need not deduplicate.  The recorded slots' nursery targets are
/// among the roots (`remembered_targets_in_roots`), and the roots are valid
/// and not free (`roots_valid_with`): roots are reachable, so never
/// garbage.
let minor_collect_pre_with (ph: Ph.gc_phase) (free: SpecFields.free_def)
  (minor_st: minor_state) (s: heap_state) (fp: U64.t)
  (rs farr sl: Seq.seq U64.t) (nslots: nat) : prop =
  GenInv.collection_shape_with ph free minor_st s fp /\
  Seq.length farr == FA.fwd_array_size /\
  (forall (i: nat). i < Seq.length farr ==> Seq.index farr i == 0UL) /\
  RT.ref_table_sound_with free s sl nslots /\
  RT.ref_table_covers_with free s sl nslots /\
  MinorFwd.remembered_targets_in_roots s rs sl nslots /\
  MinorFwd.roots_valid_with free minor_st s rs

/// What the collection guarantees, at the phase it runs at and given what
/// counts as free.
let minor_collect_post_with (ph: Ph.gc_phase) (free: SpecFields.free_def)
  (minor_st: minor_state) (s: heap_state) (fp: U64.t) (rs: Seq.seq U64.t) (ok: bool)
  (d2: minor_heap) (b2: U64.t) (s2: heap_state) (fp2: U64.t) (rs2: Seq.seq U64.t) : prop =
  let prom = CheneySpec.cheney_promote ph minor_st s fp rs in
  // The major heap is the collection's, at `ph` and for `free`.  (`full_gc`
  // and the SPOT instances reason about the result through
  // `cheney_collect_spec`; see DESIGN_AND_IMPL.md, "The contract of
  // minor_collect_with".)
  s2 == (CheneySpec.cheney_collect_spec_with ph free minor_st s fp rs).mc_major /\
  // Free pointer from promotion phase
  fp2 == prom.fp_final /\
  // Roots rewritten via forwarding map
  rs2 == PromoteSpec.rewrite_roots rs prom.fwd_map /\
  // Minor heap fully reset: the nursery bytes are cleared as well as the
  // bump pointer, so the state handed back is literally
  // `GC.Gen.MinorHeap.minor_reset`.
  U64.v b2 == 0 /\
  ({ data = d2; bump = b2 } <: minor_state) == minor_reset minor_st /\
  // The shape is kept, with the same phase and definition of free
  GenInv.collection_shape_with ph free ({ data = d2; bump = b2 } <: minor_state) s2 fp2 /\
  // If promotion succeeds, the collection is a reachable-subgraph isomorphism
  // over the graphs in which a free block has no outgoing edges.
  (not ok ==> CheneyBFS.cheney_oom ph minor_st s fp rs) /\
  (ok ==>
   CheneyBFS.cheney_no_oom ph minor_st s fp rs /\
   MinorFwd.normal_result_reachable_subgraph_isomorphism_prop ph
     minor_st s fp free rs s2 (MCFH.resolve_roots s2 rs2) /\
   MinorFwd.normal_result_non_pointer_fields_preserved_prop ph
     minor_st s fp free rs s2)

/// The collection runs at the phase the allocator holds (`gh.phase_ref`),
/// and hands it back: the same phase, its caches derived from the heap the
/// collection leaves.
fn minor_collect_with (gh: gen_heap_t)
                      (roots: array U64.t) (nroots: SZ.t)
                      (fwd_arr: array U64.t)
                      (queue: larray U64.t FA.queue_size)
                      (slots: array U64.t) (nslots: SZ.t)
                      (#free: erased SpecFields.free_def)
  requires is_gen_heap gh 'd 'b 's 'fp ** gen_phase gh 's 'ph **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           pts_to slots 'sl **
           pure (SZ.v nroots == Seq.length 'rs /\
                 minor_collect_pre_with 'ph free ({ data = 'd; bump = 'b } <: minor_state) 's
                   'fp 'rs 'farr 'sl (SZ.v nslots))
  returns ok: bool
  ensures exists* d2 b2 s2 fp2 rs2 farr2 qv2.
    is_gen_heap gh d2 b2 s2 fp2 ** gen_phase gh s2 'ph **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pts_to slots 'sl **
    pure (minor_collect_post_with 'ph free ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs
            ok d2 b2 s2 fp2 rs2)

/// --- The stop-the-world instance ---

/// The stop-the-world precondition: the whole major heap is in shape
/// (`collection_heap_shape`), the remembered set covers every nursery pointer
/// of the major heap, and `roots` is the complete valid root set for it.
let minor_collect_pre_idle
  (minor_st: minor_state) (s: heap_state) (fp: U64.t)
  (rs farr sl: Seq.seq U64.t) (nslots: nat) : prop =
  GenInv.collection_heap_shape minor_st s fp /\
  Seq.length farr == FA.fwd_array_size /\
  (forall (i: nat). i < Seq.length farr ==> Seq.index farr i == 0UL) /\
  RT.ref_table_sound s sl nslots /\
  RT.ref_table_covers_minor_ptrs s sl nslots /\
  MinorFwd.remembered_targets_in_roots s rs sl nslots /\
  MinorFwd.roots_valid_for_minor_collection minor_st s rs

/// The stop-the-world postcondition.
let minor_collect_post_idle
  (minor_st: minor_state) (s: heap_state) (fp: U64.t) (rs: Seq.seq U64.t) (ok: bool)
  (d2: minor_heap) (b2: U64.t) (s2: heap_state) (fp2: U64.t) (rs2: Seq.seq U64.t) : prop =
  let prom = CheneySpec.cheney_promote Idle minor_st s fp rs in
  // Free pointer from promotion phase
  fp2 == prom.fp_final /\
  // Roots rewritten via forwarding map
  rs2 == PromoteSpec.rewrite_roots rs prom.fwd_map /\
  // Minor heap fully reset: the nursery bytes are cleared as well as the
  // bump pointer, so the state handed back is literally
  // `GC.Gen.MinorHeap.minor_reset`.  That is what makes every minor-side
  // and cross-generation conjunct of `collection_heap_shape` vacuous for
  // the collector's output.
  U64.v b2 == 0 /\
  ({ data = d2; bump = b2 } <: minor_state) == minor_reset minor_st /\
  // The major heap is the stop-the-world collection's.
  s2 == (CheneySpec.cheney_collect_spec minor_st s fp rs).mc_major /\
  GenInv.collection_heap_shape ({ data = d2; bump = b2 } <: minor_state) s2 fp2 /\
  // If promotion succeeds, minor collection is a concrete reachable
  // subgraph isomorphism over the actual post-minor heap graph.
  (not ok ==> CheneyBFS.cheney_oom Idle minor_st s fp rs) /\
  (ok ==>
   CheneyBFS.cheney_no_oom Idle minor_st s fp rs /\
   MinorFwd.normal_result_reachable_subgraph_isomorphism_prop Idle
     minor_st s fp SpecFields.free_stw rs s2 (MCFH.resolve_roots s2 rs2) /\
   MinorFwd.normal_result_non_pointer_fields_preserved_prop Idle
     minor_st s fp SpecFields.free_stw rs s2)

/// The stop-the-world precondition is the general one at `free_stw` ...
val minor_collect_idle_pre
  (minor_st: minor_state) (s: heap_state) (fp: U64.t)
  (rs farr sl: Seq.seq U64.t) (nslots: nat)
  : Lemma (requires minor_collect_pre_idle minor_st s fp rs farr sl nslots)
          (ensures minor_collect_pre_with Ph.Idle SpecFields.free_stw minor_st s fp rs farr sl nslots)

/// ... and the general postcondition at `free_stw` gives the
/// stop-the-world one.
val minor_collect_idle_post
  (minor_st: minor_state) (s: heap_state) (fp: U64.t)
  (rs farr sl: Seq.seq U64.t) (nslots: nat) (ok: bool)
  (d2: minor_heap) (b2: U64.t) (s2: heap_state) (fp2: U64.t) (rs2: Seq.seq U64.t)
  : Lemma (requires minor_collect_pre_idle minor_st s fp rs farr sl nslots /\
                    minor_collect_post_with Ph.Idle SpecFields.free_stw minor_st s fp rs
                      ok d2 b2 s2 fp2 rs2)
          (ensures minor_collect_post_idle minor_st s fp rs ok d2 b2 s2 fp2 rs2)

/// ---------------------------------------------------------------------------
/// What the runtime supplies (trusted bridge obligations)
/// ---------------------------------------------------------------------------
///
/// Each entry point of this module is a separate call from C, and the separation-logic
/// state does not survive between calls: the bridge re-supplies `gc_state`'s
/// pure half at every call.  What justifies it is that every collector call returns
/// it, and the program's events in between keep it:
///
///   * **Allocation mid-sweep** (`GC.Impl.Allocator.allocate`, which keeps
///     the record's phase and caches; what it does to the sweep phase is
///     `Mut.alloc_sweep_phase`, of the same `alloc_phase`): either nothing
///     changed (no block fits) or the new object is a `Mut.new_block` and
///     *fresh* (`Mut.fresh_ok`: the sweep phase except that its fields are
///     uninitialised and nothing points at it).
///     The runtime initialises every field of a block it allocates with a
///     storable value (an integer, or a pointer to a non-free object --
///     reachable objects are never pending free) before the
///     next collector call; `Mut.fresh_write` and `Mut.fresh_close` then give
///     back the sweep phase.  Idle, the obligation is today's: the fields are
///     initialised before the next collection.
///   * **Field writes** (`caml_modify`, `caml_initialize`): `Mut.program_write`
///     -- a word of the body of a non-free object that is not a closure, and
///     a value that is not a pointer or points at a non-free object.
///     `Mut.write_sweep_phase` keeps the sweep phase.  The write barrier
///     records every major field that gets a nursery pointer (the remembered
///     set below).
///   * **Nursery allocation** keeps the nursery's shape and the
///     cross-generation condition (as today, mid-sweep for `free_incremental`).
///   * **The minor collection's arguments** (`minor_slots_ok`): the
///     forwarding array zeroed, the remembered set sound and covering for the
///     phase's definition of free (`RT.ref_table_sound_with`,
///     `RT.ref_table_covers_with` for `GI.phase_free`; repeated slots are
///     allowed), the remembered targets among the roots, and the roots valid and not free (never pending free).
///   * **The phase record** (`gh.phase_ref`) is written only by the collector
///     and the allocator.

/// ---------------------------------------------------------------------------
/// The minor collection
/// ---------------------------------------------------------------------------

/// The minor collection's arguments, for the phase's definition of free.
let minor_slots_ok (ph: Ph.gc_phase) (minor_st: minor_state) (s: heap_state)
    (rs farr sl: Seq.seq U64.t) (nslots: nat) : prop =
  let free = GI.phase_free ph in
  Seq.length farr == FA.fwd_array_size /\
  (forall (i: nat). i < Seq.length farr ==> Seq.index farr i == 0UL) /\
  RT.ref_table_sound_with free s sl nslots /\
  RT.ref_table_covers_with free s sl nslots /\
  MinorFwd.remembered_targets_in_roots s rs sl nslots /\
  MinorFwd.roots_valid_with free minor_st s rs

/// **The minor collection**, at the collector's phase, for the phase's
/// definition of free (`GI.phase_free`: `free_stw` idle, `free_incremental c`
/// mid-sweep): `minor_collect_with`'s contract (`minor_collect_post_with`,
/// at the phase), and the collector's state at the same phase -- idle stays
/// idle; mid-sweep the sweep keeps its cursor and the objects pending free
/// (`GI.minor_keeps_phase_shape`).
fn minor_collect (gh: gen_heap_t)
                 (roots: array U64.t) (nroots: SZ.t)
                 (fwd_arr: array U64.t)
                 (queue: larray U64.t FA.queue_size)
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
/// The major collector: starting a cycle, and its slices
/// ---------------------------------------------------------------------------
///
/// The shape of OCaml 4.14's major GC (`runtime/major_gc.c`): a cycle starts
/// at `Idle` right after a minor collection (`start_cycle`, as 4.14's
/// `start_cycle`), and then runs in slices (`major_slice`, as
/// `caml_major_collection_slice`) until it is idle again; finishing a cycle
/// (4.14's `caml_finish_major_cycle`) is slices with an unbounded budget until
/// `major_slice` reports idle.  Marking still runs to completion inside
/// `start_cycle`; the slices are the sweep's.

/// The nursery is empty: what a minor collection leaves (`minor_reset`).
let nursery_empty (d: minor_heap) (b: U64.t) : prop =
  U64.v b == 0 /\ d == Seq.create minor_heap_size 0uy

/// What starting a cycle needs of the roots and the gray stack: the stack
/// empty and able to hold the roots (`gen_gc_stack_budget`), and every root a
/// darkenable major object (`MBP.root_valid_for_darkening`: not a nursery
/// pointer -- the nursery is empty -- and naming an object that is not free).
/// A minor collection leaves its rewritten roots so
/// (`GMP.post_minor_roots_valid_for_darkening`).
let start_cycle_pre (s: heap) (rs: Seq.seq U64.t) (st: Seq.seq obj_addr) (cap: nat) : prop =
  gen_gc_stack_budget rs st cap /\
  (forall (i: nat). i < Seq.length rs ==> MBP.root_valid_for_darkening s (Seq.index rs i))

/// What starting a cycle guarantees.  With `prepared` the heap and stack
/// root darkening leaves (`darken_roots_bounded_spec`): the stack holds the
/// objects the roots name (`roots_match_stack`), and the heap is the marked
/// heap (`SpecGCPost.mark_post` of the darkened heap: every object reachable
/// from the roots is black, everything else white or free, nothing grey, and
/// the objects and their fields unchanged).
let start_cycle_post (s: heap) (fp: U64.t) (rs: Seq.seq U64.t) (st: Seq.seq obj_addr) (cap: nat)
    (s2: heap) : prop =
  let prepared = MarkBoundedImpl.darken_roots_bounded_spec s st rs cap in
  roots_match_stack s rs (snd prepared) /\
  SpecGCPost.mark_post (fst prepared) s2 (snd prepared) fp

/// **Start a major cycle**, idle and with the nursery empty (right after a
/// minor collection): darken the roots, mark to completion, and start the
/// sweep phase (`Sweeping zero_addr`, the cursor at the first block).  The
/// nursery, the free-list head and the roots are unchanged.
fn start_cycle (gh: gen_heap_t) (roots: array U64.t) (nroots: SZ.t) (st: gray_stack)
  requires gc_state gh 'd 'b 's 'fp Ph.Idle **
           pts_to roots 'rs **
           is_gray_stack st 'st **
           pure (SZ.v nroots == Seq.length 'rs /\
                 nursery_empty 'd 'b /\
                 start_cycle_pre 's 'rs 'st (stack_capacity st))
  ensures exists* s2 st2.
    gc_state gh 'd 'b s2 'fp (Ph.Sweeping zero_addr) **
    pts_to roots 'rs **
    is_gray_stack st st2 **
    pure (start_cycle_post 's 'fp 'rs 'st (stack_capacity st) s2)

/// **One major slice**, at the collector's phase (`GI.major_slice_spec`):
/// idle, nothing; mid-sweep, whole sweep steps until the blocks swept add up
/// to at least `budget` words (headers included; at most one block over), or
/// the sweep is finished (`SL.phase_slice`: some number of sweep steps,
/// keeping the sweep phase, `SL.sweep_slice_phase`).  When the sweep
/// finishes the phase is `Idle` and the state is the stop-the-world shape
/// again (`GI.sweep_end_shape`).  Returns whether the phase it leaves is
/// `Idle`.
fn major_slice (gh: gen_heap_t) (budget: U64.t)
  requires gc_state gh 'd 'b 's 'fp 'ph
  returns idle: bool
  ensures exists* s2 fp2 ph2.
    gc_state gh 'd 'b s2 fp2 ph2 **
    pure ((s2, fp2, ph2) == GI.major_slice_spec 's 'fp 'ph (U64.v budget) /\
          idle == Ph.Idle? ph2)

/// ---------------------------------------------------------------------------
/// Full generational GC (minor collection + major collection)
/// ---------------------------------------------------------------------------

/// **A full collection**, idle: `minor_collect`, then, unless promotion ran
/// out of memory, `start_cycle` and `major_slice` with an unbounded budget
/// until the collector is idle again.
///
/// Postcondition provides:
/// - the end-to-end reachable-subgraph isomorphism and the unreachable-blocks-
///   freed facts, from the heap handed in to the heap handed back
/// - Minor collection properties (roots rewritten, minor heap reset)
/// - `GenInv.collection_heap_shape` of the returned state: the precondition
///   is restored
///
/// The caller provides the idle `gc_state` (`collection_heap_shape`) plus the
/// remembered-set table the minor collection needs.  The implementation
/// derives the post-minor major-GC precondition before starting the cycle.
fn full_gc (gh: gen_heap_t)
           (roots: array U64.t) (nroots: SZ.t)
           (fwd_arr: array U64.t)
           (queue: larray U64.t FA.queue_size)
           (slots: array U64.t) (nslots: SZ.t)
           (st: gray_stack)
  requires gc_state gh 'd 'b 's 'fp Ph.Idle **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           pts_to slots 'sl **
           is_gray_stack st 'st **
           pure (
              // `Seq.length 'st <= stack_capacity st` is not restated here: it
              // is recoverable from `is_gray_stack` via `Stack.stack_facts`.
              // Everything the major phase needs about the *post*-minor heap
              // is derived from the idle shape internally, by
              // `GC.Gen.MajorPrecondition`.
              gen_gc_stack_budget 'rs 'st (stack_capacity st) /\

               // Operational array preconditions.
               SZ.v nroots == Seq.length 'rs /\
               Seq.length 'farr == FA.fwd_array_size /\
               (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\
               RT.ref_table_sound 's 'sl (SZ.v nslots) /\
               RT.ref_table_covers_minor_ptrs 's 'sl (SZ.v nslots) /\
               MinorFwd.remembered_targets_in_roots 's 'rs 'sl (SZ.v nslots) /\
               MinorFwd.roots_valid_for_minor_collection
                 ({ data = 'd; bump = 'b } <: minor_state) 's 'rs)
  returns ok: bool
  ensures exists* d2 b2 s2 fp2 rs2 farr2 qv2 st2.
    gc_state gh d2 b2 s2 fp2 Ph.Idle **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pts_to slots 'sl **
    is_gray_stack st st2 **
    pure (
      let minor_st : minor_state = { data = 'd; bump = 'b } in
      let minor_st_out : minor_state = { data = d2; bump = b2 } in
      // Failure is reported only for a concrete out-of-memory event: an object
      // the major free list had no room for, at a point of this collection.
      (not ok ==> CheneyBFS.cheney_oom Idle minor_st 's 'fp 'rs) /\
      gen_gc_roots_post minor_st 's 'fp 'rs rs2 ok 'st (stack_capacity st) /\
      // The nursery handed back is the zeroed one, `GC.Gen.MinorHeap.minor_reset`.
      // This is the only heap-shape fact in the postcondition that does *not*
      // follow from the invariant below; everything else about the returned
      // state, including `gen_gc_heap_shape_post`, is derived from it (see
      // `gen_gc_heap_shape_post_intro`).
      minor_st_out == minor_reset minor_st /\
      // **The collector restores its own precondition**: literally the shape
      // `full_gc` demands of the state it is handed (the idle `gc_state`),
      // now asserted of the state it hands back.  A runtime driving an
      // unbounded sequence of collections therefore establishes the invariant
      // once, at start-up, and never again.
      //
      // The minor half is vacuous -- the nursery returned is
      // `GC.Gen.MinorHeap.minor_reset`, i.e. zeroed -- so the content of the
      // claim is `GC.Gen.HeapInvariant.major_heap_shape` of the major heap and
      // free-list head, every conjunct of it.
      GenInv.collection_heap_shape minor_st_out s2 fp2 /\
      gen_gc_reachable_subgraph_isomorphism_post
        minor_st 's 'fp 'rs ok s2 rs2 'st (stack_capacity st) /\
      gen_gc_unreachable_final_blue_post
        minor_st 's 'fp 'rs ok s2 'st (stack_capacity st))
