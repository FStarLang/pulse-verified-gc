/// ---------------------------------------------------------------------------
/// GC.Gen.MarkPhase.Safety - an incremental cycle never frees or changes what is reachable
/// ---------------------------------------------------------------------------
///
/// Safety across a whole incremental cycle (incremental-mark-plan.md, M6),
/// stated once for every phase of the collector (`GI.phase_shape minor g fp
/// ph`), with the phase's definition of free (`GI.phase_free ph`: blue idle
/// or marking -- marking frees nothing -- and blue or pending free mid-sweep):
///
///   * **what is reachable is not free** (`cycle_reachable_not_free`): every
///     object reachable from the program's roots, through the nursery and the
///     major heap (`GC.Gen.CombinedGraph`), is a real block, not free at the
///     phase.  The sweep's form was `GC.Gen.SweepPhase.Safety.
///     reachable_not_free_combined`; this is the same at `Idle` and
///     `Marking`.  The roots must be non-free at the phase; at the hand-over
///     to the sweep they are (`handover_roots`: marking leaves every root
///     black);
///   * **the collector's own moves leave the blocks alone**: a major slice
///     (`cycle_slice_keeps`) keeps every non-free block with its size, tag
///     and fields (`SPI.same_block`) -- mark moves only recolour
///     (`MPC.mark_steps_keep_blocks`), a sweep slice frees only blocks pending
///     free -- and non-free at the phase it leaves, but for the blocks the
///     hand-over to the sweep finds white (pending free: unreachable, by the
///     previous point).  So a reachable object keeps its size, tag and fields
///     across a slice (`slice_keeps_reachable`).  A minor collection while
///     marking keeps every non-free block's header and its fields that point
///     into the major heap (`GMM.minor_keeps_block`,
///     `GMM.minor_keeps_major_field`); the rest of its fields -- nursery
///     pointers -- are rewritten through the forwarding map, which is the
///     minor collection's isomorphism theorem (`minor_collect_post_with`).

module GC.Gen.MarkPhase.Safety

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
module GMM = GC.Gen.MarkPhase.Minor
module SPI = GC.Spec.SweepPhase.Intrinsic
module CG = GC.Gen.CombinedGraph
module RBridge = GC.Gen.ReachabilityBridge

/// **At every phase, what the roots reach is not free.**
val cycle_reachable_not_free (minor: minor_state) (g: heap) (fp: U64.t) (ph: Ph.gc_phase)
                             (roots: seq U64.t) (a: U64.t)
  : Lemma (requires GI.phase_shape minor g fp ph /\
                    RBridge.roots_not_free (GI.phase_free ph) roots g /\
                    CG.combined_reachable (CG.build_combined_graph minor g (GI.phase_free ph))
                      (CG.classify_roots minor roots) (CG.MajorV a))
          (ensures GC.Spec.FusedSweep.is_obj a /\ in_use (GI.phase_free ph) g (a <: obj_addr))

/// **The roots across the hand-over**: when marking ends, every root that
/// is a block is black (the roots are held, and nothing is grey), so not
/// pending free.
val handover_roots (minor: minor_state) (g: heap) (fp: U64.t) (rs: seq U64.t)
  : Lemma (requires GI.phase_shape minor g fp Ph.Marking /\ Mark.noGreyObjects g /\
                    MP.held_reached g (GMM.roots_held g rs) /\
                    RBridge.roots_not_free free_stw rs g)
          (ensures RBridge.roots_not_free (SPI.free_incremental zero_addr) rs g)

/// **A major slice keeps every non-free block**: its size, tag and fields,
/// on the walk and not blue; and not free at the phase it leaves, unless the
/// slice handed over to the sweep and the block is white.
val cycle_slice_keeps (minor: minor_state) (g: heap) (fp: U64.t) (ph: Ph.gc_phase) (budget: nat)
                      (g': heap) (fp': U64.t) (ph': Ph.gc_phase) (x: obj_addr)
  : Lemma (requires GI.phase_shape minor g fp ph /\ GI.major_slice_post g fp ph budget g' fp' ph' /\
                    in_use (GI.phase_free ph) g x)
          (ensures SPI.same_block g g' (hd_address x) /\
                   Seq.mem x (objects zero_addr g') /\ ~(is_blue x g') /\
                   (~(Ph.Marking? ph) \/ Ph.Marking? ph' \/ ~(is_white x g') ==>
                      in_use (GI.phase_free ph') g' x))

/// **So a slice never changes a reachable object.**
val slice_keeps_reachable (minor: minor_state) (g: heap) (fp: U64.t) (ph: Ph.gc_phase) (budget: nat)
                          (g': heap) (fp': U64.t) (ph': Ph.gc_phase) (roots: seq U64.t) (a: U64.t)
  : Lemma (requires GI.phase_shape minor g fp ph /\ GI.major_slice_post g fp ph budget g' fp' ph' /\
                    RBridge.roots_not_free (GI.phase_free ph) roots g /\
                    CG.combined_reachable (CG.build_combined_graph minor g (GI.phase_free ph))
                      (CG.classify_roots minor roots) (CG.MajorV a))
          (ensures GC.Spec.FusedSweep.is_obj a /\
                   SPI.same_block g g' (hd_address (a <: obj_addr)) /\
                   Seq.mem (a <: obj_addr) (objects zero_addr g') /\ ~(is_blue (a <: obj_addr) g'))
