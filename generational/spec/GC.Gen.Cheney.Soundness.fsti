/// ---------------------------------------------------------------------------
/// GC.Gen.Cheney.Soundness - what a minor collection forwards, and to where
/// ---------------------------------------------------------------------------
///
/// Three facts about the forwarding map of a Cheney minor collection
/// (`GC.Gen.Cheney.cheney_collect_spec_with`), at any phase `ph` and any
/// definition of free `free` the collection is run with:
///
///   * **soundness of promotion** (`cheney_collect_fwd_sound`,
///     `cheney_collect_forwarded_reachable`): an address is forwarded only if
///     the nursery object it names (an interior pointer names its closure,
///     `resolve_minor`) is reachable in the nursery from the collection's
///     roots (`GC.Gen.Reachability.minor_reachable`).  The roots are the ones
///     the collection is handed -- the program's and the targets of the
///     remembered slots, which the caller appends
///     (`GC.Gen.Run.Step.collector_roots`).  The converse, under no
///     out-of-memory, is `GC.Gen.CheneyBFS.cheney_promotes_all_reachable`;
///   * **the new blocks are the forwarding targets** (`cheney_collect_new_blocks`,
///     and at the stop-the-world sense of allocated `cheney_collect_new_blocks_stw`):
///     a block in use after the collection that was not before is exactly
///     the image `fwd o` of a nursery object `o`;
///   * **the forwarding map is injective** (`cheney_collect_fwd_injective`):
///     two forwarded addresses -- nursery objects or interior pointers --
///     with the same target are the same address.
///
/// Soundness needs only the nursery's well-formedness; the other two need
/// what promotion needs of the major heap (`GC.Gen.CheneyGeneric.promote_pre`,
/// which `promote_pre_of_shape` derives from the collection's entry shape).

module GC.Gen.Cheney.Soundness

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Cheney
open GC.Gen.Reachability

module CG = GC.Gen.CheneyGeneric
module GenInv = GC.Gen.HeapInvariant

/// ---------------------------------------------------------------------------
/// Soundness of promotion
/// ---------------------------------------------------------------------------

/// **Only what is reachable is forwarded** (the promotion).
val cheney_promote_fwd_sound (ph: gc_phase)
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) (x: U64.t)
  : Lemma (requires minor_wf minor /\ minor_infix_wf minor /\
                    (cheney_promote ph minor major fp roots).fwd_map x <> 0UL)
          (ensures Seq.mem (resolve_minor minor x) (minor_reachable minor roots))

/// **Only what is reachable is forwarded** (the collection): a forwarded
/// address resolves to a nursery object reachable from the roots.
val cheney_collect_fwd_sound (ph: gc_phase) (free: free_def)
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) (x: U64.t)
  : Lemma (requires minor_wf minor /\ minor_infix_wf minor /\
                    (cheney_collect_spec_with ph free minor major fp roots).mc_fwd x <> 0UL)
          (ensures Seq.mem (resolve_minor minor x) (minor_reachable minor roots))

/// The same for a nursery object: it is promoted only if it is reachable.
val cheney_collect_forwarded_reachable (ph: gc_phase) (free: free_def)
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) (o: U64.t)
  : Lemma (requires minor_wf minor /\ minor_infix_wf minor /\
                    Seq.mem o (minor_objects minor) /\
                    (cheney_collect_spec_with ph free minor major fp roots).mc_fwd o <> 0UL)
          (ensures Seq.mem o (minor_reachable minor roots))

/// ---------------------------------------------------------------------------
/// What promotion needs, from the collection's entry shape
/// ---------------------------------------------------------------------------

val promote_pre_of_shape (ph: gc_phase) (free: free_def)
  (minor: minor_state) (major: heap) (fp: U64.t)
  : Lemma (requires GenInv.collection_shape_with ph free minor major fp)
          (ensures CG.promote_pre minor major fp)

/// ---------------------------------------------------------------------------
/// The new blocks are the forwarding targets
/// ---------------------------------------------------------------------------

/// **A block in use after the collection that was not in use before is a
/// promoted copy, and every promoted copy is one**, for any admissible sense
/// `un` of free (`free_def_ok`, and not free when just allocated at the
/// phase), whatever `free` the pointer update is run with.
val cheney_collect_new_blocks (ph: gc_phase) (free: free_def) (un: free_def)
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) (x: obj_addr)
  : Lemma (requires CG.promote_pre minor major fp /\
                    free_def_ok un /\ allocations_not_free ph un)
          (ensures (let res = cheney_collect_spec_with ph free minor major fp roots in
                    (in_use un res.mc_major x /\ ~(in_use un major x)) <==>
                    (exists (o: U64.t). Seq.mem o (minor_objects minor) /\ res.mc_fwd o == x)))

/// The same at the stop-the-world sense of allocated (a non-blue block of the
/// walk), at every phase.
val cheney_collect_new_blocks_stw (ph: gc_phase) (free: free_def)
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) (x: obj_addr)
  : Lemma (requires CG.promote_pre minor major fp)
          (ensures (let res = cheney_collect_spec_with ph free minor major fp roots in
                    ((Seq.mem x (objects zero_addr res.mc_major) /\ ~(is_blue x res.mc_major)) /\
                     ~(Seq.mem x (objects zero_addr major) /\ ~(is_blue x major))) <==>
                    (exists (o: U64.t). Seq.mem o (minor_objects minor) /\ res.mc_fwd o == x)))

/// ---------------------------------------------------------------------------
/// The forwarding map is injective
/// ---------------------------------------------------------------------------

/// **Two forwarded addresses with the same target are the same** (the
/// promotion).
val cheney_promote_fwd_injective (ph: gc_phase)
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) (x y: U64.t)
  : Lemma (requires CG.promote_pre minor major fp /\
                    (let fwd = (cheney_promote ph minor major fp roots).fwd_map in
                     fwd x <> 0UL /\ fwd x == fwd y))
          (ensures x == y)

/// **Two forwarded addresses with the same target are the same** (the
/// collection).
val cheney_collect_fwd_injective (ph: gc_phase) (free: free_def)
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) (x y: U64.t)
  : Lemma (requires CG.promote_pre minor major fp /\
                    (let fwd = (cheney_collect_spec_with ph free minor major fp roots).mc_fwd in
                     fwd x <> 0UL /\ fwd x == fwd y))
          (ensures x == y)
