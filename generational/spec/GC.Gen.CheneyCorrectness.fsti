/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyCorrectness — End-to-end correctness for Cheney minor collector
/// ---------------------------------------------------------------------------
///
/// This module states the main correctness theorem for the Cheney BFS minor
/// collector (cheney_collect_spec from GC.Gen.Cheney). The spec models:
///   1. BFS promotion of reachable minor objects into the major heap
///   2. Updating all major-heap pointer fields via the forwarding map
///   3. Rewriting program roots via the forwarding map
///   4. Resetting the minor heap (bump = 0)
///
/// The result type is minor_collect_result with fields:
///   mc_major  — the post-collection major heap (byte sequence)
///   mc_fp     — the post-collection free-list head
///   mc_minor  — the post-collection minor heap state
///   mc_roots  — the post-collection program roots
///   mc_fwd    — the forwarding map (minor addr → major addr, or 0 if not forwarded)
///
/// Properties proved:
///
/// 1. **Object survival**: all pre-existing major-heap objects survive
///    (promotion only appends into free-list nodes; never removes objects).
///    This holds even if the major heap runs out of free-list space during
///    promotion (partial promotion is safe).
/// 2. **BFS completeness** (CONDITIONAL on sufficient space): all minor objects
///    reachable from roots via minor_successors are forwarded.
///    This requires cheney_no_oom — that no promote_object call failed.
///
/// The shape the collection keeps is `GC.Gen.CheneyGeneric.cheney_collect_with_preserves_shape`.

module GC.Gen.CheneyCorrectness

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Cheney

module AllocLemmas = GC.Spec.Allocator.Lemmas

/// ---------------------------------------------------------------------------
/// Property 1: Object survival — pre-existing major objects survive collection
/// ---------------------------------------------------------------------------

/// Every object address present in objects(0, major) before collection is
/// still present in objects(0, mc_major) after collection (for any definition of free `free`;
/// the pointer update writes no header). Cheney promotion
/// consumes free-list nodes to hold promoted objects, but never overwrites
/// or removes any existing allocated object.
///
/// Preconditions: the major heap is well-formed, and the free-list from fp
/// is valid and terminates. These ensure promote_object writes only into
/// legitimate free-list nodes.
val cheney_collect_preserves_objects
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def) (roots: seq U64.t)
  : Lemma
    (requires
      // Major heap has valid OCaml object layout
      blocks_fit major /\ no_infix_block major /\
      // Free-list from fp: each node is a valid blue object with wosize >= 1
      AllocLemmas.fl_valid major fp heap_words /\
      // Free-list traversal terminates (no cycles)
      AllocLemmas.fl_chain_terminates major fp heap_words)
    (ensures (let res = cheney_collect_spec_with free minor major fp roots in
              // Every pre-existing object address is still in the post-collection object list
              forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                Seq.mem x (objects zero_addr res.mc_major)))

/// ---------------------------------------------------------------------------
/// Property 2: BFS completeness (conditional on sufficient space)
/// ---------------------------------------------------------------------------

open GC.Gen.Reachability

/// BFS completeness: every minor-heap object reachable from the program roots
/// (via the minor_reachable transitive closure) is forwarded by cheney_promote,
/// provided no out-of-memory occurred during the BFS.
///
/// minor_reachable(minor, roots) computes the set of minor-heap object
/// addresses reachable from roots via minor_successors (the pointer fields
/// of minor-heap objects that point to other minor-heap objects).
///
/// The precondition cheney_no_oom says: the final forwarding map produced by
/// cheney_promote covers all roots and is closed under minor_successors.
/// This is the structural property the BFS naturally produces when every
/// promote_object call succeeds (i.e., the major-heap free-list had enough
/// space for all reachable objects).
///
/// The conclusion: for every reachable minor address x, either:
///   - fwd_map(x) != 0UL (x was forwarded to a major-heap address), or
///   - minor_wosize(minor, x) == 0 (x has zero body size, a degenerate
///     object that needs no promotion)
///
/// The proof is NON-TRIVIAL: it uses structural induction on the
/// minor_reachable definition to show that root-coverage + successor-closure
/// implies full reachability coverage. See GC.Gen.CheneyBFS for details.
val cheney_promotes_all_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      // The BFS completed without running out of free-list space:
      // the forwarding map covers all roots and is closed under
      // minor_successors (every child of a forwarded object is also forwarded)
      GC.Gen.CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures (let prom = cheney_promote minor major fp roots in
              // Every reachable minor object is forwarded (or has zero wosize)
              forall (x: U64.t). Seq.mem x (minor_reachable minor roots) ==>
                prom.fwd_map x <> 0UL \/ minor_wosize minor x = 0))
