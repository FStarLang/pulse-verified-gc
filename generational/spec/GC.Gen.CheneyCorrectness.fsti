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
/// BFS completeness (every reachable nursery object is forwarded, given no
/// OOM) is `GC.Gen.CheneyBFS.cheney_promotes_all_reachable`.
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
