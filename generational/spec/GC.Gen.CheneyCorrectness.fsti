/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyCorrectness — End-to-end correctness for Cheney collector
/// ---------------------------------------------------------------------------
///
/// Proves that cheney_collect_spec satisfies the key correctness properties:
///
/// 1. **Object survival**: all pre-existing major-heap objects survive
/// 2. **Heap well-formedness**: well_formed_heap_part1 preserved after collection
/// 3. **Minor reset**: minor heap is properly reset (bump = 0)
/// 4. **Root update**: program roots rewritten via forwarding map
///
/// Properties 1-4 are UNCONDITIONAL (hold regardless of available space).
///
/// 5. **BFS completeness** (conditional): all reachable minor objects are
///    forwarded, provided no allocation fails during the BFS.
///    Stated separately since it requires a space precondition.

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

val cheney_collect_preserves_objects
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = cheney_collect_spec minor major fp roots in
                    forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                      Seq.mem x (objects zero_addr res.mc_major)))

/// ---------------------------------------------------------------------------
/// Property 2: well_formed_heap_part1 after collection
/// ---------------------------------------------------------------------------

val cheney_collect_preserves_wfh_part1
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures well_formed_heap_part1 (cheney_collect_spec minor major fp roots).mc_major)

/// ---------------------------------------------------------------------------
/// Property 3: Minor heap is properly reset
/// ---------------------------------------------------------------------------

val cheney_collect_resets_minor
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (ensures (let res = cheney_collect_spec minor major fp roots in
                    minor_wf res.mc_minor /\
                    U64.v res.mc_minor.bump == 0))

/// ---------------------------------------------------------------------------
/// Property 4: Roots are rewritten via forwarding map
/// ---------------------------------------------------------------------------

val cheney_collect_rewrites_roots
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (ensures (let res = cheney_collect_spec minor major fp roots in
                    let prom = cheney_promote minor major fp roots in
                    res.mc_roots == rewrite_roots roots prom.fwd_map))

/// ---------------------------------------------------------------------------
/// Main theorem: composition of properties 1-4 (unconditional)
/// ---------------------------------------------------------------------------

/// The main correctness theorem for Cheney collection. All four properties
/// hold unconditionally (no space requirement). The collector is always safe:
/// it never loses pre-existing objects, maintains heap structure, resets the
/// minor heap, and correctly rewrites roots.
val cheney_gc_correct
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp)
          (ensures (let res = cheney_collect_spec minor major fp roots in
                    let prom = cheney_promote minor major fp roots in
                    // 1. Object survival: pre-existing major objects are retained
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                      Seq.mem x (objects zero_addr res.mc_major)) /\
                    // 2. Heap well-formedness preserved
                    well_formed_heap_part1 res.mc_major /\
                    // 3. Allocator invariants preserved (enables further allocation)
                    AllocLemmas.fl_valid res.mc_major res.mc_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates res.mc_major res.mc_fp (heap_size / U64.v mword) /\
                    // 4. Minor reset: ready for new allocations
                    minor_wf res.mc_minor /\
                    U64.v res.mc_minor.bump == 0 /\
                    // 5. Root rewriting is correct
                    res.mc_roots == rewrite_roots roots prom.fwd_map))

/// ---------------------------------------------------------------------------
/// Property 6: BFS completeness (conditional on sufficient space)
/// ---------------------------------------------------------------------------

open GC.Gen.Reachability

/// BFS completeness: all reachable minor objects are forwarded.
///
/// NOTE: This is currently stated as a post-hoc observation (the precondition
/// asserts the forwarding map already covers all reachable objects). A stronger
/// theorem would prove this from a SPACE precondition:
///   "free-list capacity >= total size of all reachable minor objects"
/// implies the BFS never encounters OOM, which by forward-on-discovery
/// closure ensures all reachable objects are forwarded.
///
/// The BFS closure proof (forward-on-discovery implies reachability coverage)
/// requires showing that cheney_scan processes every queue entry and that
/// forward_fields of each parent adds all children to the queue.
/// This is left as future work — Property 6 is the placeholder statement.
val cheney_promotes_all_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    // Sufficient space: the final forwarding map shows all
                    // valid-sized reachable objects were successfully forwarded
                    (let prom = cheney_promote minor major fp roots in
                     forall (x: U64.t). Seq.mem x (minor_reachable minor roots) /\
                                        minor_wosize minor x > 0 ==>
                       prom.fwd_map x <> 0UL))
          (ensures (let prom = cheney_promote minor major fp roots in
                    forall (x: U64.t). Seq.mem x (minor_reachable minor roots) ==>
                      prom.fwd_map x <> 0UL \/ minor_wosize minor x = 0))
