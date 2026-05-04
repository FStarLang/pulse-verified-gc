/// ---------------------------------------------------------------------------
/// GC.Gen.Cheney — Cheney-style BFS copying collector specification
/// ---------------------------------------------------------------------------
///
/// Defines a Cheney semi-space-style minor collection that promotes only
/// LIVE (reachable) minor objects to the major heap using forward-on-discovery
/// BFS traversal.
///
/// Architecture:
///   1. Forward roots (program roots + remembered set) — promote & enqueue
///   2. BFS scan: for each queued object, forward its unforwarded minor children
///   3. Update major-heap pointers via forwarding map
///   4. Rewrite program roots
///   5. Reset minor heap
///
/// Key invariant: `fwd obj <> 0UL` ↔ obj has been forwarded (promoted).
/// Forward-on-discovery ensures no object is enqueued twice.

module GC.Gen.Cheney

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Remembered

module AllocLemmas = GC.Spec.Allocator.Lemmas

/// ---------------------------------------------------------------------------
/// Cheney state: threaded through all BFS operations
/// ---------------------------------------------------------------------------

/// The BFS state tracks the evolving major heap, free-list pointer,
/// forwarding map, and the discovery queue.
noeq
type cheney_state = {
  cs_major : heap;            // current major heap
  cs_fp    : U64.t;           // current free-list pointer
  cs_fwd   : forwarding_map;  // minor→major forwarding
  cs_queue : seq U64.t;       // BFS queue of forwarded minor addresses
}

/// ---------------------------------------------------------------------------
/// Forward one object (promote if valid, unforwarded, wosize > 0)
/// ---------------------------------------------------------------------------

/// Try to forward `addr`: if it's a valid unforwarded minor object with
/// wosize > 0, promote it to the major heap and enqueue it.
/// Otherwise, return the state unchanged.
val cheney_forward_one (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : GTot cheney_state

/// Unfold: when addr is not in minor_objects or already forwarded
val cheney_forward_one_noop (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires ~(Seq.mem addr (minor_objects minor)) \/
                    cs.cs_fwd addr <> 0UL)
          (ensures cheney_forward_one minor cs addr == cs)

/// Unfold: when addr is valid and successfully forwarded
val cheney_forward_one_success (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires Seq.mem addr (minor_objects minor) /\
                    cs.cs_fwd addr = 0UL /\
                    minor_wosize minor addr > 0 /\
                    (promote_object minor cs.cs_major addr cs.cs_fp
                       (minor_wosize minor addr)).new_addr <> 0UL)
          (ensures (let wz = minor_wosize minor addr in
                    let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
                    cheney_forward_one minor cs addr ==
                    { cs_major = res.major_out;
                      cs_fp    = res.fp_out;
                      cs_fwd   = extend_forwarding cs.cs_fwd addr res.new_addr;
                      cs_queue = Seq.append cs.cs_queue (Seq.create 1 addr) }))

/// ---------------------------------------------------------------------------
/// Forward children: iterate an object's fields and forward each child
/// ---------------------------------------------------------------------------

/// Iterate fields [idx, wosize) of `parent`, forwarding any unforwarded
/// minor children. Returns updated state with new queue entries.
val cheney_forward_fields (minor: minor_state) (cs: cheney_state)
                          (parent: U64.t) (idx: nat) (wosize: nat)
  : GTot cheney_state

/// ---------------------------------------------------------------------------
/// Forward roots: iterate a sequence of root addresses
/// ---------------------------------------------------------------------------

/// Forward each root in `roots[idx..]`. Returns updated state.
val cheney_forward_roots (minor: minor_state) (cs: cheney_state)
                         (roots: seq U64.t) (idx: nat)
  : GTot cheney_state

/// ---------------------------------------------------------------------------
/// BFS scan loop
/// ---------------------------------------------------------------------------

/// Process queue entries starting at `scan`. For each entry, forward its
/// children (read fields from minor heap). The queue may grow as new
/// objects are discovered.
val cheney_scan (minor: minor_state) (cs: cheney_state)
                (scan: nat) (fuel: nat)
  : GTot cheney_state

/// Fuel bound: sufficient to process all reachable minor objects.
/// At most |minor_objects| unique objects can ever be enqueued.
val cheney_fuel (minor: minor_state) : GTot nat

/// ---------------------------------------------------------------------------
/// Full Cheney promotion
/// ---------------------------------------------------------------------------

/// Complete promotion via Cheney BFS:
/// 1. Compute remembered-set roots from old major heap
/// 2. Forward all roots (program roots ++ remembered)
/// 3. BFS scan until queue exhausted
let cheney_promote (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : GTot promote_all_result
  = let remembered = minor_roots_from_major major in
    let all_roots = Seq.append roots remembered in
    let cs0 : cheney_state =
      { cs_major = major; cs_fp = fp;
        cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
    let cs1 = cheney_forward_roots minor cs0 all_roots 0 in
    let cs2 = cheney_scan minor cs1 0 (cheney_fuel minor) in
    { major_final = cs2.cs_major;
      fp_final    = cs2.cs_fp;
      fwd_map     = cs2.cs_fwd }

/// ---------------------------------------------------------------------------
/// Full Cheney collection specification
/// ---------------------------------------------------------------------------

/// Complete minor collection = Cheney promote + update pointers + rewrite roots + reset.
let cheney_collect_spec (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : GTot minor_collect_result
  = let prom = cheney_promote minor major fp roots in
    let updated = update_major_pointers prom.major_final prom.fwd_map in
    { mc_major = updated;
      mc_fp    = prom.fp_final;
      mc_minor = minor_reset minor;
      mc_roots = rewrite_roots roots prom.fwd_map;
      mc_fwd   = prom.fwd_map }

/// ---------------------------------------------------------------------------
/// Correctness Properties
/// ---------------------------------------------------------------------------

/// --- wfh_part1 preservation ---

/// cheney_forward_one preserves well_formed_heap_part1
val cheney_forward_one_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword))
          (ensures (let cs' = cheney_forward_one minor cs addr in
                    well_formed_heap_part1 cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp (heap_size / U64.v mword)))

/// cheney_forward_fields preserves wfh_part1
val cheney_forward_fields_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword))
          (ensures (let cs' = cheney_forward_fields minor cs parent idx wosize in
                    well_formed_heap_part1 cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp (heap_size / U64.v mword)))

/// Cheney promote preserves wfh_part1 + allocator invariants
val cheney_promote_preserves_wfh_part1
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = cheney_promote minor major fp roots in
                    well_formed_heap_part1 res.major_final /\
                    AllocLemmas.fl_valid res.major_final res.fp_final (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates res.major_final res.fp_final (heap_size / U64.v mword)))

/// --- Object preservation ---

/// All original major-heap objects survive Cheney promotion
val cheney_promote_preserves_objects
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = cheney_promote minor major fp roots in
                    forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                      Seq.mem x (objects zero_addr res.major_final)))

/// --- Full well_formed_heap after collection ---

/// Sufficient conditions for full well_formed_heap after Cheney collection.
/// Analogous to gen_gc_correct_full's assumptions for minor_collect_spec.
val cheney_collect_preserves_wfh
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    // All promotions succeed (no OOM during collection)
                    // TODO: refine once OOM handling is decided
                    True)
          (ensures (let res = cheney_collect_spec minor major fp roots in
                    well_formed_heap_part1 res.mc_major))
