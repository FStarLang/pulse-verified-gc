/// ---------------------------------------------------------------------------
/// GC.Gen.Allocator — Unified generational allocator specification
/// ---------------------------------------------------------------------------
///
/// Routes allocation requests based on object size:
/// - wosize <= max_young_wosize → bump-allocate in minor heap
/// - wosize > max_young_wosize → free-list allocate in major heap
///
/// When the minor heap is full, triggers a minor collection before retrying.

module GC.Gen.Allocator

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote

/// ---------------------------------------------------------------------------
/// Generational State
/// ---------------------------------------------------------------------------

/// Combined state of both heaps
noeq
type gen_state = {
  gs_minor : minor_state;   // minor heap (bump pointer)
  gs_major : heap;           // major heap (free-list)
  gs_fp    : U64.t;          // major-heap free-list pointer
}

/// Well-formedness of the generational state
let gen_wf (gs: gen_state) : prop =
  minor_wf gs.gs_minor /\
  GC.Spec.Fields.well_formed_heap gs.gs_major

/// ---------------------------------------------------------------------------
/// Allocation Spec
/// ---------------------------------------------------------------------------

/// Result of a generational allocation
noeq
type gen_alloc_result = {
  ga_state : gen_state;     // updated state
  ga_addr  : U64.t;         // object address (0 if OOM)
  ga_in_minor : bool;       // true if allocated in minor heap
}

/// Allocate an object of the given wosize and tag.
///
/// Routing logic:
/// - If wosize <= max_young_wosize AND minor has room → bump-allocate in minor
/// - If wosize <= max_young_wosize AND minor full → trigger minor collection, then retry
/// - If wosize > max_young_wosize → allocate directly in major heap
val gen_alloc_spec (gs: gen_state) (wosize: nat{wosize > 0}) (tag: nat{tag < 256})
                   (roots: seq U64.t)  // needed for minor collection if triggered
  : GTot gen_alloc_result

/// ---------------------------------------------------------------------------
/// Properties
/// ---------------------------------------------------------------------------

/// Small objects go to the minor heap (when there's room)
val small_alloc_goes_to_minor (gs: gen_state) (wosize: nat{wosize > 0 /\ wosize <= max_young_wosize})
                              (tag: nat{tag < 256}) (roots: seq U64.t)
  : Lemma (requires gen_wf gs /\ minor_can_alloc gs.gs_minor wosize)
          (ensures (let res = gen_alloc_spec gs wosize tag roots in
                    res.ga_in_minor == true /\
                    res.ga_addr <> 0UL))

/// Large objects go directly to the major heap
val large_alloc_goes_to_major (gs: gen_state) (wosize: nat{wosize > max_young_wosize})
                              (tag: nat{tag < 256}) (roots: seq U64.t)
  : Lemma (requires gen_wf gs)
          (ensures (let res = gen_alloc_spec gs wosize tag roots in
                    res.ga_in_minor == false))
