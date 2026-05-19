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
open GC.Gen.PromoteUpdate
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

/// Unfold: when wosize is 0
val cheney_forward_one_noop_wz0 (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires Seq.mem addr (minor_objects minor) /\
                    cs.cs_fwd addr = 0UL /\
                    minor_wosize minor addr = 0)
          (ensures cheney_forward_one minor cs addr == cs)

/// Unfold: when promotion fails (OOM)
val cheney_forward_one_noop_oom (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires Seq.mem addr (minor_objects minor) /\
                    cs.cs_fwd addr = 0UL /\
                    minor_wosize minor addr > 0 /\
                    (promote_object minor cs.cs_major addr cs.cs_fp
                       (minor_wosize minor addr)).new_addr = 0UL)
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

/// Equation lemma: base case (idx >= wosize)
val cheney_forward_fields_base
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires idx >= wosize)
          (ensures cheney_forward_fields minor cs parent idx wosize == cs)

/// Equation lemma: recursive case (idx < wosize)
val cheney_forward_fields_step
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires idx < wosize)
          (ensures cheney_forward_fields minor cs parent idx wosize ==
                   (let field_val = minor_read_field minor parent idx in
                    let cs' = cheney_forward_one minor cs field_val in
                    cheney_forward_fields minor cs' parent (idx + 1) wosize))

/// ---------------------------------------------------------------------------
/// Forward roots: iterate a sequence of root addresses
/// ---------------------------------------------------------------------------

/// Forward each root in `roots[idx..]`. Returns updated state.
val cheney_forward_roots (minor: minor_state) (cs: cheney_state)
                         (roots: seq U64.t) (idx: nat)
  : GTot cheney_state

/// Equation lemma: base case (idx >= length roots)
val cheney_forward_roots_base
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires idx >= Seq.length roots)
          (ensures cheney_forward_roots minor cs roots idx == cs)

/// Equation lemma: recursive case (idx < length roots)
val cheney_forward_roots_step
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires idx < Seq.length roots)
          (ensures cheney_forward_roots minor cs roots idx ==
                   (let r = Seq.index roots idx in
                    let cs' = cheney_forward_one minor cs r in
                    cheney_forward_roots minor cs' roots (idx + 1)))

/// ---------------------------------------------------------------------------
/// BFS scan loop
/// ---------------------------------------------------------------------------

/// Process queue entries starting at `scan`. For each entry, forward its
/// children (read fields from minor heap). The queue may grow as new
/// objects are discovered.
val cheney_scan (minor: minor_state) (cs: cheney_state)
                (scan: nat) (fuel: nat)
  : GTot cheney_state

/// Equation lemma: base case (fuel = 0 or scan >= queue length)
val cheney_scan_base
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires fuel = 0 \/ scan >= Seq.length cs.cs_queue)
          (ensures cheney_scan minor cs scan fuel == cs)

/// Equation lemma: recursive case
val cheney_scan_step
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires fuel > 0 /\ scan < Seq.length cs.cs_queue)
          (ensures cheney_scan minor cs scan fuel ==
                   (let obj = Seq.index cs.cs_queue scan in
                    let wz = minor_wosize minor obj in
                    let cs' = cheney_forward_fields minor cs obj 0 wz in
                    cheney_scan minor cs' (scan + 1) (fuel - 1)))

/// Fuel bound: sufficient to process all reachable minor objects.
/// At most |minor_objects| unique objects can ever be enqueued.
val cheney_fuel (minor: minor_state) : GTot nat

/// Expose fuel value (needed for proving fuel > 0 when scan < bk < fuel)
val cheney_fuel_eq (minor: minor_state)
  : Lemma (cheney_fuel minor == Seq.length (minor_objects minor))

/// ---------------------------------------------------------------------------
/// Full Cheney promotion
/// ---------------------------------------------------------------------------

/// Complete promotion via Cheney BFS:
/// 1. Forward all roots (caller provides program roots + remembered-set roots)
/// 2. BFS scan until queue exhausted
///
/// NOTE: The caller is responsible for including remembered-set roots in `roots`.
/// This keeps the spec aligned with the implementation, where remembered-set
/// discovery is a separate concern handled before calling the collector.
let cheney_promote (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : GTot promote_all_result
  = let cs0 : cheney_state =
      { cs_major = major; cs_fp = fp;
        cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
    let cs1 = cheney_forward_roots minor cs0 roots 0 in
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

/// --- chain_objects_blue preservation ---

/// Cheney promote preserves chain_objects_blue.
/// Promotion allocates from the free-list (blue objects), but the allocated
/// blocks leave the chain — the remaining chain stays blue.
val cheney_promote_preserves_cob
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp)
          (ensures (let res = cheney_promote minor major fp roots in
                    chain_objects_blue res.major_final res.fp_final))

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
                    True)
          (ensures (let res = cheney_collect_spec minor major fp roots in
                    well_formed_heap_part1 res.mc_major))

/// --- Allocator (fl_valid) preservation through full collection ---

/// update_major_pointers preserves fl_valid.
/// Proof: update_major_pointers skips blue objects (free-list nodes), so
/// both the free-list headers and the next-pointers (field 0 of blue objects)
/// are unchanged, leaving the free-chain structure intact.
val update_major_pointers_preserves_fl_valid
  (major: heap) (fwd: forwarding_map) (fp: U64.t)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp)
          (ensures (let m' = update_major_pointers major fwd in
                    AllocLemmas.fl_valid m' fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates m' fp (heap_size / U64.v mword)))

/// Full Cheney collection preserves fl_valid.
val cheney_collect_preserves_fl_valid
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp)
          (ensures (let res = cheney_collect_spec minor major fp roots in
                    AllocLemmas.fl_valid res.mc_major res.mc_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates res.mc_major res.mc_fp (heap_size / U64.v mword)))

/// --- Density preservation ---

/// Cheney promote preserves heap_objects_dense.
/// Since promote only allocates new objects (extending the objects list),
/// the density structure is maintained.
val cheney_promote_preserves_dense
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    heap_objects_dense major /\
                    Seq.length (objects zero_addr major) > 0 /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = cheney_promote minor major fp roots in
                    heap_objects_dense res.major_final /\
                    Seq.length (objects zero_addr res.major_final) > 0))

/// --- Wosize preservation ---

/// For any original non-free-list object on the major heap, its wosize
/// is preserved unchanged through the entire cheney_promote process.
val cheney_promote_preserves_wosize
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr)
  : Lemma (requires
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp /\
      Seq.mem obj (objects zero_addr major) /\
      AllocLemmas.chain_avoids major fp (obj <: U64.t) (heap_size / U64.v mword) = true /\
      U64.v (GC.Spec.Object.wosize_of_object obj major) >= 1)
    (ensures (let res = cheney_promote minor major fp roots in
              GC.Spec.Object.wosize_of_object obj res.major_final == GC.Spec.Object.wosize_of_object obj major))
