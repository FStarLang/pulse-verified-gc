/// ---------------------------------------------------------------------------
/// GC.Gen.Correctness — Implementation of generational GC correctness
/// ---------------------------------------------------------------------------

module GC.Gen.Correctness

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Spec.HeapModel
open GC.Spec.DFS
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Allocator

module MajorCorrectness = GC.Spec.Correctness
module HeapGraph = GC.Spec.HeapGraph
module AllocLemmas = GC.Spec.Allocator.Lemmas

/// ---------------------------------------------------------------------------
/// Composition bridge
/// ---------------------------------------------------------------------------

/// Proof outline for minor_preserves_major_objects:
/// 1. minor_collect_spec = promote_all_spec + update_major_pointers (identity)
/// 2. promote_all_spec = promote_all_aux (recursive)
/// 3. Each step: promote_object = alloc_spec + copy_fields
/// 4. alloc_spec_preserves_objects (PROVEN in GC.Spec.Allocator.Lemmas)
///    → objects membership preserved through allocation
/// 5. copy_fields writes within allocated block → write_word_preserves_objects
///    → objects equality (hence membership) preserved
/// 6. By induction on promote_all_aux, objects membership is preserved

let minor_preserves_major_objects
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires minor_wf minor /\ well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = minor_collect_spec minor major fp roots in
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                      Seq.mem x (objects zero_addr res.mc_major)))) =
  let live_set = minor_objects minor in
  promote_all_preserves_objects minor major fp live_set;
  let prom_res = promote_all_spec minor major fp live_set in
  update_major_pointers_id prom_res.major_final prom_res.fwd_map;
  minor_collect_spec_unfold minor major fp roots

/// ---------------------------------------------------------------------------
/// The main theorem
/// ---------------------------------------------------------------------------

let gen_gc_correct
  (gs: gen_state) (roots: seq U64.t) (gray_stack: seq obj_addr)
  (fp: U64.t)
  : Lemma (requires gen_wf gs /\
                    well_formed_heap gs.gs_major /\
                    AllocLemmas.fl_valid gs.gs_major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates gs.gs_major fp (heap_size / U64.v mword))
          (ensures (let res = minor_collect_spec gs.gs_minor gs.gs_major fp roots in
                    let live_set = minor_objects gs.gs_minor in
                    let prom_res = promote_all_spec gs.gs_minor gs.gs_major fp live_set in
                    fwd_targets_in_objects prom_res.fwd_map live_set (Seq.length live_set) res.mc_major /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr gs.gs_major) ==>
                      Seq.mem x (objects zero_addr res.mc_major)) /\
                    minor_wf res.mc_minor /\ U64.v res.mc_minor.bump == 0)) =
  let minor = gs.gs_minor in
  let major = gs.gs_major in
  assert (minor_wf minor);
  let live_set = minor_objects minor in
  // Part 1: promoted objects land in promote_all_spec's major_final
  promote_all_adds_promoted minor major fp live_set;
  let prom_res = promote_all_spec minor major fp live_set in
  // Bridge: mc_major == update_major_pointers prom_res.major_final prom_res.fwd_map == prom_res.major_final
  minor_collect_spec_unfold minor major fp roots;
  update_major_pointers_id prom_res.major_final prom_res.fwd_map;
  // Now: mc_major == prom_res.major_final, so fwd_targets_in_objects transfers
  // Part 2: existing major objects survive
  minor_preserves_major_objects minor major fp roots;
  // Part 3: minor heap reset
  minor_collect_resets_minor minor major fp roots;
  ()
