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
/// Theorem placeholders (to be proven incrementally)
/// ---------------------------------------------------------------------------

let gen_gc_correct
  (gs: gen_state) (roots: seq U64.t) (gray_stack: seq obj_addr)
  (fp: U64.t)
  : Lemma (requires gen_wf gs)
          (ensures True) =
  ()

/// Proof outline for minor_preserves_major_objects:
/// 1. minor_collect_spec = promote_all_spec + update_major_pointers (identity)
/// 2. promote_all_spec = promote_all_aux (recursive)
/// 3. Each step: promote_object = alloc_spec + copy_fields
/// 4. alloc_spec_preserves_objects (PROVEN in GC.Spec.Allocator.Lemmas)
///    → objects membership preserved through allocation
/// 5. copy_fields writes within allocated block → write_word_preserves_objects
///    → objects equality (hence membership) preserved
/// 6. By induction on promote_all_aux, objects membership is preserved
///
/// Remaining work: prove the induction + copy_fields step formally.
/// The key lemma (alloc_spec_preserves_objects) is already verified.
let minor_preserves_major_objects
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires minor_wf minor /\ well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword))
          (ensures (let res = minor_collect_spec minor major fp roots in
                    (forall (x: obj_addr). Seq.mem x (objects 0UL major) ==>
                      Seq.mem x (objects 0UL res.mc_major)))) =
  admit ()
