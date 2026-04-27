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

/// ---------------------------------------------------------------------------
/// Theorem placeholders (to be proven incrementally)
/// ---------------------------------------------------------------------------

let gen_gc_correct
  (gs: gen_state) (roots: seq U64.t) (gray_stack: seq obj_addr)
  (fp: U64.t)
  : Lemma (requires gen_wf gs)
          (ensures True) =
  ()

let minor_preserves_major_objects
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires minor_wf minor /\ well_formed_heap major)
          (ensures (let res = minor_collect_spec minor major fp roots in
                    (forall (x: obj_addr). Seq.mem x (objects 0UL major) ==>
                      Seq.mem x (objects 0UL res.mc_major)))) =
  admit ()
