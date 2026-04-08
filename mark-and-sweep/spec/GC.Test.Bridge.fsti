module GC.Test.Bridge

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
open GC.Spec.Allocator.Lemmas
open GC.Spec.Mark
open GC.Spec.SweepInv
open GC.Spec.HeapModel
open GC.Spec.Graph

/// Reading any word from a zeroed heap gives 0UL.
val zeroed_heap_read_word (addr: hp_addr)
  : Lemma (read_word (Seq.create heap_size 0uy) addr == 0UL)

/// After init_heap_spec on a zeroed heap, objects 0UL g' == [mword].
val init_objects_eq (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', fp) = init_heap_spec g in
                    fp == mword /\
                    objects 0UL g' == Seq.cons (mword <: obj_addr) Seq.empty))

/// well_formed_heap holds after init_heap_spec on a zeroed heap.
val init_wf (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in well_formed_heap g'))

/// fl_valid holds after init_heap_spec on a zeroed heap.
val init_fl_valid (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', fp) = init_heap_spec g in
                    fl_valid g' fp (heap_size / FStar.UInt64.v mword)))

/// no_black_objects holds after init_heap_spec on a zeroed heap.
val init_no_black (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in no_black_objects g'))

/// no_gray_objects holds after init_heap_spec on a zeroed heap.
val init_no_gray (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in no_gray_objects g'))

/// no_pointer_to_blue holds after init_heap_spec on a zeroed heap.
val init_no_pointer_to_blue (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in no_pointer_to_blue g'))

/// objects list is non-empty after init_heap_spec on a zeroed heap.
val init_objects_nonempty (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in
                    Seq.length (objects 0UL g') > 0))

/// graph_wf holds for the init heap (no edges → vacuously well-formed).
val init_graph_wf (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in
                    graph_wf (create_graph g')))

/// heap_objects_dense holds after init_heap_spec on a zeroed heap.
/// With the weakened predicate (guarded by membership in objects 0UL g),
/// init density is trivially satisfied.
val init_dense (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in
                    heap_objects_dense g'))

/// fl_chain_terminates holds after init_heap_spec on a zeroed heap.
/// The initial free list is a single node (mword → 0UL), which terminates in 1 step.
val init_fl_chain_terminates (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', fp) = init_heap_spec g in
                    fl_chain_terminates g' fp (heap_size / FStar.UInt64.v mword)))

open GC.Spec.Sweep

/// Returns true when the fl_valid chain from fp does NOT visit `skip`.
let rec chain_not_visits (g: heap) (fp: FStar.UInt64.t) (skip: obj_addr) (fuel: nat)
  : Tot bool (decreases fuel)
  = if fuel = 0 then true
    else if fp = 0UL then true
    else if FStar.UInt64.v fp < FStar.UInt64.v mword then true
    else if FStar.UInt64.v fp >= heap_size then true
    else if FStar.UInt64.v fp % FStar.UInt64.v mword <> 0 then true
    else if fp = skip then false
    else
      let hd = hd_address (fp <: obj_addr) in
      if FStar.UInt64.v hd + 16 > heap_size then true
      else chain_not_visits g (read_word g (fp <: obj_addr)) skip (fuel - 1)

/// mark with an empty stack is the identity on the heap.
val mark_empty_identity (g: heap)
  : Lemma (mark g Seq.empty == g)

/// After sweep, the returned free pointer is fl_valid.
val sweep_produces_fl_valid (g: heap) (fp: FStar.UInt64.t)
  : Lemma
    (requires well_formed_heap g /\
              fl_valid g fp (heap_size / FStar.UInt64.v mword) /\
              fp_in_heap fp g /\
              (forall (o: obj_addr). Seq.mem o (objects 0UL g) /\ is_white o g ==>
                FStar.UInt64.v (wosize_of_object o g) >= 1) /\
              (forall (o: obj_addr). Seq.mem o (objects 0UL g) /\ ~(is_blue o g) ==>
                chain_not_visits g fp o (heap_size / FStar.UInt64.v mword)))
    (ensures (let (g', fp') = sweep g fp in
              fl_valid g' fp' (heap_size / FStar.UInt64.v mword)))

/// All objects are blue after init_heap_spec on a zeroed heap.
val init_all_blue (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in
                    forall (obj: obj_addr). Seq.mem obj (objects 0UL g') ==> is_blue obj g'))
