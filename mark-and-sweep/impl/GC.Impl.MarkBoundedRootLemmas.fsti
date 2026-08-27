module GC.Impl.MarkBoundedRootLemmas

module U64 = FStar.UInt64
module Seq = FStar.Seq
module SpecMark = GC.Spec.Mark
module SpecObject = GC.Spec.Object
module SpecFields = GC.Spec.Fields
module HeapModel = GC.Spec.HeapModel
module MarkBounded = GC.Impl.MarkBounded

open GC.Spec.Base

val darken_roots_bounded_prefix_base
  (g: heap) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t) (cap: nat)
  : Lemma
      (ensures MarkBounded.darken_roots_bounded_prefix_spec g st roots 0 cap == (g, st))

val check_and_darken_bounded_spec_length_increases_at_most_one
  (g: heap) (st: Seq.seq obj_addr) (v: U64.t) (cap: nat)
  : Lemma
      (ensures
        Seq.length (snd (MarkBounded.check_and_darken_bounded_spec g st v cap)) <=
        Seq.length st + 1)

val darken_roots_bounded_prefix_length_increases_at_most
  (g: heap) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (idx: nat{idx <= Seq.length roots}) (cap: nat)
  : Lemma
      (ensures
        Seq.length (snd (MarkBounded.darken_roots_bounded_prefix_spec g st roots idx cap)) <=
        Seq.length st + idx)

val check_and_darken_bounded_spec_preserves_gray_objects_on_stack
  (g: heap) (st: Seq.seq obj_addr) (v: U64.t) (cap: nat)
  : Lemma
      (requires
        SpecMark.gray_objects_on_stack g st /\
        Seq.length st < cap)
      (ensures
        SpecMark.gray_objects_on_stack
          (fst (MarkBounded.check_and_darken_bounded_spec g st v cap))
          (snd (MarkBounded.check_and_darken_bounded_spec g st v cap)))

val check_and_darken_bounded_spec_preserves_stack_mem
  (g: heap) (st: Seq.seq obj_addr) (v: U64.t) (cap: nat) (x: obj_addr)
  : Lemma
      (requires Seq.mem x st)
      (ensures
        Seq.mem x (snd (MarkBounded.check_and_darken_bounded_spec g st v cap)))

val check_and_darken_bounded_spec_preserves_not_black
  (g: heap) (st: Seq.seq obj_addr) (v: U64.t) (cap: nat) (x: obj_addr)
  : Lemma
      (requires ~(SpecObject.is_black x g))
      (ensures
        ~(SpecObject.is_black x (fst (MarkBounded.check_and_darken_bounded_spec g st v cap))))

val check_and_darken_bounded_spec_preserves_not_blue
  (g: heap) (st: Seq.seq obj_addr) (v: U64.t) (cap: nat) (x: obj_addr)
  : Lemma
      (requires ~(SpecObject.is_blue x g))
      (ensures
        ~(SpecObject.is_blue x (fst (MarkBounded.check_and_darken_bounded_spec g st v cap))))

val check_and_darken_bounded_spec_pushes_valid_nonblack_nonblue_root
  (g: heap) (st: Seq.seq obj_addr) (v: U64.t) (cap: nat)
  : Lemma
      (requires
        U64.v v >= U64.v zero_addr + U64.v mword /\
        U64.v v < heap_size /\
        U64.v v % U64.v mword == 0 /\
        MarkBounded.root_points_to_object g v /\
        ~(SpecObject.is_black (v <: obj_addr) g) /\
        ~(SpecObject.is_blue (v <: obj_addr) g) /\
        SpecMark.gray_objects_on_stack g st /\
        Seq.length st < cap)
      (ensures
        Seq.mem (v <: obj_addr)
          (snd (MarkBounded.check_and_darken_bounded_spec g st v cap)))

val check_and_darken_bounded_spec_preserves_stack_roots
  (g: heap) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (v: U64.t) (cap: nat)
  : Lemma
      (requires
        MarkBounded.root_points_to_object g v /\
        (forall (x: obj_addr). Seq.mem x st ==> Seq.mem (x <: U64.t) roots) /\
        Seq.mem v roots)
      (ensures
        (forall (x: obj_addr).
          Seq.mem x (snd (MarkBounded.check_and_darken_bounded_spec g st v cap)) ==>
          Seq.mem (x <: U64.t) roots))

val darken_roots_bounded_prefix_preserves_gray_objects_on_stack
  (g: heap) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (idx: nat{idx <= Seq.length roots}) (cap: nat)
  : Lemma
      (requires
        SpecMark.gray_objects_on_stack g st /\
        Seq.length st + idx <= cap)
      (ensures
        SpecMark.gray_objects_on_stack
          (fst (MarkBounded.darken_roots_bounded_prefix_spec g st roots idx cap))
          (snd (MarkBounded.darken_roots_bounded_prefix_spec g st roots idx cap)))

val darken_roots_bounded_spec_preserves_gray_objects_on_stack
  (g: heap) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t) (cap: nat)
  : Lemma
      (requires
        SpecMark.gray_objects_on_stack g st /\
        Seq.length st + Seq.length roots <= cap)
      (ensures
        SpecMark.gray_objects_on_stack
          (fst (MarkBounded.darken_roots_bounded_spec g st roots cap))
          (snd (MarkBounded.darken_roots_bounded_spec g st roots cap)))

/// ---------------------------------------------------------------------------
/// Root darkening does not change the object graph
/// ---------------------------------------------------------------------------
///
/// Darkening only recolours headers, so the vertex and edge sets are untouched.
/// This is what lets a caller compose a statement about the pre-darkening heap
/// (e.g. the minor collector's reachable-subgraph isomorphism) with one about
/// the post-darkening heap (the major collector's).

val check_and_darken_bounded_spec_preserves_create_graph
  (g: heap) (st: Seq.seq obj_addr) (v: U64.t) (cap: nat)
  : Lemma
      (requires
        SpecFields.well_formed_heap g /\
        MarkBounded.root_points_to_object g v)
      (ensures
        (let g' = fst (MarkBounded.check_and_darken_bounded_spec g st v cap) in
         SpecFields.well_formed_heap g' /\
         HeapModel.create_graph g' == HeapModel.create_graph g))

val darken_roots_bounded_prefix_preserves_create_graph
  (g: heap) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (idx: nat{idx <= Seq.length roots}) (cap: nat)
  : Lemma
      (requires
        SpecFields.well_formed_heap g /\
        (forall (i: nat). i < idx ==>
           MarkBounded.root_points_to_object g (Seq.index roots i)))
      (ensures
        (let g' = fst (MarkBounded.darken_roots_bounded_prefix_spec g st roots idx cap) in
         SpecFields.well_formed_heap g' /\
         HeapModel.create_graph g' == HeapModel.create_graph g))

val darken_roots_bounded_spec_preserves_create_graph
  (g: heap) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t) (cap: nat)
  : Lemma
      (requires
        SpecFields.well_formed_heap g /\
        (forall (i: nat). i < Seq.length roots ==>
           MarkBounded.root_points_to_object g (Seq.index roots i)))
      (ensures
        (let g' = fst (MarkBounded.darken_roots_bounded_spec g st roots cap) in
         SpecFields.well_formed_heap g' /\
         HeapModel.create_graph g' == HeapModel.create_graph g))
