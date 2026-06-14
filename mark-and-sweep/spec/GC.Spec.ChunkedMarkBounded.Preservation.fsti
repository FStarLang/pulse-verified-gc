module GC.Spec.ChunkedMarkBounded.Preservation

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap

val chunked_push_children_bounded_preservation_ready
  (mh: MH.major_heap)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : GTot prop

val chunked_push_children_bounded_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_push_children_bounded_preservation_ready mh obj i ws)
      (ensures
        (let (mh', _) =
          GC.Spec.ChunkedMarkBounded.Defs.chunked_push_children_bounded
            mh st obj i ws cap in
         MH.major_objects mh' == MH.major_objects mh))

val chunked_push_children_bounded_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_push_children_bounded_preservation_ready mh obj i ws)
      (ensures
        (let (mh', _) =
          GC.Spec.ChunkedMarkBounded.Defs.chunked_push_children_bounded
            mh st obj i ws cap in
         MH.well_formed_major_heap mh'))

val chunked_mark_step_bounded_preservation_ready
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : GTot prop

val chunked_mark_step_bounded_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_step_bounded_preservation_ready mh st cap)
      (ensures
        (let (mh', _) =
          GC.Spec.ChunkedMarkBounded.Defs.chunked_mark_step_bounded
            mh st cap in
         MH.major_objects mh' == MH.major_objects mh))

val chunked_mark_step_bounded_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_step_bounded_preservation_ready mh st cap)
      (ensures
        (let (mh', _) =
          GC.Spec.ChunkedMarkBounded.Defs.chunked_mark_step_bounded
            mh st cap in
         MH.well_formed_major_heap mh'))

val chunked_mark_inner_loop_preservation_ready
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : GTot prop

val chunked_mark_inner_loop_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_inner_loop_preservation_ready mh st cap fuel)
      (ensures
        (let (mh', _) =
          GC.Spec.ChunkedMarkBounded.Defs.chunked_mark_inner_loop
            mh st cap fuel in
         MH.major_objects mh' == MH.major_objects mh))

val chunked_mark_inner_loop_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_inner_loop_preservation_ready mh st cap fuel)
      (ensures
        (let (mh', _) =
          GC.Spec.ChunkedMarkBounded.Defs.chunked_mark_inner_loop
            mh st cap fuel in
         MH.well_formed_major_heap mh'))

val chunked_mark_bounded_preservation_ready
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : GTot prop

val chunked_mark_bounded_preserves_major_objects
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_bounded_preservation_ready mh cap fuel)
      (ensures
        MH.major_objects
          (GC.Spec.ChunkedMarkBounded.Defs.chunked_mark_bounded
            mh cap fuel) ==
        MH.major_objects mh)

val chunked_mark_bounded_preserves_well_formed
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_bounded_preservation_ready mh cap fuel)
      (ensures
        MH.well_formed_major_heap
          (GC.Spec.ChunkedMarkBounded.Defs.chunked_mark_bounded
            mh cap fuel))
