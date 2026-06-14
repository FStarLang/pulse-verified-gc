module GC.Spec.ChunkedMarkBounded.StackStep

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module BReady = GC.Spec.ChunkedMarkBounded.TargetReady

val chunked_is_white_not_gray
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_white mh obj)
      (ensures ~(BDefs.chunked_is_gray mh obj))

val chunked_push_children_bounded_preserves_bounded_stack_props
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_push_children_bounded_preservation_ready mh obj i ws /\
        BReady.chunked_bounded_stack_props mh st)
      (ensures
        (let (mh', st') =
          BDefs.chunked_push_children_bounded mh st obj i ws cap in
         BReady.chunked_bounded_stack_props mh' st'))

val chunked_mark_step_bounded_preserves_bounded_stack_props
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_step_bounded_preservation_ready mh st cap /\
        BReady.chunked_bounded_stack_props mh st)
      (ensures
        (let (mh', st') =
          BDefs.chunked_mark_step_bounded mh st cap in
         BReady.chunked_bounded_stack_props mh' st'))

