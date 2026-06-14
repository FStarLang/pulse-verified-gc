module GC.Spec.ChunkedMarkBounded.Metadata

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module BReady = GC.Spec.ChunkedMarkBounded.TargetReady

val chunked_push_children_bounded_preserves_wosize_of_object
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_push_children_bounded_preservation_ready mh obj i ws /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        (let (mh', _) =
          BDefs.chunked_push_children_bounded mh st obj i ws cap in
         SweepDefs.chunked_wosize_of_object mh' target ==
         SweepDefs.chunked_wosize_of_object mh target))

val chunked_mark_step_bounded_preserves_wosize_of_object
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_step_bounded_preservation_ready mh st cap /\
        BReady.chunked_bounded_stack_props mh st /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        (let (mh', _) = BDefs.chunked_mark_step_bounded mh st cap in
         SweepDefs.chunked_wosize_of_object mh' target ==
         SweepDefs.chunked_wosize_of_object mh target))
