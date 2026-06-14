module GC.Spec.ChunkedMarkBounded.CountStep

module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation

val chunked_mark_step_bounded_decreases_count
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_step_bounded_preservation_ready mh st cap /\
        Seq.mem (Seq.head st) (MH.major_objects mh) /\
        BDefs.chunked_is_gray mh (Seq.head st))
      (ensures
        (let (mh', _) = BDefs.chunked_mark_step_bounded mh st cap in
         BDefs.chunked_count_non_black mh' <
         BDefs.chunked_count_non_black mh))

