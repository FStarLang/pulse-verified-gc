module GC.Spec.ChunkedMarkBounded.Completion

module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module BReady = GC.Spec.ChunkedMarkBounded.TargetReady

val chunked_count_non_black_zero_no_gray
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        BDefs.chunked_count_non_black mh == 0 /\
        Seq.mem obj (MH.major_objects mh))
      (ensures ~(BDefs.chunked_is_gray mh obj))

val chunked_rescan_heap_empty_no_gray
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (obj: obj_addr)
  : Lemma
      (requires
        Seq.length (MH.major_objects mh) <= cap /\
        Seq.length (BDefs.chunked_rescan_heap mh Seq.empty cap) = 0 /\
        Seq.mem obj (MH.major_objects mh))
      (ensures ~(BDefs.chunked_is_gray mh obj))

val chunked_mark_inner_loop_count_nonincreasing
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_inner_loop_preservation_ready mh st cap fuel /\
        BReady.chunked_bounded_stack_props mh st)
      (ensures
        (let (mh', _) =
           BDefs.chunked_mark_inner_loop mh st cap fuel in
         BDefs.chunked_count_non_black mh' <=
         BDefs.chunked_count_non_black mh))

val chunked_mark_inner_loop_count_decreases
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : Lemma
      (requires
        fuel > 0 /\
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_inner_loop_preservation_ready mh st cap fuel /\
        BReady.chunked_bounded_stack_props mh st)
      (ensures
        (let (mh', _) =
           BDefs.chunked_mark_inner_loop mh st cap fuel in
         BDefs.chunked_count_non_black mh' <
         BDefs.chunked_count_non_black mh))

val chunked_mark_bounded_completes
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        fuel >= BDefs.chunked_count_non_black mh)
      (ensures
        forall (obj: obj_addr).
          Seq.mem obj
            (MH.major_objects (BDefs.chunked_mark_bounded mh cap fuel)) ==>
          ~(BDefs.chunked_is_gray
            (BDefs.chunked_mark_bounded mh cap fuel) obj))
