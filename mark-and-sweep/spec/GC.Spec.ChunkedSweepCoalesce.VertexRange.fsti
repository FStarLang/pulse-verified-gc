module GC.Spec.ChunkedSweepCoalesce.VertexRange

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module Defs = GC.Spec.ChunkedSweepCoalesce.Defs
module Range = GC.Spec.ChunkedSweepCoalesce.RangePreservation

val chunked_fused_sweep_coalesce_chunk_range_preserves_objects_from
  (source work: MH.major_heap)
  (start stop target_idx: nat)
  (target_start: hp_addr)
  (protected: obj_addr)
  (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        MH.well_formed_major_heap work /\
        Range.same_chunk_ranges source work /\
        start <= stop /\
        stop <= Seq.length source /\
        target_idx < Seq.length source /\
        target_idx < Seq.length work /\
        (target_idx < start \/ stop <= target_idx) /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index work target_idx) target_start) /\
        (forall (idx: nat). start <= idx /\ idx < stop ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o))
      (ensures
        (let final =
          fst (Defs.chunked_fused_sweep_coalesce_chunks
            (Seq.slice source start stop) source work fp) in
         MH.well_formed_major_heap final /\
         target_idx < Seq.length final /\
         MH.objects_in_chunk_from (Seq.index final target_idx) target_start ==
           MH.objects_in_chunk_from (Seq.index work target_idx) target_start /\
         Seq.mem protected
           (MH.objects_in_chunk_from (Seq.index final target_idx) target_start) /\
         MH.object_wosize_in_chunk (Seq.index final target_idx) protected ==
           MH.object_wosize_in_chunk (Seq.index work target_idx) protected /\
         MH.chunk_start (Seq.index final target_idx) ==
           MH.chunk_start (Seq.index work target_idx) /\
         MH.chunk_end (Seq.index final target_idx) ==
           MH.chunk_end (Seq.index work target_idx)))

val chunked_fused_sweep_coalesce_prefix_preserves_objects_from
  (source work: MH.major_heap)
  (target_idx: nat)
  (target_start: hp_addr)
  (protected: obj_addr)
  (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        MH.well_formed_major_heap work /\
        Range.same_chunk_ranges source work /\
        target_idx < Seq.length source /\
        target_idx < Seq.length work /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index work target_idx) target_start) /\
        (forall (idx: nat). idx < target_idx ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o))
      (ensures
        (let final =
          fst (Defs.chunked_fused_sweep_coalesce_chunks
            (Seq.slice source 0 target_idx) source work fp) in
         MH.well_formed_major_heap final /\
         target_idx < Seq.length final /\
         MH.objects_in_chunk_from (Seq.index final target_idx) target_start ==
           MH.objects_in_chunk_from (Seq.index work target_idx) target_start /\
         Seq.mem protected
           (MH.objects_in_chunk_from (Seq.index final target_idx) target_start) /\
         MH.object_wosize_in_chunk (Seq.index final target_idx) protected ==
           MH.object_wosize_in_chunk (Seq.index work target_idx) protected /\
         MH.chunk_start (Seq.index final target_idx) ==
           MH.chunk_start (Seq.index work target_idx) /\
         MH.chunk_end (Seq.index final target_idx) ==
           MH.chunk_end (Seq.index work target_idx)))

val chunked_fused_sweep_coalesce_suffix_preserves_objects_from
  (source work: MH.major_heap)
  (target_idx: nat)
  (target_start: hp_addr)
  (protected: obj_addr)
  (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        MH.well_formed_major_heap work /\
        Range.same_chunk_ranges source work /\
        target_idx < Seq.length source /\
        target_idx < Seq.length work /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index work target_idx) target_start) /\
        (forall (idx: nat). target_idx < idx /\ idx < Seq.length source ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o))
      (ensures
        (let final =
          fst (Defs.chunked_fused_sweep_coalesce_chunks
            (Seq.slice source (target_idx + 1) (Seq.length source))
            source work fp) in
         MH.well_formed_major_heap final /\
         target_idx < Seq.length final /\
         MH.objects_in_chunk_from (Seq.index final target_idx) target_start ==
           MH.objects_in_chunk_from (Seq.index work target_idx) target_start /\
         Seq.mem protected
           (MH.objects_in_chunk_from (Seq.index final target_idx) target_start) /\
         MH.object_wosize_in_chunk (Seq.index final target_idx) protected ==
           MH.object_wosize_in_chunk (Seq.index work target_idx) protected /\
         MH.chunk_start (Seq.index final target_idx) ==
           MH.chunk_start (Seq.index work target_idx) /\
         MH.chunk_end (Seq.index final target_idx) ==
           MH.chunk_end (Seq.index work target_idx)))
