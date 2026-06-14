module GC.Spec.ChunkedSweepCoalesce.VertexSequence

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module Defs = GC.Spec.ChunkedSweepCoalesce.Defs

val chunked_fused_aux_other_chunk_preserves_objects_from_from
  (source work: MH.major_heap)
  (proc_idx: nat{proc_idx < Seq.length source})
  (target_idx: nat)
  (proc_start target_start: hp_addr)
  (protected: obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap work /\
        proc_idx < Seq.length work /\
        target_idx < Seq.length work /\
        proc_idx <> target_idx /\
        MH.chunk_start (Seq.index work proc_idx) ==
          MH.chunk_start (Seq.index source proc_idx) /\
        MH.chunk_end (Seq.index work proc_idx) ==
          MH.chunk_end (Seq.index source proc_idx) /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index work target_idx) target_start) /\
        GC.Spec.ChunkedSweepCoalesce.PendingRun.pending_run_before_start
          work proc_idx (Seq.index source proc_idx).base proc_start
          first_blue run_words /\
        (forall (o: obj_addr).
          Seq.mem o
            (MH.objects_in_chunk_from (Seq.index source proc_idx) proc_start) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source proc_idx) o))
      (ensures
        (let final =
          fst (Defs.chunked_fused_aux
            source work
            (MH.objects_in_chunk_from (Seq.index source proc_idx) proc_start)
            first_blue run_words fp) in
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

val chunked_fused_aux_other_chunk_preserves_objects_from
  (source work: MH.major_heap)
  (proc_idx: nat{proc_idx < Seq.length source})
  (target_idx: nat)
  (target_start: hp_addr)
  (protected: obj_addr)
  (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap work /\
        proc_idx < Seq.length work /\
        target_idx < Seq.length work /\
        proc_idx <> target_idx /\
        MH.chunk_start (Seq.index work proc_idx) ==
          MH.chunk_start (Seq.index source proc_idx) /\
        MH.chunk_end (Seq.index work proc_idx) ==
          MH.chunk_end (Seq.index source proc_idx) /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index work target_idx) target_start) /\
        (forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source proc_idx)) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source proc_idx) o))
      (ensures
        (let final =
          fst (Defs.chunked_fused_aux
            source work (MH.objects_in_chunk (Seq.index source proc_idx))
            0UL 0 fp) in
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
