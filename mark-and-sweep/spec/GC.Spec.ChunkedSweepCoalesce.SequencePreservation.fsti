module GC.Spec.ChunkedSweepCoalesce.SequencePreservation

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap

val chunked_fused_aux_preserves_read_from_chunk_before
  (source work: MH.major_heap)
  (idx: nat)
  (fp: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        idx < Seq.length source /\
        MH.read_word_in_major work read_addr == Some old /\
        MH.chunk_end (Seq.index source idx) <= U64.v read_addr /\
        (forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
                  source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o))
      (ensures
        (let final =
          fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_fused_aux
           source work (MH.objects_in_chunk (Seq.index source idx))
           0UL 0 fp) in
         MH.read_word_in_major final read_addr == Some old))

val chunked_fused_aux_preserves_read_from_chunk_after
  (source work: MH.major_heap)
  (idx: nat)
  (fp: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        idx < Seq.length source /\
        MH.read_word_in_major work read_addr == Some old /\
        U64.v read_addr + U64.v mword <=
          MH.chunk_start (Seq.index source idx))
      (ensures
        (let final =
          fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_fused_aux
           source work (MH.objects_in_chunk (Seq.index source idx))
           0UL 0 fp) in
         MH.read_word_in_major final read_addr == Some old))

val chunked_fused_aux_preserves_read_from_other_chunk
  (source work: MH.major_heap)
  (proc_idx target_idx: nat)
  (fp: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        proc_idx < Seq.length source /\
        target_idx < Seq.length source /\
        proc_idx <> target_idx /\
        MH.word_in_chunk (Seq.index source target_idx) read_addr /\
        MH.read_word_in_major work read_addr == Some old /\
        (forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source proc_idx)) ==>
          U64.v (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
                  source o) ==
          MH.object_wosize_in_chunk (Seq.index source proc_idx) o))
      (ensures
        (let final =
          fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_fused_aux
           source work (MH.objects_in_chunk (Seq.index source proc_idx))
           0UL 0 fp) in
         MH.read_word_in_major final read_addr == Some old))

val chunked_fused_sweep_coalesce_chunk_range_preserves_read
  (source work: MH.major_heap)
  (start stop target_idx: nat)
  (fp: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        start <= stop /\
        stop <= Seq.length source /\
        target_idx < Seq.length source /\
        (target_idx < start \/ stop <= target_idx) /\
        MH.word_in_chunk (Seq.index source target_idx) read_addr /\
        MH.read_word_in_major work read_addr == Some old /\
        (forall (idx: nat). start <= idx /\ idx < stop ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
                  source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o))
      (ensures
        (let final =
          fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_fused_sweep_coalesce_chunks
            (Seq.slice source start stop) source work fp) in
         MH.read_word_in_major final read_addr == Some old))

val chunked_fused_sweep_coalesce_prefix_preserves_read
  (source work: MH.major_heap)
  (target_idx: nat)
  (fp: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        target_idx < Seq.length source /\
        MH.word_in_chunk (Seq.index source target_idx) read_addr /\
        MH.read_word_in_major work read_addr == Some old /\
        (forall (idx: nat). idx < target_idx ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
                  source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o))
      (ensures
        (let final =
          fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_fused_sweep_coalesce_chunks
            (Seq.slice source 0 target_idx) source work fp) in
         MH.read_word_in_major final read_addr == Some old))

val chunked_fused_sweep_coalesce_suffix_preserves_read
  (source work: MH.major_heap)
  (target_idx: nat)
  (fp: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        target_idx < Seq.length source /\
        MH.word_in_chunk (Seq.index source target_idx) read_addr /\
        MH.read_word_in_major work read_addr == Some old /\
        (forall (idx: nat). target_idx < idx /\ idx < Seq.length source ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
                  source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o))
      (ensures
        (let final =
          fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_fused_sweep_coalesce_chunks
            (Seq.slice source (target_idx + 1) (Seq.length source))
            source work fp) in
         MH.read_word_in_major final read_addr == Some old))
