module GC.Spec.ChunkedSweepCoalesce.RangePreservation

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module Defs = GC.Spec.ChunkedSweepCoalesce.Defs
module ChunkedGraph = GC.Spec.ChunkedMajorGC.Graph

val same_chunk_ranges
  (before after: MH.major_heap)
  : prop

val same_chunk_ranges_refl
  (mh: MH.major_heap)
  : Lemma (same_chunk_ranges mh mh)

val same_chunk_ranges_trans
  (mh0 mh1 mh2: MH.major_heap)
  : Lemma
      (requires same_chunk_ranges mh0 mh1 /\ same_chunk_ranges mh1 mh2)
      (ensures same_chunk_ranges mh0 mh2)

val same_chunk_ranges_preserves_is_major_pointer
  (mh0 mh1: MH.major_heap)
  (v: U64.t)
  : Lemma
      (requires same_chunk_ranges mh0 mh1)
      (ensures MH.is_major_pointer mh0 v == MH.is_major_pointer mh1 v)

val major_write_word_or_same_preserves_ranges
  (mh: MH.major_heap)
  (addr: hp_addr)
  (value: U64.t)
  : Lemma
      (ensures
        same_chunk_ranges
          mh
          (GC.Spec.MajorAllocator.major_write_word_or_same mh addr value))

val chunked_flush_blue_preserves_ranges
  (mh: MH.major_heap)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  : Lemma
      (ensures
        same_chunk_ranges mh
          (fst (Defs.chunked_flush_blue mh first_blue run_words fp)))

val chunked_fused_aux_preserves_ranges
  (source work: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  : Lemma
      (ensures
        same_chunk_ranges work
          (fst (Defs.chunked_fused_aux
            source work objs first_blue run_words fp)))

val chunked_fused_aux_pointer_classification_preserved
  (source work: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  : Lemma
      (ensures
        ChunkedGraph.chunked_major_pointer_classification_preserved
          work
          (fst (Defs.chunked_fused_aux
            source work objs first_blue run_words fp)))

val chunked_fused_sweep_coalesce_chunks_preserves_ranges
  (source_chunks source work: MH.major_heap)
  (fp: U64.t)
  : Lemma
      (ensures
        same_chunk_ranges work
          (fst (Defs.chunked_fused_sweep_coalesce_chunks
            source_chunks source work fp)))

val chunked_fused_sweep_coalesce_preserves_ranges
  (mh: MH.major_heap)
  : Lemma
      (ensures
        same_chunk_ranges mh
          (fst (Defs.chunked_fused_sweep_coalesce mh)))

val chunked_fused_sweep_coalesce_chunks_pointer_classification_preserved
  (source_chunks source work: MH.major_heap)
  (fp: U64.t)
  : Lemma
      (ensures
        ChunkedGraph.chunked_major_pointer_classification_preserved
          work
          (fst (Defs.chunked_fused_sweep_coalesce_chunks
            source_chunks source work fp)))

val chunked_fused_sweep_coalesce_pointer_classification_preserved
  (mh: MH.major_heap)
  : Lemma
      (ensures
        ChunkedGraph.chunked_major_pointer_classification_preserved
          mh
          (fst (Defs.chunked_fused_sweep_coalesce mh)))
