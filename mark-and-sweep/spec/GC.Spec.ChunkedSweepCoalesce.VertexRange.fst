module GC.Spec.ChunkedSweepCoalesce.VertexRange

module U64 = FStar.UInt64
module Seq = FStar.Seq
module SeqProps = FStar.Seq.Properties

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module Defs = GC.Spec.ChunkedSweepCoalesce.Defs
module Range = GC.Spec.ChunkedSweepCoalesce.RangePreservation
module VertexSeq = GC.Spec.ChunkedSweepCoalesce.VertexSequence

#set-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always --warn_error -321"

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
let rec chunked_fused_sweep_coalesce_chunk_range_preserves_objects_from
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
      (decreases stop - start)
  =
  let chunks = Seq.slice source start stop in
  Seq.lemma_len_slice source start stop;
  if start = stop then begin
    assert (Seq.length chunks == 0);
    Defs.chunked_fused_sweep_coalesce_chunks_empty_length
      chunks source work fp;
    assert (fst (Defs.chunked_fused_sweep_coalesce_chunks
             chunks source work fp) == work)
  end else begin
    assert (start < stop);
    assert (Seq.length chunks == stop - start);
    assert (Seq.length chunks > 0);
    Seq.lemma_index_slice source start stop 0;
    assert (Seq.head chunks == Seq.index chunks 0);
    assert (Seq.head chunks == Seq.index source start);
    SeqProps.lemma_tail_slice source start stop;
    assert (Seq.tail chunks == Seq.slice source (start + 1) stop);
    Defs.chunked_fused_sweep_coalesce_chunks_step
      chunks source work fp;
    let one =
      Defs.chunked_fused_aux
        source work (MH.objects_in_chunk (Seq.index source start)) 0UL 0 fp in
    let work' = fst one in
    let fp' = snd one in
    Range.same_chunk_ranges_index source work start;
    Range.same_chunk_ranges_index source work target_idx;
    let step_wosize (o: obj_addr)
      : Lemma
          (requires Seq.mem o (MH.objects_in_chunk (Seq.index source start)))
          (ensures
            U64.v (Defs.chunked_wosize_of_object source o) ==
            MH.object_wosize_in_chunk (Seq.index source start) o)
      =
      assert (start <= start);
      assert (start < stop)
    in
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires step_wosize);
    assert (start <> target_idx);
    VertexSeq.chunked_fused_aux_other_chunk_preserves_objects_from
      source work start target_idx target_start protected fp;
    Range.chunked_fused_aux_preserves_ranges
      source work (MH.objects_in_chunk (Seq.index source start)) 0UL 0 fp;
    Range.same_chunk_ranges_trans source work work';
    assert (Range.same_chunk_ranges source work');
    let tail_wosize (idx: nat{start + 1 <= idx /\ idx < stop})
      : Lemma
          (ensures
            forall (o: obj_addr).
            Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
            U64.v (Defs.chunked_wosize_of_object source o) ==
            MH.object_wosize_in_chunk (Seq.index source idx) o)
      =
      assert (start <= idx);
      assert (idx < stop)
    in
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires tail_wosize);
    assert (target_idx < start + 1 \/ stop <= target_idx);
    chunked_fused_sweep_coalesce_chunk_range_preserves_objects_from
      source work' (start + 1) stop target_idx target_start protected fp';
    assert (
      fst (Defs.chunked_fused_sweep_coalesce_chunks
        (Seq.slice source (start + 1) stop) source work' fp') ==
      fst (Defs.chunked_fused_sweep_coalesce_chunks
        (Seq.tail chunks) source work' fp'));
    assert (
      fst (Defs.chunked_fused_sweep_coalesce_chunks
        chunks source work fp) ==
      fst (Defs.chunked_fused_sweep_coalesce_chunks
        (Seq.tail chunks) source work' fp'));
    let final =
      fst (Defs.chunked_fused_sweep_coalesce_chunks
        (Seq.tail chunks) source work' fp') in
    assert (MH.objects_in_chunk_from
              (Seq.index final target_idx) target_start ==
            MH.objects_in_chunk_from
              (Seq.index work' target_idx) target_start);
    assert (MH.objects_in_chunk_from
              (Seq.index work' target_idx) target_start ==
            MH.objects_in_chunk_from
              (Seq.index work target_idx) target_start);
    assert (MH.object_wosize_in_chunk
              (Seq.index final target_idx) protected ==
            MH.object_wosize_in_chunk
              (Seq.index work' target_idx) protected);
    assert (MH.object_wosize_in_chunk
              (Seq.index work' target_idx) protected ==
            MH.object_wosize_in_chunk
              (Seq.index work target_idx) protected);
    assert (MH.chunk_start (Seq.index final target_idx) ==
            MH.chunk_start (Seq.index work' target_idx));
    assert (MH.chunk_start (Seq.index work' target_idx) ==
            MH.chunk_start (Seq.index work target_idx));
    assert (MH.chunk_end (Seq.index final target_idx) ==
            MH.chunk_end (Seq.index work' target_idx));
    assert (MH.chunk_end (Seq.index work' target_idx) ==
            MH.chunk_end (Seq.index work target_idx))
  end
#pop-options

let chunked_fused_sweep_coalesce_prefix_preserves_objects_from
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
  =
  let range_wosize (idx: nat{idx < target_idx})
    : Lemma
        (ensures
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o)
    =
    assert (idx < target_idx)
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires range_wosize);
  chunked_fused_sweep_coalesce_chunk_range_preserves_objects_from
    source work 0 target_idx target_idx target_start protected fp

let chunked_fused_sweep_coalesce_suffix_preserves_objects_from
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
  =
  assert (target_idx + 1 <= Seq.length source);
  let range_wosize (idx: nat{target_idx + 1 <= idx /\ idx < Seq.length source})
    : Lemma
        (ensures
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o)
    =
    assert (target_idx < idx);
    assert (idx < Seq.length source)
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires range_wosize);
  chunked_fused_sweep_coalesce_chunk_range_preserves_objects_from
    source work (target_idx + 1) (Seq.length source)
    target_idx target_start protected fp
