module GC.Spec.ChunkedSweepCoalesce.SequencePreservation

module U64 = FStar.UInt64
module Seq = FStar.Seq
module SeqProps = FStar.Seq.Properties

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module Defs = GC.Spec.ChunkedSweepCoalesce.Defs
module Pending = GC.Spec.ChunkedSweepCoalesce.PendingRun
module Pres = GC.Spec.ChunkedSweepCoalesce.Preservation

#set-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always --warn_error -321"

let chunked_fused_aux_preserves_read_from_chunk_before
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
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o))
      (ensures
        (let final =
          fst (Defs.chunked_fused_aux
           source work (MH.objects_in_chunk (Seq.index source idx))
           0UL 0 fp) in
         MH.read_word_in_major final read_addr == Some old))
  =
  let c = Seq.index source idx in
  assert (MH.objects_in_chunk c == MH.objects_in_chunk_from c c.base);
  Pending.pending_run_before_start_empty source idx c.base c.base;
  let base_mem (o: obj_addr)
    : Lemma
        (requires Seq.mem o (MH.objects_in_chunk_from c c.base))
        (ensures Seq.mem o (MH.objects_in_chunk_from c c.base))
    = ()
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires base_mem);
  Pres.chunked_fused_aux_read_frame_ready_from_chunk_before
    source idx c.base c.base 0UL 0 read_addr;
  Pres.chunked_fused_aux_preserves_other_read
    source work (MH.objects_in_chunk c) 0UL 0 fp read_addr old

let chunked_fused_aux_preserves_read_from_chunk_after
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
          fst (Defs.chunked_fused_aux
           source work (MH.objects_in_chunk (Seq.index source idx))
           0UL 0 fp) in
         MH.read_word_in_major final read_addr == Some old))
  =
  let c = Seq.index source idx in
  assert (MH.objects_in_chunk c == MH.objects_in_chunk_from c c.base);
  Pending.pending_run_before_start_empty source idx c.base c.base;
  Pres.chunked_fused_aux_read_frame_ready_from_chunk_after
    source idx c.base c.base 0UL 0 read_addr;
  Pres.chunked_fused_aux_preserves_other_read
    source work (MH.objects_in_chunk c) 0UL 0 fp read_addr old

let chunked_fused_aux_preserves_read_from_other_chunk
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
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source proc_idx) o))
      (ensures
        (let final =
          fst (Defs.chunked_fused_aux
           source work (MH.objects_in_chunk (Seq.index source proc_idx))
           0UL 0 fp) in
         MH.read_word_in_major final read_addr == Some old))
  =
  let proc_chunk = Seq.index source proc_idx in
  let target_chunk = Seq.index source target_idx in
  MH.chunks_pairwise_disjoint_index source proc_idx target_idx;
  assert (MH.chunks_disjoint proc_chunk target_chunk);
  if MH.chunk_end proc_chunk <= MH.chunk_start target_chunk then begin
    assert (U64.v read_addr >= MH.chunk_start target_chunk);
    assert (MH.chunk_end proc_chunk <= U64.v read_addr);
    chunked_fused_aux_preserves_read_from_chunk_before
      source work proc_idx fp read_addr old
  end else begin
    assert (MH.chunk_end target_chunk <= MH.chunk_start proc_chunk);
    assert (U64.v read_addr + U64.v mword <= MH.chunk_end target_chunk);
    assert (U64.v read_addr + U64.v mword <= MH.chunk_start proc_chunk);
    chunked_fused_aux_preserves_read_from_chunk_after
      source work proc_idx fp read_addr old
  end

#push-options "--z3rlimit 5 --fuel 1 --ifuel 0 --split_queries always"
let rec chunked_fused_sweep_coalesce_chunk_range_preserves_read
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
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o))
      (ensures
        (let final =
          fst (Defs.chunked_fused_sweep_coalesce_chunks
            (Seq.slice source start stop) source work fp) in
         MH.read_word_in_major final read_addr == Some old))
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
    chunked_fused_aux_preserves_read_from_other_chunk
      source work start target_idx fp read_addr old;
    assert (MH.read_word_in_major work' read_addr == Some old);
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
    chunked_fused_sweep_coalesce_chunk_range_preserves_read
      source work' (start + 1) stop target_idx fp' read_addr old;
    assert (
      fst (Defs.chunked_fused_sweep_coalesce_chunks
        (Seq.slice source (start + 1) stop) source work' fp') ==
      fst (Defs.chunked_fused_sweep_coalesce_chunks
        (Seq.tail chunks) source work' fp'));
    assert (
      fst (Defs.chunked_fused_sweep_coalesce_chunks
        chunks source work fp) ==
      fst (Defs.chunked_fused_sweep_coalesce_chunks
        (Seq.tail chunks) source work' fp'))
  end
#pop-options

let chunked_fused_sweep_coalesce_prefix_preserves_read
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
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o))
      (ensures
        (let final =
          fst (Defs.chunked_fused_sweep_coalesce_chunks
            (Seq.slice source 0 target_idx) source work fp) in
         MH.read_word_in_major final read_addr == Some old))
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
  chunked_fused_sweep_coalesce_chunk_range_preserves_read
    source work 0 target_idx target_idx fp read_addr old

let chunked_fused_sweep_coalesce_suffix_preserves_read
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
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o))
      (ensures
        (let final =
          fst (Defs.chunked_fused_sweep_coalesce_chunks
            (Seq.slice source (target_idx + 1) (Seq.length source))
            source work fp) in
         MH.read_word_in_major final read_addr == Some old))
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
  chunked_fused_sweep_coalesce_chunk_range_preserves_read
    source work (target_idx + 1) (Seq.length source) target_idx fp read_addr old
