module GC.Spec.ChunkedSweepCoalesce.PendingRun

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module Obj = GC.Spec.Object

val chunked_fused_aux_nonblack_run_end_at_next_start
    (start: hp_addr)
    (first: obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (wz: U64.t)
    (next_start: hp_addr)
  : Lemma
      (requires
        U64.v first == U64.v start + U64.v mword /\
        U64.v next_start ==
          U64.v start + (U64.v wz + 1) * U64.v mword /\
        (run_words = 0 \/
         U64.v first_blue + (run_words - 1) * U64.v mword == U64.v start))
      (ensures
        (let new_first : U64.t = if run_words = 0 then first else first_blue in
         let new_run = run_words + U64.v wz + 1 in
         new_run = 0 \/
         U64.v new_first + (new_run - 1) * U64.v mword == U64.v next_start))

val pending_run_before_start
    (work: MH.major_heap)
    (idx: nat)
    (base start: hp_addr)
    (first_blue: U64.t)
    (run_words: nat)
  : Tot prop

val nonblack_tail_pending_run_before_start_from_empty
    (work: MH.major_heap)
    (idx: nat)
    (base start next_start: hp_addr)
    (first: obj_addr)
    (wz: Obj.wosize)
  : Lemma
      (requires
        idx < Seq.length work /\
        hd_address first == start /\
        U64.v first == U64.v start + U64.v mword /\
        Seq.mem first (MH.objects_in_chunk_from (Seq.index work idx) base) /\
        U64.v first < MH.chunk_end (Seq.index work idx) /\
        MH.word_in_chunk (Seq.index work idx) start /\
        U64.v start + (U64.v wz + 1) * U64.v mword ==
          U64.v next_start /\
        U64.v next_start <= MH.chunk_end (Seq.index work idx))
      (ensures
        pending_run_before_start work idx base next_start first (U64.v wz + 1))

val nonblack_tail_pending_run_before_start_from_nonempty
    (work: MH.major_heap)
    (idx: nat)
    (base start next_start: hp_addr)
    (first: obj_addr)
    (wz: Obj.wosize)
    (first_blue: obj_addr)
    (run_words: pos)
  : Lemma
      (requires
        idx < Seq.length work /\
        pending_run_before_start work idx base start first_blue run_words /\
        U64.v first == U64.v start + U64.v mword /\
        U64.v start + (U64.v wz + 1) * U64.v mword ==
          U64.v next_start /\
        U64.v next_start <= MH.chunk_end (Seq.index work idx))
      (ensures
        pending_run_before_start
          work idx base next_start first_blue
          (run_words + U64.v wz + 1))
