module GC.Spec.ChunkedSweepCoalesce.VertexSteps

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module Defs = GC.Spec.ChunkedSweepCoalesce.Defs
module Vertex = GC.Spec.ChunkedSweepCoalesce.VertexPreservation

#set-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always --warn_error -321"

let word_in_chunk_same_range
    (c c': MH.heap_chunk)
    (addr: hp_addr)
  : Lemma
      (requires
        MH.chunk_start c' == MH.chunk_start c /\
        MH.chunk_end c' == MH.chunk_end c /\
        MH.word_in_chunk c addr)
      (ensures MH.word_in_chunk c' addr)
  = ()

let protected_extent_le_after_same_wosize
    (old_c new_c: MH.heap_chunk)
    (protected: obj_addr)
    (addr: nat)
  : Lemma
      (requires
        MH.object_wosize_in_chunk new_c protected ==
          MH.object_wosize_in_chunk old_c protected /\
        U64.v (hd_address protected) +
          (1 + MH.object_wosize_in_chunk old_c protected) *
            U64.v mword <=
          addr)
      (ensures
        U64.v (hd_address protected) +
          (1 + MH.object_wosize_in_chunk new_c protected) *
            U64.v mword <=
          addr)
  = ()

let flush_after_member_pre_from_pending_run
    (work: MH.major_heap)
    (idx: nat)
    (protected: obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
  : Lemma
      (requires
        idx < Seq.length work /\
        (run_words = 0 \/
         (~(U64.v first_blue < U64.v mword) /\
          ~(U64.v first_blue >= heap_size) /\
          ~(U64.v first_blue % U64.v mword <> 0) /\
          (let fb : obj_addr = first_blue in
           let hd = hd_address fb in
           MH.word_in_chunk (Seq.index work idx) hd /\
           U64.v (hd_address protected) +
             (1 + MH.object_wosize_in_chunk (Seq.index work idx) protected) *
               U64.v mword <=
             U64.v hd /\
           U64.v hd + run_words * U64.v mword <=
             MH.chunk_end (Seq.index work idx)))))
      (ensures
        (run_words <> 0 /\
         ~(U64.v first_blue < U64.v mword) /\
         ~(U64.v first_blue >= heap_size) /\
         ~(U64.v first_blue % U64.v mword <> 0) /\
         run_words - 1 < pow2 54 ==>
          (let fb : obj_addr = first_blue in
           let hd = hd_address fb in
           MH.word_in_chunk (Seq.index work idx) hd /\
           U64.v (hd_address protected) +
             (1 + MH.object_wosize_in_chunk (Seq.index work idx) protected) *
               U64.v mword <=
             U64.v hd /\
           U64.v hd + run_words * U64.v mword <=
             MH.chunk_end (Seq.index work idx))))
  =
  if run_words = 0 then ()

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_fused_aux_black_head_after_member_step
    (source work: MH.major_heap)
    (idx: nat)
    (start: hp_addr)
    (protected: obj_addr)
    (objs: Seq.seq obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap work /\
        idx < Seq.length work /\
        Seq.length objs > 0 /\
        Defs.chunked_is_black source (Seq.head objs) /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index work idx) start) /\
        MH.word_in_chunk (Seq.index work idx) (hd_address (Seq.head objs)) /\
        U64.v (hd_address protected) +
          (1 + MH.object_wosize_in_chunk (Seq.index work idx) protected) *
            U64.v mword <=
          U64.v (hd_address (Seq.head objs)) /\
        (run_words = 0 \/
         (~(U64.v first_blue < U64.v mword) /\
          ~(U64.v first_blue >= heap_size) /\
          ~(U64.v first_blue % U64.v mword <> 0) /\
          (let fb : obj_addr = first_blue in
           let hd = hd_address fb in
           MH.word_in_chunk (Seq.index work idx) hd /\
           U64.v (hd_address protected) +
             (1 + MH.object_wosize_in_chunk (Seq.index work idx) protected) *
               U64.v mword <=
             U64.v hd /\
           U64.v hd + run_words * U64.v mword <=
             MH.chunk_end (Seq.index work idx)))) /\
        (let flushed = Defs.chunked_flush_blue work first_blue run_words fp in
         let work' = fst flushed in
         let fp' = snd flushed in
         let work'' = Defs.chunked_make_white work' (Seq.head objs) in
         let tail_final =
           fst (Defs.chunked_fused_aux
             source work'' (Seq.tail objs) 0UL 0 fp') in
         MH.well_formed_major_heap tail_final /\
         idx < Seq.length tail_final /\
         Seq.mem protected
           (MH.objects_in_chunk_from (Seq.index tail_final idx) start) /\
         MH.object_wosize_in_chunk (Seq.index tail_final idx) protected ==
         MH.object_wosize_in_chunk (Seq.index work idx) protected /\
         MH.chunk_start (Seq.index tail_final idx) ==
         MH.chunk_start (Seq.index work idx) /\
         MH.chunk_end (Seq.index tail_final idx) ==
         MH.chunk_end (Seq.index work idx)))
      (ensures
        (let final =
          fst (Defs.chunked_fused_aux
            source work objs first_blue run_words fp) in
         MH.well_formed_major_heap final /\
         idx < Seq.length final /\
         Seq.mem protected
           (MH.objects_in_chunk_from (Seq.index final idx) start) /\
         MH.object_wosize_in_chunk (Seq.index final idx) protected ==
         MH.object_wosize_in_chunk (Seq.index work idx) protected /\
         MH.chunk_start (Seq.index final idx) ==
         MH.chunk_start (Seq.index work idx) /\
         MH.chunk_end (Seq.index final idx) ==
         MH.chunk_end (Seq.index work idx)))
  =
  let obj = Seq.head objs in
  Defs.chunked_fused_aux_black_step
    source work objs first_blue run_words fp;
  let flushed = Defs.chunked_flush_blue work first_blue run_words fp in
  let work' = fst flushed in
  let fp' = snd flushed in
  flush_after_member_pre_from_pending_run
    work idx protected first_blue run_words;
  Vertex.chunked_flush_blue_after_member_preserves_objects_from
    work idx start protected first_blue run_words fp;
  assert (MH.well_formed_major_heap work');
  assert (idx < Seq.length work');
  assert (Seq.mem protected
    (MH.objects_in_chunk_from (Seq.index work' idx) start));
  assert (MH.object_wosize_in_chunk (Seq.index work' idx) protected ==
          MH.object_wosize_in_chunk (Seq.index work idx) protected);
  assert (MH.chunk_start (Seq.index work' idx) ==
          MH.chunk_start (Seq.index work idx));
  assert (MH.chunk_end (Seq.index work' idx) ==
          MH.chunk_end (Seq.index work idx));
  word_in_chunk_same_range
    (Seq.index work idx) (Seq.index work' idx) (hd_address obj);
  protected_extent_le_after_same_wosize
    (Seq.index work idx) (Seq.index work' idx) protected
    (U64.v (hd_address obj));
  Vertex.chunked_make_white_after_member_preserves_objects_from
    work' idx start protected obj;
  let work'' = Defs.chunked_make_white work' obj in
  assert (MH.well_formed_major_heap work'');
  assert (idx < Seq.length work'');
  assert (Seq.mem protected
    (MH.objects_in_chunk_from (Seq.index work'' idx) start));
  assert (MH.object_wosize_in_chunk (Seq.index work'' idx) protected ==
          MH.object_wosize_in_chunk (Seq.index work idx) protected);
  assert (MH.chunk_start (Seq.index work'' idx) ==
          MH.chunk_start (Seq.index work idx));
  assert (MH.chunk_end (Seq.index work'' idx) ==
          MH.chunk_end (Seq.index work idx));
  let tail_final =
    fst (Defs.chunked_fused_aux source work'' (Seq.tail objs) 0UL 0 fp') in
  assert (MH.well_formed_major_heap tail_final);
  assert (idx < Seq.length tail_final);
  assert (Seq.mem protected
    (MH.objects_in_chunk_from (Seq.index tail_final idx) start));
  assert (MH.object_wosize_in_chunk (Seq.index tail_final idx) protected ==
          MH.object_wosize_in_chunk (Seq.index work idx) protected);
  assert (MH.chunk_start (Seq.index tail_final idx) ==
          MH.chunk_start (Seq.index work idx));
  assert (MH.chunk_end (Seq.index tail_final idx) ==
          MH.chunk_end (Seq.index work idx));
  assert (fst (Defs.chunked_fused_aux
            source work objs first_blue run_words fp) == tail_final)

let chunked_fused_aux_nonblack_head_after_member_step
    (source work: MH.major_heap)
    (idx: nat)
    (start: hp_addr)
    (protected: obj_addr)
    (objs: Seq.seq obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap work /\
        idx < Seq.length work /\
        Seq.length objs > 0 /\
        ~(Defs.chunked_is_black source (Seq.head objs)) /\
        (let obj = Seq.head objs in
         let ws = U64.v (Defs.chunked_wosize_of_object source obj) in
         let new_first : U64.t = if run_words = 0 then obj else first_blue in
         let tail_final =
           fst (Defs.chunked_fused_aux
             source work (Seq.tail objs) new_first (run_words + ws + 1) fp) in
         MH.well_formed_major_heap tail_final /\
         idx < Seq.length tail_final /\
         Seq.mem protected
           (MH.objects_in_chunk_from (Seq.index tail_final idx) start) /\
         MH.object_wosize_in_chunk (Seq.index tail_final idx) protected ==
         MH.object_wosize_in_chunk (Seq.index work idx) protected /\
         MH.chunk_start (Seq.index tail_final idx) ==
         MH.chunk_start (Seq.index work idx) /\
         MH.chunk_end (Seq.index tail_final idx) ==
         MH.chunk_end (Seq.index work idx)))
      (ensures
        (let final =
          fst (Defs.chunked_fused_aux
            source work objs first_blue run_words fp) in
         MH.well_formed_major_heap final /\
         idx < Seq.length final /\
         Seq.mem protected
           (MH.objects_in_chunk_from (Seq.index final idx) start) /\
         MH.object_wosize_in_chunk (Seq.index final idx) protected ==
         MH.object_wosize_in_chunk (Seq.index work idx) protected /\
         MH.chunk_start (Seq.index final idx) ==
         MH.chunk_start (Seq.index work idx) /\
         MH.chunk_end (Seq.index final idx) ==
         MH.chunk_end (Seq.index work idx)))
  =
  let obj = Seq.head objs in
  let ws = U64.v (Defs.chunked_wosize_of_object source obj) in
  let new_first : U64.t = if run_words = 0 then obj else first_blue in
  let new_run = run_words + ws + 1 in
  Defs.chunked_fused_aux_nonblack_step
    source work objs first_blue run_words fp;
  let tail_final =
    fst (Defs.chunked_fused_aux
      source work (Seq.tail objs) new_first new_run fp) in
  assert (MH.well_formed_major_heap tail_final);
  assert (idx < Seq.length tail_final);
  assert (Seq.mem protected
    (MH.objects_in_chunk_from (Seq.index tail_final idx) start));
  assert (MH.object_wosize_in_chunk (Seq.index tail_final idx) protected ==
          MH.object_wosize_in_chunk (Seq.index work idx) protected);
  assert (MH.chunk_start (Seq.index tail_final idx) ==
          MH.chunk_start (Seq.index work idx));
  assert (MH.chunk_end (Seq.index tail_final idx) ==
          MH.chunk_end (Seq.index work idx));
  assert (fst (Defs.chunked_fused_aux
            source work objs first_blue run_words fp) == tail_final)
#pop-options
