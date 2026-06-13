module GC.Spec.ChunkedSweepCoalesce.VertexOrder

module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module Defs = GC.Spec.ChunkedSweepCoalesce.Defs
module Vertex = GC.Spec.ChunkedSweepCoalesce.VertexPreservation
module VS = GC.Spec.ChunkedSweepCoalesce.VertexSteps

#set-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always --warn_error -321"

let pending_run_after_member_at_start
    (work: MH.major_heap)
    (idx: nat)
    (protected: obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (start: hp_addr)
  =
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
      MH.chunk_end (Seq.index work idx) /\
    U64.v first_blue + (run_words - 1) * U64.v mword ==
      U64.v start)))

let after_member_chunk_order_pre
    (source work: MH.major_heap)
    (idx: nat)
    (c: MH.heap_chunk)
    (start: hp_addr)
    (protected_start: hp_addr)
    (protected: obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
  =
  MH.well_formed_major_heap work /\
  idx < Seq.length work /\
  MH.chunk_start (Seq.index work idx) == MH.chunk_start c /\
  MH.chunk_end (Seq.index work idx) == MH.chunk_end c /\
  Seq.mem protected
    (MH.objects_in_chunk_from (Seq.index work idx) protected_start) /\
  U64.v (hd_address protected) +
    (1 + MH.object_wosize_in_chunk (Seq.index work idx) protected) *
      U64.v mword <=
    U64.v start /\
  U64.v start <= MH.chunk_end c /\
  (forall (o: obj_addr). Seq.mem o (MH.objects_in_chunk_from c start) ==>
    U64.v (Defs.chunked_wosize_of_object source o) ==
    MH.object_wosize_in_chunk c o) /\
  pending_run_after_member_at_start work idx protected first_blue run_words start

let blue_run_empty_end_at_next_start
    (start: hp_addr)
    (first: obj_addr)
    (wz: nat)
  : Lemma
      (requires U64.v first == U64.v start + U64.v mword)
      (ensures
        U64.v first + wz * U64.v mword ==
        U64.v start + (wz + 1) * U64.v mword)
  =
  FStar.Math.Lemmas.distributivity_add_left wz 1 (U64.v mword);
  FStar.Math.Lemmas.paren_add_right
    (U64.v start) (U64.v mword) (wz * U64.v mword)

let blue_run_extended_end_at_next_start
    (first_blue: U64.t)
    (run_words: nat)
    (start: hp_addr)
    (wz: nat)
  : Lemma
      (requires
        run_words > 0 /\
        U64.v first_blue + (run_words - 1) * U64.v mword == U64.v start)
      (ensures
        U64.v first_blue + (run_words + wz + 1 - 1) * U64.v mword ==
        U64.v start + (wz + 1) * U64.v mword)
  =
  assert (run_words + wz + 1 - 1 == (run_words - 1) + (wz + 1));
  FStar.Math.Lemmas.distributivity_add_left
    (run_words - 1) (wz + 1) (U64.v mword);
  FStar.Math.Lemmas.paren_add_right
    (U64.v first_blue)
    ((run_words - 1) * U64.v mword)
    ((wz + 1) * U64.v mword)

let nat_nonzero_pos (n: nat)
  : Lemma (requires n <> 0) (ensures n > 0)
  = ()

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let nonblack_tail_pending_run_from_chunk_head
    (work: MH.major_heap)
    (idx: nat)
    (start: hp_addr)
    (protected: obj_addr)
    (first: obj_addr)
    (wz: nat)
    (first_blue: U64.t)
    (run_words: nat)
  : Lemma
      (requires
        idx < Seq.length work /\
        hd_address first == start /\
        U64.v first == U64.v start + U64.v mword /\
        MH.word_in_chunk (Seq.index work idx) start /\
        U64.v start + (wz + 1) * U64.v mword <=
          MH.chunk_end (Seq.index work idx) /\
        U64.v (hd_address protected) +
          (1 + MH.object_wosize_in_chunk (Seq.index work idx) protected) *
            U64.v mword <=
          U64.v start /\
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
             MH.chunk_end (Seq.index work idx) /\
           U64.v first_blue + (run_words - 1) * U64.v mword ==
             U64.v start))))
      (ensures
        (let new_first : U64.t = if run_words = 0 then first else first_blue in
         let new_run = run_words + wz + 1 in
         ~(U64.v new_first < U64.v mword) /\
         ~(U64.v new_first >= heap_size) /\
         ~(U64.v new_first % U64.v mword <> 0) /\
         (let fb : obj_addr = new_first in
          let hd = hd_address fb in
          MH.word_in_chunk (Seq.index work idx) hd /\
          U64.v (hd_address protected) +
            (1 + MH.object_wosize_in_chunk (Seq.index work idx) protected) *
              U64.v mword <=
            U64.v hd /\
          U64.v hd + new_run * U64.v mword <=
            MH.chunk_end (Seq.index work idx) /\
          U64.v new_first + (new_run - 1) * U64.v mword ==
            U64.v start + (wz + 1) * U64.v mword)))
  =
  let new_first : U64.t = if run_words = 0 then first else first_blue in
  let new_run = run_words + wz + 1 in
  if run_words = 0 then begin
    assert (new_first == first);
    assert (new_run == wz + 1);
    blue_run_empty_end_at_next_start start first wz;
    assert (U64.v new_first + (new_run - 1) * U64.v mword ==
            U64.v start + (wz + 1) * U64.v mword);
    assert (hd_address new_first == start);
    assert (U64.v (hd_address new_first) + new_run * U64.v mword <=
            MH.chunk_end (Seq.index work idx))
  end else begin
    nat_nonzero_pos run_words;
    assert (new_first == first_blue);
    hd_address_spec first_blue;
    blue_run_extended_end_at_next_start first_blue run_words start wz;
    assert (U64.v new_first + (new_run - 1) * U64.v mword ==
            U64.v start + (wz + 1) * U64.v mword);
    assert (U64.v (hd_address new_first) + new_run * U64.v mword ==
            U64.v start + (wz + 1) * U64.v mword);
    assert (U64.v (hd_address new_first) + new_run * U64.v mword <=
            MH.chunk_end (Seq.index work idx))
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let nonblack_tail_chunk_order_pre_from_head
    (source work: MH.major_heap)
    (idx: nat)
    (c: MH.heap_chunk)
    (start next_start: hp_addr)
    (protected_start: hp_addr)
    (protected: obj_addr)
    (first: obj_addr)
    (wz: nat)
    (first_blue: U64.t)
    (run_words: nat)
  : Lemma
      (requires
        after_member_chunk_order_pre
          source work idx c start protected_start protected first_blue run_words /\
        hd_address first == start /\
        U64.v first == U64.v start + U64.v mword /\
        MH.word_in_chunk (Seq.index work idx) start /\
        U64.v (Defs.chunked_wosize_of_object source first) == wz /\
        U64.v start + (wz + 1) * U64.v mword == U64.v next_start /\
        U64.v next_start <= MH.chunk_end c /\
        Seq.length (MH.objects_in_chunk_from c start) > 0 /\
        Seq.head (MH.objects_in_chunk_from c start) == first /\
        Seq.tail (MH.objects_in_chunk_from c start) ==
          MH.objects_in_chunk_from c next_start)
      (ensures
        (let new_first : U64.t = if run_words = 0 then first else first_blue in
         let new_run = run_words + wz + 1 in
         after_member_chunk_order_pre
           source work idx c next_start protected_start protected
           new_first new_run))
  =
  let new_first : U64.t = if run_words = 0 then first else first_blue in
  let new_run = run_words + wz + 1 in
  assert (MH.chunk_end (Seq.index work idx) == MH.chunk_end c);
  assert (U64.v start + (wz + 1) * U64.v mword <=
          MH.chunk_end (Seq.index work idx));
  nonblack_tail_pending_run_from_chunk_head
    work idx start protected first wz first_blue run_words;
  assert (U64.v (hd_address protected) +
            (1 + MH.object_wosize_in_chunk (Seq.index work idx) protected) *
              U64.v mword <=
          U64.v next_start);
  VS.wosize_match_tail_from_objects_from
    source c start next_start (MH.objects_in_chunk_from c start);
  assert (forall (o: obj_addr). Seq.mem o (MH.objects_in_chunk_from c next_start) ==>
    U64.v (Defs.chunked_wosize_of_object source o) ==
    MH.object_wosize_in_chunk c o);
  assert (pending_run_after_member_at_start
    work idx protected new_first new_run next_start)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let black_tail_chunk_order_pre_from_head
    (source work: MH.major_heap)
    (idx: nat)
    (c: MH.heap_chunk)
    (start next_start: hp_addr)
    (protected_start: hp_addr)
    (protected: obj_addr)
    (first: obj_addr)
    (wz: nat)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
  : Lemma
      (requires
        after_member_chunk_order_pre
          source work idx c start protected_start protected first_blue run_words /\
        hd_address first == start /\
        U64.v first == U64.v start + U64.v mword /\
        MH.word_in_chunk (Seq.index work idx) start /\
        U64.v (Defs.chunked_wosize_of_object source first) == wz /\
        U64.v start + (wz + 1) * U64.v mword == U64.v next_start /\
        U64.v next_start <= MH.chunk_end c /\
        Seq.length (MH.objects_in_chunk_from c start) > 0 /\
        Seq.head (MH.objects_in_chunk_from c start) == first /\
        Seq.tail (MH.objects_in_chunk_from c start) ==
          MH.objects_in_chunk_from c next_start)
      (ensures
        (let flushed = Defs.chunked_flush_blue work first_blue run_words fp in
         let work' = fst flushed in
         let fp' = snd flushed in
         let work'' = Defs.chunked_make_white work' first in
         after_member_chunk_order_pre
           source work'' idx c next_start protected_start protected 0UL 0))
  =
  let flushed = Defs.chunked_flush_blue work first_blue run_words fp in
  let work' = fst flushed in
  let fp' = snd flushed in
  VS.flush_after_member_pre_from_pending_run
    work idx protected first_blue run_words;
  Vertex.chunked_flush_blue_after_member_preserves_objects_from
    work idx protected_start protected first_blue run_words fp;
  assert (MH.well_formed_major_heap work');
  assert (idx < Seq.length work');
  assert (Seq.mem protected
    (MH.objects_in_chunk_from (Seq.index work' idx) protected_start));
  assert (MH.object_wosize_in_chunk (Seq.index work' idx) protected ==
          MH.object_wosize_in_chunk (Seq.index work idx) protected);
  assert (MH.chunk_start (Seq.index work' idx) ==
          MH.chunk_start (Seq.index work idx));
  assert (MH.chunk_end (Seq.index work' idx) ==
          MH.chunk_end (Seq.index work idx));
  assert (MH.word_in_chunk (Seq.index work idx) (hd_address first));
  VS.word_in_chunk_same_range
    (Seq.index work idx) (Seq.index work' idx) (hd_address first);
  VS.protected_extent_le_after_same_wosize
    (Seq.index work idx) (Seq.index work' idx) protected (U64.v start);
  Vertex.chunked_make_white_after_member_preserves_objects_from
    work' idx protected_start protected first;
  let work'' = Defs.chunked_make_white work' first in
  assert (MH.well_formed_major_heap work'');
  assert (idx < Seq.length work'');
  assert (Seq.mem protected
    (MH.objects_in_chunk_from (Seq.index work'' idx) protected_start));
  assert (MH.object_wosize_in_chunk (Seq.index work'' idx) protected ==
          MH.object_wosize_in_chunk (Seq.index work idx) protected);
  assert (MH.chunk_start (Seq.index work'' idx) ==
          MH.chunk_start (Seq.index work idx));
  assert (MH.chunk_end (Seq.index work'' idx) ==
          MH.chunk_end (Seq.index work idx));
  VS.protected_extent_le_after_same_wosize
    (Seq.index work idx) (Seq.index work'' idx) protected (U64.v next_start);
  VS.wosize_match_tail_from_objects_from
    source c start next_start (MH.objects_in_chunk_from c start);
  assert (forall (o: obj_addr). Seq.mem o (MH.objects_in_chunk_from c next_start) ==>
    U64.v (Defs.chunked_wosize_of_object source o) ==
    MH.object_wosize_in_chunk c o);
  assert (pending_run_after_member_at_start work'' idx protected 0UL 0 next_start)
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
let nonblack_head_ready_from_chunk_order_step
    (source work: MH.major_heap)
    (idx: nat)
    (c: MH.heap_chunk)
    (start: hp_addr)
    (protected_start: hp_addr)
    (protected: obj_addr)
    (objs: Seq.seq obj_addr)
    (first: obj_addr)
    (wz: nat)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
  : Lemma
      (requires
        after_member_chunk_order_pre
          source work idx c start protected_start protected first_blue run_words /\
        objs == MH.objects_in_chunk_from c start /\
        Seq.length objs > 0 /\
        Seq.head objs == first /\
        ~(Defs.chunked_is_black source first) /\
        hd_address first == start /\
        MH.word_in_chunk (Seq.index work idx) start /\
        U64.v (Defs.chunked_wosize_of_object source first) == wz /\
        (let new_first : U64.t = if run_words = 0 then first else first_blue in
         let new_run = run_words + wz + 1 in
         VS.chunked_fused_aux_after_member_ready
           source work idx protected_start protected (Seq.tail objs)
           new_first new_run fp))
      (ensures
        VS.chunked_fused_aux_after_member_ready
          source work idx protected_start protected objs first_blue run_words fp)
  =
  assert (Defs.chunked_is_black source (Seq.head objs) ==
          Defs.chunked_is_black source first);
  assert (U64.v (Defs.chunked_wosize_of_object source (Seq.head objs)) == wz);
  assert (MH.word_in_chunk (Seq.index work idx) (hd_address (Seq.head objs)));
  assert (U64.v (hd_address protected) +
            (1 + MH.object_wosize_in_chunk (Seq.index work idx) protected) *
              U64.v mword <=
          U64.v (hd_address (Seq.head objs)));
  VS.chunked_fused_aux_nonblack_head_after_member_ready_step
    source work idx protected_start protected objs first_blue run_words fp

let black_head_ready_from_chunk_order_step
    (source work: MH.major_heap)
    (idx: nat)
    (c: MH.heap_chunk)
    (start: hp_addr)
    (protected_start: hp_addr)
    (protected: obj_addr)
    (objs: Seq.seq obj_addr)
    (first: obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
  : Lemma
      (requires
        after_member_chunk_order_pre
          source work idx c start protected_start protected first_blue run_words /\
        objs == MH.objects_in_chunk_from c start /\
        Seq.length objs > 0 /\
        Seq.head objs == first /\
        Defs.chunked_is_black source first /\
        hd_address first == start /\
        MH.word_in_chunk (Seq.index work idx) start /\
        (let flushed = Defs.chunked_flush_blue work first_blue run_words fp in
         let work' = fst flushed in
         let fp' = snd flushed in
         let work'' = Defs.chunked_make_white work' first in
         VS.chunked_fused_aux_after_member_ready
           source work'' idx protected_start protected (Seq.tail objs) 0UL 0 fp'))
      (ensures
        VS.chunked_fused_aux_after_member_ready
          source work idx protected_start protected objs first_blue run_words fp)
  =
  assert (Defs.chunked_is_black source (Seq.head objs) ==
          Defs.chunked_is_black source first);
  assert (MH.word_in_chunk (Seq.index work idx) (hd_address (Seq.head objs)));
  assert (U64.v (hd_address protected) +
            (1 + MH.object_wosize_in_chunk (Seq.index work idx) protected) *
              U64.v mword <=
          U64.v (hd_address (Seq.head objs)));
  VS.chunked_fused_aux_black_head_after_member_ready_step
    source work idx protected_start protected objs first_blue run_words fp
#pop-options
