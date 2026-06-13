module GC.Spec.ChunkedSweepCoalesce.VertexOrder

module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module Defs = GC.Spec.ChunkedSweepCoalesce.Defs
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
