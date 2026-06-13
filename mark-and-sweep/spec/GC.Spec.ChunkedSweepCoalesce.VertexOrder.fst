module GC.Spec.ChunkedSweepCoalesce.VertexOrder

module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap

#set-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always --warn_error -321"

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
