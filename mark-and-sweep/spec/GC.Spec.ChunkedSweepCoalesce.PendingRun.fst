module GC.Spec.ChunkedSweepCoalesce.PendingRun

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module Obj = GC.Spec.Object

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

let chunked_fused_aux_nonblack_run_end_at_next_start
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
  =
  let new_first : U64.t = if run_words = 0 then first else first_blue in
  let new_run = run_words + U64.v wz + 1 in
  match run_words with
  | 0 ->
    assert (new_run - 1 == U64.v wz);
    blue_run_empty_end_at_next_start start first (U64.v wz);
    assert (U64.v new_first + (new_run - 1) * U64.v mword ==
            U64.v start + (U64.v wz + 1) * U64.v mword);
    assert (U64.v new_first + (new_run - 1) * U64.v mword ==
            U64.v next_start)
  | _ ->
    assert (run_words > 0);
    assert (U64.v first_blue +
            (run_words - 1) * U64.v mword == U64.v start);
    assert (new_run - 1 == (run_words - 1) + U64.v wz + 1);
    blue_run_extended_end_at_next_start first_blue run_words start (U64.v wz);
    assert (U64.v first_blue + (new_run - 1) * U64.v mword ==
            U64.v start + (U64.v wz + 1) * U64.v mword);
    assert (U64.v first_blue + (new_run - 1) * U64.v mword ==
            U64.v next_start)

let pending_run_before_start
    (work: MH.major_heap)
    (idx: nat)
    (base start: hp_addr)
    (first_blue: U64.t)
    (run_words: nat)
  =
  idx < Seq.length work /\
  (run_words = 0 \/
   (~(U64.v first_blue < U64.v mword) /\
    ~(U64.v first_blue >= heap_size) /\
    ~(U64.v first_blue % U64.v mword <> 0) /\
    run_words - 1 < pow2 54 /\
    run_words - 1 < pow2 64 /\
    U64.v first_blue + (run_words - 1) * U64.v mword ==
      U64.v start /\
    (let fb : obj_addr = first_blue in
     let hd = hd_address fb in
     Seq.mem fb (MH.objects_in_chunk_from (Seq.index work idx) base) /\
     U64.v fb < MH.chunk_end (Seq.index work idx) /\
     U64.v start <= MH.chunk_end (Seq.index work idx) /\
     MH.word_in_chunk (Seq.index work idx) hd)))

let pending_run_before_start_index
    (work: MH.major_heap)
    (idx: nat)
    (base start: hp_addr)
    (first_blue: U64.t)
    (run_words: nat)
  : Lemma
      (requires pending_run_before_start work idx base start first_blue run_words)
      (ensures idx < Seq.length work)
  =
  ()

let pending_run_before_start_empty
    (work: MH.major_heap)
    (idx: nat)
    (base start: hp_addr)
  : Lemma
      (requires idx < Seq.length work)
      (ensures pending_run_before_start work idx base start 0UL 0)
  =
  ()

let pending_run_before_start_nonempty_elim
    (work: MH.major_heap)
    (idx: nat)
    (base start: hp_addr)
    (first_blue: U64.t)
    (run_words: pos)
  : Lemma
      (requires pending_run_before_start work idx base start first_blue run_words)
      (ensures
        idx < Seq.length work /\
        ~(U64.v first_blue < U64.v mword) /\
        ~(U64.v first_blue >= heap_size) /\
        ~(U64.v first_blue % U64.v mword <> 0) /\
        run_words - 1 < pow2 54 /\
        run_words - 1 < pow2 64 /\
        U64.v first_blue + (run_words - 1) * U64.v mword ==
          U64.v start /\
        (let fb : obj_addr = first_blue in
         let hd = hd_address fb in
         Seq.mem fb (MH.objects_in_chunk_from (Seq.index work idx) base) /\
         U64.v fb < MH.chunk_end (Seq.index work idx) /\
         U64.v start <= MH.chunk_end (Seq.index work idx) /\
         MH.word_in_chunk (Seq.index work idx) hd))
  =
  ()

#push-options "--z3rlimit 5 --fuel 1 --ifuel 0 --split_queries always"
let words_fit_header_from_byte_bound (words: nat)
  : Lemma
      (requires words * U64.v mword < pow2 57)
      (ensures words < pow2 54)
  =
  assert_norm (U64.v mword == 8);
  assert_norm (pow2 54 * 8 == pow2 57);
  assert (pow2 54 * U64.v mword == pow2 57);
  if words >= pow2 54 then begin
    FStar.Math.Lemmas.lemma_mult_le_right
      (U64.v mword) (pow2 54) words;
    assert (pow2 54 * U64.v mword <= words * U64.v mword);
    assert False
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
let nonblack_tail_pending_run_before_start_from_empty
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
  =
  let new_run = U64.v wz + 1 in
  chunked_fused_aux_nonblack_run_end_at_next_start
    start first 0UL 0 wz next_start;
  FStar.Math.Lemmas.pow2_lt_compat 64 54;
  assert (new_run > 0);
  assert (new_run <> 0);
  assert (new_run - 1 == U64.v wz);
  assert (new_run - 1 < pow2 54);
  assert (new_run - 1 < pow2 64);
  assert (U64.v first + (new_run - 1) * U64.v mword ==
          U64.v next_start);
  assert (new_run * U64.v mword == (U64.v wz + 1) * U64.v mword);
  assert (U64.v (hd_address first) + new_run * U64.v mword ==
          U64.v next_start);
  assert (U64.v first < MH.chunk_end (Seq.index work idx))

private let pos_sum_plus_one_minus_one (n: pos) (m: nat)
  : Lemma (ensures n + m + 1 - 1 == n + m)
  =
  assert (n > 0);
  assert (n + m + 1 > 0)

private let nonempty_pending_run_words_fit_from_next_start
    (work: MH.major_heap)
    (idx: nat)
    (base start next_start: hp_addr)
    (first: obj_addr)
    (wz: Obj.wosize)
    (first_blue: U64.t)
    (run_words: pos)
  : Lemma
      (requires
        idx < Seq.length work /\
        pending_run_before_start work idx base start first_blue run_words /\
        U64.v first == U64.v start + U64.v mword /\
        U64.v start + (U64.v wz + 1) * U64.v mword ==
          U64.v next_start /\
        U64.v next_start <= MH.chunk_end (Seq.index work idx))
      (ensures run_words + U64.v wz < pow2 54)
  =
  let new_run = run_words + U64.v wz + 1 in
  chunked_fused_aux_nonblack_run_end_at_next_start
    start first first_blue run_words wz next_start;
  pos_sum_plus_one_minus_one run_words (U64.v wz);
  assert (new_run - 1 == run_words + U64.v wz);
  assert (new_run > 0);
  assert (new_run <> 0);
  assert (U64.v first_blue + (new_run - 1) * U64.v mword ==
          U64.v next_start);
  hd_address_spec first_blue;
  assert (U64.v (hd_address first_blue) + U64.v mword == U64.v first_blue);
  FStar.Math.Lemmas.distributivity_add_left
    (new_run - 1) 1 (U64.v mword);
  FStar.Math.Lemmas.paren_add_right
    (U64.v (hd_address first_blue)) (U64.v mword)
    ((new_run - 1) * U64.v mword);
  assert (U64.v (hd_address first_blue) + new_run * U64.v mword ==
          U64.v next_start);
  assert (new_run * U64.v mword <= U64.v next_start);
  assert (U64.v next_start <= heap_size);
  assert (new_run * U64.v mword < pow2 57);
  words_fit_header_from_byte_bound new_run;
  assert (new_run < pow2 54);
  assert (run_words + U64.v wz < pow2 54)

let nonblack_tail_pending_run_before_start_from_nonempty
    (work: MH.major_heap)
    (idx: nat)
    (base start next_start: hp_addr)
    (first: obj_addr)
    (wz: Obj.wosize)
    (first_blue: U64.t)
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
  =
  let new_run = run_words + U64.v wz + 1 in
  let fb : obj_addr = first_blue in
  nonempty_pending_run_words_fit_from_next_start
    work idx base start next_start first wz fb run_words;
  chunked_fused_aux_nonblack_run_end_at_next_start
    start first first_blue run_words wz next_start;
  FStar.Math.Lemmas.pow2_lt_compat 64 54;
  pos_sum_plus_one_minus_one run_words (U64.v wz);
  assert (run_words > 0);
  assert (run_words >= 1);
  assert (new_run - 1 == run_words + U64.v wz);
  assert (new_run > run_words);
  assert (new_run > 0);
  assert (new_run <> 0);
  assert (new_run - 1 < pow2 54);
  assert (new_run - 1 < pow2 64);
  assert (U64.v first_blue + (new_run - 1) * U64.v mword ==
          U64.v next_start);
  hd_address_spec fb;
  assert (U64.v (hd_address fb) + U64.v mword == U64.v first_blue);
  FStar.Math.Lemmas.distributivity_add_left
    (new_run - 1) 1 (U64.v mword);
  FStar.Math.Lemmas.paren_add_right
    (U64.v (hd_address fb)) (U64.v mword)
    ((new_run - 1) * U64.v mword);
  assert (U64.v (hd_address fb) + new_run * U64.v mword ==
          U64.v next_start)
#pop-options
