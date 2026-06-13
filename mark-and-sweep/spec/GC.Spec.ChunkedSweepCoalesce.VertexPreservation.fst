module GC.Spec.ChunkedSweepCoalesce.VertexPreservation

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module Obj = GC.Spec.Object
module Header = GC.Lib.Header
module Fields = GC.Spec.Fields

#set-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always --warn_error -321"

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let chunked_merged_block_step
    (c: MH.heap_chunk)
    (fb: obj_addr)
    (run_words: pos)
    (start: hp_addr)
    (x: obj_addr)
  : Lemma
      (requires
        U64.v fb >= U64.v mword /\
        U64.v fb < heap_size /\
        U64.v fb < MH.chunk_end c /\
        U64.v fb % U64.v mword == 0 /\
        U64.v fb + (run_words - 1) * U64.v mword == U64.v start /\
        run_words - 1 < pow2 54 /\
        run_words - 1 < pow2 64 /\
        U64.v start <= MH.chunk_end c /\
        MH.word_in_chunk c (hd_address fb) /\
        MH.read_word_in_chunk c (hd_address fb) ==
          Obj.makeHeader
            (U64.uint_to_t (run_words - 1)) Header.Blue 0UL /\
        (U64.v start < MH.chunk_end c ==>
          Seq.mem x (MH.objects_in_chunk_from c start)))
      (ensures
        Seq.mem fb (MH.objects_in_chunk_from c (hd_address fb)) /\
        (U64.v start < MH.chunk_end c ==>
          Seq.mem x (MH.objects_in_chunk_from c (hd_address fb))))
  =
  hd_address_spec fb;
  let sync = hd_address fb in
  let run_minus : n:nat{n < pow2 54 /\ n < pow2 64} = run_words - 1 in
  let wz_u64 : Obj.wosize = U64.uint_to_t run_minus in
  Obj.makeHeader_getWosize wz_u64 Header.Blue 0UL;
  assert (U64.v wz_u64 == run_words - 1);
  assert (Obj.getWosize (MH.read_word_in_chunk c sync) == wz_u64);
  f_address_spec sync;
  assert (f_address sync == fb);
  assert (U64.v sync + U64.v mword == U64.v fb);
  assert (U64.v wz_u64 + 1 == run_words);
  FStar.Math.Lemmas.distributivity_add_left
    1 (run_words - 1) (U64.v mword);
  FStar.Math.Lemmas.paren_add_right
    (U64.v sync) (U64.v mword) ((run_words - 1) * U64.v mword);
  assert (U64.v sync + (U64.v wz_u64 + 1) * U64.v mword ==
          U64.v start);
  assert (U64.v sync >= MH.chunk_start c);
  assert (U64.v sync + U64.v mword < MH.chunk_end c);
  MH.objects_in_chunk_from_cons_step c sync;
  if U64.v start >= MH.chunk_end c then begin
    assert (U64.v sync + (U64.v wz_u64 + 1) * U64.v mword >=
            MH.chunk_end c);
    assert (MH.objects_in_chunk_from c sync ==
            Seq.cons fb (Seq.empty #obj_addr));
    Fields.mem_cons_lemma fb fb (Seq.empty #obj_addr)
  end else begin
    assert (U64.v start < heap_size);
    assert (U64.v start < pow2 64);
    assert (U64.v start % U64.v mword == 0);
    let tail = MH.objects_in_chunk_from c start in
    assert (MH.objects_in_chunk_from c sync == Seq.cons fb tail);
    Fields.mem_cons_lemma fb fb tail;
    Fields.mem_cons_lemma x fb tail
  end
#pop-options
