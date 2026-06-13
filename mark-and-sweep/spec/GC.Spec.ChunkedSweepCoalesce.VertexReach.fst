module GC.Spec.ChunkedSweepCoalesce.VertexReach

module U64 = FStar.UInt64
module Seq = FStar.Seq
module SeqProps = FStar.Seq.Properties

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module Obj = GC.Spec.Object
module Header = GC.Lib.Header
module Fields = GC.Spec.Fields
module Defs = GC.Spec.ChunkedSweepCoalesce.Defs
module Vertex = GC.Spec.ChunkedSweepCoalesce.VertexPreservation
module SpecMajorAlloc = GC.Spec.MajorAllocator

#set-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always --warn_error -321"

let nat_nonzero_pos (n: nat)
  : Lemma (requires n <> 0) (ensures n > 0)
  = ()

let seq_mem_eq (#a:eqtype) (s t: Seq.seq a) (x: a)
  : Lemma
      (requires s == t /\ Seq.mem x s)
      (ensures Seq.mem x t)
  =
  assert (Seq.equal s t);
  Seq.lemma_eq_elim s t;
  assert (Seq.mem x t)

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let rec objects_in_chunk_from_write_member_header_preserves_member
    (c: MH.heap_chunk)
    (start: hp_addr)
    (obj: obj_addr)
    (value: U64.t)
  : Lemma
      (requires
        Seq.mem obj (MH.objects_in_chunk_from c start) /\
        MH.word_in_chunk c (hd_address obj) /\
        U64.v (hd_address obj) +
          (U64.v (Obj.getWosize value) + 1) * U64.v mword <=
          MH.chunk_end c /\
        U64.v (hd_address obj) +
          (U64.v (Obj.getWosize value) + 1) * U64.v mword < pow2 64)
      (ensures
        Seq.mem obj
          (MH.objects_in_chunk_from
            (MH.write_word_in_chunk c (hd_address obj) value) start))
      (decreases MH.chunk_end c - U64.v start)
  =
  let c' = MH.write_word_in_chunk c (hd_address obj) value in
  MH.write_word_in_chunk_preserves_range c (hd_address obj) value;
  if U64.v start < MH.chunk_start c then
    assert False
  else if U64.v start + U64.v mword >= MH.chunk_end c then
    assert False
  else begin
    assert (MH.word_in_chunk c start);
    let header = MH.read_word_in_chunk c start in
    let wz = Obj.getWosize header in
    let obj_size_words : nat = U64.v wz + 1 in
    assert (U64.v mword > 0);
    FStar.Math.Lemmas.lemma_mul_nat_pos_is_nat obj_size_words (U64.v mword);
    let obj_size_bytes : nat = obj_size_words * U64.v mword in
    let next_start_nat : nat =
      U64.v start + obj_size_bytes in
    if next_start_nat > MH.chunk_end c || next_start_nat >= pow2 64 then
      assert False
    else begin
      f_address_spec start;
      let first : obj_addr = f_address start in
      if next_start_nat >= MH.chunk_end c then begin
        Fields.mem_cons_lemma obj first (Seq.empty #obj_addr);
        assert (obj == first);
        hd_f_roundtrip start;
        assert (hd_address obj == start);
        MH.read_write_in_chunk_same c start value;
        let new_wz = Obj.getWosize value in
        let new_obj_size_words : nat = U64.v new_wz + 1 in
        FStar.Math.Lemmas.lemma_mul_nat_pos_is_nat
          new_obj_size_words (U64.v mword);
        let new_obj_size_bytes : nat =
          new_obj_size_words * U64.v mword in
        let new_next_start_nat : nat =
          U64.v start + new_obj_size_bytes in
        if new_next_start_nat < MH.chunk_end c' then begin
          MH.next_object_start_aligned start new_obj_size_words;
          assert (new_next_start_nat % U64.v mword == 0)
        end;
        assert (new_next_start_nat <= MH.chunk_end c');
        MH.objects_in_chunk_from_cons_step c' start;
        Fields.mem_cons_lemma obj obj (Seq.tail (MH.objects_in_chunk_from c' start))
      end else begin
        assert (next_start_nat < heap_size);
        assert (next_start_nat < pow2 64);
        MH.next_object_start_aligned start obj_size_words;
        assert (next_start_nat % U64.v mword == 0);
        let next_start : hp_addr = U64.uint_to_t next_start_nat in
        let tail = MH.objects_in_chunk_from c next_start in
        Fields.mem_cons_lemma obj first tail;
        if obj = first then begin
          hd_f_roundtrip start;
          assert (hd_address obj == start);
          MH.read_write_in_chunk_same c start value;
          let new_wz = Obj.getWosize value in
          let new_obj_size_words : nat = U64.v new_wz + 1 in
          FStar.Math.Lemmas.lemma_mul_nat_pos_is_nat
            new_obj_size_words (U64.v mword);
          let new_obj_size_bytes : nat =
            new_obj_size_words * U64.v mword in
          let new_next_start_nat : nat =
            U64.v start + new_obj_size_bytes in
          if new_next_start_nat < MH.chunk_end c' then begin
            MH.next_object_start_aligned start new_obj_size_words;
            assert (new_next_start_nat % U64.v mword == 0)
          end;
          assert (new_next_start_nat <= MH.chunk_end c');
          MH.objects_in_chunk_from_cons_step c' start;
          Fields.mem_cons_lemma obj obj (Seq.tail (MH.objects_in_chunk_from c' start))
        end else begin
          assert (Seq.mem obj tail);
          MH.objects_in_chunk_from_addresses_gt_start c next_start obj;
          assert (U64.v obj > U64.v next_start);
          hd_address_spec obj;
          hd_address_spec first;
          assert (hd_address obj <> start);
          assert (obj_size_words >= 1);
          assert (next_start_nat == U64.v start + obj_size_words * U64.v mword);
          FStar.Math.Lemmas.lemma_mult_le_right
            (U64.v mword) 1 obj_size_words;
          assert (obj_size_words * U64.v mword >= U64.v mword);
          assert (U64.v next_start >= U64.v start + U64.v mword);
          assert (U64.v obj % U64.v mword == 0);
          assert (U64.v next_start % U64.v mword == 0);
          MH.word_aligned_gt_at_least_mword (U64.v obj) (U64.v next_start);
          assert (U64.v obj >= U64.v next_start + U64.v mword);
          assert (U64.v (hd_address obj) >= U64.v next_start);
          assert (U64.v start + U64.v mword <= U64.v (hd_address obj));
          MH.read_write_in_chunk_different c (hd_address obj) start value;
          assert (MH.read_word_in_chunk c' start == MH.read_word_in_chunk c start);
          assert (Obj.getWosize (MH.read_word_in_chunk c' start) == wz);
          assert (next_start_nat < MH.chunk_end c');
          objects_in_chunk_from_write_member_header_preserves_member
            c next_start obj value;
          MH.objects_in_chunk_from_cons_step c' start;
          assert (Seq.mem obj (MH.objects_in_chunk_from c' next_start));
          Fields.mem_cons_lemma
            obj (f_address start) (MH.objects_in_chunk_from c' next_start)
        end
      end
    end
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let major_write_member_header_preserves_chunk_member
    (mh: MH.major_heap)
    (idx: nat)
    (obj: obj_addr)
    (value: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem obj (MH.objects_in_chunk (Seq.index mh idx)) /\
        MH.word_in_chunk (Seq.index mh idx) (hd_address obj) /\
        U64.v (hd_address obj) +
          (U64.v (Obj.getWosize value) + 1) * U64.v mword <=
          MH.chunk_end (Seq.index mh idx) /\
        U64.v (hd_address obj) +
          (U64.v (Obj.getWosize value) + 1) * U64.v mword < pow2 64)
      (ensures
        (let mh' = SpecMajorAlloc.major_write_word_or_same
                    mh (hd_address obj) value in
         MH.well_formed_major_heap mh' /\
         idx < Seq.length mh' /\
         Seq.mem obj (MH.objects_in_chunk (Seq.index mh' idx)) /\
         MH.chunk_start (Seq.index mh' idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index mh' idx) ==
         MH.chunk_end (Seq.index mh idx)))
  =
  let c = Seq.index mh idx in
  let c' = MH.write_word_in_chunk c (hd_address obj) value in
  MH.lookup_chunk_index_word_in_chunk mh (hd_address obj) idx;
  MH.write_word_in_major_at_lookup_index mh (hd_address obj) value idx;
  assert (MH.write_word_in_major mh (hd_address obj) value ==
          Some (Seq.upd mh idx c'));
  SpecMajorAlloc.major_write_word_or_same_some
    mh (Seq.upd mh idx c') (hd_address obj) value;
  MH.write_word_at_index_preserves_wf mh (hd_address obj) value idx;
  objects_in_chunk_from_write_member_header_preserves_member
    c c.base obj value;
  assert (Seq.index (Seq.upd mh idx c') idx == c');
  MH.write_word_in_chunk_preserves_range c (hd_address obj) value
#pop-options
