module GC.Spec.ChunkedSweepCoalesce.VertexPreservation

module U64 = FStar.UInt64
module Seq = FStar.Seq
module SeqProps = FStar.Seq.Properties

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module Obj = GC.Spec.Object
module Header = GC.Lib.Header
module Fields = GC.Spec.Fields
module SpecMajorAlloc = GC.Spec.MajorAllocator
module Defs = GC.Spec.ChunkedSweepCoalesce.Defs

#set-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always --warn_error -321"

let seq_tail_mem (#a:eqtype) (s: Seq.seq a) (x: a)
  : Lemma
      (requires Seq.length s > 0 /\ Seq.mem x (Seq.tail s))
      (ensures Seq.mem x s)
  =
  let hd = Seq.head s in
  let tl = Seq.tail s in
  assert (s == Seq.cons hd tl);
  SeqProps.lemma_mem_append (Seq.create 1 hd) tl

let seq_mem_eq (#a:eqtype) (s t: Seq.seq a) (x: a)
  : Lemma
      (requires s == t /\ Seq.mem x s)
      (ensures Seq.mem x t)
  =
  assert (Seq.equal s t);
  Seq.lemma_eq_elim s t

let nat_nonzero_pos (n: nat)
  : Lemma (requires n <> 0) (ensures n > 0)
  = ()

#push-options "--z3rlimit 10 --fuel 2 --ifuel 1 --split_queries always"
let rec objects_in_chunk_from_write_after_member_preserves
    (c: MH.heap_chunk)
    (start: hp_addr)
    (obj: obj_addr)
    (addr: hp_addr)
    (value: U64.t)
  : Lemma
      (requires
        Seq.mem obj (MH.objects_in_chunk_from c start) /\
        MH.word_in_chunk c addr /\
        U64.v (hd_address obj) +
          (1 + MH.object_wosize_in_chunk c obj) * U64.v mword <=
          U64.v addr)
      (ensures
        Seq.mem obj
          (MH.objects_in_chunk_from
            (MH.write_word_in_chunk c addr value) start))
      (decreases MH.chunk_end c - U64.v start)
  =
  let c' = MH.write_word_in_chunk c addr value in
  MH.write_word_in_chunk_preserves_range c addr value;
  if U64.v start < MH.chunk_start c then
    assert False
  else if U64.v start + U64.v mword >= MH.chunk_end c then
    assert False
  else begin
    assert (MH.word_in_chunk c start);
    MH.objects_in_chunk_from_addresses_gt_start c start obj;
    assert (U64.v obj > U64.v start);
    hd_address_spec obj;
    assert (U64.v (hd_address obj) + U64.v mword == U64.v obj);
    assert ((1 + MH.object_wosize_in_chunk c obj) * U64.v mword >=
            U64.v mword);
    assert (U64.v addr >= U64.v obj);
    assert (U64.v addr > U64.v start);
    MH.word_aligned_gt_at_least_mword (U64.v addr) (U64.v start);
    assert (U64.v start + U64.v mword <= U64.v addr);
    assert (addr <> start);
    MH.read_write_in_chunk_different c addr start value;
    assert (MH.read_word_in_chunk c' start == MH.read_word_in_chunk c start);
    let header = MH.read_word_in_chunk c start in
    let wz = Obj.getWosize header in
    let obj_size_words : nat = U64.v wz + 1 in
    assert (obj_size_words * U64.v mword >= 0);
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
        assert (MH.object_wosize_in_chunk c obj == U64.v wz);
        assert (U64.v addr >=
                U64.v start + (1 + U64.v wz) * U64.v mword);
        MH.objects_in_chunk_from_cons_step c' start;
        Fields.mem_cons_lemma obj obj (Seq.empty #obj_addr)
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
          assert (MH.object_wosize_in_chunk c obj == U64.v wz);
          assert (U64.v addr >= U64.v next_start);
          MH.objects_in_chunk_from_cons_step c' start;
          Fields.mem_cons_lemma obj obj (MH.objects_in_chunk_from c' next_start)
        end else begin
          assert (Seq.mem obj tail);
          MH.objects_in_chunk_from_addresses_gt_start c next_start obj;
          assert (U64.v obj > U64.v next_start);
          assert (U64.v next_start < MH.chunk_end c');
          objects_in_chunk_from_write_after_member_preserves
            c next_start obj addr value;
          MH.objects_in_chunk_from_cons_step c' start;
          assert (Seq.mem obj (MH.objects_in_chunk_from c' next_start));
          Fields.mem_cons_lemma
            obj (f_address start) (MH.objects_in_chunk_from c' next_start)
        end
      end
    end
  end
#pop-options
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

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let major_write_word_or_same_after_member_preserves_chunk_member
    (mh: MH.major_heap)
    (idx: nat)
    (obj: obj_addr)
    (addr: hp_addr)
    (value: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem obj (MH.objects_in_chunk (Seq.index mh idx)) /\
        MH.word_in_chunk (Seq.index mh idx) addr /\
        U64.v (hd_address obj) +
          (1 + MH.object_wosize_in_chunk (Seq.index mh idx) obj) *
            U64.v mword <=
          U64.v addr)
      (ensures
        MH.well_formed_major_heap
          (SpecMajorAlloc.major_write_word_or_same mh addr value) /\
        idx <
          Seq.length
            (SpecMajorAlloc.major_write_word_or_same mh addr value) /\
        Seq.mem obj
          (MH.objects_in_chunk
            (Seq.index
              (SpecMajorAlloc.major_write_word_or_same mh addr value)
              idx)) /\
        MH.object_wosize_in_chunk
          (Seq.index
            (SpecMajorAlloc.major_write_word_or_same mh addr value)
            idx)
          obj ==
        MH.object_wosize_in_chunk (Seq.index mh idx) obj /\
        MH.chunk_start
          (Seq.index
            (SpecMajorAlloc.major_write_word_or_same mh addr value)
            idx) ==
        MH.chunk_start (Seq.index mh idx) /\
        MH.chunk_end
          (Seq.index
            (SpecMajorAlloc.major_write_word_or_same mh addr value)
            idx) ==
        MH.chunk_end (Seq.index mh idx))
  =
  let c = Seq.index mh idx in
  let c' = MH.write_word_in_chunk c addr value in
  MH.objects_in_chunk_member_header_fits c obj;
  assert (MH.word_in_chunk c (hd_address obj));
  assert (U64.v (hd_address obj) + U64.v mword <= U64.v addr);
  MH.read_write_in_chunk_different c addr (hd_address obj) value;
  MH.lookup_chunk_index_word_in_chunk mh addr idx;
  MH.write_word_in_major_at_lookup_index mh addr value idx;
  assert (MH.write_word_in_major mh addr value == Some (Seq.upd mh idx c'));
  SpecMajorAlloc.major_write_word_or_same_some
    mh (Seq.upd mh idx c') addr value;
  MH.write_word_at_index_preserves_wf mh addr value idx;
  assert (MH.well_formed_major_heap (Seq.upd mh idx c'));
  objects_in_chunk_from_write_after_member_preserves c c.base obj addr value;
  assert (Seq.mem obj (MH.objects_in_chunk c'));
  assert (Seq.index (Seq.upd mh idx c') idx == c');
  assert (MH.read_word_in_chunk c' (hd_address obj) ==
          MH.read_word_in_chunk c (hd_address obj));
  assert (MH.object_wosize_in_chunk c' obj ==
          MH.object_wosize_in_chunk c obj);
  assert (MH.chunk_start c' == MH.chunk_start c);
  assert (MH.chunk_end c' == MH.chunk_end c)

let major_write_word_or_same_after_member_preserves_vertex
    (mh: MH.major_heap)
    (idx: nat)
    (obj: obj_addr)
    (addr: hp_addr)
    (value: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem obj (MH.objects_in_chunk (Seq.index mh idx)) /\
        MH.word_in_chunk (Seq.index mh idx) addr /\
        U64.v (hd_address obj) +
          (1 + MH.object_wosize_in_chunk (Seq.index mh idx) obj) *
            U64.v mword <=
          U64.v addr)
      (ensures
        Seq.mem obj
          (MH.major_objects
            (SpecMajorAlloc.major_write_word_or_same mh addr value)))
  =
  let mh' = SpecMajorAlloc.major_write_word_or_same mh addr value in
  major_write_word_or_same_after_member_preserves_chunk_member
    mh idx obj addr value;
  assert (idx < Seq.length mh');
  assert (Seq.mem obj (MH.objects_in_chunk (Seq.index mh' idx)));
  MH.major_objects_member_at_index mh' idx obj
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
let rec chunked_zero_fields_after_member_preserves_chunk_member
    (mh: MH.major_heap)
    (idx: nat)
    (obj: obj_addr)
    (addr: U64.t)
    (n: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem obj (MH.objects_in_chunk (Seq.index mh idx)) /\
        U64.v addr % U64.v mword == 0 /\
        U64.v addr + n * U64.v mword <= MH.chunk_end (Seq.index mh idx) /\
        U64.v (hd_address obj) +
          (1 + MH.object_wosize_in_chunk (Seq.index mh idx) obj) *
            U64.v mword <=
          U64.v addr)
      (ensures
        MH.well_formed_major_heap (Defs.chunked_zero_fields mh addr n) /\
        idx < Seq.length (Defs.chunked_zero_fields mh addr n) /\
        Seq.mem obj
          (MH.objects_in_chunk
            (Seq.index (Defs.chunked_zero_fields mh addr n) idx)) /\
        MH.object_wosize_in_chunk
          (Seq.index (Defs.chunked_zero_fields mh addr n) idx)
          obj ==
        MH.object_wosize_in_chunk (Seq.index mh idx) obj)
      (decreases n)
  =
  if n = 0 then
    Defs.chunked_zero_fields_zero mh addr
  else if U64.v addr + U64.v mword > heap_size then
    Defs.chunked_zero_fields_no_room mh addr n
  else if U64.v addr >= heap_size then
    Defs.chunked_zero_fields_out_of_heap mh addr n
  else if U64.v addr % U64.v mword <> 0 then
    Defs.chunked_zero_fields_unaligned mh addr n
  else begin
    assert (n <> 0);
    nat_nonzero_pos n;
    assert (n > 0);
    let c = Seq.index mh idx in
    MH.objects_in_chunk_member_header_fits c obj;
    assert (MH.word_in_chunk c (hd_address obj));
    hd_address_spec obj;
    assert (U64.v (hd_address obj) + U64.v mword == U64.v obj);
    assert (U64.v (hd_address obj) +
              (1 + MH.object_wosize_in_chunk c obj) * U64.v mword >=
            U64.v obj);
    assert (MH.chunk_start c <= U64.v addr);
    assert (n * U64.v mword >= U64.v mword);
    assert (U64.v addr + U64.v mword <= MH.chunk_end c);
    let hp : hp_addr = addr in
    assert (MH.word_in_chunk c hp);
    let mh' = SpecMajorAlloc.major_write_word_or_same mh hp 0UL in
    major_write_word_or_same_after_member_preserves_chunk_member
      mh idx obj hp 0UL;
    Defs.chunked_zero_fields_step mh addr n;
    if U64.v addr + U64.v mword >= pow2 64 then
      ()
    else begin
      let n1 : nat = n - 1 in
      MH.next_object_start_aligned hp 1;
      let next_addr = U64.uint_to_t (U64.v addr + U64.v mword) in
      assert (U64.v next_addr == U64.v addr + U64.v mword);
      assert ((U64.v addr + 1 * U64.v mword) % U64.v mword == 0);
      assert (U64.v next_addr % U64.v mword == 0);
      assert (n == n1 + 1);
      FStar.Math.Lemmas.distributivity_add_left
        1 n1 (U64.v mword);
      FStar.Math.Lemmas.paren_add_right
        (U64.v addr) (U64.v mword) (n1 * U64.v mword);
      assert (U64.v next_addr + n1 * U64.v mword ==
              U64.v addr + n * U64.v mword);
      assert (idx < Seq.length mh');
      assert (MH.well_formed_major_heap mh');
      assert (Seq.mem obj (MH.objects_in_chunk (Seq.index mh' idx)));
      assert (MH.object_wosize_in_chunk (Seq.index mh' idx) obj ==
              MH.object_wosize_in_chunk (Seq.index mh idx) obj);
      assert (MH.chunk_end (Seq.index mh' idx) == MH.chunk_end c);
      assert (U64.v next_addr + n1 * U64.v mword <=
              MH.chunk_end (Seq.index mh' idx));
      assert (U64.v (hd_address obj) +
                (1 + MH.object_wosize_in_chunk (Seq.index mh' idx) obj) *
                  U64.v mword <=
              U64.v next_addr);
      chunked_zero_fields_after_member_preserves_chunk_member
        mh' idx obj next_addr n1
    end
  end
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0 --split_queries always"
let chunked_flush_blue_after_member_preserves_chunk_member
    (mh: MH.major_heap)
    (idx: nat)
    (obj: obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem obj (MH.objects_in_chunk (Seq.index mh idx)) /\
        (run_words <> 0 /\
         ~(U64.v first_blue < U64.v mword) /\
         ~(U64.v first_blue >= heap_size) /\
         ~(U64.v first_blue % U64.v mword <> 0) /\
         run_words - 1 < pow2 54 ==>
          (let fb : obj_addr = first_blue in
           let hd = hd_address fb in
           MH.word_in_chunk (Seq.index mh idx) hd /\
           U64.v (hd_address obj) +
             (1 + MH.object_wosize_in_chunk (Seq.index mh idx) obj) *
               U64.v mword <=
             U64.v hd /\
           U64.v hd + run_words * U64.v mword <=
             MH.chunk_end (Seq.index mh idx))))
      (ensures
        (let final = fst (Defs.chunked_flush_blue mh first_blue run_words fp) in
        MH.well_formed_major_heap final /\
        idx < Seq.length final /\
        Seq.mem obj (MH.objects_in_chunk (Seq.index final idx)) /\
        MH.object_wosize_in_chunk (Seq.index final idx) obj ==
        MH.object_wosize_in_chunk (Seq.index mh idx) obj))
  =
  if run_words = 0 then
    Defs.chunked_flush_blue_empty mh first_blue fp
  else begin
    assert (run_words <> 0);
    nat_nonzero_pos run_words;
    let rw : pos = run_words in
    if U64.v first_blue < U64.v mword ||
       U64.v first_blue >= heap_size ||
       U64.v first_blue % U64.v mword <> 0
    then begin
      Defs.chunked_flush_blue_invalid mh first_blue rw fp
    end else if run_words - 1 >= pow2 54 then begin
      Defs.chunked_flush_blue_too_large mh first_blue rw fp
    end else begin
      assert (run_words - 1 < pow2 54);
      FStar.Math.Lemmas.pow2_lt_compat 64 54;
      assert (run_words - 1 < pow2 64);
      assert (rw == run_words);
      assert (run_words >= 1);
      assert (run_words - 1 >= 0);
      let fb : obj_addr = first_blue in
      let hd = hd_address fb in
      let wz : nat = run_words - 1 in
      let wz_u64 : Obj.wosize = U64.uint_to_t wz in
      let hdr = Obj.makeHeader wz_u64 Header.Blue 0UL in
      Defs.chunked_flush_blue_step mh first_blue rw fp;
      let mh1 = SpecMajorAlloc.major_write_word_or_same mh hd hdr in
      major_write_word_or_same_after_member_preserves_chunk_member
        mh idx obj hd hdr;
      assert (MH.well_formed_major_heap mh1);
      assert (idx < Seq.length mh1);
      assert (Seq.mem obj (MH.objects_in_chunk (Seq.index mh1 idx)));
      assert (MH.object_wosize_in_chunk (Seq.index mh1 idx) obj ==
              MH.object_wosize_in_chunk (Seq.index mh idx) obj);
      assert (MH.chunk_end (Seq.index mh1 idx) ==
              MH.chunk_end (Seq.index mh idx));
      if wz >= 1 && U64.v hd + U64.v mword * 2 <= heap_size then begin
        hd_address_spec fb;
        assert (U64.v hd + U64.v mword == U64.v fb);
        assert (run_words == wz + 1);
        assert (wz >= 1);
        assert (run_words >= 2);
        FStar.Math.Lemmas.lemma_mult_le_right
          (U64.v mword) 2 run_words;
        assert (U64.v mword * 2 <= U64.v mword * run_words);
        assert (U64.v mword * 2 == U64.v mword + U64.v mword);
        assert (2 * U64.v mword == U64.v mword * 2);
        assert (run_words * U64.v mword == U64.v mword * run_words);
        assert (U64.v hd + U64.v mword * 2 <=
                U64.v hd + run_words * U64.v mword);
        assert (U64.v fb + U64.v mword <=
                MH.chunk_end (Seq.index mh1 idx));
        assert (MH.word_in_chunk (Seq.index mh1 idx) fb);
        assert (U64.v (hd_address obj) +
                  (1 + MH.object_wosize_in_chunk (Seq.index mh1 idx) obj) *
                    U64.v mword <=
                U64.v fb);
        let mh2 = SpecMajorAlloc.major_write_word_or_same mh1 fb fp in
        major_write_word_or_same_after_member_preserves_chunk_member
          mh1 idx obj fb fp;
        assert (MH.well_formed_major_heap mh2);
        assert (idx < Seq.length mh2);
        assert (Seq.mem obj (MH.objects_in_chunk (Seq.index mh2 idx)));
        assert (MH.object_wosize_in_chunk (Seq.index mh2 idx) obj ==
                MH.object_wosize_in_chunk (Seq.index mh idx) obj);
        assert (MH.chunk_end (Seq.index mh2 idx) ==
                MH.chunk_end (Seq.index mh idx));
        let zero_start_nat = U64.v fb + U64.v mword in
        if wz >= 2 && zero_start_nat < pow2 64 then begin
          let zero_start = U64.uint_to_t zero_start_nat in
          assert (U64.v zero_start == zero_start_nat);
          MH.next_object_start_aligned fb 1;
          assert (U64.v zero_start % U64.v mword == 0);
          assert (wz - 1 + 2 == run_words);
          FStar.Math.Lemmas.distributivity_add_left
            2 (wz - 1) (U64.v mword);
          FStar.Math.Lemmas.paren_add_right
            (U64.v hd) (2 * U64.v mword) ((wz - 1) * U64.v mword);
          assert (U64.v zero_start + (wz - 1) * U64.v mword ==
                  U64.v hd + run_words * U64.v mword);
          assert (U64.v zero_start + (wz - 1) * U64.v mword <=
                  MH.chunk_end (Seq.index mh2 idx));
          assert (U64.v (hd_address obj) +
                    (1 + MH.object_wosize_in_chunk (Seq.index mh2 idx) obj) *
                      U64.v mword <=
                  U64.v zero_start);
          chunked_zero_fields_after_member_preserves_chunk_member
            mh2 idx obj zero_start (wz - 1)
        end
      end
    end
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_make_white_preserves_chunk_member
    (mh: MH.major_heap)
    (idx: nat)
    (obj: obj_addr)
    (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem obj (MH.objects_in_chunk (Seq.index mh idx)) /\
        Defs.chunked_read_header mh obj == Some hdr)
      (ensures
        MH.well_formed_major_heap (Defs.chunked_make_white mh obj) /\
        idx < Seq.length (Defs.chunked_make_white mh obj) /\
        Seq.mem obj
          (MH.objects_in_chunk
            (Seq.index (Defs.chunked_make_white mh obj) idx)) /\
        MH.object_wosize_in_chunk
          (Seq.index (Defs.chunked_make_white mh obj) idx)
          obj ==
        MH.object_wosize_in_chunk (Seq.index mh idx) obj /\
        MH.chunk_start (Seq.index (Defs.chunked_make_white mh obj) idx) ==
        MH.chunk_start (Seq.index mh idx) /\
        MH.chunk_end (Seq.index (Defs.chunked_make_white mh obj) idx) ==
        MH.chunk_end (Seq.index mh idx))
  =
  let c = Seq.index mh idx in
  Defs.chunked_make_white_step mh obj;
  Defs.chunked_set_object_color_some mh obj Header.White hdr;
  Defs.chunked_read_header_step mh obj;
  assert (MH.read_word_in_major mh (hd_address obj) == Some hdr);
  MH.objects_in_chunk_member_header_fits c obj;
  assert (MH.word_in_chunk c (hd_address obj));
  MH.lookup_chunk_index_word_in_chunk mh (hd_address obj) idx;
  MH.read_word_in_major_at_lookup_index mh (hd_address obj) idx;
  assert (MH.read_word_in_chunk c (hd_address obj) == hdr);
  MH.write_word_in_major_at_lookup_index
    mh (hd_address obj) (Obj.colorHeader hdr Header.White) idx;
  let c' =
    MH.write_word_in_chunk c (hd_address obj)
      (Obj.colorHeader hdr Header.White) in
  assert (MH.write_word_in_major
            mh (hd_address obj) (Obj.colorHeader hdr Header.White) ==
          Some (Seq.upd mh idx c'));
  SpecMajorAlloc.major_write_word_or_same_some
    mh (Seq.upd mh idx c') (hd_address obj)
    (Obj.colorHeader hdr Header.White);
  Obj.colorHeader_preserves_wosize hdr Header.White;
  assert (MH.object_wosize_in_chunk c obj == U64.v (Obj.getWosize hdr));
  assert (U64.v (Obj.getWosize (Obj.colorHeader hdr Header.White)) ==
          MH.object_wosize_in_chunk c obj);
  MH.objects_in_chunk_from_write_member_header_same_wosize_preserves
    c c.base obj (Obj.colorHeader hdr Header.White);
  assert (MH.objects_in_chunk c' == MH.objects_in_chunk c);
  assert (Seq.mem obj (MH.objects_in_chunk c'));
  MH.write_word_at_index_preserves_wf
    mh (hd_address obj) (Obj.colorHeader hdr Header.White) idx;
  MH.write_word_in_chunk_preserves_range
    c (hd_address obj) (Obj.colorHeader hdr Header.White);
  MH.read_write_in_chunk_same
    c (hd_address obj) (Obj.colorHeader hdr Header.White);
  assert (MH.read_word_in_chunk c' (hd_address obj) ==
          Obj.colorHeader hdr Header.White);
  assert (Seq.index (Seq.upd mh idx c') idx == c');
  assert (MH.chunk_start c' == MH.chunk_start c);
  assert (MH.chunk_end c' == MH.chunk_end c);
  assert (MH.object_wosize_in_chunk c' obj ==
          MH.object_wosize_in_chunk c obj)

let chunked_make_white_after_member_preserves_chunk_member
    (mh: MH.major_heap)
    (idx: nat)
    (protected: obj_addr)
    (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem protected (MH.objects_in_chunk (Seq.index mh idx)) /\
        MH.word_in_chunk (Seq.index mh idx) (hd_address obj) /\
        U64.v (hd_address protected) +
          (1 + MH.object_wosize_in_chunk (Seq.index mh idx) protected) *
            U64.v mword <=
          U64.v (hd_address obj))
      (ensures
        MH.well_formed_major_heap (Defs.chunked_make_white mh obj) /\
        idx < Seq.length (Defs.chunked_make_white mh obj) /\
        Seq.mem protected
          (MH.objects_in_chunk
            (Seq.index (Defs.chunked_make_white mh obj) idx)) /\
        MH.object_wosize_in_chunk
          (Seq.index (Defs.chunked_make_white mh obj) idx)
          protected ==
        MH.object_wosize_in_chunk (Seq.index mh idx) protected /\
        MH.chunk_start (Seq.index (Defs.chunked_make_white mh obj) idx) ==
        MH.chunk_start (Seq.index mh idx) /\
        MH.chunk_end (Seq.index (Defs.chunked_make_white mh obj) idx) ==
        MH.chunk_end (Seq.index mh idx))
  =
  Defs.chunked_make_white_step mh obj;
  match Defs.chunked_read_header mh obj with
  | None ->
    Defs.chunked_set_object_color_none mh obj Header.White
  | Some hdr ->
    Defs.chunked_set_object_color_some mh obj Header.White hdr;
    major_write_word_or_same_after_member_preserves_chunk_member
      mh idx protected (hd_address obj) (Obj.colorHeader hdr Header.White)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let major_write_word_or_same_payload_preserves_objects_from
    (mh: MH.major_heap)
    (idx: nat)
    (start: hp_addr)
    (blk: obj_addr)
    (addr: hp_addr)
    (value: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem blk (MH.objects_in_chunk_from (Seq.index mh idx) start) /\
        MH.word_in_chunk (Seq.index mh idx) addr /\
        U64.v blk <= U64.v addr /\
        U64.v addr + U64.v mword <=
          U64.v blk +
            MH.object_wosize_in_chunk (Seq.index mh idx) blk *
              U64.v mword)
      (ensures
        (let mh' = SpecMajorAlloc.major_write_word_or_same mh addr value in
         MH.well_formed_major_heap mh' /\
         idx < Seq.length mh' /\
         MH.objects_in_chunk_from (Seq.index mh' idx) start ==
         MH.objects_in_chunk_from (Seq.index mh idx) start /\
         MH.object_wosize_in_chunk (Seq.index mh' idx) blk ==
         MH.object_wosize_in_chunk (Seq.index mh idx) blk /\
         MH.chunk_start (Seq.index mh' idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index mh' idx) ==
         MH.chunk_end (Seq.index mh idx)))
  =
  let c = Seq.index mh idx in
  let c' = MH.write_word_in_chunk c addr value in
  MH.lookup_chunk_index_word_in_chunk mh addr idx;
  MH.write_word_in_major_at_lookup_index mh addr value idx;
  assert (MH.write_word_in_major mh addr value == Some (Seq.upd mh idx c'));
  SpecMajorAlloc.major_write_word_or_same_some mh (Seq.upd mh idx c') addr value;
  MH.objects_in_chunk_from_member_header_fits c start blk;
  assert (MH.word_in_chunk c (hd_address blk));
  hd_address_spec blk;
  assert (U64.v (hd_address blk) + U64.v mword == U64.v blk);
  assert (U64.v (hd_address blk) + U64.v mword <= U64.v addr);
  MH.read_write_in_chunk_different c addr (hd_address blk) value;
  MH.objects_in_chunk_from_write_member_payload_preserves
    c start blk addr value;
  assert (MH.objects_in_chunk_from c' start ==
          MH.objects_in_chunk_from c start);
  MH.write_word_at_index_preserves_wf mh addr value idx;
  MH.write_word_in_chunk_preserves_range c addr value;
  assert (Seq.index (Seq.upd mh idx c') idx == c');
  assert (MH.read_word_in_chunk c' (hd_address blk) ==
          MH.read_word_in_chunk c (hd_address blk));
  assert (MH.object_wosize_in_chunk c' blk ==
          MH.object_wosize_in_chunk c blk);
  assert (MH.chunk_start c' == MH.chunk_start c);
  assert (MH.chunk_end c' == MH.chunk_end c)
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
let rec chunked_zero_fields_payload_preserves_objects_from
    (mh: MH.major_heap)
    (idx: nat)
    (start: hp_addr)
    (blk: obj_addr)
    (addr: U64.t)
    (n: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem blk (MH.objects_in_chunk_from (Seq.index mh idx) start) /\
        U64.v addr % U64.v mword == 0 /\
        U64.v blk <= U64.v addr /\
        U64.v addr + n * U64.v mword <=
          U64.v blk +
            MH.object_wosize_in_chunk (Seq.index mh idx) blk *
              U64.v mword)
      (ensures
        (let mh' = Defs.chunked_zero_fields mh addr n in
         MH.well_formed_major_heap mh' /\
         idx < Seq.length mh' /\
         MH.objects_in_chunk_from (Seq.index mh' idx) start ==
         MH.objects_in_chunk_from (Seq.index mh idx) start /\
         MH.object_wosize_in_chunk (Seq.index mh' idx) blk ==
         MH.object_wosize_in_chunk (Seq.index mh idx) blk /\
         MH.chunk_start (Seq.index mh' idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index mh' idx) ==
         MH.chunk_end (Seq.index mh idx)))
      (decreases n)
  =
  if n = 0 then
    Defs.chunked_zero_fields_zero mh addr
  else if U64.v addr + U64.v mword > heap_size then
    Defs.chunked_zero_fields_no_room mh addr n
  else if U64.v addr >= heap_size then
    Defs.chunked_zero_fields_out_of_heap mh addr n
  else if U64.v addr % U64.v mword <> 0 then
    Defs.chunked_zero_fields_unaligned mh addr n
  else begin
    assert (n <> 0);
    nat_nonzero_pos n;
    assert (n > 0);
    let c = Seq.index mh idx in
    MH.objects_in_chunk_from_member_header_fits c start blk;
    assert (MH.object_header_size_fits_in_chunk c blk);
    assert (MH.word_in_chunk c (hd_address blk));
    hd_address_spec blk;
    assert (U64.v (hd_address blk) + U64.v mword == U64.v blk);
    let bwz = MH.object_wosize_in_chunk c blk in
    assert (U64.v (hd_address blk) + (1 + bwz) * U64.v mword <=
            MH.chunk_end c);
    FStar.Math.Lemmas.distributivity_add_left 1 bwz (U64.v mword);
    FStar.Math.Lemmas.paren_add_right
      (U64.v (hd_address blk)) (U64.v mword) (bwz * U64.v mword);
    assert (U64.v blk + bwz * U64.v mword ==
            U64.v (hd_address blk) + (1 + bwz) * U64.v mword);
    assert (MH.chunk_start c <= U64.v blk);
    assert (MH.chunk_start c <= U64.v addr);
    assert (n * U64.v mword >= U64.v mword);
    assert (U64.v addr + U64.v mword <=
            U64.v blk + MH.object_wosize_in_chunk c blk * U64.v mword);
    assert (U64.v blk + MH.object_wosize_in_chunk c blk * U64.v mword <=
            MH.chunk_end c);
    assert (U64.v addr + U64.v mword <= MH.chunk_end c);
    let hp : hp_addr = addr in
    assert (MH.word_in_chunk c hp);
    let mh1 = SpecMajorAlloc.major_write_word_or_same mh hp 0UL in
    major_write_word_or_same_payload_preserves_objects_from
      mh idx start blk hp 0UL;
    Defs.chunked_zero_fields_step mh addr n;
    if U64.v addr + U64.v mword >= pow2 64 then
      ()
    else begin
      let n1 : nat = n - 1 in
      MH.next_object_start_aligned hp 1;
      let next_addr = U64.uint_to_t (U64.v addr + U64.v mword) in
      assert (U64.v next_addr == U64.v addr + U64.v mword);
      assert ((U64.v addr + 1 * U64.v mword) % U64.v mword == 0);
      assert (U64.v next_addr % U64.v mword == 0);
      assert (n == n1 + 1);
      FStar.Math.Lemmas.distributivity_add_left
        1 n1 (U64.v mword);
      FStar.Math.Lemmas.paren_add_right
        (U64.v addr) (U64.v mword) (n1 * U64.v mword);
      assert (U64.v next_addr + n1 * U64.v mword ==
              U64.v addr + n * U64.v mword);
      assert (MH.well_formed_major_heap mh1);
      assert (idx < Seq.length mh1);
      assert (MH.objects_in_chunk_from (Seq.index mh1 idx) start ==
              MH.objects_in_chunk_from c start);
      assert (Seq.mem blk (MH.objects_in_chunk_from (Seq.index mh1 idx) start));
      assert (MH.object_wosize_in_chunk (Seq.index mh1 idx) blk ==
              MH.object_wosize_in_chunk c blk);
      assert (U64.v blk <= U64.v next_addr);
      assert (U64.v next_addr + n1 * U64.v mword <=
              U64.v blk +
                MH.object_wosize_in_chunk (Seq.index mh1 idx) blk *
                  U64.v mword);
      chunked_zero_fields_payload_preserves_objects_from
        mh1 idx start blk next_addr n1
    end
  end
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0 --split_queries always"
let chunked_flush_blue_prefix_preserves_objects_from
    (mh: MH.major_heap)
    (idx: nat)
    (fb: obj_addr)
    (run_words: pos)
    (start: hp_addr)
    (target: obj_addr)
    (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        U64.v fb < MH.chunk_end (Seq.index mh idx) /\
        U64.v fb + (run_words - 1) * U64.v mword == U64.v start /\
        run_words - 1 < pow2 54 /\
        run_words - 1 < pow2 64 /\
        U64.v start <= MH.chunk_end (Seq.index mh idx) /\
        MH.word_in_chunk (Seq.index mh idx) (hd_address fb) /\
        Seq.mem target
          (MH.objects_in_chunk_from (Seq.index mh idx) start))
      (ensures
        (let final = fst (Defs.chunked_flush_blue mh fb run_words fp) in
         MH.well_formed_major_heap final /\
         idx < Seq.length final /\
         Seq.mem target
           (MH.objects_in_chunk_from
             (Seq.index final idx) (hd_address fb)) /\
         MH.chunk_start (Seq.index final idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index final idx) ==
         MH.chunk_end (Seq.index mh idx)))
  =
  let c = Seq.index mh idx in
  let hd = hd_address fb in
  let wz : nat = run_words - 1 in
  let wz_u64 : Obj.wosize = U64.uint_to_t wz in
  let hdr = Obj.makeHeader wz_u64 Header.Blue 0UL in
  Defs.chunked_flush_blue_step mh fb run_words fp;
  let mh1 = SpecMajorAlloc.major_write_word_or_same mh hd hdr in
  let c1 = MH.write_word_in_chunk c hd hdr in
  MH.lookup_chunk_index_word_in_chunk mh hd idx;
  MH.write_word_in_major_at_lookup_index mh hd hdr idx;
  assert (MH.write_word_in_major mh hd hdr == Some (Seq.upd mh idx c1));
  SpecMajorAlloc.major_write_word_or_same_some mh (Seq.upd mh idx c1) hd hdr;
  MH.write_word_at_index_preserves_wf mh hd hdr idx;
  MH.write_word_in_chunk_preserves_range c hd hdr;
  MH.read_write_in_chunk_same c hd hdr;
  assert (MH.read_word_in_chunk c1 hd == hdr);
  hd_address_spec fb;
  assert (U64.v hd + U64.v mword == U64.v fb);
  assert (run_words >= 1);
  assert (wz == run_words - 1);
  FStar.Math.Lemmas.lemma_mult_le_right (U64.v mword) 0 wz;
  assert (0 * U64.v mword == 0);
  assert (wz * U64.v mword >= 0);
  assert (U64.v start == U64.v fb + wz * U64.v mword);
  assert (U64.v fb <= U64.v start);
  assert (U64.v hd + U64.v mword <= U64.v start);
  MH.objects_in_chunk_from_write_before_preserves c start hd hdr;
  assert (MH.objects_in_chunk_from c1 start ==
          MH.objects_in_chunk_from c start);
  Obj.makeHeader_getWosize wz_u64 Header.Blue 0UL;
  assert (U64.v wz_u64 == wz);
  assert (Obj.getWosize hdr == wz_u64);
  assert (MH.object_wosize_in_chunk c1 fb == wz);
  assert (Seq.mem target (MH.objects_in_chunk_from c1 start));
  chunked_merged_block_step c1 fb run_words start target;
  assert (Seq.mem fb (MH.objects_in_chunk_from c1 hd));
  assert (Seq.mem target (MH.objects_in_chunk_from c1 hd));
  assert (Seq.index mh1 idx == c1);
  assert (MH.well_formed_major_heap mh1);
  assert (idx < Seq.length mh1);
  assert (MH.chunk_start (Seq.index mh1 idx) == MH.chunk_start c);
  assert (MH.chunk_end (Seq.index mh1 idx) == MH.chunk_end c);
  if wz >= 1 && U64.v hd + U64.v mword * 2 <= heap_size then begin
    assert (run_words == wz + 1);
    assert (wz >= 1);
    assert (run_words >= 2);
    FStar.Math.Lemmas.lemma_mult_le_right (U64.v mword) 1 wz;
    assert (wz * U64.v mword >= U64.v mword);
    assert (U64.v start == U64.v fb + wz * U64.v mword);
    assert (U64.v fb + U64.v mword <= U64.v start);
    assert (U64.v fb + U64.v mword <= MH.chunk_end c1);
    assert (MH.word_in_chunk c1 fb);
    assert (U64.v fb + U64.v mword <= U64.v fb + wz * U64.v mword);
    let mh2 = SpecMajorAlloc.major_write_word_or_same mh1 fb fp in
    major_write_word_or_same_payload_preserves_objects_from
      mh1 idx hd fb fb fp;
    assert (MH.well_formed_major_heap mh2);
    assert (idx < Seq.length mh2);
    assert (MH.objects_in_chunk_from (Seq.index mh2 idx) hd ==
            MH.objects_in_chunk_from c1 hd);
    assert (Seq.mem target (MH.objects_in_chunk_from (Seq.index mh2 idx) hd));
    assert (MH.object_wosize_in_chunk (Seq.index mh2 idx) fb ==
            MH.object_wosize_in_chunk c1 fb);
    assert (MH.chunk_start (Seq.index mh2 idx) == MH.chunk_start c);
    assert (MH.chunk_end (Seq.index mh2 idx) == MH.chunk_end c);
    let zero_start_nat = U64.v fb + U64.v mword in
    if wz >= 2 && zero_start_nat < pow2 64 then begin
      let zero_start = U64.uint_to_t zero_start_nat in
      MH.next_object_start_aligned fb 1;
      assert (U64.v zero_start == zero_start_nat);
      assert (U64.v zero_start % U64.v mword == 0);
      assert (wz - 1 + 1 == wz);
      FStar.Math.Lemmas.distributivity_add_left
        1 (wz - 1) (U64.v mword);
      FStar.Math.Lemmas.paren_add_right
        (U64.v fb) (U64.v mword) ((wz - 1) * U64.v mword);
      assert (U64.v zero_start + (wz - 1) * U64.v mword ==
              U64.v fb + wz * U64.v mword);
      chunked_zero_fields_payload_preserves_objects_from
        mh2 idx hd fb zero_start (wz - 1)
    end
  end
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
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

#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let major_write_word_or_same_after_member_preserves_objects_from
    (mh: MH.major_heap)
    (idx: nat)
    (start: hp_addr)
    (protected: obj_addr)
    (addr: hp_addr)
    (value: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index mh idx) start) /\
        MH.word_in_chunk (Seq.index mh idx) addr /\
        U64.v (hd_address protected) +
          (1 + MH.object_wosize_in_chunk (Seq.index mh idx) protected) *
            U64.v mword <=
          U64.v addr)
      (ensures
        (let mh' = SpecMajorAlloc.major_write_word_or_same mh addr value in
         MH.well_formed_major_heap mh' /\
         idx < Seq.length mh' /\
         Seq.mem protected
           (MH.objects_in_chunk_from (Seq.index mh' idx) start) /\
         MH.object_wosize_in_chunk (Seq.index mh' idx) protected ==
         MH.object_wosize_in_chunk (Seq.index mh idx) protected /\
         MH.chunk_start (Seq.index mh' idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index mh' idx) ==
         MH.chunk_end (Seq.index mh idx)))
  =
  let c = Seq.index mh idx in
  let c' = MH.write_word_in_chunk c addr value in
  MH.lookup_chunk_index_word_in_chunk mh addr idx;
  MH.write_word_in_major_at_lookup_index mh addr value idx;
  assert (MH.write_word_in_major mh addr value == Some (Seq.upd mh idx c'));
  SpecMajorAlloc.major_write_word_or_same_some mh (Seq.upd mh idx c') addr value;
  objects_in_chunk_from_write_after_member_preserves
    c start protected addr value;
  MH.objects_in_chunk_from_member_header_fits c start protected;
  assert (MH.word_in_chunk c (hd_address protected));
  hd_address_spec protected;
  assert (U64.v (hd_address protected) + U64.v mword ==
          U64.v protected);
  assert (U64.v (hd_address protected) + U64.v mword <= U64.v addr);
  MH.read_write_in_chunk_different c addr (hd_address protected) value;
  MH.write_word_at_index_preserves_wf mh addr value idx;
  MH.write_word_in_chunk_preserves_range c addr value;
  assert (Seq.index (Seq.upd mh idx c') idx == c');
  assert (MH.read_word_in_chunk c' (hd_address protected) ==
          MH.read_word_in_chunk c (hd_address protected));
  assert (MH.object_wosize_in_chunk c' protected ==
          MH.object_wosize_in_chunk c protected);
  assert (MH.chunk_start c' == MH.chunk_start c);
  assert (MH.chunk_end c' == MH.chunk_end c)
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
let rec chunked_zero_fields_after_member_preserves_objects_from
    (mh: MH.major_heap)
    (idx: nat)
    (start: hp_addr)
    (protected: obj_addr)
    (addr: U64.t)
    (n: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index mh idx) start) /\
        U64.v addr % U64.v mword == 0 /\
        U64.v addr + n * U64.v mword <= MH.chunk_end (Seq.index mh idx) /\
        U64.v (hd_address protected) +
          (1 + MH.object_wosize_in_chunk (Seq.index mh idx) protected) *
            U64.v mword <=
          U64.v addr)
      (ensures
        (let mh' = Defs.chunked_zero_fields mh addr n in
         MH.well_formed_major_heap mh' /\
         idx < Seq.length mh' /\
         Seq.mem protected
           (MH.objects_in_chunk_from (Seq.index mh' idx) start) /\
         MH.object_wosize_in_chunk (Seq.index mh' idx) protected ==
         MH.object_wosize_in_chunk (Seq.index mh idx) protected /\
         MH.chunk_start (Seq.index mh' idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index mh' idx) ==
         MH.chunk_end (Seq.index mh idx)))
      (decreases n)
  =
  if n = 0 then
    Defs.chunked_zero_fields_zero mh addr
  else if U64.v addr + U64.v mword > heap_size then
    Defs.chunked_zero_fields_no_room mh addr n
  else if U64.v addr >= heap_size then
    Defs.chunked_zero_fields_out_of_heap mh addr n
  else if U64.v addr % U64.v mword <> 0 then
    Defs.chunked_zero_fields_unaligned mh addr n
  else begin
    assert (n <> 0);
    nat_nonzero_pos n;
    assert (n > 0);
    let c = Seq.index mh idx in
    MH.objects_in_chunk_from_member_header_fits c start protected;
    assert (MH.object_header_size_fits_in_chunk c protected);
    assert (MH.word_in_chunk c (hd_address protected));
    hd_address_spec protected;
    assert (U64.v (hd_address protected) + U64.v mword ==
            U64.v protected);
    assert (MH.chunk_start c <= U64.v (hd_address protected));
    assert ((1 + MH.object_wosize_in_chunk c protected) *
              U64.v mword >= 0);
    assert (U64.v (hd_address protected) <=
            U64.v (hd_address protected) +
              (1 + MH.object_wosize_in_chunk c protected) *
                U64.v mword);
    assert (U64.v (hd_address protected) <= U64.v addr);
    assert (MH.chunk_start c <= U64.v addr);
    assert (n * U64.v mword >= U64.v mword);
    assert (U64.v addr + U64.v mword <= MH.chunk_end c);
    let hp : hp_addr = addr in
    assert (MH.word_in_chunk c hp);
    let mh1 = SpecMajorAlloc.major_write_word_or_same mh hp 0UL in
    major_write_word_or_same_after_member_preserves_objects_from
      mh idx start protected hp 0UL;
    Defs.chunked_zero_fields_step mh addr n;
    if U64.v addr + U64.v mword >= pow2 64 then
      ()
    else begin
      let n1 : nat = n - 1 in
      MH.next_object_start_aligned hp 1;
      let next_addr = U64.uint_to_t (U64.v addr + U64.v mword) in
      assert (U64.v next_addr == U64.v addr + U64.v mword);
      assert ((U64.v addr + 1 * U64.v mword) % U64.v mword == 0);
      assert (U64.v next_addr % U64.v mword == 0);
      assert (n == n1 + 1);
      FStar.Math.Lemmas.distributivity_add_left
        1 n1 (U64.v mword);
      FStar.Math.Lemmas.paren_add_right
        (U64.v addr) (U64.v mword) (n1 * U64.v mword);
      assert (U64.v next_addr + n1 * U64.v mword ==
              U64.v addr + n * U64.v mword);
      assert (MH.well_formed_major_heap mh1);
      assert (idx < Seq.length mh1);
      assert (Seq.mem protected
        (MH.objects_in_chunk_from (Seq.index mh1 idx) start));
      assert (MH.object_wosize_in_chunk (Seq.index mh1 idx) protected ==
              MH.object_wosize_in_chunk c protected);
      assert (MH.chunk_end (Seq.index mh1 idx) == MH.chunk_end c);
      assert (U64.v next_addr + n1 * U64.v mword <=
              MH.chunk_end (Seq.index mh1 idx));
      assert (U64.v (hd_address protected) +
                (1 + MH.object_wosize_in_chunk (Seq.index mh1 idx) protected) *
                  U64.v mword <=
              U64.v next_addr);
      chunked_zero_fields_after_member_preserves_objects_from
        mh1 idx start protected next_addr n1
    end
  end
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0 --split_queries always"
let chunked_flush_blue_after_member_preserves_objects_from
    (mh: MH.major_heap)
    (idx: nat)
    (start: hp_addr)
    (protected: obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index mh idx) start) /\
        (run_words <> 0 /\
         ~(U64.v first_blue < U64.v mword) /\
         ~(U64.v first_blue >= heap_size) /\
         ~(U64.v first_blue % U64.v mword <> 0) /\
         run_words - 1 < pow2 54 ==>
          (let fb : obj_addr = first_blue in
           let hd = hd_address fb in
           MH.word_in_chunk (Seq.index mh idx) hd /\
           U64.v (hd_address protected) +
             (1 + MH.object_wosize_in_chunk (Seq.index mh idx) protected) *
               U64.v mword <=
             U64.v hd /\
           U64.v hd + run_words * U64.v mword <=
             MH.chunk_end (Seq.index mh idx))))
      (ensures
        (let final = fst (Defs.chunked_flush_blue mh first_blue run_words fp) in
         MH.well_formed_major_heap final /\
         idx < Seq.length final /\
         Seq.mem protected
           (MH.objects_in_chunk_from (Seq.index final idx) start) /\
         MH.object_wosize_in_chunk (Seq.index final idx) protected ==
         MH.object_wosize_in_chunk (Seq.index mh idx) protected /\
         MH.chunk_start (Seq.index final idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index final idx) ==
         MH.chunk_end (Seq.index mh idx)))
  =
  if run_words = 0 then
    Defs.chunked_flush_blue_empty mh first_blue fp
  else begin
    let rw : pos = run_words in
    if U64.v first_blue < U64.v mword ||
       U64.v first_blue >= heap_size ||
       U64.v first_blue % U64.v mword <> 0
    then
      Defs.chunked_flush_blue_invalid mh first_blue rw fp
    else if run_words - 1 >= pow2 54 then
      Defs.chunked_flush_blue_too_large mh first_blue rw fp
    else begin
      assert (run_words - 1 < pow2 54);
      FStar.Math.Lemmas.pow2_lt_compat 64 54;
      assert (run_words - 1 < pow2 64);
      assert (rw == run_words);
      let fb : obj_addr = first_blue in
      let hd = hd_address fb in
      let wz : nat = run_words - 1 in
      let wz_u64 : Obj.wosize = U64.uint_to_t wz in
      let hdr = Obj.makeHeader wz_u64 Header.Blue 0UL in
      Defs.chunked_flush_blue_step mh first_blue rw fp;
      let mh1 = SpecMajorAlloc.major_write_word_or_same mh hd hdr in
      major_write_word_or_same_after_member_preserves_objects_from
        mh idx start protected hd hdr;
      assert (MH.well_formed_major_heap mh1);
      assert (idx < Seq.length mh1);
      assert (Seq.mem protected
        (MH.objects_in_chunk_from (Seq.index mh1 idx) start));
      assert (MH.object_wosize_in_chunk (Seq.index mh1 idx) protected ==
              MH.object_wosize_in_chunk (Seq.index mh idx) protected);
      assert (MH.chunk_end (Seq.index mh1 idx) ==
              MH.chunk_end (Seq.index mh idx));
      if wz >= 1 && U64.v hd + U64.v mword * 2 <= heap_size then begin
        hd_address_spec fb;
        assert (U64.v hd + U64.v mword == U64.v fb);
        assert (run_words == wz + 1);
        assert (wz >= 1);
        assert (run_words >= 2);
        FStar.Math.Lemmas.lemma_mult_le_right
          (U64.v mword) 2 run_words;
        assert (2 * U64.v mword <= run_words * U64.v mword);
        assert (U64.v hd + U64.v mword * 2 <=
                U64.v hd + run_words * U64.v mword);
        assert (U64.v fb + U64.v mword <=
                MH.chunk_end (Seq.index mh1 idx));
        assert (MH.word_in_chunk (Seq.index mh1 idx) fb);
        assert (U64.v (hd_address protected) +
                  (1 + MH.object_wosize_in_chunk (Seq.index mh1 idx) protected) *
                    U64.v mword <=
                U64.v fb);
        let mh2 = SpecMajorAlloc.major_write_word_or_same mh1 fb fp in
        major_write_word_or_same_after_member_preserves_objects_from
          mh1 idx start protected fb fp;
        assert (MH.well_formed_major_heap mh2);
        assert (idx < Seq.length mh2);
        assert (Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index mh2 idx) start));
        assert (MH.object_wosize_in_chunk (Seq.index mh2 idx) protected ==
                MH.object_wosize_in_chunk (Seq.index mh idx) protected);
        assert (MH.chunk_end (Seq.index mh2 idx) ==
                MH.chunk_end (Seq.index mh idx));
        let zero_start_nat = U64.v fb + U64.v mword in
        if wz >= 2 && zero_start_nat < pow2 64 then begin
          let zero_start = U64.uint_to_t zero_start_nat in
          assert (U64.v zero_start == zero_start_nat);
          MH.next_object_start_aligned fb 1;
          assert (U64.v zero_start % U64.v mword == 0);
          assert (wz - 1 + 2 == run_words);
          FStar.Math.Lemmas.distributivity_add_left
            2 (wz - 1) (U64.v mword);
          FStar.Math.Lemmas.paren_add_right
            (U64.v hd) (2 * U64.v mword) ((wz - 1) * U64.v mword);
          assert (U64.v zero_start + (wz - 1) * U64.v mword ==
                  U64.v hd + run_words * U64.v mword);
          assert (U64.v zero_start + (wz - 1) * U64.v mword <=
                  MH.chunk_end (Seq.index mh2 idx));
          assert (U64.v (hd_address protected) +
                    (1 + MH.object_wosize_in_chunk (Seq.index mh2 idx) protected) *
                      U64.v mword <=
                  U64.v zero_start);
          chunked_zero_fields_after_member_preserves_objects_from
            mh2 idx start protected zero_start (wz - 1)
        end
      end
    end
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_make_white_after_member_preserves_objects_from
    (mh: MH.major_heap)
    (idx: nat)
    (start: hp_addr)
    (protected: obj_addr)
    (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index mh idx) start) /\
        MH.word_in_chunk (Seq.index mh idx) (hd_address obj) /\
        U64.v (hd_address protected) +
          (1 + MH.object_wosize_in_chunk (Seq.index mh idx) protected) *
            U64.v mword <=
          U64.v (hd_address obj))
      (ensures
        MH.well_formed_major_heap (Defs.chunked_make_white mh obj) /\
        idx < Seq.length (Defs.chunked_make_white mh obj) /\
        Seq.mem protected
          (MH.objects_in_chunk_from
            (Seq.index (Defs.chunked_make_white mh obj) idx) start) /\
        MH.object_wosize_in_chunk
          (Seq.index (Defs.chunked_make_white mh obj) idx)
          protected ==
        MH.object_wosize_in_chunk (Seq.index mh idx) protected /\
        MH.chunk_start (Seq.index (Defs.chunked_make_white mh obj) idx) ==
        MH.chunk_start (Seq.index mh idx) /\
        MH.chunk_end (Seq.index (Defs.chunked_make_white mh obj) idx) ==
        MH.chunk_end (Seq.index mh idx))
  =
  Defs.chunked_make_white_step mh obj;
  let c = Seq.index mh idx in
  let hdr = MH.read_word_in_chunk c (hd_address obj) in
  MH.lookup_chunk_index_word_in_chunk mh (hd_address obj) idx;
  assert (MH.lookup_chunk_index mh (hd_address obj) == Some idx);
  MH.read_word_in_major_at_lookup_index mh (hd_address obj) idx;
  assert (MH.read_word_in_major mh (hd_address obj) == Some hdr);
  Defs.chunked_read_header_step mh obj;
  assert (Defs.chunked_read_header mh obj == Some hdr);
  Defs.chunked_set_object_color_some mh obj Header.White hdr;
  let mh' =
    SpecMajorAlloc.major_write_word_or_same
      mh (hd_address obj) (Obj.colorHeader hdr Header.White) in
  major_write_word_or_same_after_member_preserves_objects_from
    mh idx start protected (hd_address obj)
      (Obj.colorHeader hdr Header.White)
#pop-options

let vertex_blue_run_empty_end_at_next_start
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

let vertex_blue_run_extended_end_at_next_start
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

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
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
#pop-options
