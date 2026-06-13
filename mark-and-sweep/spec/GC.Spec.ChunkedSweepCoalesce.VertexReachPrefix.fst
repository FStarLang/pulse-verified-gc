module GC.Spec.ChunkedSweepCoalesce.VertexReachPrefix

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module Obj = GC.Spec.Object
module Header = GC.Lib.Header
module Defs = GC.Spec.ChunkedSweepCoalesce.Defs
module Pres = GC.Spec.ChunkedSweepCoalesce.Preservation
module Vertex = GC.Spec.ChunkedSweepCoalesce.VertexPreservation
module Reach = GC.Spec.ChunkedSweepCoalesce.VertexReach
module SpecMajorAlloc = GC.Spec.MajorAllocator

#set-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always --warn_error -321"

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let base_member_and_header_member_implies_base_member
    (final: MH.major_heap)
    (idx: nat)
    (base: hp_addr)
    (fb: obj_addr)
    (target: obj_addr)
  : Lemma
      (requires
        idx < Seq.length final /\
        Seq.mem fb (MH.objects_in_chunk_from (Seq.index final idx) base) /\
        Seq.mem target
          (MH.objects_in_chunk_from (Seq.index final idx) (hd_address fb)))
      (ensures
        Seq.mem target (MH.objects_in_chunk_from (Seq.index final idx) base))
  =
  let hd = hd_address fb in
  f_hd_roundtrip fb;
  hd_address_bounds fb;
  assert (f_address hd == fb);
  MH.objects_in_chunk_from_addresses_gt_start (Seq.index final idx) base fb;
  assert (U64.v fb > U64.v base);
  assert (U64.v fb % U64.v mword == 0);
  assert (U64.v base % U64.v mword == 0);
  MH.word_aligned_gt_at_least_mword (U64.v fb) (U64.v base);
  assert (U64.v fb >= U64.v base + U64.v mword);
  hd_address_spec fb;
  assert (U64.v base <= U64.v hd);
  MH.objects_in_chunk_from_later_in_earlier
    (Seq.index final idx) base hd target
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
let chunked_flush_blue_prefix_preserves_base_member
    (mh: MH.major_heap)
    (idx: nat)
    (base: hp_addr)
    (fb: obj_addr)
    (run_words: pos)
    (start: hp_addr)
    (target: obj_addr)
    (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem fb (MH.objects_in_chunk_from (Seq.index mh idx) base) /\
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
         Seq.mem target (MH.objects_in_chunk_from (Seq.index final idx) base) /\
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
  let mh1 = SpecMajorAlloc.major_write_word_or_same mh hd hdr in
  let c1 = MH.write_word_in_chunk c hd hdr in
  Defs.chunked_flush_blue_step mh fb run_words fp;
  Vertex.chunked_flush_blue_prefix_preserves_objects_from
    mh idx fb run_words start target fp;
  Obj.makeHeader_getWosize wz_u64 Header.Blue 0UL;
  assert (U64.v (Obj.getWosize hdr) == wz);
  hd_address_spec fb;
  assert (U64.v hd + U64.v mword == U64.v fb);
  FStar.Math.Lemmas.distributivity_add_left 1 (run_words - 1) (U64.v mword);
  FStar.Math.Lemmas.paren_add_right
    (U64.v hd) (U64.v mword) ((run_words - 1) * U64.v mword);
  assert (U64.v hd + run_words * U64.v mword == U64.v start);
  assert (U64.v hd + (wz + 1) * U64.v mword <= MH.chunk_end c);
  MH.lookup_chunk_index_word_in_chunk mh hd idx;
  MH.write_word_in_major_at_lookup_index mh hd hdr idx;
  assert (MH.write_word_in_major mh hd hdr == Some (Seq.upd mh idx c1));
  SpecMajorAlloc.major_write_word_or_same_some mh (Seq.upd mh idx c1) hd hdr;
  assert (mh1 == Seq.upd mh idx c1);
  MH.write_word_at_index_preserves_wf mh hd hdr idx;
  MH.write_word_in_chunk_preserves_range c hd hdr;
  MH.read_write_in_chunk_same c hd hdr;
  assert (Seq.index mh1 idx == c1);
  assert (MH.read_word_in_chunk c1 hd == hdr);
  assert (MH.object_wosize_in_chunk c1 fb == wz);
  assert (MH.object_wosize_in_chunk (Seq.index mh1 idx) fb == wz);
  Reach.major_write_member_header_preserves_objects_from_member
    mh idx base fb hdr;
  assert (MH.well_formed_major_heap mh1);
  assert (idx < Seq.length mh1);
  assert (Seq.mem fb (MH.objects_in_chunk_from (Seq.index mh1 idx) base));
  assert (MH.chunk_start (Seq.index mh1 idx) == MH.chunk_start c);
  assert (MH.chunk_end (Seq.index mh1 idx) == MH.chunk_end c);
  let final = fst (Defs.chunked_flush_blue mh fb run_words fp) in
  if wz >= 1 && U64.v hd + U64.v mword * 2 <= heap_size then begin
    assert (run_words == wz + 1);
    FStar.Math.Lemmas.lemma_mult_le_right (U64.v mword) 1 wz;
    assert (wz * U64.v mword >= U64.v mword);
    assert (U64.v start == U64.v fb + wz * U64.v mword);
    assert (U64.v fb + U64.v mword <= U64.v start);
    assert (MH.word_in_chunk (Seq.index mh1 idx) fb);
    assert (MH.object_wosize_in_chunk (Seq.index mh1 idx) fb == wz);
    assert (U64.v fb + U64.v mword <=
            U64.v fb +
              MH.object_wosize_in_chunk (Seq.index mh1 idx) fb *
                U64.v mword);
    Vertex.major_write_word_or_same_payload_preserves_objects_from
      mh1 idx base fb fb fp;
    let mh2 = SpecMajorAlloc.major_write_word_or_same mh1 fb fp in
    assert (MH.well_formed_major_heap mh2);
    assert (idx < Seq.length mh2);
    assert (MH.objects_in_chunk_from (Seq.index mh2 idx) base ==
            MH.objects_in_chunk_from (Seq.index mh1 idx) base);
    assert (Seq.mem fb (MH.objects_in_chunk_from (Seq.index mh2 idx) base));
    assert (MH.object_wosize_in_chunk (Seq.index mh2 idx) fb ==
            MH.object_wosize_in_chunk (Seq.index mh1 idx) fb);
    assert (MH.object_wosize_in_chunk (Seq.index mh2 idx) fb == wz);
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
      assert (zero_start_nat + (wz - 1) * U64.v mword ==
              U64.v fb + wz * U64.v mword);
      assert (zero_start_nat + (wz - 1) * U64.v mword ==
              U64.v hd + run_words * U64.v mword);
      assert (zero_start_nat + (wz - 1) * U64.v mword ==
              U64.v fb +
                MH.object_wosize_in_chunk (Seq.index mh2 idx) fb *
                  U64.v mword);
      assert (zero_start_nat + (wz - 1) * U64.v mword <=
              MH.chunk_end (Seq.index mh2 idx));
      Vertex.chunked_zero_fields_payload_preserves_objects_from
        mh2 idx base fb zero_start (wz - 1);
      let mh3 = Defs.chunked_zero_fields mh2 zero_start (wz - 1) in
      assert (MH.well_formed_major_heap mh3);
      assert (idx < Seq.length mh3);
      assert (MH.objects_in_chunk_from (Seq.index mh3 idx) base ==
              MH.objects_in_chunk_from (Seq.index mh2 idx) base);
      assert (Seq.mem fb (MH.objects_in_chunk_from (Seq.index mh3 idx) base));
      Defs.chunked_flush_blue_fst_zero_step mh fb run_words fp;
      assert (final == mh3);
      assert ((final == mh3) /\
              idx < Seq.length mh3 /\
              Seq.mem fb (MH.objects_in_chunk_from (Seq.index mh3 idx) base));
      assert ((final == mh3) /\
              (idx < Seq.length mh3 /\
               Seq.mem fb (MH.objects_in_chunk_from (Seq.index mh3 idx) base)));
      Seq.lemma_eq_refl final mh3;
      Seq.lemma_eq_elim final mh3;
      assert (idx < Seq.length final);
      assert (Seq.index final idx == Seq.index mh3 idx);
      let old_objs = MH.objects_in_chunk_from (Seq.index mh3 idx) base in
      let final_objs = MH.objects_in_chunk_from (Seq.index final idx) base in
      assert (old_objs == final_objs);
      Seq.lemma_eq_refl old_objs final_objs;
      Seq.lemma_eq_elim old_objs final_objs;
      assert (Seq.mem fb old_objs);
      assert (old_objs == final_objs /\ Seq.mem fb old_objs);
      Reach.seq_mem_eq old_objs final_objs fb;
      base_member_and_header_member_implies_base_member
        final idx base fb target
    end else begin
      Defs.chunked_flush_blue_fst_link_step mh fb run_words fp;
      assert (final == mh2);
      assert (Seq.mem fb (MH.objects_in_chunk_from (Seq.index mh2 idx) base));
      assert ((final == mh2) /\
              idx < Seq.length mh2 /\
              Seq.mem fb (MH.objects_in_chunk_from (Seq.index mh2 idx) base));
      assert ((final == mh2) /\
              (idx < Seq.length mh2 /\
               Seq.mem fb (MH.objects_in_chunk_from (Seq.index mh2 idx) base)));
      Seq.lemma_eq_refl final mh2;
      Seq.lemma_eq_elim final mh2;
      assert (idx < Seq.length final);
      assert (Seq.index final idx == Seq.index mh2 idx);
      let old_objs = MH.objects_in_chunk_from (Seq.index mh2 idx) base in
      let final_objs = MH.objects_in_chunk_from (Seq.index final idx) base in
      assert (old_objs == final_objs);
      Seq.lemma_eq_refl old_objs final_objs;
      Seq.lemma_eq_elim old_objs final_objs;
      assert (Seq.mem fb old_objs);
      assert (old_objs == final_objs /\ Seq.mem fb old_objs);
      Reach.seq_mem_eq old_objs final_objs fb;
      base_member_and_header_member_implies_base_member
        final idx base fb target
    end
  end else begin
    Defs.chunked_flush_blue_fst_header_step mh fb run_words fp;
    assert (final == mh1);
    assert (Seq.mem fb (MH.objects_in_chunk_from (Seq.index mh1 idx) base));
    assert ((final == mh1) /\
            idx < Seq.length mh1 /\
            Seq.mem fb (MH.objects_in_chunk_from (Seq.index mh1 idx) base));
    assert ((final == mh1) /\
            (idx < Seq.length mh1 /\
             Seq.mem fb (MH.objects_in_chunk_from (Seq.index mh1 idx) base)));
    Seq.lemma_eq_refl final mh1;
    Seq.lemma_eq_elim final mh1;
    assert (idx < Seq.length final);
    assert (Seq.index final idx == Seq.index mh1 idx);
    let old_objs = MH.objects_in_chunk_from (Seq.index mh1 idx) base in
    let final_objs = MH.objects_in_chunk_from (Seq.index final idx) base in
    assert (old_objs == final_objs);
    Seq.lemma_eq_refl old_objs final_objs;
    Seq.lemma_eq_elim old_objs final_objs;
    assert (Seq.mem fb old_objs);
    assert (old_objs == final_objs /\ Seq.mem fb old_objs);
    Reach.seq_mem_eq old_objs final_objs fb;
    base_member_and_header_member_implies_base_member
      final idx base fb target
  end;
  ()
#pop-options

let nat_nonzero_pos (n: nat)
  : Lemma (requires n <> 0) (ensures n > 0)
  = ()

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunk_member_read_header_wosize
    (mh: MH.major_heap)
    (idx: nat)
    (base: hp_addr)
    (target: obj_addr)
    (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem target
          (MH.objects_in_chunk_from (Seq.index mh idx) base) /\
        Defs.chunked_read_header mh target == Some hdr)
      (ensures
        MH.word_in_chunk (Seq.index mh idx) (hd_address target) /\
        MH.object_wosize_in_chunk (Seq.index mh idx) target ==
        U64.v (Obj.getWosize hdr))
  =
  MH.objects_in_chunk_from_member_header_fits
    (Seq.index mh idx) base target;
  assert (MH.object_header_size_fits_in_chunk (Seq.index mh idx) target);
  assert (MH.word_in_chunk (Seq.index mh idx) (hd_address target));
  MH.lookup_chunk_index_word_in_chunk mh (hd_address target) idx;
  MH.read_word_in_major_at_lookup_index mh (hd_address target) idx;
  Defs.chunked_read_header_step mh target;
  assert (MH.read_word_in_chunk (Seq.index mh idx) (hd_address target) == hdr)

let chunked_flush_blue_then_make_white_head_preserves_base_member
    (mh: MH.major_heap)
    (idx: nat)
    (base: hp_addr)
    (target: obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
    (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem target (MH.objects_in_chunk_from (Seq.index mh idx) base) /\
        Defs.chunked_read_header mh target == Some hdr /\
        (run_words = 0 \/
         (~(U64.v first_blue < U64.v mword) /\
          ~(U64.v first_blue >= heap_size) /\
          ~(U64.v first_blue % U64.v mword <> 0) /\
          run_words - 1 < pow2 54 /\
          run_words - 1 < pow2 64 /\
          U64.v first_blue + (run_words - 1) * U64.v mword ==
            U64.v (hd_address target) /\
          (let fb : obj_addr = first_blue in
           Seq.mem fb (MH.objects_in_chunk_from (Seq.index mh idx) base) /\
           U64.v fb < MH.chunk_end (Seq.index mh idx) /\
           U64.v (hd_address target) <= MH.chunk_end (Seq.index mh idx) /\
           MH.word_in_chunk (Seq.index mh idx) (hd_address fb) /\
           Seq.mem target
             (MH.objects_in_chunk_from
               (Seq.index mh idx) (hd_address target))))))
      (ensures
        (let flushed = Defs.chunked_flush_blue mh first_blue run_words fp in
         let work' = fst flushed in
         let work'' = Defs.chunked_make_white work' target in
         MH.well_formed_major_heap work'' /\
         idx < Seq.length work'' /\
         Seq.mem target
           (MH.objects_in_chunk_from (Seq.index work'' idx) base) /\
         MH.object_wosize_in_chunk (Seq.index work'' idx) target ==
         U64.v (Obj.getWosize hdr) /\
         MH.chunk_start (Seq.index work'' idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index work'' idx) ==
         MH.chunk_end (Seq.index mh idx)))
  =
  Defs.chunked_read_header_step mh target;
  assert (MH.read_word_in_major mh (hd_address target) == Some hdr);
  let flushed = Defs.chunked_flush_blue mh first_blue run_words fp in
  let work' = fst flushed in
  let fp' = snd flushed in
  if run_words = 0 then begin
    Defs.chunked_flush_blue_empty mh first_blue fp;
    assert (work' == mh)
  end else begin
    nat_nonzero_pos run_words;
    let rw : pos = run_words in
    let fb : obj_addr = first_blue in
    assert (rw == run_words);
    chunked_flush_blue_prefix_preserves_base_member
      mh idx base fb rw (hd_address target) target fp;
    Pres.chunked_flush_blue_preserves_other_read
      mh first_blue run_words fp (hd_address target) hdr
  end;
  assert (MH.well_formed_major_heap work');
  assert (idx < Seq.length work');
  assert (Seq.mem target (MH.objects_in_chunk_from (Seq.index work' idx) base));
  assert (MH.chunk_start (Seq.index work' idx) ==
          MH.chunk_start (Seq.index mh idx));
  assert (MH.chunk_end (Seq.index work' idx) ==
          MH.chunk_end (Seq.index mh idx));
  Defs.chunked_read_header_step work' target;
  assert (Defs.chunked_read_header work' target == Some hdr);
  chunk_member_read_header_wosize work' idx base target hdr;
  Obj.colorHeader_preserves_wosize hdr Header.White;
  Defs.chunked_make_white_step work' target;
  Defs.chunked_set_object_color_some work' target Header.White hdr;
  Reach.major_write_member_header_same_wosize_preserves_objects_from
    work' idx base target (Obj.colorHeader hdr Header.White);
  let work'' = Defs.chunked_make_white work' target in
  assert (MH.well_formed_major_heap work'');
  assert (idx < Seq.length work'');
  assert (Seq.mem target
    (MH.objects_in_chunk_from (Seq.index work'' idx) base));
  assert (MH.object_wosize_in_chunk (Seq.index work'' idx) target ==
          MH.object_wosize_in_chunk (Seq.index work' idx) target);
  assert (MH.object_wosize_in_chunk (Seq.index work'' idx) target ==
          U64.v (Obj.getWosize hdr))
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
let chunked_flush_blue_before_preserves_objects_from
    (mh: MH.major_heap)
    (idx: nat)
    (start: hp_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        (run_words = 0 \/
         (~(U64.v first_blue < U64.v mword) /\
          ~(U64.v first_blue >= heap_size) /\
          ~(U64.v first_blue % U64.v mword <> 0) /\
          run_words - 1 < pow2 54 /\
          run_words - 1 < pow2 64 /\
          U64.v start <= MH.chunk_end (Seq.index mh idx) /\
          (let fb : obj_addr = first_blue in
           let hd = hd_address fb in
           MH.word_in_chunk (Seq.index mh idx) hd /\
           U64.v hd + run_words * U64.v mword <= U64.v start))))
      (ensures
        (let final = fst (Defs.chunked_flush_blue mh first_blue run_words fp) in
         MH.well_formed_major_heap final /\
         idx < Seq.length final /\
         MH.objects_in_chunk_from (Seq.index final idx) start ==
         MH.objects_in_chunk_from (Seq.index mh idx) start /\
         MH.chunk_start (Seq.index final idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index final idx) ==
         MH.chunk_end (Seq.index mh idx)))
  =
  if run_words = 0 then
    Defs.chunked_flush_blue_empty mh first_blue fp
  else begin
    nat_nonzero_pos run_words;
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
      assert (run_words - 1 < pow2 64);
      let fb : obj_addr = first_blue in
      let hd = hd_address fb in
      let wz : nat = run_words - 1 in
      let wz_u64 : Obj.wosize = U64.uint_to_t wz in
      let hdr = Obj.makeHeader wz_u64 Header.Blue 0UL in
      Defs.chunked_flush_blue_step mh first_blue rw fp;
      assert (rw == run_words);
      Reach.major_write_word_or_same_before_preserves_objects_from
        mh idx start hd hdr;
      let mh1 = SpecMajorAlloc.major_write_word_or_same mh hd hdr in
      assert (MH.well_formed_major_heap mh1);
      assert (idx < Seq.length mh1);
      assert (MH.objects_in_chunk_from (Seq.index mh1 idx) start ==
              MH.objects_in_chunk_from (Seq.index mh idx) start);
      assert (MH.chunk_start (Seq.index mh1 idx) ==
              MH.chunk_start (Seq.index mh idx));
      assert (MH.chunk_end (Seq.index mh1 idx) ==
              MH.chunk_end (Seq.index mh idx));
      if wz >= 1 && U64.v hd + U64.v mword * 2 <= heap_size then begin
        hd_address_spec fb;
        assert (U64.v hd + U64.v mword == U64.v fb);
        assert (run_words == wz + 1);
        assert (wz >= 1);
        assert (U64.v fb + U64.v mword <= U64.v start);
        assert (MH.word_in_chunk (Seq.index mh1 idx) fb);
        Reach.major_write_word_or_same_before_preserves_objects_from
          mh1 idx start fb fp;
        let mh2 = SpecMajorAlloc.major_write_word_or_same mh1 fb fp in
        assert (MH.well_formed_major_heap mh2);
        assert (idx < Seq.length mh2);
        assert (MH.objects_in_chunk_from (Seq.index mh2 idx) start ==
                MH.objects_in_chunk_from (Seq.index mh idx) start);
        assert (MH.chunk_start (Seq.index mh2 idx) ==
                MH.chunk_start (Seq.index mh idx));
        assert (MH.chunk_end (Seq.index mh2 idx) ==
                MH.chunk_end (Seq.index mh idx));
        let zero_start_nat = U64.v fb + U64.v mword in
        if wz >= 2 && zero_start_nat < pow2 64 then begin
          let zero_start = U64.uint_to_t zero_start_nat in
          MH.next_object_start_aligned fb 1;
          assert (U64.v zero_start == zero_start_nat);
          assert (U64.v zero_start % U64.v mword == 0);
          FStar.Math.Lemmas.distributivity_add_left
            2 (wz - 1) (U64.v mword);
          FStar.Math.Lemmas.paren_add_right
            (U64.v hd) (2 * U64.v mword) ((wz - 1) * U64.v mword);
          assert (U64.v zero_start + (wz - 1) * U64.v mword ==
                  U64.v hd + run_words * U64.v mword);
          assert (U64.v zero_start + (wz - 1) * U64.v mword <=
                  U64.v start);
          assert (U64.v zero_start + (wz - 1) * U64.v mword <=
                  MH.chunk_end (Seq.index mh2 idx));
          assert (U64.v zero_start >= MH.chunk_start (Seq.index mh2 idx));
          Reach.chunked_zero_fields_before_preserves_objects_from
            mh2 idx start zero_start (wz - 1);
          Defs.chunked_flush_blue_fst_zero_step mh fb run_words fp
        end else begin
          Defs.chunked_flush_blue_fst_link_step mh fb run_words fp
        end
      end else begin
        Defs.chunked_flush_blue_fst_header_step mh fb run_words fp
      end
    end
  end
#pop-options
