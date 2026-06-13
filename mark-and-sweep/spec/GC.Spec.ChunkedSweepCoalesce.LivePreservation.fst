module GC.Spec.ChunkedSweepCoalesce.LivePreservation

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
module Pres = GC.Spec.ChunkedSweepCoalesce.Preservation
module ChunkedGraph = GC.Spec.ChunkedMajorGC.Graph
module SpecMajorAlloc = GC.Spec.MajorAllocator

#set-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always --warn_error -321"

let chunked_fused_aux_black_head_preserves_wosize
    (source work: MH.major_heap)
    (objs: Seq.seq obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
    (target: obj_addr)
    (hdr: U64.t)
  : Lemma
      (requires
        Seq.length objs > 0 /\
        Seq.head objs == target /\
        Defs.chunked_is_black source target /\
        Defs.chunked_read_header work target == Some hdr /\
        (run_words = 0 \/
         U64.v first_blue + (run_words - 1) * U64.v mword <=
           U64.v (hd_address target)) /\
        (forall (o: obj_addr). Seq.mem o (Seq.tail objs) ==>
          U64.v (hd_address target) + U64.v mword * 2 <= U64.v o))
      (ensures
        Defs.chunked_wosize_of_object
          (fst (Defs.chunked_fused_aux
            source work objs first_blue run_words fp))
          target ==
        Obj.getWosize hdr)
  =
  let rest = Seq.tail objs in
  let target_hd = hd_address target in
  Defs.chunked_fused_aux_black_step
    source work objs first_blue run_words fp;
  Defs.chunked_read_header_step work target;
  assert (MH.read_word_in_major work target_hd == Some hdr);
  Pres.chunked_flush_blue_preserves_other_read
    work first_blue run_words fp target_hd hdr;
  let flushed = Defs.chunked_flush_blue work first_blue run_words fp in
  let work' = fst flushed in
  let fp' = snd flushed in
  Defs.chunked_read_header_step work' target;
  assert (Defs.chunked_read_header work' target == Some hdr);
  Pres.chunked_make_white_header_effect work' target hdr;
  let work'' = Defs.chunked_make_white work' target in
  let new_hdr = Obj.colorHeader hdr Header.White in
  assert (Defs.chunked_read_header work'' target == Some new_hdr);
  Defs.chunked_read_header_step work'' target;
  assert (MH.read_word_in_major work'' target_hd == Some new_hdr);
  Obj.colorHeader_preserves_wosize hdr Header.White;
  Pres.chunked_fused_aux_read_frame_ready_from_all_after
    source rest 0UL 0 target_hd;
  Pres.chunked_fused_aux_preserves_other_read
    source work'' rest 0UL 0 fp' target_hd new_hdr;
  let final_tail =
    fst (Defs.chunked_fused_aux source work'' rest 0UL 0 fp') in
  assert (MH.read_word_in_major final_tail target_hd == Some new_hdr);
  Defs.chunked_read_header_step final_tail target;
  assert (Defs.chunked_read_header final_tail target == Some new_hdr);
  Defs.chunked_wosize_of_object_some final_tail target new_hdr;
  assert (fst (Defs.chunked_fused_aux
           source work objs first_blue run_words fp) == final_tail)

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

#push-options "--z3rlimit 5 --fuel 1 --ifuel 0 --split_queries always"
let suffix_object_after_header_addr
    (c: MH.heap_chunk)
    (start next_start: hp_addr)
    (o: obj_addr)
    (wz: Obj.wosize)
  : Lemma
      (requires
        Seq.mem o (MH.objects_in_chunk_from c next_start) /\
        U64.v next_start ==
          U64.v start + (U64.v wz + 1) * U64.v mword)
      (ensures
        U64.v start + U64.v mword * 2 <= U64.v o)
  =
  MH.objects_in_chunk_from_addresses_gt_start c next_start o;
  assert (U64.v o > U64.v next_start);
  assert (U64.v o % U64.v mword == 0);
  assert (U64.v next_start % U64.v mword == 0);
  MH.word_aligned_gt_at_least_mword (U64.v o) (U64.v next_start);
  assert (U64.v o >= U64.v next_start + U64.v mword);
  assert (U64.v wz + 1 >= 1);
  assert (U64.v next_start + U64.v mword >=
          U64.v start + U64.v mword * 2)
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let object_after_start_header_at_or_after
    (start: hp_addr)
    (target: obj_addr)
  : Lemma
      (requires U64.v target > U64.v start)
      (ensures U64.v (hd_address target) >= U64.v start)
  =
  assert (U64.v target % U64.v mword == 0);
  assert (U64.v start % U64.v mword == 0);
  MH.word_aligned_gt_at_least_mword (U64.v target) (U64.v start);
  assert (U64.v target >= U64.v start + U64.v mword);
  hd_address_spec target;
  assert (U64.v (hd_address target) + U64.v mword == U64.v target)
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let rec chunked_fused_aux_live_wosize_preserved_from_chunk_from
    (source work: MH.major_heap)
    (c: MH.heap_chunk)
    (start: hp_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
    (target: obj_addr)
    (hdr: U64.t)
  : Lemma
      (requires
        Seq.mem target (MH.objects_in_chunk_from c start) /\
        (forall (o: obj_addr). Seq.mem o (MH.objects_in_chunk_from c start) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk c o) /\
        Defs.chunked_read_header work target == Some hdr /\
        Defs.chunked_is_black source target /\
        U64.v (Obj.getWosize hdr) == MH.object_wosize_in_chunk c target /\
        (run_words = 0 \/
         U64.v first_blue + (run_words - 1) * U64.v mword == U64.v start))
      (ensures
        Defs.chunked_wosize_of_object
          (fst (Defs.chunked_fused_aux
            source work (MH.objects_in_chunk_from c start)
            first_blue run_words fp))
          target ==
        Obj.getWosize hdr)
      (decreases MH.chunk_end c - U64.v start)
  =
  if U64.v start < MH.chunk_start c then
    assert False
  else if U64.v start + U64.v mword >= MH.chunk_end c then
    assert False
  else begin
    let header = MH.read_word_in_chunk c start in
    let wz = Obj.getWosize header in
    let obj_size_words = U64.v wz + 1 in
    let next_start_nat =
      U64.v start + obj_size_words * U64.v mword in
    if next_start_nat > MH.chunk_end c || next_start_nat >= pow2 64 then
      assert False
    else begin
      f_address_spec start;
      let first : obj_addr = f_address start in
      let tail =
        if next_start_nat >= MH.chunk_end c then
          Seq.empty
        else begin
          assert (next_start_nat < heap_size);
          assert (next_start_nat < pow2 64);
          MH.next_object_start_aligned start obj_size_words;
          assert (next_start_nat % U64.v mword == 0);
          let next_start_nat_u : n:nat{n < pow2 64} = next_start_nat in
          let next_start : hp_addr = U64.uint_to_t next_start_nat_u in
          MH.objects_in_chunk_from c next_start
        end
      in
      let objs = MH.objects_in_chunk_from c start in
      if next_start_nat < MH.chunk_end c then begin
        MH.next_object_start_aligned start obj_size_words;
        assert (next_start_nat % U64.v mword == 0)
      end;
      MH.objects_in_chunk_from_cons_step c start;
      assert (objs == Seq.cons first tail);
      assert (Seq.length objs > 0);
      assert (Seq.head objs == first);
      assert (Seq.tail objs == tail);
      Fields.mem_cons_lemma target first tail;
      if target = first then begin
        assert (Defs.chunked_is_black source first);
        hd_f_roundtrip start;
        assert (hd_address first == start);
        assert (MH.object_wosize_in_chunk c first == U64.v wz);
        assert (U64.v (Obj.getWosize hdr) == U64.v wz);
        assert (run_words = 0 \/
                U64.v first_blue + (run_words - 1) * U64.v mword <=
                  U64.v (hd_address target));
        let suffix_after (o: obj_addr) : Lemma
            (requires Seq.mem o tail)
            (ensures
              U64.v (hd_address target) + U64.v mword * 2 <= U64.v o)
          =
          if next_start_nat >= MH.chunk_end c then
            assert False
          else begin
            let next_start_nat_u : n:nat{n < pow2 64} = next_start_nat in
            let next_start : hp_addr = U64.uint_to_t next_start_nat_u in
            assert (tail == MH.objects_in_chunk_from c next_start);
            suffix_object_after_header_addr c start next_start o wz
          end
        in
        FStar.Classical.forall_intro
          (FStar.Classical.move_requires suffix_after);
        chunked_fused_aux_black_head_preserves_wosize
          source work objs first_blue run_words fp target hdr
      end else begin
        assert (Seq.mem target tail);
        if next_start_nat >= MH.chunk_end c then
          assert False
        else begin
          assert (next_start_nat < heap_size);
          assert (next_start_nat < pow2 64);
          MH.next_object_start_aligned start obj_size_words;
          assert (next_start_nat % U64.v mword == 0);
          let next_start_nat_u : n:nat{n < pow2 64} = next_start_nat in
          let next_start : hp_addr = U64.uint_to_t next_start_nat_u in
          assert (tail == MH.objects_in_chunk_from c next_start);
          let wosize_match_tail (o: obj_addr)
            : Lemma
                (requires Seq.mem o (MH.objects_in_chunk_from c next_start))
                (ensures
                  U64.v (Defs.chunked_wosize_of_object source o) ==
                  MH.object_wosize_in_chunk c o)
            =
            assert (MH.objects_in_chunk_from c next_start == tail);
            seq_mem_eq (MH.objects_in_chunk_from c next_start) tail o;
            assert (Seq.mem o tail);
            seq_tail_mem objs o;
            assert (Seq.mem o objs);
            assert (objs == MH.objects_in_chunk_from c start);
            seq_mem_eq objs (MH.objects_in_chunk_from c start) o
          in
          FStar.Classical.forall_intro
            (FStar.Classical.move_requires wosize_match_tail);
          MH.objects_in_chunk_from_addresses_gt_start c next_start target;
          assert (U64.v target > U64.v next_start);
          object_after_start_header_at_or_after next_start target;
          assert (U64.v (hd_address target) >= U64.v next_start);
          if Defs.chunked_is_black source first then begin
            hd_f_roundtrip start;
            assert (hd_address first == start);
            assert (U64.v (hd_address first) + U64.v mword <=
                    U64.v (hd_address target));
            Defs.chunked_fused_aux_black_step
              source work objs first_blue run_words fp;
            Defs.chunked_read_header_step work target;
            Pres.chunked_flush_blue_preserves_other_read
              work first_blue run_words fp (hd_address target) hdr;
            let flushed = Defs.chunked_flush_blue work first_blue run_words fp in
            let work' = fst flushed in
            let fp' = snd flushed in
            Defs.chunked_read_header_step work' target;
            assert (Defs.chunked_read_header work' target == Some hdr);
            Pres.chunked_make_white_preserves_other_read
              work' first (hd_address target) hdr;
            let work'' = Defs.chunked_make_white work' first in
            Defs.chunked_read_header_step work'' target;
            assert (Defs.chunked_read_header work'' target == Some hdr);
            chunked_fused_aux_live_wosize_preserved_from_chunk_from
              source work'' c next_start 0UL 0 fp' target hdr;
            assert (fst (Defs.chunked_fused_aux
                     source work objs first_blue run_words fp) ==
                    fst (Defs.chunked_fused_aux
                     source work'' tail 0UL 0 fp'))
          end else begin
            let new_first : U64.t =
              if run_words = 0 then first else first_blue in
            let new_run =
              run_words + U64.v (Defs.chunked_wosize_of_object source first) + 1 in
            hd_f_roundtrip start;
            assert (hd_address first == start);
            MH.objects_in_chunk_from_head_mem c start;
            assert (Seq.mem first (MH.objects_in_chunk_from c start));
            assert (MH.object_wosize_in_chunk c first == U64.v wz);
            assert (U64.v (Defs.chunked_wosize_of_object source first) ==
                    U64.v wz);
            assert (U64.v next_start ==
                    U64.v start + (U64.v wz + 1) * U64.v mword);
            assert (new_run ==
                    run_words + U64.v wz + 1);
            chunked_fused_aux_nonblack_run_end_at_next_start
              start first first_blue run_words wz next_start;
            assert (new_first == (if run_words = 0 then first else first_blue));
            Defs.chunked_fused_aux_nonblack_step
              source work objs first_blue run_words fp;
            chunked_fused_aux_live_wosize_preserved_from_chunk_from
              source work c next_start new_first new_run fp target hdr;
            assert (fst (Defs.chunked_fused_aux
                     source work objs first_blue run_words fp) ==
                    fst (Defs.chunked_fused_aux
                     source work tail new_first new_run fp))
          end
        end
      end
    end
  end
#pop-options

let chunked_fused_aux_live_wosize_preserved_from_chunk
    (source: MH.major_heap)
    (c: MH.heap_chunk)
    (fp: U64.t)
    (target: obj_addr)
    (hdr: U64.t)
  : Lemma
      (requires
        Seq.mem target (MH.objects_in_chunk c) /\
        (forall (o: obj_addr). Seq.mem o (MH.objects_in_chunk c) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk c o) /\
        Defs.chunked_read_header source target == Some hdr /\
        Defs.chunked_is_black source target /\
        U64.v (Obj.getWosize hdr) == MH.object_wosize_in_chunk c target)
      (ensures
        Defs.chunked_wosize_of_object
          (fst (Defs.chunked_fused_aux
            source source (MH.objects_in_chunk c) 0UL 0 fp))
          target ==
        Obj.getWosize hdr)
  =
  chunked_fused_aux_live_wosize_preserved_from_chunk_from
    source source c c.base 0UL 0 fp target hdr

let chunked_fused_aux_live_field_preserved_from_chunk
    (source: MH.major_heap)
    (idx: nat)
    (fp: U64.t)
    (target: obj_addr)
    (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        idx < Seq.length source /\
        Seq.mem target (MH.objects_in_chunk (Seq.index source idx)) /\
        (forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o) /\
        Defs.chunked_read_header source target == Some hdr /\
        Defs.chunked_is_black source target /\
        U64.v (Obj.getWosize hdr) ==
          MH.object_wosize_in_chunk (Seq.index source idx) target /\
        (let final =
          fst (Defs.chunked_fused_aux
            source source (MH.objects_in_chunk (Seq.index source idx))
            0UL 0 fp) in
         ChunkedGraph.chunked_major_vertex final target))
      (ensures
        (let final =
          fst (Defs.chunked_fused_aux
            source source (MH.objects_in_chunk (Seq.index source idx))
            0UL 0 fp) in
         ChunkedGraph.chunked_major_field_preserved
           source final target))
  =
  let c = Seq.index source idx in
  let final =
    fst (Defs.chunked_fused_aux source source (MH.objects_in_chunk c) 0UL 0 fp) in
  Pres.chunked_fused_aux_live_field_data_preserved_from_chunk
    source idx fp target hdr;
  ChunkedGraph.chunked_major_field_data_preserved_elim
    source final target;
  chunked_fused_aux_live_wosize_preserved_from_chunk
    source c fp target hdr;
  Defs.chunked_wosize_of_object_some source target hdr;
  assert (Defs.chunked_wosize_of_object source target == Obj.getWosize hdr);
  assert (Defs.chunked_wosize_of_object final target == Obj.getWosize hdr);
  ChunkedGraph.chunked_major_field_preserved_intro
    source final target

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_set_object_color_preserves_major_objects
    (mh: MH.major_heap)
    (idx: nat)
    (obj: obj_addr)
    (color: Header.color_sem)
    (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        MH.lookup_chunk_index mh (hd_address obj) == Some idx /\
        Seq.mem obj (MH.major_objects mh) /\
        Defs.chunked_read_header mh obj == Some hdr)
      (ensures
        MH.major_objects (Defs.chunked_set_object_color mh obj color) ==
        MH.major_objects mh)
  =
  Defs.chunked_read_header_step mh obj;
  assert (MH.read_word_in_major mh (hd_address obj) == Some hdr);
  MH.lookup_chunk_index_some mh (hd_address obj) idx;
  assert (MH.word_in_chunk (Seq.index mh idx) (hd_address obj));
  MH.read_word_in_major_at_lookup_index mh (hd_address obj) idx;
  assert (MH.read_word_in_chunk (Seq.index mh idx) (hd_address obj) == hdr);
  assert (MH.object_wosize_in_chunk (Seq.index mh idx) obj ==
          U64.v (Obj.getWosize hdr));
  Obj.colorHeader_preserves_wosize hdr color;
  assert (U64.v (Obj.getWosize (Obj.colorHeader hdr color)) ==
          MH.object_wosize_in_chunk (Seq.index mh idx) obj);
  Defs.chunked_set_object_color_some mh obj color hdr;
  MH.major_objects_write_member_header_same_wosize_preserves
    mh idx obj (Obj.colorHeader hdr color);
  MH.write_word_in_major_at_lookup_index
    mh (hd_address obj) (Obj.colorHeader hdr color) idx;
  SpecMajorAlloc.major_write_word_or_same_some
    mh
    (Seq.upd mh idx
      (MH.write_word_in_chunk
        (Seq.index mh idx) (hd_address obj) (Obj.colorHeader hdr color)))
    (hd_address obj)
    (Obj.colorHeader hdr color)

let chunked_make_white_preserves_major_objects
    (mh: MH.major_heap)
    (idx: nat)
    (obj: obj_addr)
    (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        MH.lookup_chunk_index mh (hd_address obj) == Some idx /\
        Seq.mem obj (MH.major_objects mh) /\
        Defs.chunked_read_header mh obj == Some hdr)
      (ensures
        MH.major_objects (Defs.chunked_make_white mh obj) ==
        MH.major_objects mh)
  =
  Defs.chunked_make_white_step mh obj;
  chunked_set_object_color_preserves_major_objects
    mh idx obj Header.White hdr

let chunked_make_blue_preserves_major_objects
    (mh: MH.major_heap)
    (idx: nat)
    (obj: obj_addr)
    (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        MH.lookup_chunk_index mh (hd_address obj) == Some idx /\
        Seq.mem obj (MH.major_objects mh) /\
        Defs.chunked_read_header mh obj == Some hdr)
      (ensures
        MH.major_objects (Defs.chunked_make_blue mh obj) ==
        MH.major_objects mh)
  =
  Defs.chunked_make_blue_step mh obj;
  chunked_set_object_color_preserves_major_objects
    mh idx obj Header.Blue hdr
#pop-options
