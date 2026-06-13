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
module Pending = GC.Spec.ChunkedSweepCoalesce.PendingRun
module Reach = GC.Spec.ChunkedSweepCoalesce.VertexReach
module ReachPrefix = GC.Spec.ChunkedSweepCoalesce.VertexReachPrefix
module VertexSteps = GC.Spec.ChunkedSweepCoalesce.VertexSteps
module VertexOrder = GC.Spec.ChunkedSweepCoalesce.VertexOrder
module ChunkedGraph = GC.Spec.ChunkedMajorGC.Graph
module SpecMajorAlloc = GC.Spec.MajorAllocator

#set-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always --warn_error -321"

let nat_nonzero_pos (n: nat)
  : Lemma (requires n <> 0) (ensures n > 0)
  = ()

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

let seq_tail_mem_for_head_vertex (#a:eqtype) (s: Seq.seq a) (x: a)
  : Lemma
      (requires Seq.length s > 0 /\ Seq.mem x (Seq.tail s))
      (ensures Seq.mem x s)
  =
  let hd = Seq.head s in
  let tl = Seq.tail s in
  assert (s == Seq.cons hd tl);
  SeqProps.lemma_mem_append (Seq.create 1 hd) tl

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let chunked_fused_aux_black_head_preserves_vertex_from_chunk
    (source work: MH.major_heap)
    (idx: nat)
    (c: MH.heap_chunk)
    (start: hp_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
    (target: obj_addr)
    (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap work /\
        idx < Seq.length work /\
        MH.chunk_start (Seq.index work idx) == MH.chunk_start c /\
        MH.chunk_end (Seq.index work idx) == MH.chunk_end c /\
        Seq.mem target (MH.objects_in_chunk_from c start) /\
        Seq.length (MH.objects_in_chunk_from c start) > 0 /\
        Seq.head (MH.objects_in_chunk_from c start) == target /\
        hd_address target == start /\
        Seq.mem target
          (MH.objects_in_chunk_from (Seq.index work idx) c.base) /\
        Defs.chunked_read_header work target == Some hdr /\
        Defs.chunked_is_black source target /\
        U64.v (Obj.getWosize hdr) == MH.object_wosize_in_chunk c target /\
        (forall (o: obj_addr). Seq.mem o (MH.objects_in_chunk_from c start) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk c o) /\
        (run_words = 0 \/
         (~(U64.v first_blue < U64.v mword) /\
          ~(U64.v first_blue >= heap_size) /\
          ~(U64.v first_blue % U64.v mword <> 0) /\
          run_words - 1 < pow2 54 /\
          run_words - 1 < pow2 64 /\
          U64.v first_blue + (run_words - 1) * U64.v mword ==
            U64.v start /\
          (let fb : obj_addr = first_blue in
           Seq.mem fb
             (MH.objects_in_chunk_from (Seq.index work idx) c.base) /\
           U64.v fb < MH.chunk_end (Seq.index work idx) /\
           U64.v start <= MH.chunk_end (Seq.index work idx) /\
           MH.word_in_chunk (Seq.index work idx) (hd_address fb) /\
           Seq.mem target
             (MH.objects_in_chunk_from (Seq.index work idx) start)))))
      (ensures
        (let final =
          fst (Defs.chunked_fused_aux
            source work (MH.objects_in_chunk_from c start)
            first_blue run_words fp) in
         MH.well_formed_major_heap final /\
         idx < Seq.length final /\
         Seq.mem target
           (MH.objects_in_chunk_from (Seq.index final idx) c.base) /\
         ChunkedGraph.chunked_major_vertex final target /\
         MH.chunk_start (Seq.index final idx) ==
         MH.chunk_start (Seq.index work idx) /\
         MH.chunk_end (Seq.index final idx) ==
         MH.chunk_end (Seq.index work idx)))
  =
  let objs = MH.objects_in_chunk_from c start in
  let header = MH.read_word_in_chunk c start in
  let wz = Obj.getWosize header in
  let obj_size_words = U64.v wz + 1 in
  let next_start_nat =
    U64.v start + obj_size_words * U64.v mword in
  assert (Seq.head objs == target);
  assert (Defs.chunked_is_black source (Seq.head objs));
  Defs.chunked_fused_aux_black_step
    source work objs first_blue run_words fp;
  let flushed = Defs.chunked_flush_blue work first_blue run_words fp in
  let work' = fst flushed in
  let fp' = snd flushed in
  let work'' = Defs.chunked_make_white work' target in
  ReachPrefix.chunked_flush_blue_then_make_white_head_preserves_base_member
    work idx c.base target first_blue run_words fp hdr;
  assert (MH.well_formed_major_heap work'');
  assert (idx < Seq.length work'');
  assert (Seq.mem target
    (MH.objects_in_chunk_from (Seq.index work'' idx) c.base));
  assert (MH.object_wosize_in_chunk (Seq.index work'' idx) target ==
          U64.v (Obj.getWosize hdr));
  assert (MH.object_wosize_in_chunk (Seq.index work'' idx) target ==
          MH.object_wosize_in_chunk c target);
  assert (MH.chunk_start (Seq.index work'' idx) ==
          MH.chunk_start c);
  assert (MH.chunk_end (Seq.index work'' idx) ==
          MH.chunk_end c);
  if next_start_nat > MH.chunk_end c || next_start_nat >= pow2 64 then
    assert False
  else begin
    let tail =
      if next_start_nat >= MH.chunk_end c then Seq.empty
      else begin
        assert (next_start_nat < heap_size);
        assert (next_start_nat < pow2 64);
        MH.next_object_start_aligned start obj_size_words;
        assert (next_start_nat % U64.v mword == 0);
        let next_start : hp_addr = U64.uint_to_t next_start_nat in
        MH.objects_in_chunk_from c next_start
      end
    in
    MH.objects_in_chunk_from_cons_step c start;
    assert (Seq.tail objs == tail);
    assert (U64.v (Obj.getWosize hdr) == MH.object_wosize_in_chunk c target);
    assert (U64.v start + (MH.object_wosize_in_chunk c target + 1) *
              U64.v mword == next_start_nat);
    assert (U64.v (hd_address target) +
              (1 + MH.object_wosize_in_chunk (Seq.index work'' idx) target) *
                U64.v mword == next_start_nat);
    if next_start_nat >= MH.chunk_end c then begin
      assert (tail == Seq.empty);
      Defs.chunked_fused_aux_empty_length
        source work'' tail 0UL 0 fp';
      Defs.chunked_flush_blue_empty work'' 0UL fp';
      let final =
        fst (Defs.chunked_fused_aux
          source work objs first_blue run_words fp) in
      assert (final == work'');
      MH.major_objects_member_at_index final idx target;
      ChunkedGraph.chunked_major_vertex_intro final target
    end else begin
      let next_start : hp_addr = U64.uint_to_t next_start_nat in
      assert (tail == MH.objects_in_chunk_from c next_start);
      let wosize_match_tail (o: obj_addr)
        : Lemma
            (requires Seq.mem o (MH.objects_in_chunk_from c next_start))
            (ensures
              U64.v (Defs.chunked_wosize_of_object source o) ==
              MH.object_wosize_in_chunk c o)
        =
        assert (Seq.mem o tail);
        seq_tail_mem_for_head_vertex objs o;
        assert (Seq.mem o objs)
      in
      FStar.Classical.forall_intro
        (FStar.Classical.move_requires wosize_match_tail);
      assert (VertexOrder.after_member_chunk_order_pre
        source work'' idx c next_start c.base target 0UL 0);
      VertexOrder.chunked_fused_aux_after_member_ready_from_chunk_order
        source work'' idx c next_start c.base target 0UL 0 fp';
      VertexSteps.chunked_fused_aux_after_member_preserves_objects_from_ready
        source work'' idx c.base target tail 0UL 0 fp';
      let tail_final =
        fst (Defs.chunked_fused_aux source work'' tail 0UL 0 fp') in
      assert (Seq.mem target
        (MH.objects_in_chunk_from (Seq.index tail_final idx) c.base));
      assert (MH.well_formed_major_heap tail_final);
      assert (idx < Seq.length tail_final);
      let final =
        fst (Defs.chunked_fused_aux
          source work objs first_blue run_words fp) in
      assert (final == tail_final);
      MH.major_objects_member_at_index final idx target;
      ChunkedGraph.chunked_major_vertex_intro final target
    end
  end
#pop-options

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
let objects_in_chunk_tail_member_in_base
    (c: MH.heap_chunk)
    (base: hp_addr)
    (start: hp_addr{U64.v start + U64.v mword < heap_size})
    (next_start: hp_addr{U64.v next_start + U64.v mword < heap_size})
    (first x: obj_addr)
  : Lemma
      (requires
        U64.v base <= U64.v start /\
        first == f_address start /\
        Seq.mem first (MH.objects_in_chunk_from c base) /\
        Seq.mem x (MH.objects_in_chunk_from c next_start) /\
        U64.v start >= MH.chunk_start c /\
        U64.v start + U64.v mword < MH.chunk_end c /\
        (let header = MH.read_word_in_chunk c start in
         let wz = Obj.getWosize header in
         let obj_size_words = U64.v wz + 1 in
         let next_start_nat =
           U64.v start + obj_size_words * U64.v mword in
         U64.v next_start == next_start_nat /\
         next_start_nat < MH.chunk_end c /\
         next_start_nat < pow2 64))
      (ensures Seq.mem x (MH.objects_in_chunk_from c base))
  =
  let header = MH.read_word_in_chunk c start in
  let wz = Obj.getWosize header in
  let obj_size_words = U64.v wz + 1 in
  let next_start_nat =
    U64.v start + obj_size_words * U64.v mword in
  MH.objects_in_chunk_from_tail_mem c start next_start x;
  assert (Seq.mem x (MH.objects_in_chunk_from c start));
  MH.objects_in_chunk_from_later_in_earlier c base start x
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_make_white_member_preserves_objects_from
    (mh: MH.major_heap)
    (idx: nat)
    (start: hp_addr)
    (obj: obj_addr)
    (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem obj (MH.objects_in_chunk_from (Seq.index mh idx) start) /\
        Defs.chunked_read_header mh obj == Some hdr)
      (ensures
        (let mh' = Defs.chunked_make_white mh obj in
         MH.well_formed_major_heap mh' /\
         idx < Seq.length mh' /\
         MH.objects_in_chunk_from (Seq.index mh' idx) start ==
         MH.objects_in_chunk_from (Seq.index mh idx) start /\
         MH.object_wosize_in_chunk (Seq.index mh' idx) obj ==
         MH.object_wosize_in_chunk (Seq.index mh idx) obj /\
         MH.chunk_start (Seq.index mh' idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index mh' idx) ==
         MH.chunk_end (Seq.index mh idx)))
  =
  Defs.chunked_make_white_step mh obj;
  Defs.chunked_set_object_color_some mh obj Header.White hdr;
  Defs.chunked_read_header_step mh obj;
  assert (MH.read_word_in_major mh (hd_address obj) == Some hdr);
  MH.objects_in_chunk_from_member_header_fits
    (Seq.index mh idx) start obj;
  assert (MH.word_in_chunk (Seq.index mh idx) (hd_address obj));
  MH.lookup_chunk_index_word_in_chunk mh (hd_address obj) idx;
  MH.read_word_in_major_at_lookup_index mh (hd_address obj) idx;
  assert (MH.read_word_in_chunk (Seq.index mh idx) (hd_address obj) == hdr);
  assert (MH.object_wosize_in_chunk (Seq.index mh idx) obj ==
          U64.v (Obj.getWosize hdr));
  Obj.colorHeader_preserves_wosize hdr Header.White;
  assert (U64.v (Obj.getWosize (Obj.colorHeader hdr Header.White)) ==
          MH.object_wosize_in_chunk (Seq.index mh idx) obj);
  Reach.major_write_member_header_same_wosize_preserves_objects_from
    mh idx start obj (Obj.colorHeader hdr Header.White)

let chunked_make_white_member_preserves_objects_from_at_index
    (mh: MH.major_heap)
    (idx: nat)
    (start: hp_addr)
    (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem obj (MH.objects_in_chunk_from (Seq.index mh idx) start) /\
        MH.word_in_chunk (Seq.index mh idx) (hd_address obj))
      (ensures
        (let mh' = Defs.chunked_make_white mh obj in
         MH.well_formed_major_heap mh' /\
         idx < Seq.length mh' /\
         MH.objects_in_chunk_from (Seq.index mh' idx) start ==
         MH.objects_in_chunk_from (Seq.index mh idx) start /\
         MH.object_wosize_in_chunk (Seq.index mh' idx) obj ==
         MH.object_wosize_in_chunk (Seq.index mh idx) obj /\
         MH.chunk_start (Seq.index mh' idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index mh' idx) ==
         MH.chunk_end (Seq.index mh idx)))
  =
  let hdr = MH.read_word_in_chunk (Seq.index mh idx) (hd_address obj) in
  MH.lookup_chunk_index_word_in_chunk mh (hd_address obj) idx;
  MH.read_word_in_major_at_lookup_index mh (hd_address obj) idx;
  Defs.chunked_read_header_step mh obj;
  assert (Defs.chunked_read_header mh obj == Some hdr);
  chunked_make_white_member_preserves_objects_from mh idx start obj hdr
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
let chunked_fused_aux_black_prefix_prepare_tail
    (mh: MH.major_heap)
    (idx: nat)
    (base suffix_start: hp_addr)
    (first: obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
    (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem first (MH.objects_in_chunk_from (Seq.index mh idx) base) /\
        Seq.mem target
          (MH.objects_in_chunk_from (Seq.index mh idx) (hd_address first)) /\
        Seq.mem first
          (MH.objects_in_chunk_from (Seq.index mh idx) (hd_address first)) /\
        Seq.mem target
          (MH.objects_in_chunk_from (Seq.index mh idx) suffix_start) /\
        Seq.mem target (MH.objects_in_chunk_from (Seq.index mh idx) base) /\
        target <> first /\
        MH.word_in_chunk (Seq.index mh idx) (hd_address first) /\
        U64.v (hd_address first) + U64.v mword <= U64.v suffix_start /\
        (run_words = 0 \/
         (~(U64.v first_blue < U64.v mword) /\
          ~(U64.v first_blue >= heap_size) /\
          ~(U64.v first_blue % U64.v mword <> 0) /\
          run_words - 1 < pow2 54 /\
          run_words - 1 < pow2 64 /\
          U64.v first_blue + (run_words - 1) * U64.v mword ==
            U64.v (hd_address first) /\
          (let fb : obj_addr = first_blue in
           let hd = hd_address fb in
           Seq.mem fb (MH.objects_in_chunk_from (Seq.index mh idx) base) /\
           U64.v fb < MH.chunk_end (Seq.index mh idx) /\
           U64.v suffix_start <= MH.chunk_end (Seq.index mh idx) /\
           MH.word_in_chunk (Seq.index mh idx) hd /\
           U64.v hd + run_words * U64.v mword <= U64.v suffix_start))))
      (ensures
        (let flushed = Defs.chunked_flush_blue mh first_blue run_words fp in
         let mh1 = fst flushed in
         let mh2 = Defs.chunked_make_white mh1 first in
         MH.well_formed_major_heap mh2 /\
         idx < Seq.length mh2 /\
         Seq.mem first (MH.objects_in_chunk_from (Seq.index mh2 idx) base) /\
         Seq.mem target (MH.objects_in_chunk_from (Seq.index mh2 idx) base) /\
         Seq.mem target
          (MH.objects_in_chunk_from (Seq.index mh2 idx) suffix_start) /\
         MH.objects_in_chunk_from (Seq.index mh2 idx) (hd_address first) ==
         MH.objects_in_chunk_from (Seq.index mh idx) (hd_address first) /\
         MH.objects_in_chunk_from (Seq.index mh2 idx) suffix_start ==
         MH.objects_in_chunk_from (Seq.index mh idx) suffix_start /\
         MH.chunk_start (Seq.index mh2 idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index mh2 idx) ==
         MH.chunk_end (Seq.index mh idx)))
  =
  let flushed = Defs.chunked_flush_blue mh first_blue run_words fp in
  let mh1 = fst flushed in
  let fp1 = snd flushed in
  if run_words = 0 then begin
    assert (run_words == 0);
    Defs.chunked_flush_blue_empty mh first_blue fp;
    assert (flushed == (mh, fp));
    assert (mh1 == mh)
  end else begin
    nat_nonzero_pos run_words;
    let rw : pos = run_words in
    let fb : obj_addr = first_blue in
    ReachPrefix.chunked_flush_blue_prefix_preserves_base_member
      mh idx base fb rw (hd_address first) first fp;
    ReachPrefix.chunked_flush_blue_prefix_preserves_base_member
      mh idx base fb rw (hd_address first) target fp;
    hd_address_spec fb;
    assert (U64.v (hd_address fb) + U64.v mword == U64.v fb);
    assert (run_words == (run_words - 1) + 1);
    FStar.Math.Lemmas.distributivity_add_left
      (run_words - 1) 1 (U64.v mword);
    FStar.Math.Lemmas.paren_add_right
      (U64.v (hd_address fb)) (U64.v mword)
      ((run_words - 1) * U64.v mword);
    assert (U64.v (hd_address fb) + run_words * U64.v mword ==
            U64.v fb + (run_words - 1) * U64.v mword);
    assert (U64.v (hd_address fb) + run_words * U64.v mword <=
            U64.v (hd_address first));
    ReachPrefix.chunked_flush_blue_before_preserves_objects_from
      mh idx (hd_address first) first_blue run_words fp;
    assert (U64.v (hd_address fb) + run_words * U64.v mword <=
            U64.v suffix_start);
    ReachPrefix.chunked_flush_blue_before_preserves_objects_from
      mh idx suffix_start first_blue run_words fp;
    ()
  end;
  assert (MH.word_in_chunk (Seq.index mh1 idx) (hd_address first));
  chunked_make_white_member_preserves_objects_from_at_index
    mh1 idx base first;
  chunked_make_white_member_preserves_objects_from_at_index
    mh1 idx (hd_address first) first;
  Reach.chunked_make_white_before_preserves_objects_from_at_index
    mh1 idx suffix_start first;
  let mh2 = Defs.chunked_make_white mh1 first in
  ()
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
let chunked_fused_aux_black_prefix_prepare_tail_from_pending
    (work: MH.major_heap)
    (idx: nat)
    (base start next_start: hp_addr)
    (first: obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
    (target: obj_addr)
    (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap work /\
        idx < Seq.length work /\
        Pending.pending_run_before_start
          work idx base start first_blue run_words /\
        Seq.mem first (MH.objects_in_chunk_from (Seq.index work idx) base) /\
        Seq.mem target (MH.objects_in_chunk_from (Seq.index work idx) base) /\
        Seq.mem target (MH.objects_in_chunk_from (Seq.index work idx) start) /\
        Seq.mem first (MH.objects_in_chunk_from (Seq.index work idx) start) /\
        Seq.mem target (MH.objects_in_chunk_from (Seq.index work idx) next_start) /\
        target <> first /\
        hd_address first == start /\
        MH.word_in_chunk (Seq.index work idx) start /\
        U64.v start + U64.v mword <= U64.v next_start /\
        U64.v next_start <= MH.chunk_end (Seq.index work idx) /\
        Defs.chunked_read_header work target == Some hdr)
      (ensures
        (let flushed = Defs.chunked_flush_blue work first_blue run_words fp in
         let work' = fst flushed in
         let work'' = Defs.chunked_make_white work' first in
         MH.well_formed_major_heap work'' /\
         idx < Seq.length work'' /\
         Pending.pending_run_before_start work'' idx base next_start 0UL 0 /\
         Seq.mem first (MH.objects_in_chunk_from (Seq.index work'' idx) base) /\
         Seq.mem target (MH.objects_in_chunk_from (Seq.index work'' idx) base) /\
         Seq.mem target
          (MH.objects_in_chunk_from (Seq.index work'' idx) next_start) /\
         Defs.chunked_read_header work'' target == Some hdr /\
         MH.objects_in_chunk_from (Seq.index work'' idx) start ==
         MH.objects_in_chunk_from (Seq.index work idx) start /\
         MH.objects_in_chunk_from (Seq.index work'' idx) next_start ==
         MH.objects_in_chunk_from (Seq.index work idx) next_start /\
         MH.chunk_start (Seq.index work'' idx) ==
         MH.chunk_start (Seq.index work idx) /\
         MH.chunk_end (Seq.index work'' idx) ==
         MH.chunk_end (Seq.index work idx)))
  =
  if run_words = 0 then
    ()
  else begin
    nat_nonzero_pos run_words;
    let rw : pos = run_words in
    Pending.pending_run_before_start_nonempty_elim
      work idx base start first_blue rw;
    let fb : obj_addr = first_blue in
    hd_address_spec fb;
    assert (U64.v (hd_address fb) + U64.v mword == U64.v first_blue);
    assert (run_words == (run_words - 1) + 1);
    FStar.Math.Lemmas.distributivity_add_left
      (run_words - 1) 1 (U64.v mword);
    FStar.Math.Lemmas.paren_add_right
      (U64.v (hd_address fb)) (U64.v mword)
      ((run_words - 1) * U64.v mword);
    assert (U64.v (hd_address fb) + run_words * U64.v mword ==
            U64.v first_blue + (run_words - 1) * U64.v mword);
    assert (U64.v (hd_address fb) + run_words * U64.v mword <=
            U64.v next_start)
  end;
  MH.objects_in_chunk_from_addresses_gt_start
    (Seq.index work idx) next_start target;
  object_after_start_header_at_or_after next_start target;
  assert (U64.v (hd_address target) >= U64.v next_start);
  let pending_for_black =
    if run_words = 0 then
      ()
    else begin
      nat_nonzero_pos run_words;
      let rw : pos = run_words in
      Pending.pending_run_before_start_nonempty_elim
        work idx base start first_blue rw
    end
  in
  chunked_fused_aux_black_prefix_prepare_tail
    work idx base next_start first first_blue run_words fp target;
  let flushed = Defs.chunked_flush_blue work first_blue run_words fp in
  let work' = fst flushed in
  let fp' = snd flushed in
  let work'' = Defs.chunked_make_white work' first in
  Defs.chunked_read_header_step work target;
  Pres.chunked_flush_blue_preserves_other_read
    work first_blue run_words fp (hd_address target) hdr;
  Defs.chunked_read_header_step work' target;
  assert (Defs.chunked_read_header work' target == Some hdr);
  assert (U64.v start + U64.v mword <= U64.v (hd_address target));
  Pres.chunked_make_white_preserves_other_read
    work' first (hd_address target) hdr;
  Defs.chunked_read_header_step work'' target;
  assert (Defs.chunked_read_header work'' target == Some hdr);
  Pending.pending_run_before_start_empty work'' idx base next_start
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
let chunked_fused_aux_nonblack_prefix_prepare_tail
    (work: MH.major_heap)
    (idx: nat)
    (base start next_start: hp_addr)
    (first: obj_addr)
    (wz: Obj.wosize)
    (first_blue: U64.t)
    (run_words: nat)
    (target: obj_addr)
  : Lemma
      (requires
        idx < Seq.length work /\
        Pending.pending_run_before_start
          work idx base start first_blue run_words /\
        Seq.mem first (MH.objects_in_chunk_from (Seq.index work idx) base) /\
        Seq.mem target (MH.objects_in_chunk_from (Seq.index work idx) base) /\
        Seq.mem target (MH.objects_in_chunk_from (Seq.index work idx) start) /\
        target <> first /\
        hd_address first == start /\
        U64.v first == U64.v start + U64.v mword /\
        U64.v first < MH.chunk_end (Seq.index work idx) /\
        MH.word_in_chunk (Seq.index work idx) start /\
        MH.object_wosize_in_chunk (Seq.index work idx) first == U64.v wz /\
        U64.v start + (U64.v wz + 1) * U64.v mword ==
          U64.v next_start /\
        U64.v next_start < MH.chunk_end (Seq.index work idx))
      (ensures
        (let new_first : U64.t = if run_words = 0 then first else first_blue in
         let new_run = run_words + U64.v wz + 1 in
         Pending.pending_run_before_start
          work idx base next_start new_first new_run /\
         Seq.mem target (MH.objects_in_chunk_from (Seq.index work idx) base) /\
         Seq.mem target
           (MH.objects_in_chunk_from (Seq.index work idx) next_start)))
  =
  let c = Seq.index work idx in
  let objs = MH.objects_in_chunk_from c start in
  f_hd_roundtrip first;
  assert (f_address start == first);
  MH.objects_in_chunk_from_cons_step c start;
  assert (Seq.head objs == first);
  assert (Seq.tail objs == MH.objects_in_chunk_from c next_start);
  Fields.mem_cons_lemma target first (Seq.tail objs);
  assert (Seq.mem target (Seq.tail objs));
  assert (Seq.mem target (MH.objects_in_chunk_from c next_start));
  if run_words = 0 then begin
    Pending.nonblack_tail_pending_run_before_start_from_empty
      work idx base start next_start first wz
  end else begin
    nat_nonzero_pos run_words;
    let rw : pos = run_words in
    Pending.nonblack_tail_pending_run_before_start_from_nonempty
      work idx base start next_start first wz first_blue rw
  end
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
  MH.objects_in_chunk_from_member_header_fits c start target;
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
            Pending.chunked_fused_aux_nonblack_run_end_at_next_start
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
