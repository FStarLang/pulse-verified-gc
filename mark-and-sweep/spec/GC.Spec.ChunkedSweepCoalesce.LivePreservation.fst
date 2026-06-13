module GC.Spec.ChunkedSweepCoalesce.LivePreservation

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module Obj = GC.Spec.Object
module Header = GC.Lib.Header
module Defs = GC.Spec.ChunkedSweepCoalesce.Defs
module Pres = GC.Spec.ChunkedSweepCoalesce.Preservation

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
