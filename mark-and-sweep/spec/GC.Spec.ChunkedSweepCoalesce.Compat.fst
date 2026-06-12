module GC.Spec.ChunkedSweepCoalesce.Compat

module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap

module Header = GC.Lib.Header
module MH = GC.Spec.MajorHeap
module Obj = GC.Spec.Object
module SpecMajorAlloc = GC.Spec.MajorAllocator
module Defs = GC.Spec.ChunkedSweepCoalesce.Defs
module SpecSweep = GC.Spec.Sweep

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let chunked_make_white_single_chunk_compat
    (g: heap)
    (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (Defs.chunked_make_white (MH.single_chunk_major_heap g) obj ==
       MH.single_chunk_major_heap (Obj.makeWhite obj g))
  =
  Defs.chunked_read_header_single_chunk_compat g obj;
  hd_address_spec obj;
  assert (U64.v (hd_address obj) >= U64.v zero_addr);
  assert (U64.v (hd_address obj) + U64.v mword == U64.v obj);
  assert (U64.v (hd_address obj) + U64.v mword <= heap_size);
  Defs.chunked_make_white_step (MH.single_chunk_major_heap g) obj;
  Defs.chunked_set_object_color_some
    (MH.single_chunk_major_heap g) obj Header.White
    (read_word g (hd_address obj));
  Obj.makeWhite_spec obj g;
  SpecMajorAlloc.major_write_word_or_same_single_chunk_compat
    g (hd_address obj)
    (Obj.colorHeader (read_word g (hd_address obj)) Header.White)

let chunked_make_blue_single_chunk_compat
    (g: heap)
    (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (Defs.chunked_make_blue (MH.single_chunk_major_heap g) obj ==
       MH.single_chunk_major_heap (Obj.makeBlue obj g))
  =
  Defs.chunked_read_header_single_chunk_compat g obj;
  hd_address_spec obj;
  assert (U64.v (hd_address obj) >= U64.v zero_addr);
  assert (U64.v (hd_address obj) + U64.v mword == U64.v obj);
  assert (U64.v (hd_address obj) + U64.v mword <= heap_size);
  Defs.chunked_make_blue_step (MH.single_chunk_major_heap g) obj;
  Defs.chunked_set_object_color_some
    (MH.single_chunk_major_heap g) obj Header.Blue
    (read_word g (hd_address obj));
  Obj.makeBlue_spec obj g;
  SpecMajorAlloc.major_write_word_or_same_single_chunk_compat
    g (hd_address obj)
    (Obj.colorHeader (read_word g (hd_address obj)) Header.Blue)

let chunked_sweep_object_single_chunk_compat
    (g: heap)
    (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
    (fp: U64.t)
  : Lemma
      (Defs.chunked_sweep_object (MH.single_chunk_major_heap g) obj fp ==
       (let (g', fp') = SpecSweep.sweep_object g obj fp in
        (MH.single_chunk_major_heap g', fp')))
  =
  Defs.chunked_is_infix_single_chunk_compat g obj;
  if Obj.is_infix obj g then
    Defs.chunked_sweep_object_infix_step
      (MH.single_chunk_major_heap g) obj fp
  else begin
    Defs.chunked_is_white_single_chunk_compat g obj;
    if Obj.is_white obj g then begin
      Defs.chunked_sweep_object_white_step
        (MH.single_chunk_major_heap g) obj fp;
      Defs.chunked_wosize_of_object_single_chunk_compat g obj;
      let ws = Obj.wosize_of_object obj g in
      let hd = hd_address obj in
      if U64.v ws > 0 && U64.v hd + U64.v mword * 2 <= heap_size then begin
        hd_address_spec obj;
        assert (U64.v obj >= U64.v zero_addr);
        assert (U64.v obj + U64.v mword <= heap_size);
        let g' = write_word g obj fp in
        SpecMajorAlloc.major_write_word_or_same_single_chunk_compat g obj fp;
        chunked_make_blue_single_chunk_compat g' obj
      end else
        chunked_make_blue_single_chunk_compat g obj
    end else begin
      Defs.chunked_is_black_single_chunk_compat g obj;
      if Obj.is_black obj g then begin
        Defs.chunked_sweep_object_black_step
          (MH.single_chunk_major_heap g) obj fp;
        chunked_make_white_single_chunk_compat g obj
      end
      else
        Defs.chunked_sweep_object_other_step
          (MH.single_chunk_major_heap g) obj fp
    end
  end
