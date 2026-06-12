module GC.Spec.ChunkedSweepCoalesce.Compat

module U64 = FStar.UInt64
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical

open GC.Spec.Base
open GC.Spec.Heap

module Header = GC.Lib.Header
module MH = GC.Spec.MajorHeap
module Obj = GC.Spec.Object
module Fields = GC.Spec.Fields
module SpecMajorAlloc = GC.Spec.MajorAllocator
module Defs = GC.Spec.ChunkedSweepCoalesce.Defs
module SpecSweep = GC.Spec.Sweep

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

private let aligned_gt_ge_plus_mword (x z: nat)
  : Lemma
      (requires x > z /\ x % U64.v mword == 0 /\ z % U64.v mword == 0)
      (ensures x >= z + U64.v mword)
  =
  if x < z + U64.v mword then begin
    assert (x - z > 0);
    assert (x - z < U64.v mword);
    Math.lemma_mod_sub_distr x z (U64.v mword);
    assert ((x - z) % U64.v mword == 0);
    Math.small_mod (x - z) (U64.v mword);
    assert False
  end

private let single_chunk_objects_have_header_room (g: heap)
  : Lemma
      (ensures
        forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk
            (Seq.head (MH.single_chunk_major_heap g))) ==>
          U64.v o >= U64.v zero_addr + U64.v mword)
  =
  assert (Seq.head (MH.single_chunk_major_heap g) == MH.single_chunk_of_heap g);
  MH.single_chunk_objects_compat g;
  let aux (o: obj_addr)
    : Lemma
        (requires
          Seq.mem o (MH.objects_in_chunk
            (Seq.head (MH.single_chunk_major_heap g))))
        (ensures U64.v o >= U64.v zero_addr + U64.v mword)
    =
    assert (Seq.mem o (Fields.objects zero_addr g));
    Fields.objects_addresses_gt_start zero_addr g o;
    aligned_gt_ge_plus_mword (U64.v o) (U64.v zero_addr)
  in
  Classical.forall_intro (Classical.move_requires aux)

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

let rec chunked_sweep_aux_single_chunk_compat
        (g: heap)
        (objs: Seq.seq obj_addr)
        (fp: U64.t)
      : Lemma
          (requires
            (forall (o: obj_addr). Seq.mem o objs ==> U64.v o >= U64.v zero_addr + U64.v mword))
          (ensures
            Defs.chunked_sweep_aux (MH.single_chunk_major_heap g) objs fp ==
            (let (g', fp') = SpecSweep.sweep_aux g objs fp in
             (MH.single_chunk_major_heap g', fp')))
          (decreases Seq.length objs)
      =
      if Seq.length objs = 0 then begin
        assert (Seq.length objs == Seq.length (Seq.empty #obj_addr));
        assert (forall i. i < Seq.length objs ==>
          Seq.index objs i == Seq.index (Seq.empty #obj_addr) i);
        Seq.lemma_eq_intro objs (Seq.empty #obj_addr);
        Seq.lemma_eq_elim objs (Seq.empty #obj_addr);
        Defs.chunked_sweep_aux_empty (MH.single_chunk_major_heap g) fp;
        SpecSweep.sweep_aux_empty g fp
      end else begin
        assert (Seq.length objs > 0);
        let obj = Seq.head objs in
        let rest = Seq.tail objs in
        Seq.mem_cons obj rest;
        assert (Seq.mem obj objs);
        assert (U64.v obj >= U64.v zero_addr + U64.v mword);
        Defs.chunked_sweep_aux_step (MH.single_chunk_major_heap g) objs fp;
        SpecSweep.sweep_aux_step g objs fp;
        chunked_sweep_object_single_chunk_compat g obj fp;
        let (g', fp') = SpecSweep.sweep_object g obj fp in
        chunked_sweep_aux_single_chunk_compat g' rest fp'
      end

let chunked_sweep_single_chunk_compat
    (g: heap)
    (fp: U64.t)
  : Lemma
      (Defs.chunked_sweep (MH.single_chunk_major_heap g) fp ==
       (let (g', fp') = SpecSweep.sweep g fp in
        (MH.single_chunk_major_heap g', fp')))
  =
  Defs.chunked_sweep_step (MH.single_chunk_major_heap g) fp;
  assert (Seq.length (MH.single_chunk_major_heap g) > 0);
  Defs.chunked_sweep_chunks_step
    (MH.single_chunk_major_heap g) (MH.single_chunk_major_heap g) fp;
  assert (Seq.head (MH.single_chunk_major_heap g) == MH.single_chunk_of_heap g);
  MH.single_chunk_objects_compat g;
  assert (MH.objects_in_chunk (Seq.head (MH.single_chunk_major_heap g)) ==
          Fields.objects zero_addr g);
  single_chunk_objects_have_header_room g;
  chunked_sweep_aux_single_chunk_compat
    g (MH.objects_in_chunk (Seq.head (MH.single_chunk_major_heap g))) fp;
  let (g', fp') = SpecSweep.sweep g fp in
  assert (Seq.length (Seq.tail (MH.single_chunk_major_heap g)) == 0);
  Seq.lemma_empty (Seq.tail (MH.single_chunk_major_heap g));
  Defs.chunked_sweep_chunks_empty (MH.single_chunk_major_heap g') fp'
