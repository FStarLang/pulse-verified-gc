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
module SpecAlloc = GC.Spec.Allocator
module SpecMajorAlloc = GC.Spec.MajorAllocator
module SpecCoalesce = GC.Spec.Coalesce
module Defs = GC.Spec.ChunkedSweepCoalesce.Defs
module SpecSweep = GC.Spec.Sweep
module DenseFused = GC.Spec.SweepCoalesce.Defs

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

let rec chunked_zero_fields_single_chunk_compat
    (g: heap)
    (addr: U64.t)
    (n: nat)
  : Lemma
      (requires n = 0 \/ U64.v addr >= U64.v zero_addr)
      (ensures
        Defs.chunked_zero_fields (MH.single_chunk_major_heap g) addr n ==
        MH.single_chunk_major_heap (SpecAlloc.zero_fields g addr n))
      (decreases n)
  =
  assert (U64.v mword == 8);
  if n = 0 then
    Defs.chunked_zero_fields_zero (MH.single_chunk_major_heap g) addr
  else if U64.v addr + U64.v mword > heap_size then
    Defs.chunked_zero_fields_no_room
      (MH.single_chunk_major_heap g) addr n
  else if U64.v addr >= heap_size then
    Defs.chunked_zero_fields_out_of_heap
      (MH.single_chunk_major_heap g) addr n
  else if U64.v addr % U64.v mword <> 0 then
    Defs.chunked_zero_fields_unaligned
      (MH.single_chunk_major_heap g) addr n
  else begin
    assert (n > 0);
    assert (U64.v addr >= U64.v zero_addr);
    assert (U64.v addr + U64.v mword <= heap_size);
    Defs.chunked_zero_fields_step
      (MH.single_chunk_major_heap g) addr n;
    SpecMajorAlloc.major_write_word_or_same_single_chunk_compat
      g (addr <: hp_addr) 0UL;
    if U64.v addr + U64.v mword >= pow2 64 then ()
    else begin
      let next = U64.uint_to_t (U64.v addr + U64.v mword) in
      assert (U64.v next >= U64.v zero_addr);
      chunked_zero_fields_single_chunk_compat
        (write_word g (addr <: hp_addr) 0UL) next (n - 1)
    end
  end

private let chunked_zero_fields_tail_single_chunk_compat
    (g: heap)
    (addr: U64.t)
    (n: nat)
  : Lemma
      (requires n = 0 \/ U64.v addr >= U64.v zero_addr)
      (ensures
        Defs.chunked_zero_fields (MH.single_chunk_major_heap g) addr n ==
        MH.single_chunk_major_heap (SpecAlloc.zero_fields g addr n))
  =
  chunked_zero_fields_single_chunk_compat g addr n

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let chunked_flush_blue_single_chunk_compat
    (g: heap)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
  : Lemma
      (requires
        run_words = 0 \/
        U64.v first_blue >= U64.v zero_addr + U64.v mword)
      (ensures
        Defs.chunked_flush_blue
          (MH.single_chunk_major_heap g) first_blue run_words fp ==
        (let (g', fp') =
          SpecCoalesce.flush_blue g first_blue run_words fp in
         (MH.single_chunk_major_heap g', fp')))
  =
  assert (U64.v mword == 8);
  if run_words = 0 then
    Defs.chunked_flush_blue_empty (MH.single_chunk_major_heap g) first_blue fp
  else begin
  assert (run_words > 0);
  if U64.v first_blue < U64.v mword ||
          U64.v first_blue >= heap_size ||
          U64.v first_blue % U64.v mword <> 0
  then
    Defs.chunked_flush_blue_invalid
      (MH.single_chunk_major_heap g) first_blue run_words fp
  else begin
    let fb : obj_addr = first_blue in
    let hd = hd_address fb in
    let wz : nat = run_words - 1 in
    if wz >= pow2 54 then
      Defs.chunked_flush_blue_too_large
        (MH.single_chunk_major_heap g) first_blue run_words fp
    else begin
      FStar.Math.Lemmas.pow2_lt_compat 64 54;
      assert (wz < pow2 64);
      let wz_u64 : Obj.wosize = U64.uint_to_t wz in
      let hdr = Obj.makeHeader wz_u64 Header.Blue 0UL in
      Defs.chunked_flush_blue_step
        (MH.single_chunk_major_heap g) first_blue run_words fp;
      hd_address_spec fb;
      assert (U64.v hd >= U64.v zero_addr);
      assert (U64.v hd + U64.v mword == U64.v fb);
      assert (U64.v hd + U64.v mword <= heap_size);
      SpecMajorAlloc.major_write_word_or_same_single_chunk_compat g hd hdr;
      let g1 = write_word g hd hdr in
      if wz >= 1 && U64.v hd + U64.v mword * 2 <= heap_size then begin
        assert (U64.v fb >= U64.v zero_addr);
        assert (U64.v fb + U64.v mword <= heap_size);
        SpecMajorAlloc.major_write_word_or_same_single_chunk_compat g1 fb fp;
        let g2 = write_word g1 fb fp in
        let zero_start_nat = U64.v fb + U64.v mword in
        if wz >= 2 && zero_start_nat < pow2 64 then begin
          assert (wz > 0);
          let rem : nat = wz - 1 in
          let zero_start = U64.uint_to_t zero_start_nat in
          assert (U64.v zero_start >= U64.v zero_addr);
          assert (rem = 0 \/ U64.v zero_start >= U64.v zero_addr);
          assert (rem == wz - 1);
          chunked_zero_fields_tail_single_chunk_compat g2 zero_start rem;
          assert (Defs.chunked_zero_fields
                    (MH.single_chunk_major_heap g2) zero_start rem ==
                  MH.single_chunk_major_heap
                    (SpecAlloc.zero_fields g2 zero_start rem));
          assert (Defs.chunked_zero_fields
                    (MH.single_chunk_major_heap g2) zero_start (wz - 1) ==
                  Defs.chunked_zero_fields
                    (MH.single_chunk_major_heap g2) zero_start rem);
          assert (SpecAlloc.zero_fields g2 zero_start (wz - 1) ==
                  SpecAlloc.zero_fields g2 zero_start rem);
          assert (MH.single_chunk_major_heap
                    (SpecAlloc.zero_fields g2 zero_start (wz - 1)) ==
                  MH.single_chunk_major_heap
                    (SpecAlloc.zero_fields g2 zero_start rem));
          assert (Defs.chunked_zero_fields
                    (MH.single_chunk_major_heap g2) zero_start (wz - 1) ==
                  MH.single_chunk_major_heap
                    (SpecAlloc.zero_fields g2 zero_start (wz - 1)));
          assert (Defs.chunked_flush_blue
                    (MH.single_chunk_major_heap g) first_blue run_words fp ==
                  (MH.single_chunk_major_heap
                    (SpecAlloc.zero_fields g2 zero_start (wz - 1)), fb));
          assert (SpecCoalesce.flush_blue g first_blue run_words fp ==
                  (SpecAlloc.zero_fields g2 zero_start (wz - 1), fb))
        end else begin
          assert (Defs.chunked_flush_blue
                    (MH.single_chunk_major_heap g) first_blue run_words fp ==
                  (MH.single_chunk_major_heap g2, fb));
          assert (SpecCoalesce.flush_blue g first_blue run_words fp ==
                  (g2, fb))
        end
      end else begin
        assert (Defs.chunked_flush_blue
                  (MH.single_chunk_major_heap g) first_blue run_words fp ==
                (MH.single_chunk_major_heap g1, fp));
        assert (SpecCoalesce.flush_blue g first_blue run_words fp ==
                (g1, fp))
      end
    end
  end
  end
#pop-options

let rec chunked_fused_aux_single_chunk_compat
    (source work: heap)
    (objs: Seq.seq obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
  : Lemma
      (requires
        (forall (o: obj_addr). Seq.mem o objs ==> U64.v o >= U64.v zero_addr + U64.v mword) /\
        (run_words = 0 \/
         U64.v first_blue >= U64.v zero_addr + U64.v mword))
      (ensures
        Defs.chunked_fused_aux
          (MH.single_chunk_major_heap source)
          (MH.single_chunk_major_heap work)
          objs first_blue run_words fp ==
        (let (work', fp') =
          DenseFused.fused_aux source work objs first_blue run_words fp in
         (MH.single_chunk_major_heap work', fp')))
      (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then begin
    assert (Seq.length objs == Seq.length (Seq.empty #obj_addr));
    assert (forall i. i < Seq.length objs ==>
      Seq.index objs i == Seq.index (Seq.empty #obj_addr) i);
    Seq.lemma_eq_intro objs (Seq.empty #obj_addr);
    Seq.lemma_eq_elim objs (Seq.empty #obj_addr);
    Defs.chunked_fused_aux_empty
      (MH.single_chunk_major_heap source)
      (MH.single_chunk_major_heap work)
      first_blue run_words fp;
    DenseFused.fused_aux_empty source work first_blue run_words fp;
    chunked_flush_blue_single_chunk_compat work first_blue run_words fp
  end else begin
    assert (Seq.length objs > 0);
    let obj = Seq.head objs in
    let rest = Seq.tail objs in
    Seq.mem_cons obj rest;
    assert (Seq.mem obj objs);
    assert (U64.v obj >= U64.v zero_addr + U64.v mword);
    Defs.chunked_is_black_single_chunk_compat source obj;
    if Obj.is_black obj source then begin
      Defs.chunked_fused_aux_black_step
        (MH.single_chunk_major_heap source)
        (MH.single_chunk_major_heap work)
        objs first_blue run_words fp;
      DenseFused.fused_aux_black_step source work objs first_blue run_words fp;
      chunked_flush_blue_single_chunk_compat work first_blue run_words fp;
      let (work', fp') = SpecCoalesce.flush_blue work first_blue run_words fp in
      chunked_make_white_single_chunk_compat work' obj;
      let work'' = Obj.makeWhite obj work' in
      chunked_fused_aux_single_chunk_compat
        source work'' rest 0UL 0 fp'
    end else begin
      Defs.chunked_fused_aux_nonblack_step
        (MH.single_chunk_major_heap source)
        (MH.single_chunk_major_heap work)
        objs first_blue run_words fp;
      DenseFused.fused_aux_nonblack_step
        source work objs first_blue run_words fp;
      Defs.chunked_wosize_of_object_single_chunk_compat source obj;
      let ws = U64.v (Obj.wosize_of_object obj source) in
      let new_first : U64.t = if run_words = 0 then obj else first_blue in
      assert (run_words + ws + 1 <> 0);
      assert (U64.v new_first >= U64.v zero_addr + U64.v mword);
      chunked_fused_aux_single_chunk_compat
        source work rest new_first (run_words + ws + 1) fp
    end
  end

let chunked_fused_sweep_coalesce_single_chunk_compat
    (g: heap)
  : Lemma
      (Defs.chunked_fused_sweep_coalesce (MH.single_chunk_major_heap g) ==
       (let (g', fp') = DenseFused.fused_sweep_coalesce g in
        (MH.single_chunk_major_heap g', fp')))
  =
  Defs.chunked_fused_sweep_coalesce_step (MH.single_chunk_major_heap g);
  assert (Seq.length (MH.single_chunk_major_heap g) > 0);
  Defs.chunked_fused_sweep_coalesce_chunks_step
    (MH.single_chunk_major_heap g)
    (MH.single_chunk_major_heap g)
    (MH.single_chunk_major_heap g)
    0UL;
  assert (Seq.head (MH.single_chunk_major_heap g) == MH.single_chunk_of_heap g);
  MH.single_chunk_objects_compat g;
  assert (MH.objects_in_chunk (Seq.head (MH.single_chunk_major_heap g)) ==
          Fields.objects zero_addr g);
  single_chunk_objects_have_header_room g;
  chunked_fused_aux_single_chunk_compat
    g g (MH.objects_in_chunk (Seq.head (MH.single_chunk_major_heap g)))
    0UL 0 0UL;
  let (g', fp') = DenseFused.fused_sweep_coalesce g in
  assert (Seq.length (Seq.tail (MH.single_chunk_major_heap g)) == 0);
  Seq.lemma_empty (Seq.tail (MH.single_chunk_major_heap g));
  Defs.chunked_fused_sweep_coalesce_chunks_empty
    (MH.single_chunk_major_heap g)
    (MH.single_chunk_major_heap g') fp'
