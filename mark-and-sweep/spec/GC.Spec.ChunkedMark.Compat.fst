module GC.Spec.ChunkedMark.Compat

module U64 = FStar.UInt64
module Math = FStar.Math.Lemmas

open GC.Spec.Base
open GC.Spec.Heap

module Header = GC.Lib.Header
module Obj = GC.Spec.Object
module Fields = GC.Spec.Fields
module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark
module MH = GC.Spec.MajorHeap
module SpecMajorAlloc = GC.Spec.MajorAllocator
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module MarkDefs = GC.Spec.ChunkedMark.Defs

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

private let field_addr_in_bounds
    (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
    (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        U64.v (hd_address obj) + U64.v mword * U64.v i + U64.v mword <= heap_size)
      (ensures
        (let field_addr = U64.add (hd_address obj) (U64.mul mword i) in
         U64.v field_addr >= U64.v zero_addr /\
         U64.v field_addr + U64.v mword <= heap_size))
  =
  hd_address_spec obj;
  assert (U64.v (hd_address obj) + U64.v mword == U64.v obj);
  assert (U64.v (hd_address obj) + U64.v mword * U64.v i >= U64.v obj);
  assert (U64.v (hd_address obj) + U64.v mword * U64.v i + U64.v mword <= heap_size);
  assert (U64.v (hd_address obj) + U64.v mword * U64.v i < heap_size);
  assert (U64.v (hd_address obj) + U64.v mword * U64.v i < pow2 64);
  assert (U64.v mword * U64.v i < heap_size);
  assert (U64.v mword * U64.v i < pow2 64);
  assert (U64.v i * U64.v mword < pow2 64);
  assert (U64.v (U64.mul mword i) == U64.v mword * U64.v i);
  assert (U64.v (U64.add (hd_address obj) (U64.mul mword i)) ==
          U64.v (hd_address obj) + U64.v mword * U64.v i)

let chunked_get_field_single_chunk_compat
    (g: heap)
    (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
    (i: U64.t{U64.v i >= 1})
  : Lemma
      (MarkDefs.chunked_get_field (MH.single_chunk_major_heap g) obj i ==
       HeapGraph.get_field g obj i)
  =
  if U64.v (hd_address obj) + U64.v mword * U64.v i + U64.v mword <= heap_size then begin
    field_addr_in_bounds obj i;
    let field_addr = U64.add (hd_address obj) (U64.mul mword i) in
    assert (U64.v field_addr >= U64.v zero_addr);
    assert (U64.v field_addr + U64.v mword <= heap_size);
    assert (MH.word_in_chunk (MH.single_chunk_of_heap g) field_addr);
    MH.single_chunk_read_word_compat g field_addr;
    MarkDefs.chunked_get_field_read_some
      (MH.single_chunk_major_heap g) obj i (read_word g field_addr)
  end else begin
    MarkDefs.chunked_get_field_no_room (MH.single_chunk_major_heap g) obj i;
    assert (HeapGraph.get_field g obj i == 0UL)
  end

let chunked_is_pointer_field_single_chunk_compat
    (g: heap)
    (v: U64.t)
  : Lemma
      (MarkDefs.chunked_is_pointer_field (MH.single_chunk_major_heap g) v ==
       HeapGraph.is_pointer_field v)
  =
  MarkDefs.chunked_is_pointer_field_step (MH.single_chunk_major_heap g) v;
  MH.single_chunk_major_pointer_compat g v;
  assert (Fields.is_pointer v == HeapGraph.is_pointer_field v)

let chunked_make_gray_single_chunk_compat
    (g: heap)
    (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (MarkDefs.chunked_make_gray (MH.single_chunk_major_heap g) obj ==
       MH.single_chunk_major_heap (Obj.makeGray obj g))
  =
  SweepDefs.chunked_read_header_single_chunk_compat g obj;
  hd_address_spec obj;
  assert (U64.v (hd_address obj) >= U64.v zero_addr);
  assert (U64.v (hd_address obj) + U64.v mword == U64.v obj);
  assert (U64.v (hd_address obj) + U64.v mword <= heap_size);
  MarkDefs.chunked_make_gray_step (MH.single_chunk_major_heap g) obj;
  SweepDefs.chunked_set_object_color_some
    (MH.single_chunk_major_heap g) obj Header.Gray
    (read_word g (hd_address obj));
  Obj.makeGray_spec obj g;
  SpecMajorAlloc.major_write_word_or_same_single_chunk_compat
    g (hd_address obj)
    (Obj.colorHeader (read_word g (hd_address obj)) Header.Gray)

let chunked_make_black_single_chunk_compat
    (g: heap)
    (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (MarkDefs.chunked_make_black (MH.single_chunk_major_heap g) obj ==
       MH.single_chunk_major_heap (Obj.makeBlack obj g))
  =
  SweepDefs.chunked_read_header_single_chunk_compat g obj;
  hd_address_spec obj;
  assert (U64.v (hd_address obj) >= U64.v zero_addr);
  assert (U64.v (hd_address obj) + U64.v mword == U64.v obj);
  assert (U64.v (hd_address obj) + U64.v mword <= heap_size);
  MarkDefs.chunked_make_black_step (MH.single_chunk_major_heap g) obj;
  SweepDefs.chunked_set_object_color_some
    (MH.single_chunk_major_heap g) obj Header.Black
    (read_word g (hd_address obj));
  Obj.makeBlack_spec obj g;
  SpecMajorAlloc.major_write_word_or_same_single_chunk_compat
    g (hd_address obj)
    (Obj.colorHeader (read_word g (hd_address obj)) Header.Black)

let chunked_is_no_scan_single_chunk_compat
    (g: heap)
    (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (MarkDefs.chunked_is_no_scan (MH.single_chunk_major_heap g) obj ==
       Obj.is_no_scan obj g)
  =
  MarkDefs.chunked_is_no_scan_step (MH.single_chunk_major_heap g) obj;
  SweepDefs.chunked_tag_of_object_single_chunk_compat g obj;
  Obj.is_no_scan_spec obj g

let chunked_parent_closure_addr_nat_single_chunk_compat
    (g: heap)
    (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (MarkDefs.chunked_parent_closure_addr_nat
        obj (MH.single_chunk_major_heap g) ==
       Obj.parent_closure_addr_nat obj g)
  =
  MarkDefs.chunked_parent_closure_addr_nat_step
    obj (MH.single_chunk_major_heap g);
  SweepDefs.chunked_wosize_of_object_single_chunk_compat g obj;
  Obj.parent_closure_addr_nat_spec obj g

let chunked_resolve_object_single_chunk_compat
    (g: heap)
    (addr: obj_addr{U64.v addr >= U64.v zero_addr + U64.v mword})
  : Lemma
      (requires
        Obj.is_infix addr g ==>
        (let p = Obj.parent_closure_addr_nat addr g in
         p >= 8 /\ p < heap_size /\ p % 8 == 0 /\
         Fields.is_pointer (U64.uint_to_t p)))
      (ensures
        MarkDefs.chunked_resolve_object (MH.single_chunk_major_heap g) addr ==
        Obj.resolve_object addr g)
  =
  SweepDefs.chunked_is_infix_single_chunk_compat g addr;
  chunked_parent_closure_addr_nat_single_chunk_compat g addr;
  if Obj.is_infix addr g then begin
    let p = Obj.parent_closure_addr_nat addr g in
    assert (p >= 8 /\ p < heap_size /\ p % 8 == 0);
    assert (Fields.is_pointer (U64.uint_to_t p));
    MarkDefs.chunked_is_pointer_field_step
      (MH.single_chunk_major_heap g) (U64.uint_to_t p);
    MH.single_chunk_major_pointer_compat g (U64.uint_to_t p);
    assert (MarkDefs.chunked_is_pointer_field
              (MH.single_chunk_major_heap g) (U64.uint_to_t p));
    MarkDefs.chunked_resolve_infix_valid_active
      (MH.single_chunk_major_heap g) addr;
    Obj.resolve_infix_spec addr g
  end else begin
    MarkDefs.chunked_resolve_non_infix (MH.single_chunk_major_heap g) addr;
    Obj.resolve_non_infix addr g
  end

let chunked_mark_step_empty_single_chunk_compat
    (g: heap)
    (st: Seq.seq obj_addr)
  : Lemma
      (requires Seq.length st = 0)
      (ensures
        MarkDefs.chunked_mark_step (MH.single_chunk_major_heap g) st ==
        (let (g', st') = Mark.mark_step g st in
         (MH.single_chunk_major_heap g', st')))
  =
  MarkDefs.chunked_mark_step_empty (MH.single_chunk_major_heap g) st

let chunked_mark_step_no_scan_single_chunk_compat
    (g: heap)
    (st: Seq.seq obj_addr)
  : Lemma
      (requires Seq.length st > 0 /\
                U64.v (Seq.head st) >= U64.v zero_addr + U64.v mword /\
                Obj.is_no_scan (Seq.head st) g)
      (ensures
        MarkDefs.chunked_mark_step (MH.single_chunk_major_heap g) st ==
        (let (g', st') = Mark.mark_step g st in
         (MH.single_chunk_major_heap g', st')))
  =
  let obj = Seq.head st in
  chunked_is_no_scan_single_chunk_compat g obj;
  chunked_make_black_single_chunk_compat g obj;
  MarkDefs.chunked_mark_step_no_scan (MH.single_chunk_major_heap g) st

let chunked_mark_aux_empty_single_chunk_compat
    (g: heap)
    (st: Seq.seq obj_addr)
    (fuel: nat)
  : Lemma
      (requires Seq.length st = 0)
      (ensures
        MarkDefs.chunked_mark_aux (MH.single_chunk_major_heap g) st fuel ==
        MH.single_chunk_major_heap (Mark.mark_aux g st fuel))
  =
  MarkDefs.chunked_mark_aux_empty (MH.single_chunk_major_heap g) st fuel

let chunked_mark_aux_out_of_fuel_single_chunk_compat
    (g: heap)
    (st: Seq.seq obj_addr)
  : Lemma
      (ensures
        MarkDefs.chunked_mark_aux (MH.single_chunk_major_heap g) st 0 ==
        MH.single_chunk_major_heap (Mark.mark_aux g st 0))
  =
  MarkDefs.chunked_mark_aux_out_of_fuel (MH.single_chunk_major_heap g) st
