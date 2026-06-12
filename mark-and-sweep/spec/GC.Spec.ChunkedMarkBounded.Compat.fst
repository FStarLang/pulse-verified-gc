module GC.Spec.ChunkedMarkBounded.Compat

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module Obj = GC.Spec.Object
module Fields = GC.Spec.Fields
module HeapGraph = GC.Spec.HeapGraph
module BMark = GC.Spec.MarkBounded
module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module MarkDefs = GC.Spec.ChunkedMark.Defs
module MarkCompat = GC.Spec.ChunkedMark.Compat

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let chunked_is_gray_single_chunk_compat
    (g: heap)
    (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (BDefs.chunked_is_gray (MH.single_chunk_major_heap g) obj ==
       Obj.is_gray obj g)
  =
  BDefs.chunked_is_gray_step (MH.single_chunk_major_heap g) obj;
  SweepDefs.chunked_color_of_object_single_chunk_compat g obj;
  Obj.is_gray_iff obj g

let pointer_field_as_obj_addr (v: U64.t{HeapGraph.is_pointer_field v})
  : GTot obj_addr
  =
  v

let rec push_children_bounded_single_chunk_ready
    (g: heap)
    (st: Seq.seq obj_addr)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
    (cap: nat)
  : Tot prop
    (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then True
  else
    let v = HeapGraph.get_field g obj i in
    if HeapGraph.is_pointer_field v then
      let child_raw = pointer_field_as_obj_addr v in
      let child = Obj.resolve_object child_raw g in
      (Obj.is_infix child_raw g ==>
        (let p = Obj.parent_closure_addr_nat child_raw g in
         p >= 8 /\ p < heap_size /\ p % 8 == 0 /\
         Fields.is_pointer (U64.uint_to_t p))) /\
      U64.v child >= U64.v zero_addr + U64.v mword /\
      (if Obj.is_white child g then
        let g' = Obj.makeGray child g in
        let st' = if Seq.length st < cap then Seq.cons child st else st in
        if U64.v i < U64.v ws then
          push_children_bounded_single_chunk_ready
            g' st' obj (U64.add i 1UL) ws cap
        else
          True
      else
        if U64.v i < U64.v ws then
          push_children_bounded_single_chunk_ready
            g st obj (U64.add i 1UL) ws cap
        else
          True)
    else
      if U64.v i < U64.v ws then
        push_children_bounded_single_chunk_ready
          g st obj (U64.add i 1UL) ws cap
      else
        True

let rec chunked_push_children_bounded_single_chunk_compat
    (g: heap)
    (st: Seq.seq obj_addr)
    (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
    (cap: nat)
  : Lemma
      (requires push_children_bounded_single_chunk_ready g st obj i ws cap)
      (ensures
        BDefs.chunked_push_children_bounded
          (MH.single_chunk_major_heap g) st obj i ws cap ==
        (let (g', st') =
          BMark.push_children_bounded g st obj i ws cap in
         (MH.single_chunk_major_heap g', st')))
      (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then
    BDefs.chunked_push_children_bounded_done
      (MH.single_chunk_major_heap g) st obj i ws cap
  else begin
    let v = HeapGraph.get_field g obj i in
    MarkCompat.chunked_get_field_single_chunk_compat g obj i;
    MarkCompat.chunked_is_pointer_field_single_chunk_compat g v;
    BDefs.chunked_push_children_bounded_step
      (MH.single_chunk_major_heap g) st obj i ws cap;
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let child_raw : obj_addr = v in
      assert (MarkDefs.chunked_is_pointer_field
        (MH.single_chunk_major_heap g)
        (MarkDefs.chunked_get_field (MH.single_chunk_major_heap g) obj i));
      MarkDefs.chunked_pointer_field_as_obj_addr_step
        (MH.single_chunk_major_heap g)
        (MarkDefs.chunked_get_field (MH.single_chunk_major_heap g) obj i);
      assert (MarkDefs.chunked_pointer_field_as_obj_addr
        (MH.single_chunk_major_heap g)
        (MarkDefs.chunked_get_field (MH.single_chunk_major_heap g) obj i) ==
        child_raw);
      let child = Obj.resolve_object child_raw g in
      MarkCompat.chunked_resolve_object_single_chunk_compat g child_raw;
      SweepDefs.chunked_is_white_single_chunk_compat g child;
      if Obj.is_white child g then begin
        let g' = Obj.makeGray child g in
        let st' = if Seq.length st < cap then Seq.cons child st else st in
        MarkCompat.chunked_make_gray_single_chunk_compat g child;
        assert (MarkDefs.chunked_make_gray (MH.single_chunk_major_heap g) child ==
                MH.single_chunk_major_heap g');
        if U64.v i < U64.v ws then begin
          assert (U64.v (U64.add i 1UL) == U64.v i + 1);
          assert (U64.v ws - U64.v (U64.add i 1UL) <
                  U64.v ws - U64.v i);
          assert (push_children_bounded_single_chunk_ready
            g' st' obj (U64.add i 1UL) ws cap);
          chunked_push_children_bounded_single_chunk_compat
            g' st' obj (U64.add i 1UL) ws cap
        end else
          ()
      end else begin
        if U64.v i < U64.v ws then begin
          assert (U64.v (U64.add i 1UL) == U64.v i + 1);
          assert (U64.v ws - U64.v (U64.add i 1UL) <
                  U64.v ws - U64.v i);
          assert (push_children_bounded_single_chunk_ready
            g st obj (U64.add i 1UL) ws cap);
          chunked_push_children_bounded_single_chunk_compat
            g st obj (U64.add i 1UL) ws cap
        end else
          ()
      end
    end else begin
      assert (~(MarkDefs.chunked_is_pointer_field
        (MH.single_chunk_major_heap g)
        (MarkDefs.chunked_get_field (MH.single_chunk_major_heap g) obj i)));
      if U64.v i < U64.v ws then begin
        assert (U64.v (U64.add i 1UL) == U64.v i + 1);
        assert (U64.v ws - U64.v (U64.add i 1UL) <
                U64.v ws - U64.v i);
        assert (push_children_bounded_single_chunk_ready
          g st obj (U64.add i 1UL) ws cap);
        chunked_push_children_bounded_single_chunk_compat
          g st obj (U64.add i 1UL) ws cap
      end else
        ()
    end
  end

let chunked_mark_step_bounded_single_chunk_compat
    (g: heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
  : Lemma
      (requires
        (if Seq.length st = 0 then True
         else
           let obj = Seq.head st in
           U64.v obj >= U64.v zero_addr + U64.v mword /\
           (if Obj.is_no_scan obj g then
              True
            else
              push_children_bounded_single_chunk_ready
                (Obj.makeBlack obj g)
                (Seq.tail st)
                obj
                1UL
                (Obj.wosize_of_object obj g)
                cap)))
      (ensures
        BDefs.chunked_mark_step_bounded
          (MH.single_chunk_major_heap g) st cap ==
        (let (g', st') = BMark.mark_step_bounded g st cap in
         (MH.single_chunk_major_heap g', st')))
  =
  if Seq.length st = 0 then
    BDefs.chunked_mark_step_bounded_empty (MH.single_chunk_major_heap g) st cap
  else begin
    let obj = Seq.head st in
    if Obj.is_no_scan obj g then begin
      MarkCompat.chunked_is_no_scan_single_chunk_compat g obj;
      MarkCompat.chunked_make_black_single_chunk_compat g obj;
      BDefs.chunked_mark_step_bounded_no_scan
        (MH.single_chunk_major_heap g) st cap
    end else begin
      MarkCompat.chunked_is_no_scan_single_chunk_compat g obj;
      MarkCompat.chunked_make_black_single_chunk_compat g obj;
      SweepDefs.chunked_wosize_of_object_single_chunk_compat g obj;
      BDefs.chunked_mark_step_bounded_scan
        (MH.single_chunk_major_heap g) st cap;
      assert (MarkDefs.chunked_make_black
        (MH.single_chunk_major_heap g) obj ==
        MH.single_chunk_major_heap (Obj.makeBlack obj g));
      assert (SweepDefs.chunked_wosize_of_object
        (MH.single_chunk_major_heap g) obj ==
        Obj.wosize_of_object obj g);
      chunked_push_children_bounded_single_chunk_compat
        (Obj.makeBlack obj g) (Seq.tail st) obj 1UL
        (Obj.wosize_of_object obj g) cap
    end
  end
