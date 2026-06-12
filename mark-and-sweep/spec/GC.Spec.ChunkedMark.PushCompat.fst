module GC.Spec.ChunkedMark.PushCompat

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module Obj = GC.Spec.Object
module Fields = GC.Spec.Fields
module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark
module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module MarkDefs = GC.Spec.ChunkedMark.Defs
module MarkCompat = GC.Spec.ChunkedMark.Compat

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let pointer_field_as_obj_addr (v: U64.t{HeapGraph.is_pointer_field v})
  : GTot obj_addr
  =
  v

let rec push_children_single_chunk_ready
    (g: heap)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
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
        if U64.v i < U64.v ws then
          push_children_single_chunk_ready
            (Obj.makeGray child g) obj (U64.add i 1UL) ws
        else
          True
      else
        if U64.v i < U64.v ws then
          push_children_single_chunk_ready g obj (U64.add i 1UL) ws
        else
          True)
    else
      if U64.v i < U64.v ws then
        push_children_single_chunk_ready g obj (U64.add i 1UL) ws
      else
        True

let rec chunked_push_children_single_chunk_compat
    (g: heap)
    (st: Seq.seq obj_addr)
    (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
  : Lemma
      (requires push_children_single_chunk_ready g obj i ws)
      (ensures
        MarkDefs.chunked_push_children
          (MH.single_chunk_major_heap g) st obj i ws ==
        (let (g', st') = Mark.push_children g st obj i ws in
         (MH.single_chunk_major_heap g', st')))
      (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then begin
    MarkDefs.chunked_push_children_done
      (MH.single_chunk_major_heap g) st obj i ws
  end else begin
    let v = HeapGraph.get_field g obj i in
    MarkCompat.chunked_get_field_single_chunk_compat g obj i;
    MarkCompat.chunked_is_pointer_field_single_chunk_compat g v;
    MarkDefs.chunked_push_children_step
      (MH.single_chunk_major_heap g) st obj i ws;
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
        MarkCompat.chunked_make_gray_single_chunk_compat g child;
        assert (MarkDefs.chunked_make_gray (MH.single_chunk_major_heap g) child ==
                MH.single_chunk_major_heap (Obj.makeGray child g));
        if U64.v i < U64.v ws then begin
          assert (U64.v (U64.add i 1UL) == U64.v i + 1);
          assert (U64.v ws - U64.v (U64.add i 1UL) <
                  U64.v ws - U64.v i);
          assert (push_children_single_chunk_ready
            (Obj.makeGray child g) obj (U64.add i 1UL) ws);
          chunked_push_children_single_chunk_compat
            (Obj.makeGray child g) (Seq.cons child st) obj
            (U64.add i 1UL) ws
        end else
          ()
      end else begin
        if U64.v i < U64.v ws then begin
          assert (U64.v (U64.add i 1UL) == U64.v i + 1);
          assert (U64.v ws - U64.v (U64.add i 1UL) <
                  U64.v ws - U64.v i);
          assert (push_children_single_chunk_ready
            g obj (U64.add i 1UL) ws);
          chunked_push_children_single_chunk_compat
            g st obj (U64.add i 1UL) ws
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
        assert (push_children_single_chunk_ready
          g obj (U64.add i 1UL) ws);
        chunked_push_children_single_chunk_compat
          g st obj (U64.add i 1UL) ws
      end else
        ()
    end
  end

let chunked_mark_step_scan_single_chunk_compat
    (g: heap)
    (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        U64.v (Seq.head st) >= U64.v zero_addr + U64.v mword /\
        ~(Obj.is_no_scan (Seq.head st) g) /\
        push_children_single_chunk_ready
          (Obj.makeBlack (Seq.head st) g)
          (Seq.head st)
          1UL
          (Obj.wosize_of_object (Seq.head st) g))
      (ensures
        MarkDefs.chunked_mark_step (MH.single_chunk_major_heap g) st ==
        (let (g', st') = Mark.mark_step g st in
         (MH.single_chunk_major_heap g', st')))
  =
  let obj = Seq.head st in
  let st' = Seq.tail st in
  MarkCompat.chunked_is_no_scan_single_chunk_compat g obj;
  MarkCompat.chunked_make_black_single_chunk_compat g obj;
  SweepDefs.chunked_wosize_of_object_single_chunk_compat g obj;
  MarkDefs.chunked_mark_step_scan (MH.single_chunk_major_heap g) st;
  assert (MarkDefs.chunked_make_black (MH.single_chunk_major_heap g) obj ==
          MH.single_chunk_major_heap (Obj.makeBlack obj g));
  assert (SweepDefs.chunked_wosize_of_object (MH.single_chunk_major_heap g) obj ==
          Obj.wosize_of_object obj g);
  chunked_push_children_single_chunk_compat
    (Obj.makeBlack obj g) st' obj 1UL (Obj.wosize_of_object obj g)
