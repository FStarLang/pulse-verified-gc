module GC.Spec.ChunkedMark.Defs

open FStar.Seq

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base

module Header = GC.Lib.Header
module MH = GC.Spec.MajorHeap
module Obj = GC.Spec.Object
module ChunkedSweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs

val chunked_get_field
  (mh: MH.major_heap)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  : GTot U64.t

val chunked_is_pointer_field
  (mh: MH.major_heap)
  (v: U64.t)
  : GTot bool

val chunked_is_pointer_field_is_obj_addr
  (mh: MH.major_heap)
  (v: U64.t)
  : Lemma
      (requires chunked_is_pointer_field mh v)
      (ensures U64.v v >= U64.v mword /\
               U64.v v < heap_size /\
               U64.v v % U64.v mword == 0)

val chunked_pointer_field_as_obj_addr
  (mh: MH.major_heap)
  (v: U64.t{chunked_is_pointer_field mh v})
  : GTot obj_addr

val chunked_parent_closure_addr_nat
  (infix_obj: obj_addr)
  (mh: MH.major_heap)
  : GTot int

val chunked_resolve_object
  (mh: MH.major_heap)
  (addr: obj_addr)
  : GTot obj_addr

val chunked_is_no_scan
  (mh: MH.major_heap)
  (obj: obj_addr)
  : GTot bool

val chunked_make_gray
  (mh: MH.major_heap)
  (obj: obj_addr)
  : GTot MH.major_heap

val chunked_make_black
  (mh: MH.major_heap)
  (obj: obj_addr)
  : GTot MH.major_heap

val chunked_push_children
  (mh: MH.major_heap)
  (st: seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : GTot (MH.major_heap & seq obj_addr)

val chunked_mark_step
  (mh: MH.major_heap)
  (st: seq obj_addr)
  : GTot (MH.major_heap & seq obj_addr)

val chunked_mark_aux
  (mh: MH.major_heap)
  (st: seq obj_addr)
  (fuel: nat)
  : GTot MH.major_heap

val chunked_mark
  (mh: MH.major_heap)
  (st: seq obj_addr)
  : GTot MH.major_heap

val chunked_make_gray_step:
  mh:MH.major_heap ->
  obj:obj_addr ->
  Lemma
    (chunked_make_gray mh obj ==
     ChunkedSweepDefs.chunked_set_object_color mh obj Header.Gray)

val chunked_make_black_step:
  mh:MH.major_heap ->
  obj:obj_addr ->
  Lemma
    (chunked_make_black mh obj ==
     ChunkedSweepDefs.chunked_set_object_color mh obj Header.Black)

val chunked_resolve_non_infix:
  mh:MH.major_heap ->
  addr:obj_addr ->
  Lemma
    (requires ~(ChunkedSweepDefs.chunked_is_infix mh addr))
    (ensures chunked_resolve_object mh addr == addr)

val chunked_push_children_done:
  mh:MH.major_heap ->
  st:seq obj_addr ->
  obj:obj_addr ->
  i:U64.t{U64.v i >= 1} ->
  ws:U64.t ->
  Lemma
    (requires U64.v i > U64.v ws)
    (ensures chunked_push_children mh st obj i ws == (mh, st))

val chunked_push_children_step:
  mh:MH.major_heap ->
  st:seq obj_addr ->
  obj:obj_addr ->
  i:U64.t{U64.v i >= 1} ->
  ws:U64.t ->
  Lemma
    (requires U64.v i <= U64.v ws)
    (ensures
      (let v = chunked_get_field mh obj i in
       let (mh', st') =
         if chunked_is_pointer_field mh v then
           let child_raw = chunked_pointer_field_as_obj_addr mh v in
           let child = chunked_resolve_object mh child_raw in
           if ChunkedSweepDefs.chunked_is_white mh child then
             (chunked_make_gray mh child, Seq.cons child st)
           else
             (mh, st)
         else
           (mh, st)
       in
       chunked_push_children mh st obj i ws ==
       (if U64.v i < U64.v ws then
         chunked_push_children mh' st' obj (U64.add i 1UL) ws
       else
         (mh', st'))))

val chunked_mark_step_empty:
  mh:MH.major_heap ->
  st:seq obj_addr ->
  Lemma
    (requires Seq.length st = 0)
    (ensures chunked_mark_step mh st == (mh, st))

val chunked_mark_step_no_scan:
  mh:MH.major_heap ->
  st:seq obj_addr ->
  Lemma
    (requires Seq.length st > 0 /\
              chunked_is_no_scan mh (Seq.head st))
    (ensures
      (let obj = Seq.head st in
       let st' = Seq.tail st in
       chunked_mark_step mh st == (chunked_make_black mh obj, st')))

val chunked_mark_step_scan:
  mh:MH.major_heap ->
  st:seq obj_addr ->
  Lemma
    (requires Seq.length st > 0 /\
              ~(chunked_is_no_scan mh (Seq.head st)))
    (ensures
      (let obj = Seq.head st in
       let st' = Seq.tail st in
       let mh' = chunked_make_black mh obj in
       let ws = ChunkedSweepDefs.chunked_wosize_of_object mh obj in
       chunked_mark_step mh st ==
       chunked_push_children mh' st' obj 1UL ws))

val chunked_mark_aux_empty:
  mh:MH.major_heap ->
  st:seq obj_addr ->
  fuel:nat ->
  Lemma
    (requires Seq.length st = 0)
    (ensures chunked_mark_aux mh st fuel == mh)

val chunked_mark_aux_out_of_fuel:
  mh:MH.major_heap ->
  st:seq obj_addr ->
  Lemma
    (ensures chunked_mark_aux mh st 0 == mh)

val chunked_mark_aux_step:
  mh:MH.major_heap ->
  st:seq obj_addr ->
  fuel:nat{fuel > 0} ->
  Lemma
    (requires Seq.length st > 0)
    (ensures
      (let (mh', st') = chunked_mark_step mh st in
       chunked_mark_aux mh st fuel ==
       chunked_mark_aux mh' st' (fuel - 1)))
