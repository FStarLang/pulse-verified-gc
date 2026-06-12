module GC.Spec.ChunkedMarkBounded.Defs

module U64 = FStar.UInt64
module Seq = FStar.Seq

open FStar.Seq
open GC.Spec.Base

module Header = GC.Lib.Header
module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module MarkDefs = GC.Spec.ChunkedMark.Defs

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let chunked_is_gray
    (mh: MH.major_heap)
    (obj: obj_addr)
  : GTot bool
  =
  match SweepDefs.chunked_color_of_object mh obj with
  | Some Header.Gray -> true
  | _ -> false

let rec chunked_count_non_black_in
    (mh: MH.major_heap)
    (objs: seq obj_addr)
  : GTot nat
    (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then 0
  else
    let obj = Seq.head objs in
    let rest = chunked_count_non_black_in mh (Seq.tail objs) in
    if SweepDefs.chunked_is_black mh obj then rest
    else rest + 1

let chunked_count_non_black (mh: MH.major_heap) : GTot nat =
  chunked_count_non_black_in mh (MH.major_objects mh)

let rec chunked_push_children_bounded
    (mh: MH.major_heap)
    (st: seq obj_addr)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
    (cap: nat)
  : GTot (MH.major_heap & seq obj_addr)
    (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then (mh, st)
  else
    let v = MarkDefs.chunked_get_field mh obj i in
    let (mh', st') =
      if MarkDefs.chunked_is_pointer_field mh v then
        let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
        let child = MarkDefs.chunked_resolve_object mh child_raw in
        if SweepDefs.chunked_is_white mh child then
          let mh' = MarkDefs.chunked_make_gray mh child in
          if Seq.length st < cap then
            (mh', Seq.cons child st)
          else
            (mh', st)
        else
          (mh, st)
      else
        (mh, st)
    in
    if U64.v i < U64.v ws then
      chunked_push_children_bounded mh' st' obj (U64.add i 1UL) ws cap
    else
      (mh', st')

let chunked_mark_step_bounded
    (mh: MH.major_heap)
    (st: seq obj_addr)
    (cap: nat)
  : GTot (MH.major_heap & seq obj_addr)
  =
  if Seq.length st = 0 then (mh, st)
  else
    let obj = Seq.head st in
    let st' = Seq.tail st in
    let mh' = MarkDefs.chunked_make_black mh obj in
    let ws = SweepDefs.chunked_wosize_of_object mh obj in
    if MarkDefs.chunked_is_no_scan mh obj then
      (mh', st')
    else
      chunked_push_children_bounded mh' st' obj 1UL ws cap

let rec chunked_mark_inner_loop
    (mh: MH.major_heap)
    (st: seq obj_addr)
    (cap: nat)
    (fuel: nat)
  : GTot (MH.major_heap & seq obj_addr)
    (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then (mh, st)
  else begin
    assert (fuel > 0);
    let (mh', st') = chunked_mark_step_bounded mh st cap in
    chunked_mark_inner_loop mh' st' cap (fuel - 1)
  end

let rec chunked_rescan_objects
    (mh: MH.major_heap)
    (objs: seq obj_addr)
    (st: seq obj_addr)
    (cap: nat)
  : GTot (seq obj_addr)
    (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then st
  else
    let obj = Seq.head objs in
    let st' =
      if chunked_is_gray mh obj && not (Seq.mem obj st) &&
         Seq.length st < cap then
        Seq.cons obj st
      else
        st
    in
    chunked_rescan_objects mh (Seq.tail objs) st' cap

let chunked_rescan_heap
    (mh: MH.major_heap)
    (st: seq obj_addr)
    (cap: nat)
  : GTot (seq obj_addr)
  =
  chunked_rescan_objects mh (MH.major_objects mh) st cap

let rec chunked_mark_bounded
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : GTot MH.major_heap
    (decreases fuel)
  =
  if fuel = 0 then mh
  else begin
    assert (fuel > 0);
    let st = chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then mh
    else
      let inner_fuel = chunked_count_non_black mh in
      let (mh', _) = chunked_mark_inner_loop mh st cap inner_fuel in
      chunked_mark_bounded mh' cap (fuel - 1)
  end

let chunked_is_gray_step
    (mh: MH.major_heap)
    (obj: obj_addr)
  : Lemma
      (chunked_is_gray mh obj ==
       (match SweepDefs.chunked_color_of_object mh obj with
        | Some Header.Gray -> true
        | _ -> false))
  = ()

let chunked_count_non_black_in_empty
    (mh: MH.major_heap)
    (objs: seq obj_addr)
  : Lemma
      (requires Seq.length objs = 0)
      (ensures chunked_count_non_black_in mh objs == 0)
  = ()

let chunked_count_non_black_in_step
    (mh: MH.major_heap)
    (objs: seq obj_addr)
  : Lemma
      (requires Seq.length objs > 0)
      (ensures
        (let obj = Seq.head objs in
         let rest = chunked_count_non_black_in mh (Seq.tail objs) in
         chunked_count_non_black_in mh objs ==
         (if SweepDefs.chunked_is_black mh obj then rest else rest + 1)))
  = ()

let chunked_count_non_black_equation
    (mh: MH.major_heap)
  : Lemma
      (chunked_count_non_black mh ==
       chunked_count_non_black_in mh (MH.major_objects mh))
  = ()

let chunked_push_children_bounded_done
    (mh: MH.major_heap)
    (st: seq obj_addr)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
    (cap: nat)
  : Lemma
      (requires U64.v i > U64.v ws)
      (ensures chunked_push_children_bounded mh st obj i ws cap == (mh, st))
  = ()

let chunked_push_children_bounded_step
    (mh: MH.major_heap)
    (st: seq obj_addr)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
    (cap: nat)
  : Lemma
      (requires U64.v i <= U64.v ws)
      (ensures
        (let v = MarkDefs.chunked_get_field mh obj i in
         let (mh', st') =
           if MarkDefs.chunked_is_pointer_field mh v then
             let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
             let child = MarkDefs.chunked_resolve_object mh child_raw in
             if SweepDefs.chunked_is_white mh child then
               let mh' = MarkDefs.chunked_make_gray mh child in
               if Seq.length st < cap then
                 (mh', Seq.cons child st)
               else
                 (mh', st)
             else
               (mh, st)
           else
             (mh, st)
         in
         chunked_push_children_bounded mh st obj i ws cap ==
         (if U64.v i < U64.v ws then
            chunked_push_children_bounded mh' st' obj (U64.add i 1UL) ws cap
          else
            (mh', st'))))
  = ()

let chunked_mark_step_bounded_empty
    (mh: MH.major_heap)
    (st: seq obj_addr)
    (cap: nat)
  : Lemma
      (requires Seq.length st = 0)
      (ensures chunked_mark_step_bounded mh st cap == (mh, st))
  = ()

let chunked_mark_step_bounded_no_scan
    (mh: MH.major_heap)
    (st: seq obj_addr)
    (cap: nat)
  : Lemma
      (requires Seq.length st > 0 /\
                MarkDefs.chunked_is_no_scan mh (Seq.head st))
      (ensures
        (let obj = Seq.head st in
         let st' = Seq.tail st in
         chunked_mark_step_bounded mh st cap ==
         (MarkDefs.chunked_make_black mh obj, st')))
  = ()

let chunked_mark_step_bounded_scan
    (mh: MH.major_heap)
    (st: seq obj_addr)
    (cap: nat)
  : Lemma
      (requires Seq.length st > 0 /\
                ~(MarkDefs.chunked_is_no_scan mh (Seq.head st)))
      (ensures
        (let obj = Seq.head st in
         let st' = Seq.tail st in
         let mh' = MarkDefs.chunked_make_black mh obj in
         let ws = SweepDefs.chunked_wosize_of_object mh obj in
         chunked_mark_step_bounded mh st cap ==
         chunked_push_children_bounded mh' st' obj 1UL ws cap))
  = ()

let chunked_mark_inner_loop_base
    (mh: MH.major_heap)
    (st: seq obj_addr)
    (cap: nat)
    (fuel: nat)
  : Lemma
      (requires fuel = 0 \/ Seq.length st = 0)
      (ensures chunked_mark_inner_loop mh st cap fuel == (mh, st))
  = ()

let chunked_mark_inner_loop_step
    (mh: MH.major_heap)
    (st: seq obj_addr)
    (cap: nat)
    (fuel: nat{fuel > 0})
  : Lemma
      (requires Seq.length st > 0)
      (ensures
        (let (mh', st') = chunked_mark_step_bounded mh st cap in
         chunked_mark_inner_loop mh st cap fuel ==
         chunked_mark_inner_loop mh' st' cap (fuel - 1)))
  =
  assert (fuel > 0)

let chunked_rescan_objects_empty
    (mh: MH.major_heap)
    (objs: seq obj_addr)
    (st: seq obj_addr)
    (cap: nat)
  : Lemma
      (requires Seq.length objs = 0)
      (ensures chunked_rescan_objects mh objs st cap == st)
  = ()

let chunked_rescan_objects_step
    (mh: MH.major_heap)
    (objs: seq obj_addr)
    (st: seq obj_addr)
    (cap: nat)
  : Lemma
      (requires Seq.length objs > 0)
      (ensures
        (let obj = Seq.head objs in
         let st' =
           if chunked_is_gray mh obj && not (Seq.mem obj st) &&
              Seq.length st < cap then
             Seq.cons obj st
           else
             st
         in
         chunked_rescan_objects mh objs st cap ==
         chunked_rescan_objects mh (Seq.tail objs) st' cap))
  = ()

let chunked_rescan_heap_equation
    (mh: MH.major_heap)
    (st: seq obj_addr)
    (cap: nat)
  : Lemma
      (chunked_rescan_heap mh st cap ==
       chunked_rescan_objects mh (MH.major_objects mh) st cap)
  = ()

let chunked_mark_bounded_base
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
  : Lemma
      (chunked_mark_bounded mh cap 0 == mh)
  = ()

let chunked_mark_bounded_step
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat{fuel > 0})
  : Lemma
      (ensures
        (let st = chunked_rescan_heap mh Seq.empty cap in
         chunked_mark_bounded mh cap fuel ==
         (if Seq.length st = 0 then mh
          else
            let inner_fuel = chunked_count_non_black mh in
            let (mh', _) = chunked_mark_inner_loop mh st cap inner_fuel in
            chunked_mark_bounded mh' cap (fuel - 1))))
  =
  assert (fuel > 0)
