module GC.Spec.ChunkedMark.Defs

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module Header = GC.Lib.Header
module MH = GC.Spec.MajorHeap
module Obj = GC.Spec.Object
module ChunkedSweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let chunked_get_field
    (mh: MH.major_heap)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
  : GTot U64.t
  =
  let hd = hd_address obj in
  if U64.v hd + U64.v mword * U64.v i + U64.v mword <= heap_size then
    let field_addr = U64.add hd (U64.mul mword i) in
    match MH.read_word_in_major mh field_addr with
    | Some v -> v
    | None -> 0UL
  else
    0UL

let chunked_get_field_no_room
    (mh: MH.major_heap)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        ~(U64.v (hd_address obj) + U64.v mword * U64.v i + U64.v mword <=
          heap_size))
      (ensures chunked_get_field mh obj i == 0UL)
  = ()

let chunked_get_field_read_some
    (mh: MH.major_heap)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (v: U64.t)
  : Lemma
      (requires
        U64.v (hd_address obj) + U64.v mword * U64.v i + U64.v mword <=
          heap_size /\
        (let field_addr = U64.add (hd_address obj) (U64.mul mword i) in
         MH.read_word_in_major mh field_addr == Some v))
      (ensures chunked_get_field mh obj i == v)
  = ()

let chunked_get_field_read_none
    (mh: MH.major_heap)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        U64.v (hd_address obj) + U64.v mword * U64.v i + U64.v mword <=
          heap_size /\
        (let field_addr = U64.add (hd_address obj) (U64.mul mword i) in
         MH.read_word_in_major mh field_addr == None))
      (ensures chunked_get_field mh obj i == 0UL)
  = ()

let chunked_is_pointer_field (mh: MH.major_heap) (v: U64.t) : GTot bool =
  MH.is_major_pointer mh v

let chunked_is_pointer_field_step (mh: MH.major_heap) (v: U64.t)
  : Lemma (chunked_is_pointer_field mh v == MH.is_major_pointer mh v)
  = ()

let rec chunked_is_pointer_field_is_obj_addr
    (mh: MH.major_heap)
    (v: U64.t)
  : Lemma
      (requires chunked_is_pointer_field mh v)
      (ensures U64.v v >= U64.v mword /\
               U64.v v < heap_size /\
               U64.v v % U64.v mword == 0)
      (decreases Seq.length mh)
  =
  if Seq.length mh = 0 then
    assert False
  else begin
    let c = Seq.head mh in
    if MH.pointer_in_chunk c v then begin
      assert (U64.v v >= MH.chunk_start c + U64.v mword);
      assert (U64.v v < MH.chunk_end c);
      assert (MH.chunk_end c <= heap_size)
    end else
      chunked_is_pointer_field_is_obj_addr (Seq.tail mh) v
  end

let chunked_pointer_field_as_obj_addr
    (mh: MH.major_heap)
    (v: U64.t{chunked_is_pointer_field mh v})
  : GTot obj_addr
  =
  chunked_is_pointer_field_is_obj_addr mh v;
  v

let chunked_pointer_field_as_obj_addr_step
    (mh: MH.major_heap)
    (v: U64.t{chunked_is_pointer_field mh v})
  : Lemma (chunked_pointer_field_as_obj_addr mh v == v)
  = ()

let chunked_parent_closure_addr_nat
    (infix_obj: obj_addr)
    (mh: MH.major_heap)
  : GTot int
  =
  U64.v infix_obj - 8 -
  (U64.v (ChunkedSweepDefs.chunked_wosize_of_object mh infix_obj) * 8)

let chunked_parent_closure_addr_nat_step
    (infix_obj: obj_addr)
    (mh: MH.major_heap)
  : Lemma
      (chunked_parent_closure_addr_nat infix_obj mh ==
       U64.v infix_obj - 8 -
       (U64.v (ChunkedSweepDefs.chunked_wosize_of_object mh infix_obj) * 8))
  = ()

let chunked_resolve_object
    (mh: MH.major_heap)
    (addr: obj_addr)
  : GTot obj_addr
  =
  if ChunkedSweepDefs.chunked_is_infix mh addr then
    let p = chunked_parent_closure_addr_nat addr mh in
    if p >= 8 && p < heap_size && p % 8 = 0 then
      let parent : obj_addr = U64.uint_to_t p in
      if chunked_is_pointer_field mh parent then parent else addr
    else addr
  else addr

let chunked_is_no_scan
    (mh: MH.major_heap)
    (obj: obj_addr)
  : GTot bool
  =
  U64.gte (ChunkedSweepDefs.chunked_tag_of_object mh obj) Obj.no_scan_tag

let chunked_is_no_scan_step (mh: MH.major_heap) (obj: obj_addr)
  : Lemma
      (chunked_is_no_scan mh obj ==
       U64.gte (ChunkedSweepDefs.chunked_tag_of_object mh obj) Obj.no_scan_tag)
  = ()

let chunked_make_gray (mh: MH.major_heap) (obj: obj_addr) : GTot MH.major_heap =
  ChunkedSweepDefs.chunked_set_object_color mh obj Header.Gray

let chunked_make_black (mh: MH.major_heap) (obj: obj_addr) : GTot MH.major_heap =
  ChunkedSweepDefs.chunked_set_object_color mh obj Header.Black

let rec chunked_push_children
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
  : GTot (MH.major_heap & Seq.seq obj_addr)
    (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then (mh, st)
  else
    let v = chunked_get_field mh obj i in
    let (mh', st') =
      if chunked_is_pointer_field mh v then begin
        let child_raw = chunked_pointer_field_as_obj_addr mh v in
        let child = chunked_resolve_object mh child_raw in
        if ChunkedSweepDefs.chunked_is_white mh child then
          (chunked_make_gray mh child, Seq.cons child st)
        else
          (mh, st)
      end else
        (mh, st)
    in
    if U64.v i < U64.v ws then
      chunked_push_children mh' st' obj (U64.add i 1UL) ws
    else
      (mh', st')

let chunked_mark_step
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
  : GTot (MH.major_heap & Seq.seq obj_addr)
  =
  if Seq.length st = 0 then (mh, st)
  else
    let obj = Seq.head st in
    let st' = Seq.tail st in
    let mh' = chunked_make_black mh obj in
    let ws = ChunkedSweepDefs.chunked_wosize_of_object mh obj in
    if chunked_is_no_scan mh obj then
      (mh', st')
    else
      chunked_push_children mh' st' obj 1UL ws

let rec chunked_mark_aux
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (fuel: nat)
  : GTot MH.major_heap
    (decreases fuel)
  =
  if Seq.length st = 0 then mh
  else if fuel = 0 then mh
  else begin
    assert (fuel > 0);
    let (mh', st') = chunked_mark_step mh st in
    chunked_mark_aux mh' st' (fuel - 1)
  end

let chunked_mark
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
  : GTot MH.major_heap
  =
  chunked_mark_aux mh st (heap_size / U64.v mword)

let chunked_mark_equation
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
  : Lemma
      (chunked_mark mh st ==
       chunked_mark_aux mh st (heap_size / U64.v mword))
  = ()

let chunked_make_gray_step (mh: MH.major_heap) (obj: obj_addr)
  : Lemma
      (chunked_make_gray mh obj ==
       ChunkedSweepDefs.chunked_set_object_color mh obj Header.Gray)
  = ()

let chunked_make_black_step (mh: MH.major_heap) (obj: obj_addr)
  : Lemma
      (chunked_make_black mh obj ==
       ChunkedSweepDefs.chunked_set_object_color mh obj Header.Black)
  = ()

let chunked_resolve_non_infix (mh: MH.major_heap) (addr: obj_addr)
  : Lemma
      (requires ~(ChunkedSweepDefs.chunked_is_infix mh addr))
      (ensures chunked_resolve_object mh addr == addr)
  = ()

let chunked_resolve_infix_valid_active (mh: MH.major_heap) (addr: obj_addr)
  : Lemma
      (requires
        ChunkedSweepDefs.chunked_is_infix mh addr /\
        (let p = chunked_parent_closure_addr_nat addr mh in
         p >= 8 /\ p < heap_size /\ p % 8 == 0 /\
         chunked_is_pointer_field mh (U64.uint_to_t p)))
      (ensures
        chunked_resolve_object mh addr ==
        U64.uint_to_t (chunked_parent_closure_addr_nat addr mh))
  = ()

let chunked_push_children_done
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
  : Lemma
      (requires U64.v i > U64.v ws)
      (ensures chunked_push_children mh st obj i ws == (mh, st))
  = ()

let chunked_push_children_step
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
  : Lemma
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
  =
  let v = chunked_get_field mh obj i in
  if chunked_is_pointer_field mh v then
    chunked_is_pointer_field_is_obj_addr mh v

let chunked_mark_step_empty (mh: MH.major_heap) (st: Seq.seq obj_addr)
  : Lemma
      (requires Seq.length st = 0)
      (ensures chunked_mark_step mh st == (mh, st))
  = ()

let chunked_mark_step_no_scan (mh: MH.major_heap) (st: Seq.seq obj_addr)
  : Lemma
      (requires Seq.length st > 0 /\
                chunked_is_no_scan mh (Seq.head st))
      (ensures
        (let obj = Seq.head st in
         let st' = Seq.tail st in
         chunked_mark_step mh st == (chunked_make_black mh obj, st')))
  = ()

let chunked_mark_step_scan (mh: MH.major_heap) (st: Seq.seq obj_addr)
  : Lemma
      (requires Seq.length st > 0 /\
                ~(chunked_is_no_scan mh (Seq.head st)))
      (ensures
        (let obj = Seq.head st in
         let st' = Seq.tail st in
         let mh' = chunked_make_black mh obj in
         let ws = ChunkedSweepDefs.chunked_wosize_of_object mh obj in
         chunked_mark_step mh st ==
         chunked_push_children mh' st' obj 1UL ws))
  = ()

let chunked_mark_aux_empty
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (fuel: nat)
  : Lemma
      (requires Seq.length st = 0)
      (ensures chunked_mark_aux mh st fuel == mh)
  = ()

let chunked_mark_aux_out_of_fuel
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
  : Lemma
      (ensures chunked_mark_aux mh st 0 == mh)
  = if Seq.length st = 0 then () else ()

let chunked_mark_aux_step
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (fuel: nat{fuel > 0})
  : Lemma
      (requires Seq.length st > 0)
      (ensures
        (let (mh', st') = chunked_mark_step mh st in
         chunked_mark_aux mh st fuel ==
         chunked_mark_aux mh' st' (fuel - 1)))
  = ()
