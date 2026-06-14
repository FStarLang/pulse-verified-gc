module GC.Spec.ChunkedMark.Preservation

module U64 = FStar.UInt64
module Seq = FStar.Seq
module SeqProps = FStar.Seq.Properties

open GC.Spec.Base
open GC.Spec.Heap

module Header = GC.Lib.Header
module MH = GC.Spec.MajorHeap
module Obj = GC.Spec.Object
module SpecMajorAlloc = GC.Spec.MajorAllocator
module MarkDefs = GC.Spec.ChunkedMark.Defs
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module SweepLive = GC.Spec.ChunkedSweepCoalesce.LivePreservation

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let nat_nonzero_pos (n: nat)
  : Lemma (requires n <> 0) (ensures n > 0)
  = ()

let stack_objects_in_major
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
  : GTot prop
  =
  forall (obj: obj_addr). Seq.mem obj st ==> Seq.mem obj (MH.major_objects mh)

let stack_objects_in_major_elim
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (obj: obj_addr)
  : Lemma
      (requires
        stack_objects_in_major mh st /\
        Seq.mem obj st)
      (ensures Seq.mem obj (MH.major_objects mh))
  = ()

let seq_tail_mem (#a:eqtype) (s: Seq.seq a) (x: a)
  : Lemma
      (requires Seq.length s > 0 /\ Seq.mem x (Seq.tail s))
      (ensures Seq.mem x s)
  =
  let hd = Seq.head s in
  let tl = Seq.tail s in
  assert (s == Seq.cons hd tl);
  SeqProps.lemma_mem_append (Seq.create 1 hd) tl

let stack_objects_in_major_tail
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        stack_objects_in_major mh st)
      (ensures stack_objects_in_major mh (Seq.tail st))
  =
  let each (obj: obj_addr)
    : Lemma
        (requires Seq.mem obj (Seq.tail st))
        (ensures Seq.mem obj (MH.major_objects mh))
    =
    seq_tail_mem st obj;
    stack_objects_in_major_elim mh st obj
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each)

let stack_objects_in_major_preserved_by_major_objects
    (mh mh': MH.major_heap)
    (st: Seq.seq obj_addr)
  : Lemma
      (requires
        stack_objects_in_major mh st /\
        MH.major_objects mh' == MH.major_objects mh)
      (ensures stack_objects_in_major mh' st)
  =
  let each (obj: obj_addr)
    : Lemma
        (requires Seq.mem obj st)
        (ensures Seq.mem obj (MH.major_objects mh'))
    =
    stack_objects_in_major_elim mh st obj;
    assert (MH.major_objects mh' == MH.major_objects mh)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each)

let color_member_read_witness
    (mh: MH.major_heap)
    (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        (match SweepDefs.chunked_read_header mh obj with
         | Some hdr ->
           let idx = MH.lookup_chunk_index_value mh (hd_address obj) in
           idx < Seq.length mh /\
           MH.lookup_chunk_index mh (hd_address obj) == Some idx /\
           MH.word_in_chunk (Seq.index mh idx) (hd_address obj) /\
           MH.read_word_in_chunk (Seq.index mh idx) (hd_address obj) == hdr
         | None -> False))
  =
  let hd = hd_address obj in
  SweepDefs.chunked_read_header_step mh obj;
  MH.major_objects_member_header_read_some mh obj;
  match MH.read_word_in_major mh hd with
  | None -> assert False
  | Some hdr ->
    assert (SweepDefs.chunked_read_header mh obj == Some hdr);
    MH.read_word_in_major_lookup_index mh hd hdr;
    let idx = MH.lookup_chunk_index_value mh hd in
    assert (idx < Seq.length mh);
    assert (MH.lookup_chunk_index mh hd == Some idx);
    assert (MH.word_in_chunk (Seq.index mh idx) hd);
    assert (MH.read_word_in_chunk (Seq.index mh idx) hd == hdr)

let chunked_set_object_color_member_preserves_major_objects
    (mh: MH.major_heap)
    (obj: obj_addr)
    (color: Header.color_sem)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        MH.major_objects
          (SweepDefs.chunked_set_object_color mh obj color) ==
        MH.major_objects mh)
  =
  color_member_read_witness mh obj;
  match SweepDefs.chunked_read_header mh obj with
  | None -> assert False
  | Some hdr ->
    let idx = MH.lookup_chunk_index_value mh (hd_address obj) in
    SweepLive.chunked_set_object_color_preserves_major_objects
      mh idx obj color hdr

let chunked_make_gray_preserves_major_objects
    (mh: MH.major_heap)
    (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        MH.major_objects (MarkDefs.chunked_make_gray mh obj) ==
        MH.major_objects mh)
  =
  MarkDefs.chunked_make_gray_step mh obj;
  chunked_set_object_color_member_preserves_major_objects mh obj Header.Gray

let chunked_make_black_preserves_major_objects
    (mh: MH.major_heap)
    (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        MH.major_objects (MarkDefs.chunked_make_black mh obj) ==
        MH.major_objects mh)
  =
  MarkDefs.chunked_make_black_step mh obj;
  chunked_set_object_color_member_preserves_major_objects mh obj Header.Black

let chunked_set_object_color_member_preserves_well_formed
    (mh: MH.major_heap)
    (obj: obj_addr)
    (color: Header.color_sem)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        MH.well_formed_major_heap
          (SweepDefs.chunked_set_object_color mh obj color))
  =
  color_member_read_witness mh obj;
  match SweepDefs.chunked_read_header mh obj with
  | None -> assert False
  | Some hdr ->
    let hd = hd_address obj in
    let idx = MH.lookup_chunk_index_value mh hd in
    let new_hdr = Obj.colorHeader hdr color in
    SweepDefs.chunked_set_object_color_some mh obj color hdr;
    MH.write_word_in_major_at_lookup_index mh hd new_hdr idx;
    MH.write_word_at_index_preserves_wf mh hd new_hdr idx;
    let mh' =
      Seq.upd mh idx
        (MH.write_word_in_chunk (Seq.index mh idx) hd new_hdr) in
    SpecMajorAlloc.major_write_word_or_same_some mh mh' hd new_hdr

let chunked_make_gray_preserves_well_formed
    (mh: MH.major_heap)
    (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        MH.well_formed_major_heap
          (MarkDefs.chunked_make_gray mh obj))
  =
  MarkDefs.chunked_make_gray_step mh obj;
  chunked_set_object_color_member_preserves_well_formed mh obj Header.Gray

let chunked_make_black_preserves_well_formed
    (mh: MH.major_heap)
    (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        MH.well_formed_major_heap
          (MarkDefs.chunked_make_black mh obj))
  =
  MarkDefs.chunked_make_black_step mh obj;
  chunked_set_object_color_member_preserves_well_formed mh obj Header.Black

let rec chunked_push_children_preservation_ready
    (mh: MH.major_heap)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
  : Tot prop
    (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then True
  else
    let v = MarkDefs.chunked_get_field mh obj i in
    let mh' =
      if MarkDefs.chunked_is_pointer_field mh v then
        let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
        let child = MarkDefs.chunked_resolve_object mh child_raw in
        if SweepDefs.chunked_is_white mh child then
          MarkDefs.chunked_make_gray mh child
        else
          mh
      else
        mh in
    (if MarkDefs.chunked_is_pointer_field mh v then
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      let child = MarkDefs.chunked_resolve_object mh child_raw in
      SweepDefs.chunked_is_white mh child ==>
        Seq.mem child (MH.major_objects mh)
     else
      True) /\
    (if U64.v i < U64.v ws then
      chunked_push_children_preservation_ready
        mh' obj (U64.add i 1UL) ws
     else
      True)

let rec chunked_push_children_preserves_major_objects
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_push_children_preservation_ready mh obj i ws)
      (ensures
        (let (mh', _) = MarkDefs.chunked_push_children mh st obj i ws in
         MH.major_objects mh' == MH.major_objects mh))
      (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then
    MarkDefs.chunked_push_children_done mh st obj i ws
  else begin
    MarkDefs.chunked_push_children_step mh st obj i ws;
    let v = MarkDefs.chunked_get_field mh obj i in
    if MarkDefs.chunked_is_pointer_field mh v then begin
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      let child = MarkDefs.chunked_resolve_object mh child_raw in
      if SweepDefs.chunked_is_white mh child then begin
        assert (Seq.mem child (MH.major_objects mh));
        chunked_make_gray_preserves_major_objects mh child;
        chunked_make_gray_preserves_well_formed mh child;
        if U64.v i < U64.v ws then
          chunked_push_children_preserves_major_objects
            (MarkDefs.chunked_make_gray mh child)
            (Seq.cons child st)
            obj (U64.add i 1UL) ws
      end else if U64.v i < U64.v ws then
        chunked_push_children_preserves_major_objects
          mh st obj (U64.add i 1UL) ws
    end else if U64.v i < U64.v ws then
      chunked_push_children_preserves_major_objects
        mh st obj (U64.add i 1UL) ws
  end

let rec chunked_push_children_preserves_well_formed
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_push_children_preservation_ready mh obj i ws)
      (ensures
        (let (mh', _) = MarkDefs.chunked_push_children mh st obj i ws in
         MH.well_formed_major_heap mh'))
      (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then
    MarkDefs.chunked_push_children_done mh st obj i ws
  else begin
    MarkDefs.chunked_push_children_step mh st obj i ws;
    let v = MarkDefs.chunked_get_field mh obj i in
    if MarkDefs.chunked_is_pointer_field mh v then begin
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      let child = MarkDefs.chunked_resolve_object mh child_raw in
      if SweepDefs.chunked_is_white mh child then begin
        assert (Seq.mem child (MH.major_objects mh));
        chunked_make_gray_preserves_well_formed mh child;
        if U64.v i < U64.v ws then
          chunked_push_children_preserves_well_formed
            (MarkDefs.chunked_make_gray mh child)
            (Seq.cons child st)
            obj (U64.add i 1UL) ws
      end else if U64.v i < U64.v ws then
        chunked_push_children_preserves_well_formed
          mh st obj (U64.add i 1UL) ws
    end else if U64.v i < U64.v ws then
      chunked_push_children_preserves_well_formed
        mh st obj (U64.add i 1UL) ws
  end

let chunked_mark_step_empty_preserves_major_objects
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
  : Lemma
      (requires Seq.length st = 0)
      (ensures
        (let (mh', _) = MarkDefs.chunked_mark_step mh st in
         MH.major_objects mh' == MH.major_objects mh))
  =
  MarkDefs.chunked_mark_step_empty mh st

let chunked_mark_step_empty_preserves_well_formed
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st = 0 /\
        MH.well_formed_major_heap mh)
      (ensures
        (let (mh', _) = MarkDefs.chunked_mark_step mh st in
         MH.well_formed_major_heap mh'))
  =
  MarkDefs.chunked_mark_step_empty mh st

let chunked_mark_step_empty_preserves_stack_objects
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st = 0 /\
        stack_objects_in_major mh st)
      (ensures
        (let (mh', st') = MarkDefs.chunked_mark_step mh st in
         stack_objects_in_major mh' st'))
  =
  MarkDefs.chunked_mark_step_empty mh st

let chunked_mark_step_no_scan_preserves_major_objects
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        Seq.mem (Seq.head st) (MH.major_objects mh) /\
        MarkDefs.chunked_is_no_scan mh (Seq.head st))
      (ensures
        (let (mh', _) = MarkDefs.chunked_mark_step mh st in
         MH.major_objects mh' == MH.major_objects mh))
  =
  let obj = Seq.head st in
  MarkDefs.chunked_mark_step_no_scan mh st;
  chunked_make_black_preserves_major_objects mh obj

let chunked_mark_step_no_scan_preserves_well_formed
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        Seq.mem (Seq.head st) (MH.major_objects mh) /\
        MarkDefs.chunked_is_no_scan mh (Seq.head st))
      (ensures
        (let (mh', _) = MarkDefs.chunked_mark_step mh st in
         MH.well_formed_major_heap mh'))
  =
  let obj = Seq.head st in
  MarkDefs.chunked_mark_step_no_scan mh st;
  chunked_make_black_preserves_well_formed mh obj

let chunked_mark_step_no_scan_preserves_stack_objects
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        stack_objects_in_major mh st /\
        MarkDefs.chunked_is_no_scan mh (Seq.head st))
      (ensures
        (let (mh', st') = MarkDefs.chunked_mark_step mh st in
         stack_objects_in_major mh' st'))
  =
  let obj = Seq.head st in
  let st' = Seq.tail st in
  stack_objects_in_major_elim mh st obj;
  MarkDefs.chunked_mark_step_no_scan mh st;
  chunked_make_black_preserves_major_objects mh obj;
  stack_objects_in_major_tail mh st;
  stack_objects_in_major_preserved_by_major_objects
    mh (MarkDefs.chunked_make_black mh obj) st'

let chunked_mark_step_scan_preserves_major_objects
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        Seq.mem (Seq.head st) (MH.major_objects mh) /\
        ~(MarkDefs.chunked_is_no_scan mh (Seq.head st)) /\
        (let obj = Seq.head st in
         let mh' = MarkDefs.chunked_make_black mh obj in
         let ws = SweepDefs.chunked_wosize_of_object mh obj in
         chunked_push_children_preservation_ready mh' obj 1UL ws))
      (ensures
        (let (mh', _) = MarkDefs.chunked_mark_step mh st in
         MH.major_objects mh' == MH.major_objects mh))
  =
  let obj = Seq.head st in
  let st' = Seq.tail st in
  let mh_black = MarkDefs.chunked_make_black mh obj in
  let ws = SweepDefs.chunked_wosize_of_object mh obj in
  MarkDefs.chunked_mark_step_scan mh st;
  chunked_make_black_preserves_major_objects mh obj;
  chunked_make_black_preserves_well_formed mh obj;
  chunked_push_children_preserves_major_objects mh_black st' obj 1UL ws

let chunked_mark_step_scan_preserves_well_formed
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        Seq.mem (Seq.head st) (MH.major_objects mh) /\
        ~(MarkDefs.chunked_is_no_scan mh (Seq.head st)) /\
        (let obj = Seq.head st in
         let mh' = MarkDefs.chunked_make_black mh obj in
         let ws = SweepDefs.chunked_wosize_of_object mh obj in
         chunked_push_children_preservation_ready mh' obj 1UL ws))
      (ensures
        (let (mh', _) = MarkDefs.chunked_mark_step mh st in
         MH.well_formed_major_heap mh'))
  =
  let obj = Seq.head st in
  let st' = Seq.tail st in
  let mh_black = MarkDefs.chunked_make_black mh obj in
  let ws = SweepDefs.chunked_wosize_of_object mh obj in
  MarkDefs.chunked_mark_step_scan mh st;
  chunked_make_black_preserves_well_formed mh obj;
  chunked_push_children_preserves_well_formed mh_black st' obj 1UL ws

let chunked_mark_step_preservation_ready
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
  : GTot prop
  =
  if Seq.length st = 0 then True
  else
    let obj = Seq.head st in
    Seq.mem obj (MH.major_objects mh) /\
    (if MarkDefs.chunked_is_no_scan mh obj then
      True
     else
      let mh' = MarkDefs.chunked_make_black mh obj in
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      chunked_push_children_preservation_ready mh' obj 1UL ws)

let chunked_mark_step_preserves_major_objects
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_step_preservation_ready mh st)
      (ensures
        (let (mh', _) = MarkDefs.chunked_mark_step mh st in
         MH.major_objects mh' == MH.major_objects mh))
  =
  if Seq.length st = 0 then
    chunked_mark_step_empty_preserves_major_objects mh st
  else begin
    assert (Seq.length st <> 0);
    nat_nonzero_pos (Seq.length st);
    let obj = Seq.head st in
    assert (Seq.length st > 0);
    assert (obj == Seq.head st);
    assert (Seq.mem obj (MH.major_objects mh));
    if MarkDefs.chunked_is_no_scan mh obj then begin
      assert (MarkDefs.chunked_is_no_scan mh (Seq.head st));
      chunked_mark_step_no_scan_preserves_major_objects mh st
    end else begin
      let mh' = MarkDefs.chunked_make_black mh obj in
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      assert (~(MarkDefs.chunked_is_no_scan mh (Seq.head st)));
      assert (chunked_push_children_preservation_ready mh' obj 1UL ws);
      chunked_mark_step_scan_preserves_major_objects mh st
    end
  end

let chunked_mark_step_preserves_well_formed
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_step_preservation_ready mh st)
      (ensures
        (let (mh', _) = MarkDefs.chunked_mark_step mh st in
         MH.well_formed_major_heap mh'))
  =
  if Seq.length st = 0 then
    chunked_mark_step_empty_preserves_well_formed mh st
  else begin
    assert (Seq.length st <> 0);
    nat_nonzero_pos (Seq.length st);
    let obj = Seq.head st in
    assert (Seq.length st > 0);
    assert (obj == Seq.head st);
    assert (Seq.mem obj (MH.major_objects mh));
    if MarkDefs.chunked_is_no_scan mh obj then begin
      assert (MarkDefs.chunked_is_no_scan mh (Seq.head st));
      chunked_mark_step_no_scan_preserves_well_formed mh st
    end else begin
      let mh' = MarkDefs.chunked_make_black mh obj in
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      assert (~(MarkDefs.chunked_is_no_scan mh (Seq.head st)));
      assert (chunked_push_children_preservation_ready mh' obj 1UL ws);
      chunked_mark_step_scan_preserves_well_formed mh st
    end
  end
