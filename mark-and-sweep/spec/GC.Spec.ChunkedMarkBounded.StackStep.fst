module GC.Spec.ChunkedMarkBounded.StackStep

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base

module Header = GC.Lib.Header
module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module MarkDefs = GC.Spec.ChunkedMark.Defs
module MarkPres = GC.Spec.ChunkedMark.Preservation
module SpecMark = GC.Spec.Mark
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module BReady = GC.Spec.ChunkedMarkBounded.TargetReady
module SeqMem = GC.Spec.SeqMemLemmas

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let seq_tail_mem (#a:eqtype) (s: Seq.seq a) (x: a)
  : Lemma
      (requires Seq.length s > 0 /\ Seq.mem x (Seq.tail s))
      (ensures Seq.mem x s)
  =
  let hd = Seq.head s in
  let tl = Seq.tail s in
  assert (s == Seq.cons hd tl);
  FStar.Seq.Properties.lemma_mem_append (Seq.create 1 hd) tl

let chunked_is_white_not_gray
    (mh: MH.major_heap)
    (obj: obj_addr)
  : Lemma
      (requires SweepDefs.chunked_is_white mh obj)
      (ensures ~(BDefs.chunked_is_gray mh obj))
  =
  BDefs.chunked_is_gray_step mh obj;
  if BDefs.chunked_is_gray mh obj then begin
    SweepDefs.chunked_is_white_read_header mh obj;
    SweepDefs.chunked_color_of_object_elim mh obj Header.Gray;
    match SweepDefs.chunked_read_header mh obj with
    | None -> assert False
    | Some hdr ->
      assert (SweepDefs.chunked_color_of_object mh obj == Some Header.Gray);
      assert (GC.Spec.Object.getColor hdr == Header.Gray);
      assert (GC.Spec.Object.getColor hdr == Header.White);
      assert False
  end

let stack_gray_to_color
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (target: obj_addr)
  : Lemma
      (requires
        BReady.chunked_stack_points_to_gray mh st /\
        Seq.mem target st)
      (ensures
        SweepDefs.chunked_color_of_object mh target == Some Header.Gray)
  =
  BReady.chunked_stack_points_to_gray_elim mh st target;
  BDefs.chunked_is_gray_step mh target

let make_gray_preserves_stack_gray
    (mh: MH.major_heap)
    (child: obj_addr)
    (st: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem child (MH.major_objects mh) /\
        BReady.chunked_stack_points_to_gray mh st)
      (ensures
        BReady.chunked_stack_points_to_gray
          (MarkDefs.chunked_make_gray mh child) st)
  =
  let each (target: obj_addr)
    : Lemma
        (requires Seq.mem target st)
        (ensures BDefs.chunked_is_gray (MarkDefs.chunked_make_gray mh child) target)
    =
    if target = child then begin
      MarkPres.chunked_make_gray_makes_gray mh child;
      BDefs.chunked_is_gray_step (MarkDefs.chunked_make_gray mh child) target
    end else begin
      stack_gray_to_color mh st target;
      MarkPres.chunked_make_gray_preserves_other_gray mh child target;
      BDefs.chunked_is_gray_step (MarkDefs.chunked_make_gray mh child) target
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each);
  BReady.chunked_stack_points_to_gray_intro (MarkDefs.chunked_make_gray mh child) st

let make_black_preserves_tail_stack_gray
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        SpecMark.stack_no_dups st /\
        BReady.chunked_stack_points_to_gray mh st)
      (ensures
        BReady.chunked_stack_points_to_gray
          (MarkDefs.chunked_make_black mh (Seq.head st)) (Seq.tail st))
  =
  let head = Seq.head st in
  let tail = Seq.tail st in
  let each (target: obj_addr)
    : Lemma
        (requires Seq.mem target tail)
        (ensures BDefs.chunked_is_gray (MarkDefs.chunked_make_black mh head) target)
    =
    assert (~(Seq.mem head tail));
    assert (target <> head);
    seq_tail_mem st target;
    stack_gray_to_color mh st target;
    MarkPres.chunked_make_black_preserves_other_gray mh head target;
    BDefs.chunked_is_gray_step (MarkDefs.chunked_make_black mh head) target
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each);
  BReady.chunked_stack_points_to_gray_intro
    (MarkDefs.chunked_make_black mh head) tail

let stack_no_dups_tail
    (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        SpecMark.stack_no_dups st)
      (ensures SpecMark.stack_no_dups (Seq.tail st))
  = ()

let rec chunked_push_children_bounded_preserves_bounded_stack_props
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
    (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_push_children_bounded_preservation_ready mh obj i ws /\
        BReady.chunked_bounded_stack_props mh st)
      (ensures
        (let (mh', st') =
          BDefs.chunked_push_children_bounded mh st obj i ws cap in
         BReady.chunked_bounded_stack_props mh' st'))
      (decreases (U64.v ws - U64.v i))
  =
  BReady.chunked_bounded_stack_props_objects mh st;
  BReady.chunked_bounded_stack_props_gray mh st;
  BReady.chunked_bounded_stack_props_no_dups mh st;
  if U64.v i > U64.v ws then
    BDefs.chunked_push_children_bounded_done mh st obj i ws cap
  else begin
    assert (U64.v i <= U64.v ws);
    BDefs.chunked_push_children_bounded_step mh st obj i ws cap;
    let v = MarkDefs.chunked_get_field mh obj i in
    if MarkDefs.chunked_is_pointer_field mh v then begin
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      let child = MarkDefs.chunked_resolve_object mh child_raw in
      if SweepDefs.chunked_is_white mh child then begin
        let mh_gray = MarkDefs.chunked_make_gray mh child in
        BPres.chunked_push_children_bounded_preservation_ready_child
          mh obj i ws;
        MarkPres.chunked_make_gray_preserves_major_objects mh child;
        MarkPres.chunked_make_gray_preserves_well_formed mh child;
        MarkPres.stack_objects_in_major_preserved_by_major_objects
          mh mh_gray st;
        make_gray_preserves_stack_gray mh child st;
        BReady.chunked_bounded_stack_props_intro mh_gray st;
        if Seq.mem child st then begin
          BReady.chunked_stack_points_to_gray_elim mh st child;
          chunked_is_white_not_gray mh child;
          assert False
        end;
        let st' =
          if Seq.length st < cap then begin
            BReady.chunked_stack_objects_in_major_cons mh_gray child st;
            MarkPres.chunked_make_gray_makes_gray mh child;
            BDefs.chunked_is_gray_step mh_gray child;
            BReady.chunked_stack_points_to_gray_cons mh_gray child st;
            assert (Seq.head (Seq.cons child st) == child);
            assert (Seq.equal (Seq.tail (Seq.cons child st)) st);
            Seq.lemma_eq_elim (Seq.tail (Seq.cons child st)) st;
            assert (Seq.tail (Seq.cons child st) == st);
            assert (~ (Seq.mem
              (Seq.head (Seq.cons child st))
              (Seq.tail (Seq.cons child st))));
            assert (SpecMark.stack_no_dups (Seq.tail (Seq.cons child st)));
            assert (SpecMark.stack_no_dups (Seq.cons child st));
            BReady.chunked_bounded_stack_props_intro mh_gray (Seq.cons child st);
            Seq.cons child st
          end else
            st in
        if U64.v i < U64.v ws then
          BPres.chunked_push_children_bounded_preservation_ready_next
            mh obj i ws;
        if U64.v i < U64.v ws then
          chunked_push_children_bounded_preserves_bounded_stack_props
            mh_gray st' obj (U64.add i 1UL) ws cap
      end else if U64.v i < U64.v ws then begin
        BPres.chunked_push_children_bounded_preservation_ready_next
          mh obj i ws;
        chunked_push_children_bounded_preserves_bounded_stack_props
          mh st obj (U64.add i 1UL) ws cap
      end
    end else if U64.v i < U64.v ws then begin
      BPres.chunked_push_children_bounded_preservation_ready_next
        mh obj i ws;
      chunked_push_children_bounded_preserves_bounded_stack_props
        mh st obj (U64.add i 1UL) ws cap
    end
  end

let chunked_mark_step_bounded_preserves_bounded_stack_props
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_step_bounded_preservation_ready mh st cap /\
        BReady.chunked_bounded_stack_props mh st)
      (ensures
        (let (mh', st') =
          BDefs.chunked_mark_step_bounded mh st cap in
         BReady.chunked_bounded_stack_props mh' st'))
  =
  let obj = Seq.head st in
  let tail = Seq.tail st in
  BReady.chunked_bounded_stack_props_objects mh st;
  BReady.chunked_bounded_stack_props_gray mh st;
  BReady.chunked_bounded_stack_props_no_dups mh st;
  BReady.chunked_bounded_stack_head mh st;
  MarkPres.stack_objects_in_major_tail mh st;
  stack_no_dups_tail st;
  if MarkDefs.chunked_is_no_scan mh obj then begin
    BDefs.chunked_mark_step_bounded_no_scan mh st cap;
    MarkPres.chunked_make_black_preserves_major_objects mh obj;
    MarkPres.stack_objects_in_major_preserved_by_major_objects
      mh (MarkDefs.chunked_make_black mh obj) tail;
    make_black_preserves_tail_stack_gray mh st;
    BReady.chunked_bounded_stack_props_intro
      (MarkDefs.chunked_make_black mh obj) tail
  end else begin
    let mh_black = MarkDefs.chunked_make_black mh obj in
    let ws = SweepDefs.chunked_wosize_of_object mh obj in
    BPres.chunked_mark_step_bounded_preservation_ready_scan mh st cap;
    BDefs.chunked_mark_step_bounded_scan mh st cap;
    MarkPres.chunked_make_black_preserves_major_objects mh obj;
    MarkPres.chunked_make_black_preserves_well_formed mh obj;
    MarkPres.stack_objects_in_major_preserved_by_major_objects
      mh mh_black tail;
    make_black_preserves_tail_stack_gray mh st;
    BReady.chunked_bounded_stack_props_intro mh_black tail;
    chunked_push_children_bounded_preserves_bounded_stack_props
      mh_black tail obj 1UL ws cap
  end
