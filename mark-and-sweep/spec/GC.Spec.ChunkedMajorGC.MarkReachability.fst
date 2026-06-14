module GC.Spec.ChunkedMajorGC.MarkReachability

module Seq = FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module MarkPres = GC.Spec.ChunkedMark.Preservation
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module BReady = GC.Spec.ChunkedMarkBounded.TargetReady
module RangePres = GC.Spec.ChunkedSweepCoalesce.RangePreservation
module ChunkedMajorGraph = GC.Spec.ChunkedMajorGC.Graph
module Reach = GC.Spec.ChunkedMajorGC.Reachability

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let chunked_stack_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  : prop
  =
  forall (obj: obj_addr).
    Seq.mem obj st ==>
    Reach.chunked_major_reachable_from_roots mh roots obj

let chunked_stack_reachable_from_roots_intro
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        (forall (obj: obj_addr).
          Seq.mem obj st ==>
          Reach.chunked_major_reachable_from_roots mh roots obj))
      (ensures chunked_stack_reachable_from_roots mh roots st)
  = ()

let chunked_stack_reachable_from_roots_elim
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  : Lemma
      (requires
        chunked_stack_reachable_from_roots mh roots st /\
        Seq.mem obj st)
      (ensures Reach.chunked_major_reachable_from_roots mh roots obj)
  = ()

let chunked_stack_reachable_from_roots_empty
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (ensures
        chunked_stack_reachable_from_roots mh roots Seq.empty)
  =
  let one (obj: obj_addr)
    : Lemma
        (requires Seq.mem obj Seq.empty)
        (ensures Reach.chunked_major_reachable_from_roots mh roots obj)
    = ()
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires one)

let chunked_stack_reachable_from_roots_cons
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (obj: obj_addr)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Reach.chunked_major_reachable_from_roots mh roots obj /\
        chunked_stack_reachable_from_roots mh roots st)
      (ensures
        chunked_stack_reachable_from_roots mh roots (Seq.cons obj st))
  =
  let one (target: obj_addr)
    : Lemma
        (requires Seq.mem target (Seq.cons obj st))
        (ensures Reach.chunked_major_reachable_from_roots mh roots target)
    =
    GC.Spec.Fields.mem_cons_lemma target obj st;
    if target = obj then
      ()
    else
      chunked_stack_reachable_from_roots_elim mh roots st target
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires one)

#push-options "--z3rlimit 5 --fuel 2 --ifuel 1 --split_queries always"
let chunked_gray_or_black_from_gray
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires BDefs.chunked_is_gray mh obj)
      (ensures BDefs.chunked_is_gray mh obj \/ SweepDefs.chunked_is_black mh obj)
  = ()
#pop-options

let chunked_stack_reachable_from_gray_black
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Reach.chunked_gray_black_reachable mh roots /\
        MarkPres.stack_objects_in_major mh st /\
        BReady.chunked_stack_points_to_gray mh st)
      (ensures chunked_stack_reachable_from_roots mh roots st)
  =
  let one (obj: obj_addr)
    : Lemma
        (requires Seq.mem obj st)
        (ensures Reach.chunked_major_reachable_from_roots mh roots obj)
    =
    MarkPres.stack_objects_in_major_elim mh st obj;
    BReady.chunked_stack_points_to_gray_elim mh st obj;
    assert (BDefs.chunked_is_gray mh obj);
    ChunkedMajorGraph.chunked_major_vertex_intro mh obj;
    chunked_gray_or_black_from_gray mh obj;
    Reach.chunked_gray_black_reachable_elim mh roots obj
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires one)

let chunked_rescan_objects_stack_reachable_from_gray_black
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (objs: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        Reach.chunked_gray_black_reachable mh roots /\
        MarkPres.stack_objects_in_major mh st /\
        BReady.chunked_stack_points_to_gray mh st /\
        (forall (obj: obj_addr).
          Seq.mem obj objs ==> Seq.mem obj (MH.major_objects mh)))
      (ensures
        chunked_stack_reachable_from_roots mh roots
          (BDefs.chunked_rescan_objects mh objs st cap))
  =
  BReady.chunked_rescan_objects_preserves_stack_objects_in_major
    mh objs st cap;
  BReady.chunked_rescan_objects_preserves_stack_gray
    mh objs st cap;
  chunked_stack_reachable_from_gray_black
    mh roots (BDefs.chunked_rescan_objects mh objs st cap)

let chunked_rescan_heap_stack_reachable_from_gray_black
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires Reach.chunked_gray_black_reachable mh roots)
      (ensures
        chunked_stack_reachable_from_roots mh roots
          (BDefs.chunked_rescan_heap mh Seq.empty cap))
  =
  BReady.chunked_rescan_heap_stack_objects_in_major mh cap;
  BReady.chunked_rescan_heap_stack_gray mh cap;
  chunked_stack_reachable_from_gray_black
    mh roots (BDefs.chunked_rescan_heap mh Seq.empty cap)

let chunked_resolved_pointer_field_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        Reach.chunked_major_reachable_from_roots mh roots obj /\
        U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj) /\
        (let v = MarkDefs.chunked_get_field mh obj i in
         MarkDefs.chunked_is_pointer_field mh v /\
         (let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
          let child = MarkDefs.chunked_resolve_object mh child_raw in
          child == child_raw /\
          ChunkedMajorGraph.chunked_major_vertex mh child)))
      (ensures
        (let v = MarkDefs.chunked_get_field mh obj i in
         let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
         let child = MarkDefs.chunked_resolve_object mh child_raw in
         Reach.chunked_major_reachable_from_roots mh roots child))
  =
  Reach.chunked_major_reachable_from_roots_vertex mh roots obj;
  let v = MarkDefs.chunked_get_field mh obj i in
  let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
  let child = MarkDefs.chunked_resolve_object mh child_raw in
  assert (child == child_raw);
  ChunkedMajorGraph.chunked_major_field_points_to_intro mh obj i child;
  Reach.chunked_major_reachable_from_roots_field mh roots obj i child

let chunked_non_infix_pointer_field_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        Reach.chunked_major_reachable_from_roots mh roots obj /\
        U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj) /\
        (let v = MarkDefs.chunked_get_field mh obj i in
         MarkDefs.chunked_is_pointer_field mh v /\
         (let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
          ~(SweepDefs.chunked_is_infix mh child_raw) /\
          ChunkedMajorGraph.chunked_major_vertex mh child_raw)))
      (ensures
        (let v = MarkDefs.chunked_get_field mh obj i in
         let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
         let child = MarkDefs.chunked_resolve_object mh child_raw in
         Reach.chunked_major_reachable_from_roots mh roots child))
  =
  let v = MarkDefs.chunked_get_field mh obj i in
  let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
  MarkDefs.chunked_resolve_non_infix mh child_raw;
  chunked_resolved_pointer_field_reachable_from_roots mh roots obj i

[@@"opaque_to_smt"]
let rec chunked_push_children_bounded_reachability_ready
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
      if SweepDefs.chunked_is_white mh child then
        ~(SweepDefs.chunked_is_infix mh child_raw) /\
        ChunkedMajorGraph.chunked_major_vertex mh child_raw
      else
        True
     else
      True) /\
    (if U64.v i < U64.v ws then
      chunked_push_children_bounded_reachability_ready
        mh' obj (U64.add i 1UL) ws
     else
      True)

#push-options "--z3rlimit 1 --fuel 0 --ifuel 0 --split_queries always"
let chunked_push_children_bounded_reachability_ready_child
    (mh: MH.major_heap)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
  : Lemma
      (requires
        U64.v i <= U64.v ws /\
        chunked_push_children_bounded_reachability_ready mh obj i ws /\
        (let v = MarkDefs.chunked_get_field mh obj i in
         MarkDefs.chunked_is_pointer_field mh v /\
         (let child_raw =
            MarkDefs.chunked_pointer_field_as_obj_addr mh v in
          let child = MarkDefs.chunked_resolve_object mh child_raw in
          SweepDefs.chunked_is_white mh child)))
      (ensures
        (let v = MarkDefs.chunked_get_field mh obj i in
         let child_raw =
           MarkDefs.chunked_pointer_field_as_obj_addr mh v in
         ~(SweepDefs.chunked_is_infix mh child_raw) /\
         ChunkedMajorGraph.chunked_major_vertex mh child_raw))
  =
  reveal_opaque (`%chunked_push_children_bounded_reachability_ready)
    (chunked_push_children_bounded_reachability_ready mh obj i ws);
  if U64.v i > U64.v ws then
    assert False
  else begin
    let v = MarkDefs.chunked_get_field mh obj i in
    let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
    let child = MarkDefs.chunked_resolve_object mh child_raw in
    assert (MarkDefs.chunked_is_pointer_field mh v);
    assert (SweepDefs.chunked_is_white mh child);
    assert
      (~(SweepDefs.chunked_is_infix mh child_raw) /\
       ChunkedMajorGraph.chunked_major_vertex mh child_raw)
  end

let chunked_push_children_bounded_reachability_ready_next
    (mh: MH.major_heap)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
  : Lemma
      (requires
        U64.v i <= U64.v ws /\
        U64.v i < U64.v ws /\
        chunked_push_children_bounded_reachability_ready mh obj i ws)
      (ensures
        (let v = MarkDefs.chunked_get_field mh obj i in
         let mh' =
           if MarkDefs.chunked_is_pointer_field mh v then
             let child_raw =
               MarkDefs.chunked_pointer_field_as_obj_addr mh v in
             let child =
               MarkDefs.chunked_resolve_object mh child_raw in
             if SweepDefs.chunked_is_white mh child then
               MarkDefs.chunked_make_gray mh child
             else
               mh
           else
             mh in
         chunked_push_children_bounded_reachability_ready
           mh' obj (U64.add i 1UL) ws))
  =
  reveal_opaque (`%chunked_push_children_bounded_reachability_ready)
    (chunked_push_children_bounded_reachability_ready mh obj i ws);
  if U64.v i > U64.v ws then
    assert False
  else
    ()
#pop-options

let chunked_make_gray_preserves_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (obj target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Reach.chunked_major_reachable_from_roots mh roots target)
      (ensures
        Reach.chunked_major_reachable_from_roots
          (MarkDefs.chunked_make_gray mh obj) roots target)
  =
  let mh' = MarkDefs.chunked_make_gray mh obj in
  MarkPres.chunked_make_gray_preserves_major_objects mh obj;
  MarkPres.chunked_make_gray_preserves_well_formed mh obj;
  MarkPres.chunked_make_gray_preserves_ranges mh obj;
  let live (x: obj_addr) : prop = ChunkedMajorGraph.chunked_major_vertex mh x in
  let fields (x: obj_addr)
    : Lemma
        (requires live x)
        (ensures ChunkedMajorGraph.chunked_major_field_preserved mh mh' x)
    =
    ChunkedMajorGraph.chunked_major_vertex_elim mh x;
    assert (Seq.mem x (MH.major_objects mh'));
    ChunkedMajorGraph.chunked_major_vertex_intro mh' x;
    MarkPres.chunked_make_gray_preserves_wosize_of_object mh obj x;
    let same_field (i: U64.t{U64.v i >= 1})
      : Lemma
          (requires
            U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh x))
          (ensures
            MarkDefs.chunked_get_field mh x i ==
            MarkDefs.chunked_get_field mh' x i)
      =
      MarkPres.chunked_make_gray_preserves_get_field mh obj x i
    in
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires same_field);
    ChunkedMajorGraph.chunked_major_field_preserved_intro mh mh' x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires fields);
  let pc (v: U64.t)
    : Lemma
        (MarkDefs.chunked_is_pointer_field mh v ==
         MarkDefs.chunked_is_pointer_field mh' v)
    =
    MarkDefs.chunked_is_pointer_field_step mh v;
    MarkDefs.chunked_is_pointer_field_step mh' v;
    RangePres.same_chunk_ranges_preserves_is_major_pointer mh mh' v
  in
  FStar.Classical.forall_intro pc;
  ChunkedMajorGraph.chunked_major_pointer_classification_preserved_intro mh mh';
  ChunkedMajorGraph.chunked_major_live_subgraph_preserved_from_fields
    mh mh' live;
  Reach.chunked_major_reachable_from_roots_preserved_by_live_subgraph
    mh mh' live roots target

let chunked_make_gray_preserves_stack_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (obj: obj_addr)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        chunked_stack_reachable_from_roots mh roots st)
      (ensures
        chunked_stack_reachable_from_roots
          (MarkDefs.chunked_make_gray mh obj) roots st)
  =
  let mh' = MarkDefs.chunked_make_gray mh obj in
  let one (target: obj_addr)
    : Lemma
        (requires Seq.mem target st)
        (ensures Reach.chunked_major_reachable_from_roots mh' roots target)
    =
    chunked_stack_reachable_from_roots_elim mh roots st target;
    chunked_make_gray_preserves_reachable_from_roots mh roots obj target
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires one)

let rec chunked_push_children_bounded_preserves_stack_reachable_from_roots
    (mh: MH.major_heap)
    (roots: Seq.seq obj_addr)
    (st: Seq.seq obj_addr)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
    (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_push_children_bounded_preservation_ready mh obj i ws /\
        chunked_push_children_bounded_reachability_ready mh obj i ws /\
        ws == SweepDefs.chunked_wosize_of_object mh obj /\
        Reach.chunked_major_reachable_from_roots mh roots obj /\
        chunked_stack_reachable_from_roots mh roots st)
      (ensures
        (let (mh', st') =
          BDefs.chunked_push_children_bounded mh st obj i ws cap in
         chunked_stack_reachable_from_roots mh' roots st'))
      (decreases (U64.v ws - U64.v i))
  =
  Reach.chunked_major_reachable_from_roots_vertex mh roots obj;
  ChunkedMajorGraph.chunked_major_vertex_elim mh obj;
  if U64.v i > U64.v ws then
    BDefs.chunked_push_children_bounded_done mh st obj i ws cap
  else begin
    assert (U64.v i <= U64.v ws);
    assert (U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj));
    BDefs.chunked_push_children_bounded_step mh st obj i ws cap;
    let v = MarkDefs.chunked_get_field mh obj i in
    if MarkDefs.chunked_is_pointer_field mh v then begin
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      let child = MarkDefs.chunked_resolve_object mh child_raw in
      if SweepDefs.chunked_is_white mh child then begin
        let mh_gray = MarkDefs.chunked_make_gray mh child in
        BPres.chunked_push_children_bounded_preservation_ready_child
          mh obj i ws;
        chunked_push_children_bounded_reachability_ready_child
          mh obj i ws;
        chunked_non_infix_pointer_field_reachable_from_roots
          mh roots obj i;
        MarkPres.chunked_make_gray_preserves_well_formed mh child;
        MarkPres.chunked_make_gray_preserves_wosize_of_object mh child obj;
        chunked_make_gray_preserves_reachable_from_roots
          mh roots child obj;
        chunked_make_gray_preserves_reachable_from_roots
          mh roots child child;
        chunked_make_gray_preserves_stack_reachable_from_roots
          mh roots child st;
        let st' =
          if Seq.length st < cap then begin
            chunked_stack_reachable_from_roots_cons
              mh_gray roots child st;
            Seq.cons child st
          end else
            st in
        if U64.v i < U64.v ws then begin
          BPres.chunked_push_children_bounded_preservation_ready_next
            mh obj i ws;
          chunked_push_children_bounded_reachability_ready_next
            mh obj i ws;
          assert (ws == SweepDefs.chunked_wosize_of_object mh_gray obj);
          chunked_push_children_bounded_preserves_stack_reachable_from_roots
            mh_gray roots st' obj (U64.add i 1UL) ws cap
        end
      end else if U64.v i < U64.v ws then begin
        BPres.chunked_push_children_bounded_preservation_ready_next
          mh obj i ws;
        chunked_push_children_bounded_reachability_ready_next
          mh obj i ws;
        chunked_push_children_bounded_preserves_stack_reachable_from_roots
          mh roots st obj (U64.add i 1UL) ws cap
      end
    end else if U64.v i < U64.v ws then begin
      BPres.chunked_push_children_bounded_preservation_ready_next
        mh obj i ws;
      chunked_push_children_bounded_reachability_ready_next
        mh obj i ws;
      chunked_push_children_bounded_preserves_stack_reachable_from_roots
        mh roots st obj (U64.add i 1UL) ws cap
    end
  end
