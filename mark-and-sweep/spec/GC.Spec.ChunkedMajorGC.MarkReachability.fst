module GC.Spec.ChunkedMajorGC.MarkReachability

module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module MarkPres = GC.Spec.ChunkedMark.Preservation
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BReady = GC.Spec.ChunkedMarkBounded.TargetReady
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

#push-options "--z3rlimit 1 --fuel 0 --ifuel 0 --split_queries always"
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
