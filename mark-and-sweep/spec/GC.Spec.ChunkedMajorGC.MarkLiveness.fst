module GC.Spec.ChunkedMajorGC.MarkLiveness

module Seq = FStar.Seq

open GC.Spec.Base

module Header = GC.Lib.Header
module Obj = GC.Spec.Object
module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module BStackReady = GC.Spec.ChunkedMarkBounded.StackReady
module ChunkedMajorGraph = GC.Spec.ChunkedMajorGC.Graph
module Reach = GC.Spec.ChunkedMajorGC.Reachability

let chunked_roots_gray_or_black
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : prop
  =
  forall (root: obj_addr).
    ChunkedMajorGraph.chunked_major_vertex mh root ==>
    Seq.mem root roots ==>
    BDefs.chunked_is_gray mh root \/
    SweepDefs.chunked_is_black mh root

#push-options "--z3rlimit 1 --fuel 0 --ifuel 0"
let chunked_roots_gray_or_black_elim
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (root: obj_addr)
  : Lemma
      (requires
        chunked_roots_gray_or_black mh roots /\
        ChunkedMajorGraph.chunked_major_vertex mh root /\
        Seq.mem root roots)
      (ensures
        BDefs.chunked_is_gray mh root \/
        SweepDefs.chunked_is_black mh root)
  =
  ()
#pop-options

let chunked_roots_black
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : prop
  =
  forall (root: obj_addr).
    ChunkedMajorGraph.chunked_major_vertex mh root ==>
    Seq.mem root roots ==>
    SweepDefs.chunked_is_black mh root

#push-options "--z3rlimit 1 --fuel 0 --ifuel 0"
let chunked_roots_black_elim
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (root: obj_addr)
  : Lemma
      (requires
        chunked_roots_black mh roots /\
        ChunkedMajorGraph.chunked_major_vertex mh root /\
        Seq.mem root roots)
      (ensures SweepDefs.chunked_is_black mh root)
  =
  ()
#pop-options

let chunked_no_gray_objects
  (mh: MH.major_heap)
  : prop
  =
  forall (obj: obj_addr).
    ChunkedMajorGraph.chunked_major_vertex mh obj ==>
    ~(BDefs.chunked_is_gray mh obj)

#push-options "--z3rlimit 1 --fuel 0 --ifuel 0"
let chunked_no_gray_objects_elim
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        chunked_no_gray_objects mh /\
        ChunkedMajorGraph.chunked_major_vertex mh obj)
      (ensures ~(BDefs.chunked_is_gray mh obj))
  =
  ()
#pop-options

let chunked_no_pointer_to_blue
  (mh: MH.major_heap)
  : prop
  =
  forall (src dst: obj_addr).
    ChunkedMajorGraph.chunked_major_edge mh src dst ==>
    ~(SweepDefs.chunked_is_blue mh src) ==>
    ~(SweepDefs.chunked_is_blue mh dst)

#push-options "--z3rlimit 1 --fuel 0 --ifuel 0"
let chunked_no_pointer_to_blue_elim
  (mh: MH.major_heap)
  (src dst: obj_addr)
  : Lemma
      (requires
        chunked_no_pointer_to_blue mh /\
        ChunkedMajorGraph.chunked_major_edge mh src dst /\
        ~(SweepDefs.chunked_is_blue mh src))
      (ensures ~(SweepDefs.chunked_is_blue mh dst))
  =
  ()
#pop-options

let chunked_no_black_to_white
  (mh: MH.major_heap)
  : prop
  =
  forall (src dst: obj_addr).
    ChunkedMajorGraph.chunked_major_edge mh src dst ==>
    SweepDefs.chunked_is_black mh src ==>
    ~(SweepDefs.chunked_is_white mh dst)

#push-options "--z3rlimit 1 --fuel 0 --ifuel 0"
let chunked_no_black_to_white_elim
  (mh: MH.major_heap)
  (src dst: obj_addr)
  : Lemma
      (requires
        chunked_no_black_to_white mh /\
        ChunkedMajorGraph.chunked_major_edge mh src dst /\
        SweepDefs.chunked_is_black mh src)
      (ensures ~(SweepDefs.chunked_is_white mh dst))
  =
  ()
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0"
let chunked_is_black_not_blue
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires SweepDefs.chunked_is_black mh obj)
      (ensures ~(SweepDefs.chunked_is_blue mh obj))
  =
  if SweepDefs.chunked_is_blue mh obj then begin
    SweepDefs.chunked_is_black_read_header mh obj;
    SweepDefs.chunked_is_blue_read_header mh obj;
    assert (Some? (SweepDefs.chunked_read_header mh obj));
    let hdr = Some?.v (SweepDefs.chunked_read_header mh obj) in
    assert (Obj.getColor hdr == Header.Black);
    assert (Obj.getColor hdr == Header.Blue);
    assert False
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let chunked_not_white_gray_blue_implies_black
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMajorGraph.chunked_major_vertex mh obj /\
        ~(SweepDefs.chunked_is_white mh obj) /\
        ~(BDefs.chunked_is_gray mh obj) /\
        ~(SweepDefs.chunked_is_blue mh obj))
      (ensures SweepDefs.chunked_is_black mh obj)
  =
  ChunkedMajorGraph.chunked_major_vertex_elim mh obj;
  SweepDefs.chunked_read_header_step mh obj;
  MH.major_objects_member_header_read_some mh obj;
  assert (Some? (SweepDefs.chunked_read_header mh obj));
  let hdr = Some?.v (SweepDefs.chunked_read_header mh obj) in
  assert (SweepDefs.chunked_read_header mh obj == Some hdr);
  SweepDefs.chunked_color_of_object_some mh obj hdr;
  match Obj.getColor hdr with
  | Header.White ->
    SweepDefs.chunked_is_white_from_color mh obj;
    assert False
  | Header.Gray ->
    BDefs.chunked_is_gray_from_color mh obj;
    assert False
  | Header.Blue ->
    SweepDefs.chunked_is_blue_from_color mh obj;
    assert False
  | Header.Black ->
    SweepDefs.chunked_is_black_from_color mh obj
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_major_reachable_from_roots_black_from_invariants
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_roots_black mh roots /\
        chunked_no_gray_objects mh /\
        chunked_no_pointer_to_blue mh /\
        chunked_no_black_to_white mh /\
        ChunkedMajorGraph.chunked_major_vertex mh target /\
        Reach.chunked_major_reachable_from_roots mh roots target)
      (ensures SweepDefs.chunked_is_black mh target)
  =
  let p (x: obj_addr) : prop = SweepDefs.chunked_is_black mh x in
  let root_case (r: obj_addr)
    : Lemma
        (requires
          ChunkedMajorGraph.chunked_major_vertex mh r /\
          Seq.mem r roots)
        (ensures p r)
    =
    chunked_roots_black_elim mh roots r
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires root_case);
  let edge_case (y: obj_addr) (z: obj_addr)
    : Lemma
        (requires
          Reach.chunked_major_reachable_from_roots mh roots y /\
          p y /\
          ChunkedMajorGraph.chunked_major_vertex mh z /\
          ChunkedMajorGraph.chunked_major_edge mh y z)
        (ensures p z)
    =
    chunked_is_black_not_blue mh y;
    chunked_no_pointer_to_blue_elim mh y z;
    chunked_no_black_to_white_elim mh y z;
    chunked_no_gray_objects_elim mh z;
    chunked_not_white_gray_blue_implies_black mh z
  in
  let edge_case_forall (y: obj_addr) (z: obj_addr)
    : Lemma
        (Reach.chunked_major_reachable_from_roots mh roots y /\
         p y /\
         ChunkedMajorGraph.chunked_major_vertex mh z /\
         ChunkedMajorGraph.chunked_major_edge mh y z ==> p z)
    =
    FStar.Classical.move_requires (edge_case y) z
  in
  FStar.Classical.forall_intro_2 edge_case_forall;
  Reach.chunked_major_reachable_from_roots_induct mh roots p target
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0"
let chunked_mark_bounded_root_ready
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (fuel: nat)
  (root: obj_addr)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        chunked_roots_gray_or_black mh roots /\
        ChunkedMajorGraph.chunked_major_vertex mh root /\
        Seq.mem root roots)
      (ensures
        BPres.chunked_mark_bounded_marks_target_ready
          mh cap fuel root)
  =
  ChunkedMajorGraph.chunked_major_vertex_elim mh root;
  chunked_roots_gray_or_black_elim mh roots root;
  BStackReady.chunked_mark_bounded_marks_rescan_gray_or_black_member_ready
    mh cap fuel root
#pop-options
