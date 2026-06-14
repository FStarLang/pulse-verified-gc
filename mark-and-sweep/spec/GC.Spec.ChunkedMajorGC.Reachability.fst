module GC.Spec.ChunkedMajorGC.Reachability

module Seq = FStar.Seq
module SeqProps = FStar.Seq.Properties

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module ChunkedMajorGraph = GC.Spec.ChunkedMajorGC.Graph

#set-options "--z3rlimit 5 --fuel 2 --ifuel 1 --split_queries always --warn_error -321"

let rec chunked_major_path
  (mh: MH.major_heap)
  (cur: obj_addr)
  (path: Seq.seq obj_addr)
  (dst: obj_addr)
  : Tot prop
    (decreases Seq.length path)
  =
  if Seq.length path = 0 then
    cur == dst
  else
    let next = Seq.head path in
    ChunkedMajorGraph.chunked_major_vertex mh next /\
    ChunkedMajorGraph.chunked_major_edge mh cur next /\
    chunked_major_path mh next (Seq.tail path) dst

let chunked_major_reachable
  (mh: MH.major_heap)
  (x: obj_addr)
  (y: obj_addr)
  : prop
  =
  ChunkedMajorGraph.chunked_major_vertex mh x /\
  ChunkedMajorGraph.chunked_major_vertex mh y /\
  exists (path: Seq.seq obj_addr).
    chunked_major_path mh x path y

#push-options "--z3rlimit 5 --fuel 2 --ifuel 0 --split_queries always"
let chunked_major_path_cons
  (mh: MH.major_heap)
  (cur next: obj_addr)
  (path: Seq.seq obj_addr)
  (dst: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGraph.chunked_major_vertex mh next /\
        ChunkedMajorGraph.chunked_major_edge mh cur next /\
        chunked_major_path mh next path dst)
      (ensures chunked_major_path mh cur (Seq.cons next path) dst)
  =
  assert (Seq.length (Seq.cons next path) > 0);
  assert (Seq.head (Seq.cons next path) == next);
  assert (Seq.equal (Seq.tail (Seq.cons next path)) path);
  Seq.lemma_eq_elim (Seq.tail (Seq.cons next path)) path;
  assert (chunked_major_path mh cur (Seq.cons next path) dst)
#pop-options

let chunked_major_reachable_refl
  (mh: MH.major_heap)
  (x: obj_addr)
  : Lemma
      (requires ChunkedMajorGraph.chunked_major_vertex mh x)
      (ensures chunked_major_reachable mh x x)
  =
  FStar.Classical.exists_intro
    (fun (path: Seq.seq obj_addr) -> chunked_major_path mh x path x)
    Seq.empty

let chunked_major_edge_reachable
  (mh: MH.major_heap)
  (x: obj_addr)
  (y: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGraph.chunked_major_vertex mh x /\
        ChunkedMajorGraph.chunked_major_vertex mh y /\
        ChunkedMajorGraph.chunked_major_edge mh x y)
      (ensures chunked_major_reachable mh x y)
  =
  assert (chunked_major_path mh x (Seq.cons y Seq.empty) y);
  FStar.Classical.exists_intro
    (fun (path: Seq.seq obj_addr) -> chunked_major_path mh x path y)
    (Seq.cons y Seq.empty)

#push-options "--z3rlimit 5 --fuel 2 --ifuel 1 --split_queries always"
let rec chunked_major_path_extend_edge
  (mh: MH.major_heap)
  (cur: obj_addr)
  (path: Seq.seq obj_addr)
  (mid: obj_addr)
  (dst: obj_addr)
  : Lemma
      (requires
        chunked_major_path mh cur path mid /\
        ChunkedMajorGraph.chunked_major_vertex mh dst /\
        ChunkedMajorGraph.chunked_major_edge mh mid dst)
      (ensures
        chunked_major_path mh cur (Seq.append path (Seq.cons dst Seq.empty)) dst)
      (decreases Seq.length path)
  =
  if Seq.length path = 0 then
    assert (chunked_major_path mh cur (Seq.append path (Seq.cons dst Seq.empty)) dst)
  else begin
    Seq.cons_head_tail path;
    let next = Seq.head path in
    let tail = Seq.tail path in
    assert (path == Seq.cons next tail);
    assert (ChunkedMajorGraph.chunked_major_vertex mh next);
    assert (ChunkedMajorGraph.chunked_major_edge mh cur next);
    assert (chunked_major_path mh next tail mid);
    chunked_major_path_extend_edge mh next tail mid dst;
    assert (chunked_major_path mh next (Seq.append tail (Seq.cons dst Seq.empty)) dst);
    SeqProps.append_cons next tail (Seq.cons dst Seq.empty);
    assert (Seq.append path (Seq.cons dst Seq.empty) ==
            Seq.cons next (Seq.append tail (Seq.cons dst Seq.empty)));
    chunked_major_path_cons
      mh cur next (Seq.append tail (Seq.cons dst Seq.empty)) dst;
    assert (chunked_major_path mh cur (Seq.append path (Seq.cons dst Seq.empty)) dst)
  end
#pop-options

let chunked_major_reachable_extend_edge
  (mh: MH.major_heap)
  (x y z: obj_addr)
  : Lemma
      (requires
        chunked_major_reachable mh x y /\
        ChunkedMajorGraph.chunked_major_vertex mh z /\
        ChunkedMajorGraph.chunked_major_edge mh y z)
      (ensures chunked_major_reachable mh x z)
  =
  FStar.Classical.exists_elim
    (chunked_major_reachable mh x z)
    #_
    #(fun (path: Seq.seq obj_addr) -> chunked_major_path mh x path y)
    ()
    (fun path ->
      chunked_major_path_extend_edge mh x path y z;
      FStar.Classical.exists_intro
        (fun (path': Seq.seq obj_addr) -> chunked_major_path mh x path' z)
        (Seq.append path (Seq.cons z Seq.empty)))

let chunked_major_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (x: obj_addr)
  : prop
  =
  ChunkedMajorGraph.chunked_major_vertex mh x /\
  exists (root: obj_addr).
    ChunkedMajorGraph.chunked_major_vertex mh root /\
    Seq.mem root roots /\
    chunked_major_reachable mh root x

let chunked_major_root_reachable
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (x: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGraph.chunked_major_vertex mh x /\
        Seq.mem x roots)
      (ensures chunked_major_reachable_from_roots mh roots x)
  =
  chunked_major_reachable_refl mh x;
  FStar.Classical.exists_intro
    (fun (root: obj_addr) ->
      ChunkedMajorGraph.chunked_major_vertex mh root /\
      Seq.mem root roots /\
      chunked_major_reachable mh root x)
    x

let chunked_major_reachable_from_roots_extend_edge
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (x y: obj_addr)
  : Lemma
      (requires
        chunked_major_reachable_from_roots mh roots x /\
        ChunkedMajorGraph.chunked_major_vertex mh y /\
        ChunkedMajorGraph.chunked_major_edge mh x y)
      (ensures chunked_major_reachable_from_roots mh roots y)
  =
  FStar.Classical.exists_elim
    (chunked_major_reachable_from_roots mh roots y)
    #_
    #(fun (root: obj_addr) ->
      ChunkedMajorGraph.chunked_major_vertex mh root /\
      Seq.mem root roots /\
      chunked_major_reachable mh root x)
    ()
    (fun root ->
      chunked_major_reachable_extend_edge mh root x y;
      FStar.Classical.exists_intro
        (fun (root': obj_addr) ->
          ChunkedMajorGraph.chunked_major_vertex mh root' /\
          Seq.mem root' roots /\
          chunked_major_reachable mh root' y)
        root)

let chunked_gray_black_reachable
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : prop
  =
  forall (x: obj_addr).
    ChunkedMajorGraph.chunked_major_vertex mh x /\
    (BDefs.chunked_is_gray mh x \/
     SweepDefs.chunked_is_black mh x) ==>
    chunked_major_reachable_from_roots mh roots x

let chunked_gray_black_reachable_init
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        (forall (x: obj_addr).
          ChunkedMajorGraph.chunked_major_vertex mh x /\
          (BDefs.chunked_is_gray mh x \/
           SweepDefs.chunked_is_black mh x) ==>
          Seq.mem x roots))
      (ensures chunked_gray_black_reachable mh roots)
  =
  let one (x: obj_addr)
    : Lemma
        (requires
          ChunkedMajorGraph.chunked_major_vertex mh x /\
          (BDefs.chunked_is_gray mh x \/
           SweepDefs.chunked_is_black mh x))
        (ensures chunked_major_reachable_from_roots mh roots x)
    =
    assert (Seq.mem x roots);
    chunked_major_root_reachable mh roots x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires one)

let chunked_gray_black_reachable_elim
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (x: obj_addr)
  : Lemma
      (requires
        chunked_gray_black_reachable mh roots /\
        ChunkedMajorGraph.chunked_major_vertex mh x /\
        (BDefs.chunked_is_gray mh x \/
         SweepDefs.chunked_is_black mh x))
      (ensures chunked_major_reachable_from_roots mh roots x)
  = ()
