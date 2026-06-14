module GC.Spec.ChunkedMarkBounded.Count

module Seq = FStar.Seq

open GC.Spec.Base

module Header = GC.Lib.Header
module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let rec chunked_count_non_black_in_preserved_by_black_status
    (mh mh': MH.major_heap)
    (objs: Seq.seq obj_addr)
  : Lemma
      (requires
        (forall (obj: obj_addr).
          Seq.mem obj objs ==>
            SweepDefs.chunked_is_black mh' obj ==
            SweepDefs.chunked_is_black mh obj))
      (ensures
        BDefs.chunked_count_non_black_in mh' objs ==
        BDefs.chunked_count_non_black_in mh objs)
      (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then begin
    BDefs.chunked_count_non_black_in_empty mh objs;
    BDefs.chunked_count_non_black_in_empty mh' objs
  end else begin
    BDefs.chunked_count_non_black_in_step mh objs;
    BDefs.chunked_count_non_black_in_step mh' objs;
    let head = Seq.head objs in
    let tail = Seq.tail objs in
    assert (Seq.mem head objs);
    assert (
      SweepDefs.chunked_is_black mh' head ==
      SweepDefs.chunked_is_black mh head);
    let each_tail (obj: obj_addr)
      : Lemma
          (requires Seq.mem obj tail)
          (ensures
            SweepDefs.chunked_is_black mh' obj ==
            SweepDefs.chunked_is_black mh obj)
      =
      assert (Seq.mem obj objs)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires each_tail);
    chunked_count_non_black_in_preserved_by_black_status mh mh' tail
  end

let chunked_count_non_black_preserved_by_black_status
    (mh mh': MH.major_heap)
  : Lemma
      (requires
        MH.major_objects mh' == MH.major_objects mh /\
        (forall (obj: obj_addr).
          Seq.mem obj (MH.major_objects mh) ==>
            SweepDefs.chunked_is_black mh' obj ==
            SweepDefs.chunked_is_black mh obj))
      (ensures
        BDefs.chunked_count_non_black mh' ==
        BDefs.chunked_count_non_black mh)
  =
  BDefs.chunked_count_non_black_equation mh;
  BDefs.chunked_count_non_black_equation mh';
  chunked_count_non_black_in_preserved_by_black_status
    mh mh' (MH.major_objects mh)

let chunked_is_gray_not_black
    (mh: MH.major_heap)
    (obj: obj_addr)
  : Lemma
      (requires BDefs.chunked_is_gray mh obj)
      (ensures ~(SweepDefs.chunked_is_black mh obj))
  =
  BDefs.chunked_is_gray_step mh obj;
  if SweepDefs.chunked_is_black mh obj then begin
    SweepDefs.chunked_is_black_read_header mh obj;
    match SweepDefs.chunked_read_header mh obj with
    | None -> assert False
    | Some hdr ->
      SweepDefs.chunked_color_of_object_some mh obj hdr;
      assert (SweepDefs.chunked_color_of_object mh obj == Some Header.Gray);
      assert (GC.Spec.Object.getColor hdr == Header.Gray);
      assert (GC.Spec.Object.getColor hdr == Header.Black);
      assert False
  end

