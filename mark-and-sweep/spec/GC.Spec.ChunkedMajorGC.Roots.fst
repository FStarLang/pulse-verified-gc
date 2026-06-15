module GC.Spec.ChunkedMajorGC.Roots

module Seq = FStar.Seq

open GC.Spec.Base

module Header = GC.Lib.Header
module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module MarkDefs = GC.Spec.ChunkedMark.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module MarkPres = GC.Spec.ChunkedMark.Preservation
module ChunkedMajorGraph = GC.Spec.ChunkedMajorGC.Graph
module MarkLive = GC.Spec.ChunkedMajorGC.MarkLiveness

#set-options "--split_queries always --z3rlimit 5 --fuel 1 --ifuel 0 --warn_error -321"

let rec chunked_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : GTot MH.major_heap
    (decreases Seq.length roots)
  =
  if Seq.length roots = 0 then
    mh
  else
    let root = Seq.head roots in
    let rest = Seq.tail roots in
    assert (Seq.length rest == Seq.length roots - 1);
    assert (Seq.length rest < Seq.length roots);
    let mh1 =
      if Seq.mem root (MH.major_objects mh) then
        MarkDefs.chunked_make_gray mh root
      else
        mh in
    chunked_gray_roots mh1 rest

let rec chunked_gray_roots_preserves_major_objects
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires MH.well_formed_major_heap mh)
      (ensures
        MH.major_objects (chunked_gray_roots mh roots) ==
        MH.major_objects mh)
      (decreases Seq.length roots)
  =
  if Seq.length roots = 0 then
    ()
  else begin
    assert (Seq.length roots > 0);
    let root = Seq.head roots in
    let rest = Seq.tail roots in
    assert (Seq.length rest == Seq.length roots - 1);
    assert (Seq.length rest < Seq.length roots);
    if Seq.mem root (MH.major_objects mh) then begin
      let mh1 = MarkDefs.chunked_make_gray mh root in
      MarkPres.chunked_make_gray_preserves_major_objects mh root;
      MarkPres.chunked_make_gray_preserves_well_formed mh root;
      chunked_gray_roots_preserves_major_objects mh1 rest
    end else
      chunked_gray_roots_preserves_major_objects mh rest
  end

let rec chunked_gray_roots_preserves_well_formed
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires MH.well_formed_major_heap mh)
      (ensures MH.well_formed_major_heap (chunked_gray_roots mh roots))
      (decreases Seq.length roots)
  =
  if Seq.length roots = 0 then
    ()
  else begin
    assert (Seq.length roots > 0);
    let root = Seq.head roots in
    let rest = Seq.tail roots in
    assert (Seq.length rest == Seq.length roots - 1);
    assert (Seq.length rest < Seq.length roots);
    if Seq.mem root (MH.major_objects mh) then begin
      let mh1 = MarkDefs.chunked_make_gray mh root in
      MarkPres.chunked_make_gray_preserves_well_formed mh root;
      chunked_gray_roots_preserves_well_formed mh1 rest
    end else
      chunked_gray_roots_preserves_well_formed mh rest
  end

private let gray_status_to_color
  (mh: MH.major_heap)
  (target: obj_addr)
  : Lemma
      (requires BDefs.chunked_is_gray mh target)
      (ensures SweepDefs.chunked_color_of_object mh target == Some Header.Gray)
  =
  BDefs.chunked_is_gray_step mh target;
  match SweepDefs.chunked_color_of_object mh target with
  | Some Header.Gray -> ()
  | _ -> assert False

let rec chunked_gray_roots_preserves_gray_or_black
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh) /\
        (BDefs.chunked_is_gray mh target \/
         SweepDefs.chunked_is_black mh target))
      (ensures
        BDefs.chunked_is_gray (chunked_gray_roots mh roots) target \/
        SweepDefs.chunked_is_black (chunked_gray_roots mh roots) target)
      (decreases Seq.length roots)
  =
  if Seq.length roots = 0 then
    ()
  else begin
    assert (Seq.length roots > 0);
    let root = Seq.head roots in
    let rest = Seq.tail roots in
    assert (Seq.length rest < Seq.length roots);
    if Seq.mem root (MH.major_objects mh) then begin
      let mh1 = MarkDefs.chunked_make_gray mh root in
      MarkPres.chunked_make_gray_preserves_major_objects mh root;
      MarkPres.chunked_make_gray_preserves_well_formed mh root;
      assert (Seq.mem target (MH.major_objects mh1));
      if target == root then begin
        MarkPres.chunked_make_gray_makes_gray mh root;
        BDefs.chunked_is_gray_from_color mh1 target
      end else if BDefs.chunked_is_gray mh target then begin
        gray_status_to_color mh target;
        MarkPres.chunked_make_gray_preserves_other_gray mh root target;
        BDefs.chunked_is_gray_from_color mh1 target
      end else begin
        assert (SweepDefs.chunked_is_black mh target);
        MarkPres.chunked_make_gray_preserves_other_black mh root target
      end;
      chunked_gray_roots_preserves_gray_or_black mh1 rest target
    end else
      chunked_gray_roots_preserves_gray_or_black mh rest target
  end

let rec chunked_gray_roots_roots_gray_or_black
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires MH.well_formed_major_heap mh)
      (ensures
        MarkLive.chunked_roots_gray_or_black
          (chunked_gray_roots mh roots) roots)
      (decreases Seq.length roots)
  =
  let final = chunked_gray_roots mh roots in
  let prove (root: obj_addr)
    : Lemma
        (requires
          ChunkedMajorGraph.chunked_major_vertex final root /\
          Seq.mem root roots)
        (ensures
          BDefs.chunked_is_gray final root \/
          SweepDefs.chunked_is_black final root)
    =
    if Seq.length roots = 0 then
      assert False
    else begin
      assert (Seq.length roots > 0);
      let hd = Seq.head roots in
      let tl = Seq.tail roots in
      assert (Seq.length tl == Seq.length roots - 1);
      assert (Seq.length tl < Seq.length roots);
      let mh1 =
        if Seq.mem hd (MH.major_objects mh) then
          MarkDefs.chunked_make_gray mh hd
        else
          mh in
      assert (final == chunked_gray_roots mh1 tl);
      if Seq.mem hd (MH.major_objects mh) then
        MarkPres.chunked_make_gray_preserves_well_formed mh hd;
      assert (MH.well_formed_major_heap mh1);
      chunked_gray_roots_preserves_major_objects mh roots;
      ChunkedMajorGraph.chunked_major_vertex_elim final root;
      assert (Seq.mem root (MH.major_objects mh));
      Seq.mem_cons hd tl;
      if root == hd then begin
        if Seq.mem hd (MH.major_objects mh) then begin
          MarkPres.chunked_make_gray_makes_gray mh hd;
          BDefs.chunked_is_gray_from_color mh1 root;
          MarkPres.chunked_make_gray_preserves_well_formed mh hd;
          MarkPres.chunked_make_gray_preserves_major_objects mh hd;
          assert (Seq.mem root (MH.major_objects mh1));
          chunked_gray_roots_preserves_gray_or_black mh1 tl root
        end else
          assert False
      end else begin
        assert (Seq.mem root tl);
        chunked_gray_roots_roots_gray_or_black mh1 tl;
        let final_tl = chunked_gray_roots mh1 tl in
        assert (final_tl == final);
        MarkLive.chunked_roots_gray_or_black_elim final tl root
      end
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires prove);
  MarkLive.chunked_roots_gray_or_black_intro final roots
