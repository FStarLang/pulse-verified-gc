module GC.Spec.ChunkedMarkBounded.TargetMembership

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module MarkDefs = GC.Spec.ChunkedMark.Defs
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module Pres = GC.Spec.ChunkedMarkBounded.Preservation
module MarkPres = GC.Spec.ChunkedMark.Preservation
module RangePres = GC.Spec.ChunkedSweepCoalesce.RangePreservation
module Readiness = GC.Spec.ChunkedMarkBounded.Readiness
module BReady = GC.Spec.ChunkedMarkBounded.TargetReady
module BStackStep = GC.Spec.ChunkedMarkBounded.StackStep
module Roots = GC.Spec.ChunkedMajorGC.Roots
module SeqMem = GC.Spec.SeqMemLemmas

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let nat_nonzero_pos (n: nat)
  : Lemma (requires n <> 0) (ensures n > 0)
  = ()

let chunked_is_white_not_blue
    (mh: MH.major_heap)
    (obj: obj_addr)
  : Lemma
      (requires SweepDefs.chunked_is_white mh obj)
      (ensures ~(SweepDefs.chunked_is_blue mh obj))
  =
  if SweepDefs.chunked_is_blue mh obj then begin
    SweepDefs.chunked_is_white_read_header mh obj;
    SweepDefs.chunked_is_blue_read_header mh obj;
    match SweepDefs.chunked_read_header mh obj with
    | Some hdr -> ()
    | None -> assert False
  end

let chunked_is_gray_not_blue
    (mh: MH.major_heap)
    (obj: obj_addr)
  : Lemma
      (requires BDefs.chunked_is_gray mh obj)
      (ensures ~(SweepDefs.chunked_is_blue mh obj))
  =
  if SweepDefs.chunked_is_blue mh obj then begin
    BDefs.chunked_is_gray_read_header mh obj;
    SweepDefs.chunked_is_blue_read_header mh obj;
    match SweepDefs.chunked_read_header mh obj with
    | Some hdr -> ()
    | None -> assert False
  end

let chunked_scanned_white_targets_in_major
    (mh: MH.major_heap)
  : GTot prop
  =
  forall (obj: obj_addr) (i: U64.t{U64.v i >= 1}).
    Seq.mem obj (MH.major_objects mh) /\
    ~(MarkDefs.chunked_is_no_scan mh obj) /\
    U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj) ==>
    (let v = MarkDefs.chunked_get_field mh obj i in
     if MarkDefs.chunked_is_pointer_field mh v then
       let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
       let child = MarkDefs.chunked_resolve_object mh child_raw in
       SweepDefs.chunked_is_white mh child ==>
         Seq.mem child (MH.major_objects mh)
     else
       True)

#push-options "--z3rlimit 1 --fuel 0 --ifuel 0"
let chunked_scanned_raw_targets_in_major
    (mh: MH.major_heap)
  : GTot prop
  =
  forall (obj: obj_addr) (i: U64.t{U64.v i >= 1}).
    Seq.mem obj (MH.major_objects mh) /\
    ~(MarkDefs.chunked_is_no_scan mh obj) /\
    U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj) ==>
    (let v = MarkDefs.chunked_get_field mh obj i in
     if MarkDefs.chunked_is_pointer_field mh v then
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      Seq.mem child_raw (MH.major_objects mh) /\
      ~(SweepDefs.chunked_is_infix mh child_raw)
     else
      True)

let chunked_nonblue_scanned_raw_targets_in_major
    (mh: MH.major_heap)
  : GTot prop
  =
  forall (obj: obj_addr) (i: U64.t{U64.v i >= 1}).
    Seq.mem obj (MH.major_objects mh) /\
    ~(SweepDefs.chunked_is_blue mh obj) /\
    ~(MarkDefs.chunked_is_no_scan mh obj) /\
    U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj) ==>
    (let v = MarkDefs.chunked_get_field mh obj i in
     if MarkDefs.chunked_is_pointer_field mh v then
     let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
     Seq.mem child_raw (MH.major_objects mh) /\
     ~(SweepDefs.chunked_is_infix mh child_raw)
     else
     True)

let chunked_scanned_raw_targets_in_major_intro
  (mh: MH.major_heap)
  : Lemma
     (requires
       forall (obj: obj_addr) (i: U64.t{U64.v i >= 1}).
         Seq.mem obj (MH.major_objects mh) /\
         ~(MarkDefs.chunked_is_no_scan mh obj) /\
         U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj) ==>
         (let v = MarkDefs.chunked_get_field mh obj i in
          if MarkDefs.chunked_is_pointer_field mh v then
            let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
            Seq.mem child_raw (MH.major_objects mh) /\
            ~(SweepDefs.chunked_is_infix mh child_raw)
          else
            True))
     (ensures chunked_scanned_raw_targets_in_major mh)
  =
  ()

let chunked_nonblue_scanned_raw_targets_in_major_intro
  (mh: MH.major_heap)
  : Lemma
    (requires
      forall (obj: obj_addr) (i: U64.t{U64.v i >= 1}).
        Seq.mem obj (MH.major_objects mh) /\
        ~(SweepDefs.chunked_is_blue mh obj) /\
        ~(MarkDefs.chunked_is_no_scan mh obj) /\
        U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj) ==>
        (let v = MarkDefs.chunked_get_field mh obj i in
         if MarkDefs.chunked_is_pointer_field mh v then
           let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
           Seq.mem child_raw (MH.major_objects mh) /\
           ~(SweepDefs.chunked_is_infix mh child_raw)
         else
           True))
    (ensures chunked_nonblue_scanned_raw_targets_in_major mh)
  =
  ()

let chunked_scanned_white_targets_in_major_from_raw_targets
   (mh: MH.major_heap)
  : Lemma
     (requires chunked_scanned_raw_targets_in_major mh)
     (ensures chunked_scanned_white_targets_in_major mh)
  =
  let one (obj: obj_addr) (i: U64.t{U64.v i >= 1})
    : Lemma
       (requires
         Seq.mem obj (MH.major_objects mh) /\
         ~(MarkDefs.chunked_is_no_scan mh obj) /\
         U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj))
       (ensures
         (let v = MarkDefs.chunked_get_field mh obj i in
          if MarkDefs.chunked_is_pointer_field mh v then
            let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
            let child = MarkDefs.chunked_resolve_object mh child_raw in
            SweepDefs.chunked_is_white mh child ==>
              Seq.mem child (MH.major_objects mh)
          else
            True))
    =
    let v = MarkDefs.chunked_get_field mh obj i in
    if MarkDefs.chunked_is_pointer_field mh v then begin
     let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
     let child = MarkDefs.chunked_resolve_object mh child_raw in
     assert (Seq.mem child_raw (MH.major_objects mh));
     assert (~(SweepDefs.chunked_is_infix mh child_raw));
     MarkDefs.chunked_resolve_non_infix mh child_raw;
     assert (child == child_raw)
    end
  in
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 one)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_scanned_raw_targets_in_major_preserved_by_make_gray
    (mh: MH.major_heap)
    (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh) /\
        chunked_scanned_raw_targets_in_major mh)
      (ensures
        chunked_scanned_raw_targets_in_major
          (MarkDefs.chunked_make_gray mh target))
  =
  let mh' = MarkDefs.chunked_make_gray mh target in
  MarkPres.chunked_make_gray_preserves_major_objects mh target;
  MarkPres.chunked_make_gray_preserves_well_formed mh target;
  MarkPres.chunked_make_gray_preserves_ranges mh target;
  let one (obj: obj_addr) (i: U64.t{U64.v i >= 1})
    : Lemma
        (requires
          Seq.mem obj (MH.major_objects mh') /\
          ~(MarkDefs.chunked_is_no_scan mh' obj) /\
          U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh' obj))
        (ensures
          (let v = MarkDefs.chunked_get_field mh' obj i in
           if MarkDefs.chunked_is_pointer_field mh' v then
            let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh' v in
            Seq.mem child_raw (MH.major_objects mh') /\
            ~(SweepDefs.chunked_is_infix mh' child_raw)
           else
            True))
    =
    assert (Seq.mem obj (MH.major_objects mh));
    MarkPres.chunked_make_gray_preserves_no_scan_status mh target obj;
    MarkPres.chunked_make_gray_preserves_wosize_of_object mh target obj;
    assert (~(MarkDefs.chunked_is_no_scan mh obj));
    assert (U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj));
    MarkPres.chunked_make_gray_preserves_get_field mh target obj i;
    let v = MarkDefs.chunked_get_field mh' obj i in
    assert (v == MarkDefs.chunked_get_field mh obj i);
    RangePres.same_chunk_ranges_preserves_is_major_pointer mh mh' v;
    MarkDefs.chunked_is_pointer_field_step mh v;
    MarkDefs.chunked_is_pointer_field_step mh' v;
    if MarkDefs.chunked_is_pointer_field mh' v then begin
      assert (MarkDefs.chunked_is_pointer_field mh v);
      MarkDefs.chunked_pointer_field_as_obj_addr_step mh v;
      MarkDefs.chunked_pointer_field_as_obj_addr_step mh' v;
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      let child_raw' = MarkDefs.chunked_pointer_field_as_obj_addr mh' v in
      assert (child_raw == child_raw');
      assert (Seq.mem child_raw (MH.major_objects mh));
      assert (~(SweepDefs.chunked_is_infix mh child_raw));
      assert (Seq.mem child_raw' (MH.major_objects mh'));
      MarkPres.chunked_make_gray_preserves_infix_status mh target child_raw;
      assert (SweepDefs.chunked_is_infix mh' child_raw' ==
              SweepDefs.chunked_is_infix mh child_raw)
    end
  in
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 one)

let chunked_scanned_raw_targets_in_major_preserved_by_make_black
    (mh: MH.major_heap)
    (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh) /\
        chunked_scanned_raw_targets_in_major mh)
      (ensures
        chunked_scanned_raw_targets_in_major
          (MarkDefs.chunked_make_black mh target))
  =
  let mh' = MarkDefs.chunked_make_black mh target in
  MarkPres.chunked_make_black_preserves_major_objects mh target;
  MarkPres.chunked_make_black_preserves_well_formed mh target;
  MarkPres.chunked_make_black_preserves_ranges mh target;
  let one (obj: obj_addr) (i: U64.t{U64.v i >= 1})
    : Lemma
        (requires
          Seq.mem obj (MH.major_objects mh') /\
          ~(MarkDefs.chunked_is_no_scan mh' obj) /\
          U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh' obj))
        (ensures
          (let v = MarkDefs.chunked_get_field mh' obj i in
           if MarkDefs.chunked_is_pointer_field mh' v then
            let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh' v in
            Seq.mem child_raw (MH.major_objects mh') /\
            ~(SweepDefs.chunked_is_infix mh' child_raw)
           else
            True))
    =
    assert (Seq.mem obj (MH.major_objects mh));
    MarkPres.chunked_make_black_preserves_no_scan_status mh target obj;
    MarkPres.chunked_make_black_preserves_wosize_of_object mh target obj;
    assert (~(MarkDefs.chunked_is_no_scan mh obj));
    assert (U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj));
    MarkPres.chunked_make_black_preserves_get_field mh target obj i;
    let v = MarkDefs.chunked_get_field mh' obj i in
    assert (v == MarkDefs.chunked_get_field mh obj i);
    RangePres.same_chunk_ranges_preserves_is_major_pointer mh mh' v;
    MarkDefs.chunked_is_pointer_field_step mh v;
    MarkDefs.chunked_is_pointer_field_step mh' v;
    if MarkDefs.chunked_is_pointer_field mh' v then begin
      assert (MarkDefs.chunked_is_pointer_field mh v);
      MarkDefs.chunked_pointer_field_as_obj_addr_step mh v;
      MarkDefs.chunked_pointer_field_as_obj_addr_step mh' v;
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      let child_raw' = MarkDefs.chunked_pointer_field_as_obj_addr mh' v in
      assert (child_raw == child_raw');
      assert (Seq.mem child_raw (MH.major_objects mh));
      assert (~(SweepDefs.chunked_is_infix mh child_raw));
      assert (Seq.mem child_raw' (MH.major_objects mh'));
      MarkPres.chunked_make_black_preserves_infix_status mh target child_raw;
      assert (SweepDefs.chunked_is_infix mh' child_raw' ==
              SweepDefs.chunked_is_infix mh child_raw)
    end
  in
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 one)

let chunked_nonblue_scanned_raw_targets_in_major_preserved_by_make_gray
    (mh: MH.major_heap)
    (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh) /\
        ~(SweepDefs.chunked_is_blue mh target) /\
        chunked_nonblue_scanned_raw_targets_in_major mh)
      (ensures
        chunked_nonblue_scanned_raw_targets_in_major
          (MarkDefs.chunked_make_gray mh target))
  =
  let mh' = MarkDefs.chunked_make_gray mh target in
  MarkPres.chunked_make_gray_preserves_major_objects mh target;
  MarkPres.chunked_make_gray_preserves_well_formed mh target;
  MarkPres.chunked_make_gray_preserves_ranges mh target;
  let one (obj: obj_addr) (i: U64.t{U64.v i >= 1})
    : Lemma
        (requires
          Seq.mem obj (MH.major_objects mh') /\
          ~(SweepDefs.chunked_is_blue mh' obj) /\
          ~(MarkDefs.chunked_is_no_scan mh' obj) /\
          U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh' obj))
        (ensures
          (let v = MarkDefs.chunked_get_field mh' obj i in
           if MarkDefs.chunked_is_pointer_field mh' v then
            let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh' v in
            Seq.mem child_raw (MH.major_objects mh') /\
            ~(SweepDefs.chunked_is_infix mh' child_raw)
           else
            True))
    =
    assert (Seq.mem obj (MH.major_objects mh));
    if obj = target then
      assert (~(SweepDefs.chunked_is_blue mh obj))
    else begin
      MarkPres.chunked_make_gray_preserves_other_blue_status mh target obj;
      assert (SweepDefs.chunked_is_blue mh' obj ==
              SweepDefs.chunked_is_blue mh obj);
      assert (~(SweepDefs.chunked_is_blue mh obj))
    end;
    MarkPres.chunked_make_gray_preserves_no_scan_status mh target obj;
    MarkPres.chunked_make_gray_preserves_wosize_of_object mh target obj;
    assert (~(MarkDefs.chunked_is_no_scan mh obj));
    assert (U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj));
    MarkPres.chunked_make_gray_preserves_get_field mh target obj i;
    let v = MarkDefs.chunked_get_field mh' obj i in
    assert (v == MarkDefs.chunked_get_field mh obj i);
    RangePres.same_chunk_ranges_preserves_is_major_pointer mh mh' v;
    MarkDefs.chunked_is_pointer_field_step mh v;
    MarkDefs.chunked_is_pointer_field_step mh' v;
    if MarkDefs.chunked_is_pointer_field mh' v then begin
      assert (MarkDefs.chunked_is_pointer_field mh v);
      MarkDefs.chunked_pointer_field_as_obj_addr_step mh v;
      MarkDefs.chunked_pointer_field_as_obj_addr_step mh' v;
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      let child_raw' = MarkDefs.chunked_pointer_field_as_obj_addr mh' v in
      assert (child_raw == child_raw');
      assert (Seq.mem child_raw (MH.major_objects mh));
      assert (~(SweepDefs.chunked_is_infix mh child_raw));
      assert (Seq.mem child_raw' (MH.major_objects mh'));
      MarkPres.chunked_make_gray_preserves_infix_status mh target child_raw;
      assert (SweepDefs.chunked_is_infix mh' child_raw' ==
              SweepDefs.chunked_is_infix mh child_raw)
    end
  in
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 one)

let chunked_nonblue_scanned_raw_targets_in_major_preserved_by_make_black
    (mh: MH.major_heap)
    (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh) /\
        ~(SweepDefs.chunked_is_blue mh target) /\
        chunked_nonblue_scanned_raw_targets_in_major mh)
      (ensures
        chunked_nonblue_scanned_raw_targets_in_major
          (MarkDefs.chunked_make_black mh target))
  =
  let mh' = MarkDefs.chunked_make_black mh target in
  MarkPres.chunked_make_black_preserves_major_objects mh target;
  MarkPres.chunked_make_black_preserves_well_formed mh target;
  MarkPres.chunked_make_black_preserves_ranges mh target;
  let one (obj: obj_addr) (i: U64.t{U64.v i >= 1})
    : Lemma
        (requires
          Seq.mem obj (MH.major_objects mh') /\
          ~(SweepDefs.chunked_is_blue mh' obj) /\
          ~(MarkDefs.chunked_is_no_scan mh' obj) /\
          U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh' obj))
        (ensures
          (let v = MarkDefs.chunked_get_field mh' obj i in
           if MarkDefs.chunked_is_pointer_field mh' v then
            let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh' v in
            Seq.mem child_raw (MH.major_objects mh') /\
            ~(SweepDefs.chunked_is_infix mh' child_raw)
           else
            True))
    =
    assert (Seq.mem obj (MH.major_objects mh));
    if obj = target then
      assert (~(SweepDefs.chunked_is_blue mh obj))
    else begin
      MarkPres.chunked_make_black_preserves_other_blue_status mh target obj;
      assert (SweepDefs.chunked_is_blue mh' obj ==
              SweepDefs.chunked_is_blue mh obj);
      assert (~(SweepDefs.chunked_is_blue mh obj))
    end;
    MarkPres.chunked_make_black_preserves_no_scan_status mh target obj;
    MarkPres.chunked_make_black_preserves_wosize_of_object mh target obj;
    assert (~(MarkDefs.chunked_is_no_scan mh obj));
    assert (U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj));
    MarkPres.chunked_make_black_preserves_get_field mh target obj i;
    let v = MarkDefs.chunked_get_field mh' obj i in
    assert (v == MarkDefs.chunked_get_field mh obj i);
    RangePres.same_chunk_ranges_preserves_is_major_pointer mh mh' v;
    MarkDefs.chunked_is_pointer_field_step mh v;
    MarkDefs.chunked_is_pointer_field_step mh' v;
    if MarkDefs.chunked_is_pointer_field mh' v then begin
      assert (MarkDefs.chunked_is_pointer_field mh v);
      MarkDefs.chunked_pointer_field_as_obj_addr_step mh v;
      MarkDefs.chunked_pointer_field_as_obj_addr_step mh' v;
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      let child_raw' = MarkDefs.chunked_pointer_field_as_obj_addr mh' v in
      assert (child_raw == child_raw');
      assert (Seq.mem child_raw (MH.major_objects mh));
      assert (~(SweepDefs.chunked_is_infix mh child_raw));
      assert (Seq.mem child_raw' (MH.major_objects mh'));
      MarkPres.chunked_make_black_preserves_infix_status mh target child_raw;
      assert (SweepDefs.chunked_is_infix mh' child_raw' ==
              SweepDefs.chunked_is_infix mh child_raw)
    end
  in
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 one)
#pop-options

#push-options "--z3rlimit 1 --fuel 1 --ifuel 0 --split_queries always"
let rec chunked_scanned_raw_targets_in_major_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_scanned_raw_targets_in_major mh)
      (ensures
        chunked_scanned_raw_targets_in_major
          (Roots.chunked_gray_roots mh roots))
      (decreases Seq.length roots)
  =
  let len = Seq.length roots in
  if len = 0 then
    begin
      Roots.chunked_gray_roots_empty mh roots;
      assert (chunked_scanned_raw_targets_in_major
        (Roots.chunked_gray_roots mh roots))
    end
  else begin
    assert (len <> 0);
    nat_nonzero_pos len;
    assert (Seq.length roots == len);
    assert (Seq.length roots > 0);
    let root = Seq.head roots in
    let rest = Seq.tail roots in
    assert (Seq.length rest == Seq.length roots - 1);
    assert (Seq.length rest < Seq.length roots);
    if Seq.mem root (MH.major_objects mh) then begin
      let mh1 = MarkDefs.chunked_make_gray mh root in
      Roots.chunked_gray_roots_cons_mem mh roots;
      chunked_scanned_raw_targets_in_major_preserved_by_make_gray mh root;
      MarkPres.chunked_make_gray_preserves_well_formed mh root;
      chunked_scanned_raw_targets_in_major_preserved_by_gray_roots
        mh1 rest;
      assert (chunked_scanned_raw_targets_in_major
        (Roots.chunked_gray_roots mh1 rest));
      assert (Roots.chunked_gray_roots mh roots ==
              Roots.chunked_gray_roots mh1 rest);
      assert (chunked_scanned_raw_targets_in_major
        (Roots.chunked_gray_roots mh roots))
    end else begin
      Roots.chunked_gray_roots_cons_miss mh roots;
      chunked_scanned_raw_targets_in_major_preserved_by_gray_roots
        mh rest;
      assert (chunked_scanned_raw_targets_in_major
        (Roots.chunked_gray_roots mh rest));
      assert (Roots.chunked_gray_roots mh roots ==
              Roots.chunked_gray_roots mh rest);
      assert (chunked_scanned_raw_targets_in_major
        (Roots.chunked_gray_roots mh roots))
    end
  end

let rec chunked_nonblue_scanned_raw_targets_in_major_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        (forall (root: obj_addr).
          Seq.mem root roots /\
          Seq.mem root (MH.major_objects mh) ==>
          ~(SweepDefs.chunked_is_blue mh root)) /\
        chunked_nonblue_scanned_raw_targets_in_major mh)
      (ensures
        chunked_nonblue_scanned_raw_targets_in_major
          (Roots.chunked_gray_roots mh roots))
      (decreases Seq.length roots)
  =
  let len = Seq.length roots in
  if len = 0 then
    begin
      Roots.chunked_gray_roots_empty mh roots;
      assert (chunked_nonblue_scanned_raw_targets_in_major
        (Roots.chunked_gray_roots mh roots))
    end
  else begin
    assert (len <> 0);
    nat_nonzero_pos len;
    assert (Seq.length roots == len);
    assert (Seq.length roots > 0);
    let root = Seq.head roots in
    let rest = Seq.tail roots in
    assert (roots == Seq.cons root rest);
    assert (Seq.length rest == Seq.length roots - 1);
    assert (Seq.length rest < Seq.length roots);
    if Seq.mem root (MH.major_objects mh) then begin
      let mh1 = MarkDefs.chunked_make_gray mh root in
      Roots.chunked_gray_roots_cons_mem mh roots;
      SeqMem.seq_mem_cons_head root rest;
      assert (Seq.mem root roots);
      assert (~(SweepDefs.chunked_is_blue mh root));
      chunked_nonblue_scanned_raw_targets_in_major_preserved_by_make_gray
        mh root;
      MarkPres.chunked_make_gray_preserves_well_formed mh root;
      MarkPres.chunked_make_gray_preserves_major_objects mh root;
      let rest_nonblue (r: obj_addr)
        : Lemma
            (requires
              Seq.mem r rest /\
              Seq.mem r (MH.major_objects mh1))
            (ensures ~(SweepDefs.chunked_is_blue mh1 r))
        =
        assert (Seq.mem r (MH.major_objects mh));
        if r = root then
          MarkPres.chunked_make_gray_not_blue mh root
        else begin
          MarkPres.chunked_make_gray_preserves_other_blue_status mh root r;
          SeqMem.seq_mem_cons_tail root r rest;
          assert (Seq.mem r roots);
          assert (~(SweepDefs.chunked_is_blue mh r));
          assert (SweepDefs.chunked_is_blue mh1 r ==
                  SweepDefs.chunked_is_blue mh r)
        end
      in
      FStar.Classical.forall_intro
        (FStar.Classical.move_requires rest_nonblue);
      chunked_nonblue_scanned_raw_targets_in_major_preserved_by_gray_roots
        mh1 rest;
      assert (chunked_nonblue_scanned_raw_targets_in_major
        (Roots.chunked_gray_roots mh1 rest));
      assert (Roots.chunked_gray_roots mh roots ==
              Roots.chunked_gray_roots mh1 rest);
      assert (chunked_nonblue_scanned_raw_targets_in_major
        (Roots.chunked_gray_roots mh roots))
    end else begin
      Roots.chunked_gray_roots_cons_miss mh roots;
      let rest_nonblue (r: obj_addr)
        : Lemma
            (requires
              Seq.mem r rest /\
              Seq.mem r (MH.major_objects mh))
            (ensures ~(SweepDefs.chunked_is_blue mh r))
        =
        SeqMem.seq_mem_cons_tail root r rest;
        assert (Seq.mem r roots)
      in
      FStar.Classical.forall_intro
        (FStar.Classical.move_requires rest_nonblue);
      chunked_nonblue_scanned_raw_targets_in_major_preserved_by_gray_roots
        mh rest;
      assert (chunked_nonblue_scanned_raw_targets_in_major
        (Roots.chunked_gray_roots mh rest));
      assert (Roots.chunked_gray_roots mh roots ==
              Roots.chunked_gray_roots mh rest);
      assert (chunked_nonblue_scanned_raw_targets_in_major
        (Roots.chunked_gray_roots mh roots))
    end
  end
#pop-options

let chunked_scanned_white_targets_in_major_elim
    (mh: MH.major_heap)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        chunked_scanned_white_targets_in_major mh /\
        Seq.mem obj (MH.major_objects mh) /\
        ~(MarkDefs.chunked_is_no_scan mh obj) /\
        U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj) /\
        (let v = MarkDefs.chunked_get_field mh obj i in
         MarkDefs.chunked_is_pointer_field mh v /\
         (let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
          let child = MarkDefs.chunked_resolve_object mh child_raw in
          SweepDefs.chunked_is_white mh child)))
      (ensures
        (let v = MarkDefs.chunked_get_field mh obj i in
         let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
         let child = MarkDefs.chunked_resolve_object mh child_raw in
         Seq.mem child (MH.major_objects mh)))
  =
  ()

let rec chunked_push_children_scanned_targets_policy
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
    chunked_scanned_white_targets_in_major mh /\
    (if U64.v i < U64.v ws then
      chunked_push_children_scanned_targets_policy
        mh' obj (U64.add i 1UL) ws
     else
      True)

let rec chunked_push_children_raw_targets_policy
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
    chunked_scanned_raw_targets_in_major mh /\
    (if U64.v i < U64.v ws then
      chunked_push_children_raw_targets_policy
       mh' obj (U64.add i 1UL) ws
     else
      True)

let chunked_push_children_raw_targets_policy_base_intro
    (mh: MH.major_heap)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
  : Lemma
     (requires U64.v i > U64.v ws)
     (ensures chunked_push_children_raw_targets_policy mh obj i ws)
  =
  ()

let chunked_push_children_raw_targets_policy_step_intro
    (mh: MH.major_heap)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
  : Lemma
     (requires
       U64.v i <= U64.v ws /\
       chunked_scanned_raw_targets_in_major mh /\
       (if U64.v i < U64.v ws then
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
          chunked_push_children_raw_targets_policy
            mh' obj (U64.add i 1UL) ws)
        else
          True))
     (ensures chunked_push_children_raw_targets_policy mh obj i ws)
  =
  ()

let rec chunked_push_children_scanned_targets_policy_from_raw_targets
    (mh: MH.major_heap)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
  : Lemma
      (requires chunked_push_children_raw_targets_policy mh obj i ws)
      (ensures chunked_push_children_scanned_targets_policy mh obj i ws)
      (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then
    chunked_push_children_raw_targets_policy_base_intro mh obj i ws
  else begin
    chunked_scanned_white_targets_in_major_from_raw_targets mh;
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
    if U64.v i < U64.v ws then
      chunked_push_children_scanned_targets_policy_from_raw_targets
       mh' obj (U64.add i 1UL) ws
  end

let rec chunked_push_children_target_membership_policy_from_scanned_targets
    (mh: MH.major_heap)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        ~(MarkDefs.chunked_is_no_scan mh obj) /\
        U64.v ws <= U64.v (SweepDefs.chunked_wosize_of_object mh obj) /\
        chunked_push_children_scanned_targets_policy mh obj i ws)
      (ensures
        Readiness.chunked_push_children_target_membership_policy
          mh obj i ws)
      (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then
    Readiness.chunked_push_children_target_membership_policy_base_intro
      mh obj i ws
  else begin
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
    if MarkDefs.chunked_is_pointer_field mh v then begin
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      let child = MarkDefs.chunked_resolve_object mh child_raw in
      if SweepDefs.chunked_is_white mh child then
        chunked_scanned_white_targets_in_major_elim mh obj i
    end;
    if U64.v i < U64.v ws then begin
      if MarkDefs.chunked_is_pointer_field mh v then begin
        let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
        let child = MarkDefs.chunked_resolve_object mh child_raw in
        if SweepDefs.chunked_is_white mh child then begin
          assert (Seq.mem child (MH.major_objects mh));
          MarkPres.chunked_make_gray_preserves_major_objects mh child;
          MarkPres.chunked_make_gray_preserves_well_formed mh child;
          assert (MH.major_objects mh' == MH.major_objects mh);
          assert (Seq.mem obj (MH.major_objects mh'));
          MarkPres.chunked_make_gray_preserves_wosize_of_object mh child obj;
          MarkPres.chunked_make_gray_preserves_no_scan_status mh child obj;
          assert (SweepDefs.chunked_wosize_of_object mh' obj ==
                  SweepDefs.chunked_wosize_of_object mh obj);
          assert (~(MarkDefs.chunked_is_no_scan mh' obj))
        end
      end;
      assert (MH.well_formed_major_heap mh');
      assert (Seq.mem obj (MH.major_objects mh'));
      assert (~(MarkDefs.chunked_is_no_scan mh' obj));
      assert (U64.v ws <= U64.v (SweepDefs.chunked_wosize_of_object mh' obj));
      assert (chunked_push_children_scanned_targets_policy
        mh' obj (U64.add i 1UL) ws);
      chunked_push_children_target_membership_policy_from_scanned_targets
        mh' obj (U64.add i 1UL) ws
    end;
    Readiness.chunked_push_children_target_membership_policy_step_intro
      mh obj i ws
  end

let chunked_mark_step_scanned_targets_policy
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
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
      chunked_push_children_scanned_targets_policy mh' obj 1UL ws)

let chunked_mark_step_raw_targets_policy
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
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
      chunked_push_children_raw_targets_policy mh' obj 1UL ws)

let chunked_mark_step_scanned_targets_policy_from_raw_targets
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
  : Lemma
      (requires chunked_mark_step_raw_targets_policy mh st cap)
      (ensures chunked_mark_step_scanned_targets_policy mh st cap)
  =
  if Seq.length st = 0 then
    ()
  else begin
    let obj = Seq.head st in
    if MarkDefs.chunked_is_no_scan mh obj then
      ()
    else begin
      let mh' = MarkDefs.chunked_make_black mh obj in
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      chunked_push_children_scanned_targets_policy_from_raw_targets
       mh' obj 1UL ws
    end
  end

let chunked_mark_step_target_membership_policy_from_scanned_targets
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_step_scanned_targets_policy mh st cap)
      (ensures
        Readiness.chunked_mark_step_target_membership_policy mh st cap)
  =
  if Seq.length st = 0 then
    Readiness.chunked_mark_step_target_membership_policy_intro mh st cap
  else begin
    let obj = Seq.head st in
    if MarkDefs.chunked_is_no_scan mh obj then
      ()
    else begin
      let mh' = MarkDefs.chunked_make_black mh obj in
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      MarkPres.chunked_make_black_preserves_major_objects mh obj;
      MarkPres.chunked_make_black_preserves_well_formed mh obj;
      MarkPres.chunked_make_black_preserves_wosize_of_object mh obj obj;
      MarkPres.chunked_make_black_preserves_no_scan_status mh obj obj;
      assert (MH.major_objects mh' == MH.major_objects mh);
      assert (Seq.mem obj (MH.major_objects mh'));
      assert (SweepDefs.chunked_wosize_of_object mh' obj ==
              SweepDefs.chunked_wosize_of_object mh obj);
      assert (~(MarkDefs.chunked_is_no_scan mh' obj));
      chunked_push_children_target_membership_policy_from_scanned_targets
        mh' obj 1UL ws
    end;
    Readiness.chunked_mark_step_target_membership_policy_intro mh st cap
  end

let rec chunked_mark_inner_loop_scanned_targets_policy
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
  : Tot prop
    (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then True
  else
    let fuel_pred : n:nat{n < fuel} = fuel - 1 in
    chunked_mark_step_scanned_targets_policy mh st cap /\
    (let (mh', st') = BDefs.chunked_mark_step_bounded mh st cap in
     chunked_mark_inner_loop_scanned_targets_policy
       mh' st' cap fuel_pred)

let rec chunked_mark_inner_loop_raw_targets_policy
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
  : Tot prop
    (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then True
  else
    let fuel_pred : n:nat{n < fuel} = fuel - 1 in
    chunked_mark_step_raw_targets_policy mh st cap /\
    (let (mh', st') = BDefs.chunked_mark_step_bounded mh st cap in
     chunked_mark_inner_loop_raw_targets_policy
       mh' st' cap fuel_pred)

let chunked_mark_inner_loop_raw_targets_policy_base_intro
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
  : Lemma
      (requires fuel = 0 \/ Seq.length st = 0)
      (ensures chunked_mark_inner_loop_raw_targets_policy mh st cap fuel)
  =
  ()

let chunked_mark_inner_loop_raw_targets_policy_step_intro
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
  : Lemma
      (requires
       fuel > 0 /\
       Seq.length st > 0 /\
       chunked_mark_step_raw_targets_policy mh st cap /\
       (let fuel_pred : n:nat{n < fuel} = fuel - 1 in
        let (mh', st') = BDefs.chunked_mark_step_bounded mh st cap in
        chunked_mark_inner_loop_raw_targets_policy
          mh' st' cap fuel_pred))
      (ensures chunked_mark_inner_loop_raw_targets_policy mh st cap fuel)
  =
  ()

let rec chunked_mark_inner_loop_scanned_targets_policy_from_raw_targets
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
  : Lemma
      (requires chunked_mark_inner_loop_raw_targets_policy mh st cap fuel)
      (ensures chunked_mark_inner_loop_scanned_targets_policy mh st cap fuel)
      (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then
    ()
  else begin
    assert (fuel <> 0);
    nat_nonzero_pos fuel;
    let fuel_pred : n:nat{n < fuel} = fuel - 1 in
    chunked_mark_step_scanned_targets_policy_from_raw_targets mh st cap;
    let (mh', st') = BDefs.chunked_mark_step_bounded mh st cap in
    chunked_mark_inner_loop_scanned_targets_policy_from_raw_targets
      mh' st' cap fuel_pred
  end

let rec chunked_mark_inner_loop_target_membership_policy_from_scanned_targets
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_inner_loop_scanned_targets_policy mh st cap fuel)
      (ensures
        Readiness.chunked_mark_inner_loop_target_membership_policy
          mh st cap fuel)
      (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then
    Readiness.chunked_mark_inner_loop_target_membership_policy_base_intro
      mh st cap fuel
  else begin
    assert (fuel <> 0);
    nat_nonzero_pos fuel;
    assert (fuel > 0);
    let fuel_pred : n:nat{n < fuel} = fuel - 1 in
    chunked_mark_step_target_membership_policy_from_scanned_targets mh st cap;
    Readiness.chunked_mark_step_bounded_preservation_ready_from_target_membership
      mh st cap;
    Pres.chunked_mark_step_bounded_preserves_well_formed mh st cap;
    let (mh', st') = BDefs.chunked_mark_step_bounded mh st cap in
    assert (MH.well_formed_major_heap mh');
    assert (chunked_mark_inner_loop_scanned_targets_policy
      mh' st' cap fuel_pred);
    chunked_mark_inner_loop_target_membership_policy_from_scanned_targets
      mh' st' cap fuel_pred;
    Readiness.chunked_mark_inner_loop_target_membership_policy_step_intro
      mh st cap fuel
  end

let rec chunked_mark_bounded_scanned_targets_policy
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Tot prop
    (decreases fuel)
  =
  if fuel = 0 then True
  else
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then True
    else
      let inner_fuel = BDefs.chunked_count_non_black mh in
      let fuel_pred : n:nat{n < fuel} = fuel - 1 in
      chunked_mark_inner_loop_scanned_targets_policy mh st cap inner_fuel /\
      (let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
       chunked_mark_bounded_scanned_targets_policy mh' cap fuel_pred)

let rec chunked_mark_bounded_raw_targets_policy
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Tot prop
    (decreases fuel)
  =
  if fuel = 0 then True
  else
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then True
    else
      let inner_fuel = BDefs.chunked_count_non_black mh in
      let fuel_pred : n:nat{n < fuel} = fuel - 1 in
      chunked_mark_inner_loop_raw_targets_policy mh st cap inner_fuel /\
      (let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
       chunked_mark_bounded_raw_targets_policy mh' cap fuel_pred)

let chunked_mark_bounded_raw_targets_policy_base_intro
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
  : Lemma
      (ensures chunked_mark_bounded_raw_targets_policy mh cap 0)
  =
  ()

let chunked_mark_bounded_raw_targets_policy_empty_intro
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        fuel > 0 /\
        Seq.length (BDefs.chunked_rescan_heap mh Seq.empty cap) = 0)
      (ensures chunked_mark_bounded_raw_targets_policy mh cap fuel)
  =
  ()

let chunked_mark_bounded_raw_targets_policy_step_intro
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        fuel > 0 /\
        (let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
         let inner_fuel = BDefs.chunked_count_non_black mh in
         let fuel_pred : n:nat{n < fuel} = fuel - 1 in
         Seq.length st > 0 /\
         chunked_mark_inner_loop_raw_targets_policy mh st cap inner_fuel /\
         (let (mh', _) =
           BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
          chunked_mark_bounded_raw_targets_policy mh' cap fuel_pred)))
      (ensures chunked_mark_bounded_raw_targets_policy mh cap fuel)
  =
  ()

let rec chunked_mark_bounded_scanned_targets_policy_from_raw_targets
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires chunked_mark_bounded_raw_targets_policy mh cap fuel)
      (ensures chunked_mark_bounded_scanned_targets_policy mh cap fuel)
      (decreases fuel)
  =
  if fuel = 0 then
    chunked_mark_bounded_raw_targets_policy_base_intro mh cap
  else begin
    assert (fuel <> 0);
    nat_nonzero_pos fuel;
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then
      chunked_mark_bounded_raw_targets_policy_empty_intro mh cap fuel
    else begin
      let inner_fuel = BDefs.chunked_count_non_black mh in
      let fuel_pred : n:nat{n < fuel} = fuel - 1 in
      chunked_mark_inner_loop_scanned_targets_policy_from_raw_targets
        mh st cap inner_fuel;
      let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
      chunked_mark_bounded_scanned_targets_policy_from_raw_targets
        mh' cap fuel_pred
    end
  end

let rec chunked_mark_bounded_target_membership_policy_from_scanned_targets
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_bounded_scanned_targets_policy mh cap fuel)
      (ensures
        Readiness.chunked_mark_bounded_target_membership_policy mh cap fuel)
      (decreases fuel)
  =
  if fuel = 0 then
    Readiness.chunked_mark_bounded_target_membership_policy_base_intro
      mh cap
  else begin
    assert (fuel <> 0);
    nat_nonzero_pos fuel;
    assert (fuel > 0);
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then
      Readiness.chunked_mark_bounded_target_membership_policy_empty_intro
        mh cap fuel
    else begin
      let inner_fuel = BDefs.chunked_count_non_black mh in
      let fuel_pred : n:nat{n < fuel} = fuel - 1 in
      chunked_mark_inner_loop_target_membership_policy_from_scanned_targets
        mh st cap inner_fuel;
      Readiness.chunked_mark_inner_loop_preservation_ready_from_target_membership
        mh st cap inner_fuel;
      Pres.chunked_mark_inner_loop_preserves_well_formed
        mh st cap inner_fuel;
      let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
      assert (MH.well_formed_major_heap mh');
      assert (chunked_mark_bounded_scanned_targets_policy
        mh' cap fuel_pred);
      chunked_mark_bounded_target_membership_policy_from_scanned_targets
        mh' cap fuel_pred;
      Readiness.chunked_mark_bounded_target_membership_policy_step_intro
        mh cap fuel
    end
  end

let chunked_mark_bounded_target_membership_policy_from_raw_targets
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_bounded_raw_targets_policy mh cap fuel)
      (ensures
        Readiness.chunked_mark_bounded_target_membership_policy mh cap fuel)
  =
  chunked_mark_bounded_scanned_targets_policy_from_raw_targets
    mh cap fuel;
  chunked_mark_bounded_target_membership_policy_from_scanned_targets
    mh cap fuel

let chunked_mark_bounded_preservation_ready_from_scanned_targets
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_bounded_scanned_targets_policy mh cap fuel)
      (ensures
        Pres.chunked_mark_bounded_preservation_ready mh cap fuel)
  =
  chunked_mark_bounded_target_membership_policy_from_scanned_targets
    mh cap fuel;
  Readiness.chunked_mark_bounded_preservation_ready_from_target_membership
    mh cap fuel

let chunked_mark_bounded_preservation_ready_from_raw_targets
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_bounded_raw_targets_policy mh cap fuel)
      (ensures
        Pres.chunked_mark_bounded_preservation_ready mh cap fuel)
  =
  chunked_mark_bounded_target_membership_policy_from_raw_targets
    mh cap fuel;
  Readiness.chunked_mark_bounded_preservation_ready_from_target_membership
    mh cap fuel

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let rec chunked_push_children_raw_targets_policy_from_static
    (mh: MH.major_heap)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        ~(MarkDefs.chunked_is_no_scan mh obj) /\
        U64.v ws <= U64.v (SweepDefs.chunked_wosize_of_object mh obj) /\
        chunked_scanned_raw_targets_in_major mh)
      (ensures chunked_push_children_raw_targets_policy mh obj i ws)
      (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then
    chunked_push_children_raw_targets_policy_base_intro mh obj i ws
  else begin
    assert (U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj));
    let v = MarkDefs.chunked_get_field mh obj i in
    if U64.v i < U64.v ws then begin
      if MarkDefs.chunked_is_pointer_field mh v then begin
        let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
        let child = MarkDefs.chunked_resolve_object mh child_raw in
        if SweepDefs.chunked_is_white mh child then begin
          let mh' = MarkDefs.chunked_make_gray mh child in
          assert (Seq.mem child_raw (MH.major_objects mh));
          assert (~(SweepDefs.chunked_is_infix mh child_raw));
          MarkDefs.chunked_resolve_non_infix mh child_raw;
          assert (child == child_raw);
          assert (Seq.mem child (MH.major_objects mh));
          chunked_scanned_raw_targets_in_major_preserved_by_make_gray mh child;
          MarkPres.chunked_make_gray_preserves_major_objects mh child;
          MarkPres.chunked_make_gray_preserves_well_formed mh child;
          MarkPres.chunked_make_gray_preserves_no_scan_status mh child obj;
          MarkPres.chunked_make_gray_preserves_wosize_of_object mh child obj;
          chunked_push_children_raw_targets_policy_from_static
            mh' obj (U64.add i 1UL) ws
        end else begin
          chunked_push_children_raw_targets_policy_from_static
            mh obj (U64.add i 1UL) ws
        end
      end else begin
        chunked_push_children_raw_targets_policy_from_static
          mh obj (U64.add i 1UL) ws
      end
    end;
    chunked_push_children_raw_targets_policy_step_intro mh obj i ws
  end

let rec chunked_push_children_bounded_preserves_scanned_raw_targets
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
    (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        ~(MarkDefs.chunked_is_no_scan mh obj) /\
        U64.v ws <= U64.v (SweepDefs.chunked_wosize_of_object mh obj) /\
        chunked_scanned_raw_targets_in_major mh)
      (ensures
        (let (mh', _) =
          BDefs.chunked_push_children_bounded mh st obj i ws cap in
         chunked_scanned_raw_targets_in_major mh'))
      (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then
    BDefs.chunked_push_children_bounded_done mh st obj i ws cap
  else begin
    assert (U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj));
    BDefs.chunked_push_children_bounded_step mh st obj i ws cap;
    let v = MarkDefs.chunked_get_field mh obj i in
    let (mh_step, st_step) =
      if MarkDefs.chunked_is_pointer_field mh v then
        let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
        let child = MarkDefs.chunked_resolve_object mh child_raw in
        if SweepDefs.chunked_is_white mh child then
          let mh_gray = MarkDefs.chunked_make_gray mh child in
          if Seq.length st < cap then
            (mh_gray, Seq.cons child st)
          else
            (mh_gray, st)
        else
          (mh, st)
      else
        (mh, st) in
    if MarkDefs.chunked_is_pointer_field mh v then begin
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      let child = MarkDefs.chunked_resolve_object mh child_raw in
      assert (Seq.mem child_raw (MH.major_objects mh));
      assert (~(SweepDefs.chunked_is_infix mh child_raw));
      MarkDefs.chunked_resolve_non_infix mh child_raw;
      assert (child == child_raw);
      if SweepDefs.chunked_is_white mh child then begin
        chunked_scanned_raw_targets_in_major_preserved_by_make_gray mh child;
        if U64.v i < U64.v ws then begin
          MarkPres.chunked_make_gray_preserves_major_objects mh child;
          MarkPres.chunked_make_gray_preserves_well_formed mh child;
          MarkPres.chunked_make_gray_preserves_no_scan_status mh child obj;
          MarkPres.chunked_make_gray_preserves_wosize_of_object mh child obj;
          assert (MH.well_formed_major_heap mh_step);
          assert (Seq.mem obj (MH.major_objects mh_step));
          assert (~(MarkDefs.chunked_is_no_scan mh_step obj));
          assert (U64.v ws <=
                  U64.v (SweepDefs.chunked_wosize_of_object mh_step obj));
          chunked_push_children_bounded_preserves_scanned_raw_targets
            mh_step st_step obj (U64.add i 1UL) ws cap
        end
      end else if U64.v i < U64.v ws then
        chunked_push_children_bounded_preserves_scanned_raw_targets
          mh_step st_step obj (U64.add i 1UL) ws cap
    end else if U64.v i < U64.v ws then
      chunked_push_children_bounded_preserves_scanned_raw_targets
        mh_step st_step obj (U64.add i 1UL) ws cap
  end

let chunked_mark_step_raw_targets_policy_from_static
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BReady.chunked_bounded_stack_props mh st /\
        chunked_scanned_raw_targets_in_major mh)
      (ensures chunked_mark_step_raw_targets_policy mh st cap)
  =
  if Seq.length st = 0 then
    ()
  else begin
    let obj = Seq.head st in
    BReady.chunked_bounded_stack_head mh st;
    if MarkDefs.chunked_is_no_scan mh obj then
      ()
    else begin
      let mh' = MarkDefs.chunked_make_black mh obj in
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      chunked_scanned_raw_targets_in_major_preserved_by_make_black mh obj;
      MarkPres.chunked_make_black_preserves_major_objects mh obj;
      MarkPres.chunked_make_black_preserves_well_formed mh obj;
      MarkPres.chunked_make_black_preserves_no_scan_status mh obj obj;
      MarkPres.chunked_make_black_preserves_wosize_of_object mh obj obj;
      assert (MH.well_formed_major_heap mh');
      assert (Seq.mem obj (MH.major_objects mh'));
      assert (~(MarkDefs.chunked_is_no_scan mh' obj));
      assert (U64.v ws <= U64.v (SweepDefs.chunked_wosize_of_object mh' obj));
      chunked_push_children_raw_targets_policy_from_static
        mh' obj 1UL ws
    end
  end

let chunked_mark_step_bounded_preserves_scanned_raw_targets
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BReady.chunked_bounded_stack_props mh st /\
        chunked_scanned_raw_targets_in_major mh)
      (ensures
        (let (mh', _) = BDefs.chunked_mark_step_bounded mh st cap in
         chunked_scanned_raw_targets_in_major mh'))
  =
  if Seq.length st = 0 then
    BDefs.chunked_mark_step_bounded_empty mh st cap
  else begin
    let obj = Seq.head st in
    BReady.chunked_bounded_stack_head mh st;
    if MarkDefs.chunked_is_no_scan mh obj then begin
      BDefs.chunked_mark_step_bounded_no_scan mh st cap;
      chunked_scanned_raw_targets_in_major_preserved_by_make_black mh obj
    end else begin
      BDefs.chunked_mark_step_bounded_scan mh st cap;
      let mh_black = MarkDefs.chunked_make_black mh obj in
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      chunked_scanned_raw_targets_in_major_preserved_by_make_black mh obj;
      MarkPres.chunked_make_black_preserves_major_objects mh obj;
      MarkPres.chunked_make_black_preserves_well_formed mh obj;
      MarkPres.chunked_make_black_preserves_no_scan_status mh obj obj;
      MarkPres.chunked_make_black_preserves_wosize_of_object mh obj obj;
      assert (MH.well_formed_major_heap mh_black);
      assert (Seq.mem obj (MH.major_objects mh_black));
      assert (~(MarkDefs.chunked_is_no_scan mh_black obj));
      assert (U64.v ws <=
              U64.v (SweepDefs.chunked_wosize_of_object mh_black obj));
      chunked_push_children_bounded_preserves_scanned_raw_targets
        mh_black (Seq.tail st) obj 1UL ws cap
    end
  end

let chunked_mark_step_preservation_ready_from_raw_targets_static
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BReady.chunked_bounded_stack_props mh st /\
        chunked_scanned_raw_targets_in_major mh)
      (ensures Pres.chunked_mark_step_bounded_preservation_ready mh st cap)
  =
  chunked_mark_step_raw_targets_policy_from_static mh st cap;
  chunked_mark_step_scanned_targets_policy_from_raw_targets mh st cap;
  chunked_mark_step_target_membership_policy_from_scanned_targets mh st cap;
  Readiness.chunked_mark_step_bounded_preservation_ready_from_target_membership
    mh st cap

let rec chunked_mark_inner_loop_raw_targets_policy_from_static
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BReady.chunked_bounded_stack_props mh st /\
        chunked_scanned_raw_targets_in_major mh)
      (ensures chunked_mark_inner_loop_raw_targets_policy mh st cap fuel)
      (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then
    chunked_mark_inner_loop_raw_targets_policy_base_intro mh st cap fuel
  else begin
    assert (fuel <> 0);
    nat_nonzero_pos fuel;
    let fuel_pred : n:nat{n < fuel} = fuel - 1 in
    chunked_mark_step_raw_targets_policy_from_static mh st cap;
    chunked_mark_step_preservation_ready_from_raw_targets_static mh st cap;
    chunked_mark_step_bounded_preserves_scanned_raw_targets mh st cap;
    Pres.chunked_mark_step_bounded_preserves_well_formed mh st cap;
    BStackStep.chunked_mark_step_bounded_preserves_bounded_stack_props
      mh st cap;
    let (mh', st') = BDefs.chunked_mark_step_bounded mh st cap in
    chunked_mark_inner_loop_raw_targets_policy_from_static
      mh' st' cap fuel_pred;
    chunked_mark_inner_loop_raw_targets_policy_step_intro
      mh st cap fuel
  end

let rec chunked_mark_inner_loop_preserves_scanned_raw_targets
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BReady.chunked_bounded_stack_props mh st /\
        chunked_scanned_raw_targets_in_major mh)
      (ensures
        (let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap fuel in
         chunked_scanned_raw_targets_in_major mh'))
      (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then
    BDefs.chunked_mark_inner_loop_base mh st cap fuel
  else begin
    assert (fuel <> 0);
    nat_nonzero_pos fuel;
    BDefs.chunked_mark_inner_loop_step mh st cap fuel;
    chunked_mark_step_preservation_ready_from_raw_targets_static mh st cap;
    chunked_mark_step_bounded_preserves_scanned_raw_targets mh st cap;
    Pres.chunked_mark_step_bounded_preserves_well_formed mh st cap;
    BStackStep.chunked_mark_step_bounded_preserves_bounded_stack_props
      mh st cap;
    let (mh_step, st_step) = BDefs.chunked_mark_step_bounded mh st cap in
    chunked_mark_inner_loop_preserves_scanned_raw_targets
      mh_step st_step cap (fuel - 1)
  end

let rec chunked_mark_bounded_raw_targets_policy_from_static
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_scanned_raw_targets_in_major mh)
      (ensures chunked_mark_bounded_raw_targets_policy mh cap fuel)
      (decreases fuel)
  =
  if fuel = 0 then
    chunked_mark_bounded_raw_targets_policy_base_intro mh cap
  else begin
    assert (fuel <> 0);
    nat_nonzero_pos fuel;
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then
      chunked_mark_bounded_raw_targets_policy_empty_intro mh cap fuel
    else begin
      let inner_fuel = BDefs.chunked_count_non_black mh in
      let fuel_pred : n:nat{n < fuel} = fuel - 1 in
      BReady.chunked_rescan_heap_bounded_stack_props mh cap;
      chunked_mark_inner_loop_raw_targets_policy_from_static
        mh st cap inner_fuel;
      chunked_mark_inner_loop_scanned_targets_policy_from_raw_targets
        mh st cap inner_fuel;
      chunked_mark_inner_loop_target_membership_policy_from_scanned_targets
        mh st cap inner_fuel;
      Readiness.chunked_mark_inner_loop_preservation_ready_from_target_membership
        mh st cap inner_fuel;
      Pres.chunked_mark_inner_loop_preserves_well_formed
        mh st cap inner_fuel;
      chunked_mark_inner_loop_preserves_scanned_raw_targets
        mh st cap inner_fuel;
      let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
      chunked_mark_bounded_raw_targets_policy_from_static
        mh' cap fuel_pred;
      chunked_mark_bounded_raw_targets_policy_step_intro mh cap fuel
    end
  end

let rec chunked_push_children_target_membership_policy_from_nonblue_static
    (mh: MH.major_heap)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        ~(SweepDefs.chunked_is_blue mh obj) /\
        ~(MarkDefs.chunked_is_no_scan mh obj) /\
        U64.v ws <= U64.v (SweepDefs.chunked_wosize_of_object mh obj) /\
        chunked_nonblue_scanned_raw_targets_in_major mh)
      (ensures
        Readiness.chunked_push_children_target_membership_policy
          mh obj i ws)
      (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then
    Readiness.chunked_push_children_target_membership_policy_base_intro
      mh obj i ws
  else begin
    assert (U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj));
    let v = MarkDefs.chunked_get_field mh obj i in
    if MarkDefs.chunked_is_pointer_field mh v then begin
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      let child = MarkDefs.chunked_resolve_object mh child_raw in
      assert (Seq.mem child_raw (MH.major_objects mh));
      assert (~(SweepDefs.chunked_is_infix mh child_raw));
      MarkDefs.chunked_resolve_non_infix mh child_raw;
      assert (child == child_raw);
      if SweepDefs.chunked_is_white mh child then
        assert (Seq.mem child (MH.major_objects mh))
    end;
    if U64.v i < U64.v ws then begin
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
      if MarkDefs.chunked_is_pointer_field mh v then begin
        let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
        let child = MarkDefs.chunked_resolve_object mh child_raw in
        if SweepDefs.chunked_is_white mh child then begin
          assert (Seq.mem child (MH.major_objects mh));
          chunked_is_white_not_blue mh child;
          chunked_nonblue_scanned_raw_targets_in_major_preserved_by_make_gray
            mh child;
          MarkPres.chunked_make_gray_preserves_major_objects mh child;
          MarkPres.chunked_make_gray_preserves_well_formed mh child;
          MarkPres.chunked_make_gray_preserves_no_scan_status mh child obj;
          MarkPres.chunked_make_gray_preserves_wosize_of_object mh child obj;
          if obj = child then
            MarkPres.chunked_make_gray_not_blue mh child
          else begin
            MarkPres.chunked_make_gray_preserves_other_blue_status mh child obj;
            assert (SweepDefs.chunked_is_blue mh' obj ==
                    SweepDefs.chunked_is_blue mh obj)
          end;
          assert (MH.well_formed_major_heap mh');
          assert (Seq.mem obj (MH.major_objects mh'));
          assert (~(SweepDefs.chunked_is_blue mh' obj));
          assert (~(MarkDefs.chunked_is_no_scan mh' obj));
          assert (U64.v ws <=
                  U64.v (SweepDefs.chunked_wosize_of_object mh' obj));
          chunked_push_children_target_membership_policy_from_nonblue_static
            mh' obj (U64.add i 1UL) ws
        end else
          chunked_push_children_target_membership_policy_from_nonblue_static
            mh' obj (U64.add i 1UL) ws
      end else
        chunked_push_children_target_membership_policy_from_nonblue_static
          mh' obj (U64.add i 1UL) ws
    end;
    Readiness.chunked_push_children_target_membership_policy_step_intro
      mh obj i ws
  end

let rec chunked_push_children_bounded_preserves_nonblue_scanned_raw_targets
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
    (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        ~(SweepDefs.chunked_is_blue mh obj) /\
        ~(MarkDefs.chunked_is_no_scan mh obj) /\
        U64.v ws <= U64.v (SweepDefs.chunked_wosize_of_object mh obj) /\
        chunked_nonblue_scanned_raw_targets_in_major mh)
      (ensures
        (let (mh', _) =
          BDefs.chunked_push_children_bounded mh st obj i ws cap in
         chunked_nonblue_scanned_raw_targets_in_major mh'))
      (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then
    BDefs.chunked_push_children_bounded_done mh st obj i ws cap
  else begin
    assert (U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj));
    BDefs.chunked_push_children_bounded_step mh st obj i ws cap;
    let v = MarkDefs.chunked_get_field mh obj i in
    let (mh_step, st_step) =
      if MarkDefs.chunked_is_pointer_field mh v then
        let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
        let child = MarkDefs.chunked_resolve_object mh child_raw in
        if SweepDefs.chunked_is_white mh child then
          let mh_gray = MarkDefs.chunked_make_gray mh child in
          if Seq.length st < cap then
            (mh_gray, Seq.cons child st)
          else
            (mh_gray, st)
        else
          (mh, st)
      else
        (mh, st) in
    if MarkDefs.chunked_is_pointer_field mh v then begin
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      let child = MarkDefs.chunked_resolve_object mh child_raw in
      assert (Seq.mem child_raw (MH.major_objects mh));
      assert (~(SweepDefs.chunked_is_infix mh child_raw));
      MarkDefs.chunked_resolve_non_infix mh child_raw;
      assert (child == child_raw);
      if SweepDefs.chunked_is_white mh child then begin
        chunked_is_white_not_blue mh child;
        chunked_nonblue_scanned_raw_targets_in_major_preserved_by_make_gray
          mh child;
        if U64.v i < U64.v ws then begin
          MarkPres.chunked_make_gray_preserves_major_objects mh child;
          MarkPres.chunked_make_gray_preserves_well_formed mh child;
          MarkPres.chunked_make_gray_preserves_no_scan_status mh child obj;
          MarkPres.chunked_make_gray_preserves_wosize_of_object mh child obj;
          if obj = child then
            MarkPres.chunked_make_gray_not_blue mh child
          else begin
            MarkPres.chunked_make_gray_preserves_other_blue_status
              mh child obj;
            assert (SweepDefs.chunked_is_blue mh_step obj ==
                    SweepDefs.chunked_is_blue mh obj)
          end;
          assert (MH.well_formed_major_heap mh_step);
          assert (Seq.mem obj (MH.major_objects mh_step));
          assert (~(SweepDefs.chunked_is_blue mh_step obj));
          assert (~(MarkDefs.chunked_is_no_scan mh_step obj));
          assert (U64.v ws <=
                  U64.v (SweepDefs.chunked_wosize_of_object mh_step obj));
          chunked_push_children_bounded_preserves_nonblue_scanned_raw_targets
            mh_step st_step obj (U64.add i 1UL) ws cap
        end
      end else if U64.v i < U64.v ws then
        chunked_push_children_bounded_preserves_nonblue_scanned_raw_targets
          mh_step st_step obj (U64.add i 1UL) ws cap
    end else if U64.v i < U64.v ws then
      chunked_push_children_bounded_preserves_nonblue_scanned_raw_targets
        mh_step st_step obj (U64.add i 1UL) ws cap
  end

let chunked_mark_step_target_membership_policy_from_nonblue_static
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BReady.chunked_bounded_stack_props mh st /\
        chunked_nonblue_scanned_raw_targets_in_major mh)
      (ensures
        Readiness.chunked_mark_step_target_membership_policy mh st cap)
  =
  if Seq.length st = 0 then
    Readiness.chunked_mark_step_target_membership_policy_intro mh st cap
  else begin
    let obj = Seq.head st in
    BReady.chunked_bounded_stack_head mh st;
    BReady.chunked_bounded_stack_props_gray mh st;
    BReady.chunked_stack_points_to_gray_elim mh st obj;
    chunked_is_gray_not_blue mh obj;
    if MarkDefs.chunked_is_no_scan mh obj then
      ()
    else begin
      let mh' = MarkDefs.chunked_make_black mh obj in
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      chunked_nonblue_scanned_raw_targets_in_major_preserved_by_make_black
        mh obj;
      MarkPres.chunked_make_black_preserves_major_objects mh obj;
      MarkPres.chunked_make_black_preserves_well_formed mh obj;
      MarkPres.chunked_make_black_not_blue mh obj;
      MarkPres.chunked_make_black_preserves_no_scan_status mh obj obj;
      MarkPres.chunked_make_black_preserves_wosize_of_object mh obj obj;
      assert (MH.well_formed_major_heap mh');
      assert (Seq.mem obj (MH.major_objects mh'));
      assert (~(SweepDefs.chunked_is_blue mh' obj));
      assert (~(MarkDefs.chunked_is_no_scan mh' obj));
      assert (U64.v ws <= U64.v (SweepDefs.chunked_wosize_of_object mh' obj));
      chunked_push_children_target_membership_policy_from_nonblue_static
        mh' obj 1UL ws
    end;
    Readiness.chunked_mark_step_target_membership_policy_intro mh st cap
  end

let chunked_mark_step_bounded_preserves_nonblue_scanned_raw_targets
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BReady.chunked_bounded_stack_props mh st /\
        chunked_nonblue_scanned_raw_targets_in_major mh)
      (ensures
        (let (mh', _) = BDefs.chunked_mark_step_bounded mh st cap in
         chunked_nonblue_scanned_raw_targets_in_major mh'))
  =
  if Seq.length st = 0 then
    BDefs.chunked_mark_step_bounded_empty mh st cap
  else begin
    let obj = Seq.head st in
    BReady.chunked_bounded_stack_head mh st;
    BReady.chunked_bounded_stack_props_gray mh st;
    BReady.chunked_stack_points_to_gray_elim mh st obj;
    chunked_is_gray_not_blue mh obj;
    if MarkDefs.chunked_is_no_scan mh obj then begin
      BDefs.chunked_mark_step_bounded_no_scan mh st cap;
      chunked_nonblue_scanned_raw_targets_in_major_preserved_by_make_black
        mh obj
    end else begin
      BDefs.chunked_mark_step_bounded_scan mh st cap;
      let mh_black = MarkDefs.chunked_make_black mh obj in
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      chunked_nonblue_scanned_raw_targets_in_major_preserved_by_make_black
        mh obj;
      MarkPres.chunked_make_black_preserves_major_objects mh obj;
      MarkPres.chunked_make_black_preserves_well_formed mh obj;
      MarkPres.chunked_make_black_not_blue mh obj;
      MarkPres.chunked_make_black_preserves_no_scan_status mh obj obj;
      MarkPres.chunked_make_black_preserves_wosize_of_object mh obj obj;
      assert (MH.well_formed_major_heap mh_black);
      assert (Seq.mem obj (MH.major_objects mh_black));
      assert (~(SweepDefs.chunked_is_blue mh_black obj));
      assert (~(MarkDefs.chunked_is_no_scan mh_black obj));
      assert (U64.v ws <=
              U64.v (SweepDefs.chunked_wosize_of_object mh_black obj));
      chunked_push_children_bounded_preserves_nonblue_scanned_raw_targets
        mh_black (Seq.tail st) obj 1UL ws cap
    end
  end

let rec chunked_mark_inner_loop_target_membership_policy_from_nonblue_static
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BReady.chunked_bounded_stack_props mh st /\
        chunked_nonblue_scanned_raw_targets_in_major mh)
      (ensures
        Readiness.chunked_mark_inner_loop_target_membership_policy
          mh st cap fuel)
      (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then
    Readiness.chunked_mark_inner_loop_target_membership_policy_base_intro
      mh st cap fuel
  else begin
    assert (fuel <> 0);
    nat_nonzero_pos fuel;
    chunked_mark_step_target_membership_policy_from_nonblue_static mh st cap;
    Readiness.chunked_mark_step_bounded_preservation_ready_from_target_membership
      mh st cap;
    Pres.chunked_mark_step_bounded_preserves_well_formed mh st cap;
    BStackStep.chunked_mark_step_bounded_preserves_bounded_stack_props
      mh st cap;
    chunked_mark_step_bounded_preserves_nonblue_scanned_raw_targets
      mh st cap;
    let (mh', st') = BDefs.chunked_mark_step_bounded mh st cap in
    chunked_mark_inner_loop_target_membership_policy_from_nonblue_static
      mh' st' cap (fuel - 1);
    Readiness.chunked_mark_inner_loop_target_membership_policy_step_intro
      mh st cap fuel
  end

let rec chunked_mark_inner_loop_preserves_nonblue_scanned_raw_targets
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BReady.chunked_bounded_stack_props mh st /\
        chunked_nonblue_scanned_raw_targets_in_major mh)
      (ensures
        (let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap fuel in
         chunked_nonblue_scanned_raw_targets_in_major mh'))
      (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then
    BDefs.chunked_mark_inner_loop_base mh st cap fuel
  else begin
    assert (fuel <> 0);
    nat_nonzero_pos fuel;
    BDefs.chunked_mark_inner_loop_step mh st cap fuel;
    chunked_mark_step_target_membership_policy_from_nonblue_static mh st cap;
    Readiness.chunked_mark_step_bounded_preservation_ready_from_target_membership
      mh st cap;
    chunked_mark_step_bounded_preserves_nonblue_scanned_raw_targets
      mh st cap;
    Pres.chunked_mark_step_bounded_preserves_well_formed mh st cap;
    BStackStep.chunked_mark_step_bounded_preserves_bounded_stack_props
      mh st cap;
    let (mh_step, st_step) = BDefs.chunked_mark_step_bounded mh st cap in
    chunked_mark_inner_loop_preserves_nonblue_scanned_raw_targets
      mh_step st_step cap (fuel - 1)
  end

let rec chunked_mark_bounded_target_membership_policy_from_nonblue_static
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_nonblue_scanned_raw_targets_in_major mh)
      (ensures
        Readiness.chunked_mark_bounded_target_membership_policy mh cap fuel)
      (decreases fuel)
  =
  if fuel = 0 then
    Readiness.chunked_mark_bounded_target_membership_policy_base_intro
      mh cap
  else begin
    assert (fuel <> 0);
    nat_nonzero_pos fuel;
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then
      Readiness.chunked_mark_bounded_target_membership_policy_empty_intro
        mh cap fuel
    else begin
      let inner_fuel = BDefs.chunked_count_non_black mh in
      BReady.chunked_rescan_heap_bounded_stack_props mh cap;
      chunked_mark_inner_loop_target_membership_policy_from_nonblue_static
        mh st cap inner_fuel;
      Readiness.chunked_mark_inner_loop_preservation_ready_from_target_membership
        mh st cap inner_fuel;
      Pres.chunked_mark_inner_loop_preserves_well_formed
        mh st cap inner_fuel;
      chunked_mark_inner_loop_preserves_nonblue_scanned_raw_targets
        mh st cap inner_fuel;
      let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
      chunked_mark_bounded_target_membership_policy_from_nonblue_static
        mh' cap (fuel - 1);
      Readiness.chunked_mark_bounded_target_membership_policy_step_intro
        mh cap fuel
    end
  end

let chunked_mark_bounded_preservation_ready_from_nonblue_static
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_nonblue_scanned_raw_targets_in_major mh)
      (ensures
        Pres.chunked_mark_bounded_preservation_ready mh cap fuel)
  =
  chunked_mark_bounded_target_membership_policy_from_nonblue_static
    mh cap fuel;
  Readiness.chunked_mark_bounded_preservation_ready_from_target_membership
    mh cap fuel
#pop-options
