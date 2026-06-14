module GC.Spec.ChunkedMark.Preservation

module U64 = FStar.UInt64
module Seq = FStar.Seq
module SeqProps = FStar.Seq.Properties

open GC.Spec.Base
open GC.Spec.Heap

module Header = GC.Lib.Header
module MH = GC.Spec.MajorHeap
module MHReadFrame = GC.Spec.MajorHeap.ReadFrame
module Obj = GC.Spec.Object
module SpecMajorAlloc = GC.Spec.MajorAllocator
module MarkDefs = GC.Spec.ChunkedMark.Defs
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module SweepLive = GC.Spec.ChunkedSweepCoalesce.LivePreservation
module RangePres = GC.Spec.ChunkedSweepCoalesce.RangePreservation

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let nat_nonzero_pos (n: nat)
  : Lemma (requires n <> 0) (ensures n > 0)
  = ()

let distinct_word_aligned_addrs_disjoint
    (a b: hp_addr)
  : Lemma
      (requires a <> b)
      (ensures
        U64.v a + U64.v mword <= U64.v b \/
        U64.v b + U64.v mword <= U64.v a)
  =
  assert (U64.v mword == 8);
  if U64.v a < U64.v b then begin
    assert (U64.v a % 8 == 0);
    assert (U64.v b % 8 == 0);
    assert (U64.v a + 8 <= U64.v b)
  end else begin
    assert (U64.v b < U64.v a);
    assert (U64.v a % 8 == 0);
    assert (U64.v b % 8 == 0);
    assert (U64.v b + 8 <= U64.v a)
  end

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

let stack_objects_in_major_empty
    (mh: MH.major_heap)
  : Lemma
      (ensures stack_objects_in_major mh Seq.empty)
  =
  let each (obj: obj_addr)
    : Lemma
        (requires Seq.mem obj Seq.empty)
        (ensures Seq.mem obj (MH.major_objects mh))
    = ()
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each)

let stack_objects_in_major_cons
    (mh: MH.major_heap)
    (obj: obj_addr)
    (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.mem obj (MH.major_objects mh) /\
        stack_objects_in_major mh st)
      (ensures stack_objects_in_major mh (Seq.cons obj st))
  =
  let each (target: obj_addr)
    : Lemma
        (requires Seq.mem target (Seq.cons obj st))
        (ensures Seq.mem target (MH.major_objects mh))
    =
    if Seq.mem target st then
      stack_objects_in_major_elim mh st target
    else begin
      GC.Spec.SeqMemLemmas.seq_mem_cons_not_mem_implies_eq obj target st;
      assert (target == obj);
      assert (Seq.mem target (MH.major_objects mh))
    end
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

let chunked_set_object_color_member_read_header
    (mh: MH.major_heap)
    (obj: obj_addr)
    (color: Header.color_sem)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        (match SweepDefs.chunked_read_header mh obj with
         | Some hdr ->
           SweepDefs.chunked_read_header
             (SweepDefs.chunked_set_object_color mh obj color) obj ==
           Some (Obj.colorHeader hdr color)
         | None -> False))
  =
  let hd = hd_address obj in
  color_member_read_witness mh obj;
  SweepDefs.chunked_read_header_step mh obj;
  match SweepDefs.chunked_read_header mh obj with
  | None -> assert False
  | Some hdr ->
    let new_hdr = Obj.colorHeader hdr color in
    SweepDefs.chunked_set_object_color_some mh obj color hdr;
    MHReadFrame.write_word_in_major_preserves_same_read mh hd hdr new_hdr;
    match MH.write_word_in_major mh hd new_hdr with
    | None -> assert False
    | Some mh' ->
      SpecMajorAlloc.major_write_word_or_same_some mh mh' hd new_hdr;
      assert (SweepDefs.chunked_set_object_color mh obj color == mh');
      SweepDefs.chunked_read_header_step mh' obj

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_set_object_color_preserves_wosize_of_object
    (mh: MH.major_heap)
    (obj target: obj_addr)
    (color: Header.color_sem)
  : Lemma
      (requires
      MH.well_formed_major_heap mh /\
      Seq.mem obj (MH.major_objects mh) /\
      Seq.mem target (MH.major_objects mh))
      (ensures
      SweepDefs.chunked_wosize_of_object
        (SweepDefs.chunked_set_object_color mh obj color) target ==
      SweepDefs.chunked_wosize_of_object mh target)
  =
  color_member_read_witness mh obj;
  color_member_read_witness mh target;
  SweepDefs.chunked_read_header_step mh target;
  match SweepDefs.chunked_read_header mh target with
  | None -> assert False
  | Some target_hdr ->
    SweepDefs.chunked_wosize_of_object_some mh target target_hdr;
    if obj = target then begin
      chunked_set_object_color_member_read_header mh obj color;
      assert (SweepDefs.chunked_read_header
      (SweepDefs.chunked_set_object_color mh obj color) target ==
      Some (Obj.colorHeader target_hdr color));
      Obj.colorHeader_preserves_wosize target_hdr color;
      SweepDefs.chunked_wosize_of_object_some
      (SweepDefs.chunked_set_object_color mh obj color)
      target
      (Obj.colorHeader target_hdr color)
    end else begin
      match SweepDefs.chunked_read_header mh obj with
      | None -> assert False
      | Some obj_hdr ->
      let obj_hd = hd_address obj in
      let target_hd = hd_address target in
      let new_hdr = Obj.colorHeader obj_hdr color in
      SweepDefs.chunked_read_header_step mh obj;
      SweepDefs.chunked_set_object_color_some mh obj color obj_hdr;
      MHReadFrame.write_word_in_major_preserves_same_read
        mh obj_hd obj_hdr new_hdr;
      match MH.write_word_in_major mh obj_hd new_hdr with
      | None -> assert False
      | Some mh' ->
        SpecMajorAlloc.major_write_word_or_same_some
          mh mh' obj_hd new_hdr;
        assert (SweepDefs.chunked_set_object_color mh obj color == mh');
        hd_address_injective obj target;
        assert (obj_hd <> target_hd);
        distinct_word_aligned_addrs_disjoint obj_hd target_hd;
        assert (MH.read_word_in_major mh target_hd == Some target_hdr);
        MHReadFrame.write_word_in_major_preserves_other_read
          mh obj_hd new_hdr target_hd target_hdr;
        assert (MH.read_word_in_major mh' target_hd == Some target_hdr);
        SweepDefs.chunked_read_header_step mh' target;
        assert (SweepDefs.chunked_read_header mh' target == Some target_hdr);
        SweepDefs.chunked_wosize_of_object_some mh' target target_hdr
    end
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_object_header_disjoint_from_field_addr
    (mh: MH.major_heap)
    (obj target: obj_addr)
    (hdr: U64.t)
    (i: U64.t{U64.v i >= 1})
    (field_addr: hp_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh) /\
        MH.read_word_in_major mh (hd_address target) == Some hdr /\
        U64.v i <= U64.v (Obj.getWosize hdr) /\
        U64.v field_addr ==
          U64.v (hd_address target) + U64.v mword * U64.v i)
      (ensures
        U64.v (hd_address obj) + U64.v mword <= U64.v field_addr \/
        U64.v field_addr + U64.v mword <= U64.v (hd_address obj))
  =
  let target_hd = hd_address target in
  let obj_hd = hd_address obj in
  MH.read_word_in_major_lookup_index mh target_hd hdr;
  let target_idx = MH.lookup_chunk_index_value mh target_hd in
  assert (target_idx < Seq.length mh);
  assert (MH.lookup_chunk_index mh target_hd == Some target_idx);
  assert (MH.word_in_chunk (Seq.index mh target_idx) target_hd);
  assert (MH.read_word_in_chunk (Seq.index mh target_idx) target_hd == hdr);
  MH.major_objects_member_in_lookup_chunk mh target_idx target;
  assert (Seq.mem target (MH.objects_in_chunk (Seq.index mh target_idx)));
  MH.objects_in_chunk_member_header_fits (Seq.index mh target_idx) target;
  assert (MH.object_header_size_fits_in_chunk (Seq.index mh target_idx) target);
  assert (MH.object_wosize_in_chunk (Seq.index mh target_idx) target ==
          U64.v (Obj.getWosize hdr));
  hd_address_spec target;
  assert (U64.v target_hd + U64.v mword == U64.v target);
  assert (U64.v field_addr ==
          U64.v target_hd + U64.v mword * U64.v i);
  assert (U64.v target <= U64.v field_addr);
  assert (U64.v field_addr + U64.v mword <=
          U64.v target +
          MH.object_wosize_in_chunk (Seq.index mh target_idx) target *
            U64.v mword);
  MH.major_object_payload_word_in_lookup_chunk
    mh target_idx target field_addr;
  assert (MH.word_in_chunk (Seq.index mh target_idx) field_addr);
  MH.major_objects_member_header_read_some mh obj;
  match MH.read_word_in_major mh obj_hd with
  | None -> assert False
  | Some obj_hdr ->
    MH.read_word_in_major_lookup_index mh obj_hd obj_hdr;
    let obj_idx = MH.lookup_chunk_index_value mh obj_hd in
    assert (obj_idx < Seq.length mh);
    assert (MH.lookup_chunk_index mh obj_hd == Some obj_idx);
    assert (MH.word_in_chunk (Seq.index mh obj_idx) obj_hd);
    if obj_idx <> target_idx then begin
      MH.chunks_pairwise_disjoint_index mh obj_idx target_idx;
      MH.chunks_disjoint_words_disjoint
        (Seq.index mh obj_idx) (Seq.index mh target_idx)
        obj_hd field_addr
    end else begin
      assert (Seq.index mh obj_idx == Seq.index mh target_idx);
      let c = Seq.index mh target_idx in
      MH.major_objects_member_in_lookup_chunk mh target_idx obj;
      assert (Seq.mem obj (MH.objects_in_chunk c));
      assert (Seq.mem target (MH.objects_in_chunk c));
      if obj = target then begin
        assert (obj_hd == target_hd);
        assert (U64.v target_hd + U64.v mword <= U64.v field_addr)
      end else if U64.v obj < U64.v target then begin
        hd_address_spec obj;
        assert (U64.v obj_hd + U64.v mword == U64.v obj);
        assert (U64.v field_addr >= U64.v target);
        assert (U64.v obj <= U64.v target);
        assert (U64.v obj_hd + U64.v mword <= U64.v field_addr)
      end else begin
        assert (U64.v target < U64.v obj);
        MH.objects_in_chunk_separated c target obj;
        let target_end =
          U64.v target +
          MH.object_wosize_in_chunk c target * U64.v mword in
        assert (U64.v obj > target_end);
        MH.next_object_start_aligned
          target_hd
          (1 + MH.object_wosize_in_chunk c target);
        assert (target_end ==
          U64.v target_hd +
          (1 + MH.object_wosize_in_chunk c target) * U64.v mword);
        assert (target_end % U64.v mword == 0);
        MH.word_aligned_gt_at_least_mword (U64.v obj) target_end;
        hd_address_spec obj;
        assert (U64.v obj_hd + U64.v mword == U64.v obj);
        assert (U64.v obj_hd >= target_end);
        assert (U64.v field_addr + U64.v mword <= target_end);
        assert (U64.v field_addr + U64.v mword <= U64.v obj_hd)
      end
    end

let chunked_set_object_color_preserves_get_field
    (mh: MH.major_heap)
    (obj target: obj_addr)
    (color: Header.color_sem)
    (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh target))
      (ensures
        MarkDefs.chunked_get_field
          (SweepDefs.chunked_set_object_color mh obj color) target i ==
        MarkDefs.chunked_get_field mh target i)
  =
  color_member_read_witness mh obj;
  color_member_read_witness mh target;
  SweepDefs.chunked_read_header_step mh target;
  match SweepDefs.chunked_read_header mh target with
  | None -> assert False
  | Some target_hdr ->
    SweepDefs.chunked_wosize_of_object_some mh target target_hdr;
    let target_hd = hd_address target in
    hd_address_spec target;
    MH.read_word_in_major_lookup_index mh target_hd target_hdr;
    let target_idx = MH.lookup_chunk_index_value mh target_hd in
    assert (target_idx < Seq.length mh);
    assert (MH.lookup_chunk_index mh target_hd == Some target_idx);
    assert (MH.word_in_chunk (Seq.index mh target_idx) target_hd);
    assert (MH.read_word_in_chunk (Seq.index mh target_idx) target_hd ==
            target_hdr);
    MH.major_objects_member_in_lookup_chunk mh target_idx target;
    assert (Seq.mem target (MH.objects_in_chunk (Seq.index mh target_idx)));
    MH.objects_in_chunk_member_header_fits (Seq.index mh target_idx) target;
    assert (MH.object_header_size_fits_in_chunk
              (Seq.index mh target_idx) target);
    assert (MH.object_wosize_in_chunk (Seq.index mh target_idx) target ==
            U64.v (Obj.getWosize target_hdr));
    assert (U64.v target_hd + U64.v mword == U64.v target);
    assert (U64.v target_hd + U64.v mword * U64.v i + U64.v mword <=
            U64.v target_hd +
            (1 + MH.object_wosize_in_chunk (Seq.index mh target_idx) target) *
              U64.v mword);
    assert (U64.v target_hd + U64.v mword * U64.v i + U64.v mword <=
            heap_size);
    let field_addr: hp_addr =
      U64.add target_hd (U64.mul mword i) in
    assert (U64.v field_addr ==
            U64.v target_hd + U64.v mword * U64.v i);
    assert (U64.v target <= U64.v field_addr);
    assert (U64.v field_addr + U64.v mword <=
            U64.v target +
            MH.object_wosize_in_chunk (Seq.index mh target_idx) target *
              U64.v mword);
    MH.major_object_payload_word_in_lookup_chunk
      mh target_idx target field_addr;
    assert (MH.word_in_chunk (Seq.index mh target_idx) field_addr);
    MH.read_word_in_major_at_lookup_index mh field_addr target_idx;
    let old =
      MH.read_word_in_chunk (Seq.index mh target_idx) field_addr in
    assert (MH.read_word_in_major mh field_addr == Some old);
    MarkDefs.chunked_get_field_read_some mh target i old;
    SweepDefs.chunked_read_header_step mh obj;
    match SweepDefs.chunked_read_header mh obj with
    | None -> assert False
    | Some obj_hdr ->
      let obj_hd = hd_address obj in
      let new_hdr = Obj.colorHeader obj_hdr color in
      SweepDefs.chunked_set_object_color_some mh obj color obj_hdr;
      assert (MH.read_word_in_major mh obj_hd == Some obj_hdr);
      MHReadFrame.write_word_in_major_preserves_same_read
        mh obj_hd obj_hdr new_hdr;
      chunked_object_header_disjoint_from_field_addr
        mh obj target target_hdr i field_addr;
      MHReadFrame.write_word_in_major_preserves_other_read
        mh obj_hd new_hdr field_addr old;
      match MH.write_word_in_major mh obj_hd new_hdr with
      | None -> assert False
      | Some mh' ->
        SpecMajorAlloc.major_write_word_or_same_some mh mh' obj_hd new_hdr;
        assert (SweepDefs.chunked_set_object_color mh obj color == mh');
        assert (MH.read_word_in_major mh' field_addr == Some old);
        MarkDefs.chunked_get_field_read_some mh' target i old
#pop-options

let chunked_set_object_color_preserves_ranges
    (mh: MH.major_heap)
    (obj: obj_addr)
    (color: Header.color_sem)
  : Lemma
      (ensures
        RangePres.same_chunk_ranges mh
          (SweepDefs.chunked_set_object_color mh obj color))
  =
  match SweepDefs.chunked_read_header mh obj with
  | None ->
    SweepDefs.chunked_set_object_color_none mh obj color;
    RangePres.same_chunk_ranges_refl mh
  | Some hdr ->
    SweepDefs.chunked_set_object_color_some mh obj color hdr;
    RangePres.major_write_word_or_same_preserves_ranges
      mh (hd_address obj) (Obj.colorHeader hdr color)

let chunked_set_object_color_member_sets_color
    (mh: MH.major_heap)
    (obj: obj_addr)
    (color: Header.color_sem)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        SweepDefs.chunked_color_of_object
          (SweepDefs.chunked_set_object_color mh obj color) obj ==
        Some color)
  =
  color_member_read_witness mh obj;
  match SweepDefs.chunked_read_header mh obj with
  | None -> assert False
  | Some hdr ->
    chunked_set_object_color_member_read_header mh obj color;
    Obj.colorHeader_getColor hdr color;
    SweepDefs.chunked_color_of_object_some
      (SweepDefs.chunked_set_object_color mh obj color)
      obj
      (Obj.colorHeader hdr color)

let chunked_make_gray_makes_gray
    (mh: MH.major_heap)
    (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        SweepDefs.chunked_color_of_object
          (MarkDefs.chunked_make_gray mh obj) obj ==
        Some Header.Gray)
  =
  MarkDefs.chunked_make_gray_step mh obj;
  chunked_set_object_color_member_sets_color mh obj Header.Gray

let chunked_make_gray_preserves_wosize_of_object
    (mh: MH.major_heap)
    (obj target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        SweepDefs.chunked_wosize_of_object
          (MarkDefs.chunked_make_gray mh obj) target ==
        SweepDefs.chunked_wosize_of_object mh target)
  =
  MarkDefs.chunked_make_gray_step mh obj;
  chunked_set_object_color_preserves_wosize_of_object
    mh obj target Header.Gray

let chunked_make_gray_preserves_get_field
    (mh: MH.major_heap)
    (obj target: obj_addr)
    (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh target))
      (ensures
        MarkDefs.chunked_get_field
          (MarkDefs.chunked_make_gray mh obj) target i ==
        MarkDefs.chunked_get_field mh target i)
  =
  MarkDefs.chunked_make_gray_step mh obj;
  chunked_set_object_color_preserves_get_field
    mh obj target Header.Gray i

let chunked_make_gray_preserves_ranges
    (mh: MH.major_heap)
    (obj: obj_addr)
  : Lemma
      (ensures
        RangePres.same_chunk_ranges mh (MarkDefs.chunked_make_gray mh obj))
  =
  MarkDefs.chunked_make_gray_step mh obj;
  chunked_set_object_color_preserves_ranges mh obj Header.Gray

let chunked_make_black_makes_black
    (mh: MH.major_heap)
    (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures SweepDefs.chunked_is_black (MarkDefs.chunked_make_black mh obj) obj)
  =
  MarkDefs.chunked_make_black_step mh obj;
  chunked_set_object_color_member_sets_color mh obj Header.Black;
  SweepDefs.chunked_is_black_from_color (MarkDefs.chunked_make_black mh obj) obj

let chunked_make_black_preserves_wosize_of_object
    (mh: MH.major_heap)
    (obj target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        SweepDefs.chunked_wosize_of_object
          (MarkDefs.chunked_make_black mh obj) target ==
        SweepDefs.chunked_wosize_of_object mh target)
  =
  MarkDefs.chunked_make_black_step mh obj;
  chunked_set_object_color_preserves_wosize_of_object
    mh obj target Header.Black

let chunked_make_black_preserves_get_field
    (mh: MH.major_heap)
    (obj target: obj_addr)
    (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh target))
      (ensures
        MarkDefs.chunked_get_field
          (MarkDefs.chunked_make_black mh obj) target i ==
        MarkDefs.chunked_get_field mh target i)
  =
  MarkDefs.chunked_make_black_step mh obj;
  chunked_set_object_color_preserves_get_field
    mh obj target Header.Black i

let chunked_make_black_preserves_ranges
    (mh: MH.major_heap)
    (obj: obj_addr)
  : Lemma
      (ensures
        RangePres.same_chunk_ranges mh (MarkDefs.chunked_make_black mh obj))
  =
  MarkDefs.chunked_make_black_step mh obj;
  chunked_set_object_color_preserves_ranges mh obj Header.Black

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_set_object_color_preserves_other_blue
    (mh: MH.major_heap)
    (obj target: obj_addr)
    (color: Header.color_sem)
  : Lemma
      (requires
        obj <> target /\
        SweepDefs.chunked_is_blue mh target)
      (ensures
        SweepDefs.chunked_is_blue
          (SweepDefs.chunked_set_object_color mh obj color) target)
  =
  let target_hd = hd_address target in
  SweepDefs.chunked_read_header_step mh target;
  SweepDefs.chunked_is_blue_read_header mh target;
  match SweepDefs.chunked_read_header mh target with
  | None -> assert False
  | Some target_hdr ->
    let obj_hd = hd_address obj in
    hd_address_injective obj target;
    match SweepDefs.chunked_read_header mh obj with
    | None ->
      SweepDefs.chunked_set_object_color_none mh obj color;
      SweepDefs.chunked_is_blue_read_header mh target;
      SweepDefs.chunked_color_of_object_some mh target target_hdr;
      assert (SweepDefs.chunked_color_of_object mh target == Some Header.Blue);
      SweepDefs.chunked_is_blue_from_color mh target
    | Some obj_hdr ->
      let new_hdr = Obj.colorHeader obj_hdr color in
      SweepDefs.chunked_read_header_step mh obj;
      SweepDefs.chunked_set_object_color_some mh obj color obj_hdr;
      MHReadFrame.write_word_in_major_preserves_same_read
        mh obj_hd obj_hdr new_hdr;
      match MH.write_word_in_major mh obj_hd new_hdr with
      | None -> assert False
      | Some mh' ->
        assert (obj_hd <> target_hd);
        distinct_word_aligned_addrs_disjoint obj_hd target_hd;
        assert (MH.read_word_in_major mh target_hd == Some target_hdr);
        MHReadFrame.write_word_in_major_preserves_other_read
          mh obj_hd new_hdr target_hd target_hdr;
        SpecMajorAlloc.major_write_word_or_same_some mh mh' obj_hd new_hdr;
        assert (SweepDefs.chunked_set_object_color mh obj color == mh');
        SweepDefs.chunked_read_header_step mh' target;
        SweepDefs.chunked_color_of_object_some mh' target target_hdr;
        assert (SweepDefs.chunked_color_of_object mh' target ==
                Some Header.Blue);
        SweepDefs.chunked_is_blue_from_color mh' target

let chunked_set_object_color_preserves_other_blue_back
    (mh: MH.major_heap)
    (obj target: obj_addr)
    (color: Header.color_sem)
  : Lemma
      (requires
        obj <> target /\
        SweepDefs.chunked_is_blue
          (SweepDefs.chunked_set_object_color mh obj color) target)
      (ensures SweepDefs.chunked_is_blue mh target)
  =
  let target_hd = hd_address target in
  let obj_hd = hd_address obj in
  hd_address_injective obj target;
  SweepDefs.chunked_read_header_step mh obj;
  match SweepDefs.chunked_read_header mh obj with
  | None ->
    SweepDefs.chunked_set_object_color_none mh obj color
  | Some obj_hdr ->
    let new_hdr = Obj.colorHeader obj_hdr color in
    SweepDefs.chunked_set_object_color_some mh obj color obj_hdr;
    match MH.write_word_in_major mh obj_hd new_hdr with
    | None ->
      SpecMajorAlloc.major_write_word_or_same_none mh obj_hd new_hdr
    | Some mh' ->
      SpecMajorAlloc.major_write_word_or_same_some mh mh' obj_hd new_hdr;
      assert (SweepDefs.chunked_set_object_color mh obj color == mh');
      SweepDefs.chunked_is_blue_read_header mh' target;
      SweepDefs.chunked_read_header_step mh' target;
      match SweepDefs.chunked_read_header mh' target with
      | None -> assert False
      | Some target_hdr ->
        assert (obj_hd <> target_hd);
        distinct_word_aligned_addrs_disjoint obj_hd target_hd;
        assert (MH.read_word_in_major mh' target_hd == Some target_hdr);
        MHReadFrame.write_word_in_major_preserves_other_read_back
          mh obj_hd new_hdr target_hd target_hdr;
        SweepDefs.chunked_read_header_step mh target;
        assert (SweepDefs.chunked_read_header mh target == Some target_hdr);
        SweepDefs.chunked_color_of_object_some mh target target_hdr;
        assert (Obj.getColor target_hdr == Header.Blue);
        SweepDefs.chunked_is_blue_from_color mh target

let chunked_set_object_color_preserves_other_blue_status
    (mh: MH.major_heap)
    (obj target: obj_addr)
    (color: Header.color_sem)
  : Lemma
      (requires obj <> target)
      (ensures
        SweepDefs.chunked_is_blue
          (SweepDefs.chunked_set_object_color mh obj color) target ==
        SweepDefs.chunked_is_blue mh target)
  =
  if SweepDefs.chunked_is_blue mh target then
    chunked_set_object_color_preserves_other_blue mh obj target color
  else if SweepDefs.chunked_is_blue
            (SweepDefs.chunked_set_object_color mh obj color) target then begin
    chunked_set_object_color_preserves_other_blue_back mh obj target color;
    assert False
  end

let chunked_make_gray_not_blue
    (mh: MH.major_heap)
    (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        ~(SweepDefs.chunked_is_blue (MarkDefs.chunked_make_gray mh obj) obj))
  =
  chunked_make_gray_makes_gray mh obj;
  if SweepDefs.chunked_is_blue (MarkDefs.chunked_make_gray mh obj) obj then begin
    SweepDefs.chunked_is_blue_read_header
      (MarkDefs.chunked_make_gray mh obj) obj;
    SweepDefs.chunked_color_of_object_elim
      (MarkDefs.chunked_make_gray mh obj) obj Header.Gray;
    assert False
  end

let chunked_make_black_not_blue
    (mh: MH.major_heap)
    (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        ~(SweepDefs.chunked_is_blue (MarkDefs.chunked_make_black mh obj) obj))
  =
  MarkDefs.chunked_make_black_step mh obj;
  chunked_set_object_color_member_sets_color mh obj Header.Black;
  if SweepDefs.chunked_is_blue (MarkDefs.chunked_make_black mh obj) obj then begin
    SweepDefs.chunked_is_blue_read_header
      (MarkDefs.chunked_make_black mh obj) obj;
    SweepDefs.chunked_color_of_object_elim
      (MarkDefs.chunked_make_black mh obj) obj Header.Black;
    assert False
  end

let chunked_make_gray_preserves_other_blue_status
    (mh: MH.major_heap)
    (obj target: obj_addr)
  : Lemma
      (requires obj <> target)
      (ensures
        SweepDefs.chunked_is_blue (MarkDefs.chunked_make_gray mh obj) target ==
        SweepDefs.chunked_is_blue mh target)
  =
  MarkDefs.chunked_make_gray_step mh obj;
  chunked_set_object_color_preserves_other_blue_status mh obj target Header.Gray

let chunked_make_black_preserves_other_blue_status
    (mh: MH.major_heap)
    (obj target: obj_addr)
  : Lemma
      (requires obj <> target)
      (ensures
        SweepDefs.chunked_is_blue (MarkDefs.chunked_make_black mh obj) target ==
        SweepDefs.chunked_is_blue mh target)
  =
  MarkDefs.chunked_make_black_step mh obj;
  chunked_set_object_color_preserves_other_blue_status mh obj target Header.Black

let chunked_set_object_color_preserves_other_white
    (mh: MH.major_heap)
    (obj target: obj_addr)
    (color: Header.color_sem)
  : Lemma
      (requires
        obj <> target /\
        SweepDefs.chunked_is_white mh target)
      (ensures
        SweepDefs.chunked_is_white
          (SweepDefs.chunked_set_object_color mh obj color) target)
  =
  let target_hd = hd_address target in
  SweepDefs.chunked_read_header_step mh target;
  SweepDefs.chunked_is_white_read_header mh target;
  match SweepDefs.chunked_read_header mh target with
  | None -> assert False
  | Some target_hdr ->
    let obj_hd = hd_address obj in
    hd_address_injective obj target;
    match SweepDefs.chunked_read_header mh obj with
    | None ->
      SweepDefs.chunked_set_object_color_none mh obj color;
      SweepDefs.chunked_is_white_read_header mh target;
      SweepDefs.chunked_color_of_object_some mh target target_hdr;
      assert (SweepDefs.chunked_color_of_object mh target == Some Header.White);
      SweepDefs.chunked_is_white_from_color mh target
    | Some obj_hdr ->
      let new_hdr = Obj.colorHeader obj_hdr color in
      SweepDefs.chunked_read_header_step mh obj;
      SweepDefs.chunked_set_object_color_some mh obj color obj_hdr;
      MHReadFrame.write_word_in_major_preserves_same_read
        mh obj_hd obj_hdr new_hdr;
      match MH.write_word_in_major mh obj_hd new_hdr with
      | None -> assert False
      | Some mh' ->
        assert (obj_hd <> target_hd);
        distinct_word_aligned_addrs_disjoint obj_hd target_hd;
        assert (MH.read_word_in_major mh target_hd == Some target_hdr);
        MHReadFrame.write_word_in_major_preserves_other_read
          mh obj_hd new_hdr target_hd target_hdr;
        SpecMajorAlloc.major_write_word_or_same_some mh mh' obj_hd new_hdr;
        assert (SweepDefs.chunked_set_object_color mh obj color == mh');
        SweepDefs.chunked_read_header_step mh' target;
        SweepDefs.chunked_color_of_object_some mh' target target_hdr;
        assert (SweepDefs.chunked_color_of_object mh' target ==
                Some Header.White);
        SweepDefs.chunked_is_white_from_color mh' target

let chunked_set_object_color_preserves_other_white_back
    (mh: MH.major_heap)
    (obj target: obj_addr)
    (color: Header.color_sem)
  : Lemma
      (requires
        obj <> target /\
        SweepDefs.chunked_is_white
          (SweepDefs.chunked_set_object_color mh obj color) target)
      (ensures SweepDefs.chunked_is_white mh target)
  =
  let target_hd = hd_address target in
  let obj_hd = hd_address obj in
  hd_address_injective obj target;
  SweepDefs.chunked_read_header_step mh obj;
  match SweepDefs.chunked_read_header mh obj with
  | None ->
    SweepDefs.chunked_set_object_color_none mh obj color
  | Some obj_hdr ->
    let new_hdr = Obj.colorHeader obj_hdr color in
    SweepDefs.chunked_set_object_color_some mh obj color obj_hdr;
    match MH.write_word_in_major mh obj_hd new_hdr with
    | None ->
      SpecMajorAlloc.major_write_word_or_same_none mh obj_hd new_hdr
    | Some mh' ->
      SpecMajorAlloc.major_write_word_or_same_some mh mh' obj_hd new_hdr;
      assert (SweepDefs.chunked_set_object_color mh obj color == mh');
      SweepDefs.chunked_is_white_read_header mh' target;
      SweepDefs.chunked_read_header_step mh' target;
      match SweepDefs.chunked_read_header mh' target with
      | None -> assert False
      | Some target_hdr ->
        assert (obj_hd <> target_hd);
        distinct_word_aligned_addrs_disjoint obj_hd target_hd;
        assert (MH.read_word_in_major mh' target_hd == Some target_hdr);
        MHReadFrame.write_word_in_major_preserves_other_read_back
          mh obj_hd new_hdr target_hd target_hdr;
        SweepDefs.chunked_read_header_step mh target;
        assert (SweepDefs.chunked_read_header mh target == Some target_hdr);
        SweepDefs.chunked_color_of_object_some mh target target_hdr;
        assert (Obj.getColor target_hdr == Header.White);
        SweepDefs.chunked_is_white_from_color mh target

let chunked_set_object_color_preserves_other_white_status
    (mh: MH.major_heap)
    (obj target: obj_addr)
    (color: Header.color_sem)
  : Lemma
      (requires obj <> target)
      (ensures
        SweepDefs.chunked_is_white
          (SweepDefs.chunked_set_object_color mh obj color) target ==
        SweepDefs.chunked_is_white mh target)
  =
  if SweepDefs.chunked_is_white mh target then
    chunked_set_object_color_preserves_other_white mh obj target color
  else if SweepDefs.chunked_is_white
            (SweepDefs.chunked_set_object_color mh obj color) target then begin
    chunked_set_object_color_preserves_other_white_back mh obj target color;
    assert False
  end

let chunked_make_gray_not_white
    (mh: MH.major_heap)
    (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        ~(SweepDefs.chunked_is_white (MarkDefs.chunked_make_gray mh obj) obj))
  =
  chunked_make_gray_makes_gray mh obj;
  if SweepDefs.chunked_is_white (MarkDefs.chunked_make_gray mh obj) obj then begin
    SweepDefs.chunked_is_white_read_header
      (MarkDefs.chunked_make_gray mh obj) obj;
    SweepDefs.chunked_color_of_object_elim
      (MarkDefs.chunked_make_gray mh obj) obj Header.Gray;
    assert False
  end

let chunked_make_black_not_white
    (mh: MH.major_heap)
    (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        ~(SweepDefs.chunked_is_white (MarkDefs.chunked_make_black mh obj) obj))
  =
  MarkDefs.chunked_make_black_step mh obj;
  chunked_set_object_color_member_sets_color mh obj Header.Black;
  if SweepDefs.chunked_is_white (MarkDefs.chunked_make_black mh obj) obj then begin
    SweepDefs.chunked_is_white_read_header
      (MarkDefs.chunked_make_black mh obj) obj;
    SweepDefs.chunked_color_of_object_elim
      (MarkDefs.chunked_make_black mh obj) obj Header.Black;
    assert False
  end

let chunked_make_gray_preserves_other_white_status
    (mh: MH.major_heap)
    (obj target: obj_addr)
  : Lemma
      (requires obj <> target)
      (ensures
        SweepDefs.chunked_is_white (MarkDefs.chunked_make_gray mh obj) target ==
        SweepDefs.chunked_is_white mh target)
  =
  MarkDefs.chunked_make_gray_step mh obj;
  chunked_set_object_color_preserves_other_white_status mh obj target Header.Gray

let chunked_make_black_preserves_other_white_status
    (mh: MH.major_heap)
    (obj target: obj_addr)
  : Lemma
      (requires obj <> target)
      (ensures
        SweepDefs.chunked_is_white (MarkDefs.chunked_make_black mh obj) target ==
        SweepDefs.chunked_is_white mh target)
  =
  MarkDefs.chunked_make_black_step mh obj;
  chunked_set_object_color_preserves_other_white_status mh obj target Header.Black

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_set_object_color_preserves_no_scan_status
    (mh: MH.major_heap)
    (obj target: obj_addr)
    (color: Header.color_sem)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        MarkDefs.chunked_is_no_scan
          (SweepDefs.chunked_set_object_color mh obj color) target ==
        MarkDefs.chunked_is_no_scan mh target)
  =
  color_member_read_witness mh obj;
  color_member_read_witness mh target;
  MarkDefs.chunked_is_no_scan_step mh target;
  SweepDefs.chunked_read_header_step mh target;
  match SweepDefs.chunked_read_header mh target with
  | None -> assert False
  | Some target_hdr ->
    SweepDefs.chunked_tag_of_object_some mh target target_hdr;
    if obj = target then begin
      chunked_set_object_color_member_read_header mh obj color;
      assert (SweepDefs.chunked_read_header
        (SweepDefs.chunked_set_object_color mh obj color) target ==
        Some (Obj.colorHeader target_hdr color));
      Obj.colorHeader_preserves_tag target_hdr color;
      SweepDefs.chunked_tag_of_object_some
        (SweepDefs.chunked_set_object_color mh obj color)
        target
        (Obj.colorHeader target_hdr color);
      MarkDefs.chunked_is_no_scan_step
        (SweepDefs.chunked_set_object_color mh obj color) target
    end else begin
      match SweepDefs.chunked_read_header mh obj with
      | None -> assert False
      | Some obj_hdr ->
        let obj_hd = hd_address obj in
        let target_hd = hd_address target in
        let new_hdr = Obj.colorHeader obj_hdr color in
        SweepDefs.chunked_read_header_step mh obj;
        SweepDefs.chunked_set_object_color_some mh obj color obj_hdr;
        MHReadFrame.write_word_in_major_preserves_same_read
          mh obj_hd obj_hdr new_hdr;
        match MH.write_word_in_major mh obj_hd new_hdr with
        | None -> assert False
        | Some mh' ->
          SpecMajorAlloc.major_write_word_or_same_some
            mh mh' obj_hd new_hdr;
          assert (SweepDefs.chunked_set_object_color mh obj color == mh');
          hd_address_injective obj target;
          assert (obj_hd <> target_hd);
          distinct_word_aligned_addrs_disjoint obj_hd target_hd;
          assert (MH.read_word_in_major mh target_hd == Some target_hdr);
          MHReadFrame.write_word_in_major_preserves_other_read
            mh obj_hd new_hdr target_hd target_hdr;
          assert (MH.read_word_in_major mh' target_hd == Some target_hdr);
          SweepDefs.chunked_read_header_step mh' target;
          assert (SweepDefs.chunked_read_header mh' target == Some target_hdr);
          SweepDefs.chunked_tag_of_object_some mh' target target_hdr;
          MarkDefs.chunked_is_no_scan_step mh' target
    end

let chunked_make_gray_preserves_no_scan_status
    (mh: MH.major_heap)
    (obj target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        MarkDefs.chunked_is_no_scan
          (MarkDefs.chunked_make_gray mh obj) target ==
        MarkDefs.chunked_is_no_scan mh target)
  =
  MarkDefs.chunked_make_gray_step mh obj;
  chunked_set_object_color_preserves_no_scan_status mh obj target Header.Gray

let chunked_make_black_preserves_no_scan_status
    (mh: MH.major_heap)
    (obj target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        MarkDefs.chunked_is_no_scan
          (MarkDefs.chunked_make_black mh obj) target ==
        MarkDefs.chunked_is_no_scan mh target)
  =
  MarkDefs.chunked_make_black_step mh obj;
  chunked_set_object_color_preserves_no_scan_status mh obj target Header.Black
#pop-options
#pop-options

let chunked_set_object_color_preserves_other_black
    (mh: MH.major_heap)
    (obj target: obj_addr)
    (color: Header.color_sem)
  : Lemma
      (requires
        obj <> target /\
        SweepDefs.chunked_is_black mh target)
      (ensures
        SweepDefs.chunked_is_black
          (SweepDefs.chunked_set_object_color mh obj color) target)
  =
  let target_hd = hd_address target in
  SweepDefs.chunked_read_header_step mh target;
  SweepDefs.chunked_is_black_read_header mh target;
  match SweepDefs.chunked_read_header mh target with
  | None -> assert False
  | Some target_hdr ->
    let obj_hd = hd_address obj in
    hd_address_injective obj target;
    match SweepDefs.chunked_read_header mh obj with
    | None ->
      SweepDefs.chunked_set_object_color_none mh obj color;
      SweepDefs.chunked_is_black_read_header mh target;
      SweepDefs.chunked_color_of_object_some mh target target_hdr;
      assert (SweepDefs.chunked_color_of_object mh target == Some Header.Black);
      SweepDefs.chunked_is_black_from_color mh target
    | Some obj_hdr ->
      let new_hdr = Obj.colorHeader obj_hdr color in
      SweepDefs.chunked_read_header_step mh obj;
      SweepDefs.chunked_set_object_color_some mh obj color obj_hdr;
      MHReadFrame.write_word_in_major_preserves_same_read
        mh obj_hd obj_hdr new_hdr;
      match MH.write_word_in_major mh obj_hd new_hdr with
      | None -> assert False
      | Some mh' ->
        assert (obj_hd <> target_hd);
        distinct_word_aligned_addrs_disjoint obj_hd target_hd;
        assert (MH.read_word_in_major mh target_hd == Some target_hdr);
        MHReadFrame.write_word_in_major_preserves_other_read
          mh obj_hd new_hdr target_hd target_hdr;
        SpecMajorAlloc.major_write_word_or_same_some mh mh' obj_hd new_hdr;
        assert (SweepDefs.chunked_set_object_color mh obj color == mh');
        SweepDefs.chunked_read_header_step mh' target;
        SweepDefs.chunked_color_of_object_some mh' target target_hdr;
        assert (SweepDefs.chunked_color_of_object mh' target ==
                Some Header.Black);
        SweepDefs.chunked_is_black_from_color mh' target

let chunked_set_object_color_preserves_other_black_back
    (mh: MH.major_heap)
    (obj target: obj_addr)
    (color: Header.color_sem)
  : Lemma
      (requires
        obj <> target /\
        SweepDefs.chunked_is_black
          (SweepDefs.chunked_set_object_color mh obj color) target)
      (ensures SweepDefs.chunked_is_black mh target)
  =
  let target_hd = hd_address target in
  let obj_hd = hd_address obj in
  hd_address_injective obj target;
  SweepDefs.chunked_read_header_step mh obj;
  match SweepDefs.chunked_read_header mh obj with
  | None ->
    SweepDefs.chunked_set_object_color_none mh obj color
  | Some obj_hdr ->
    let new_hdr = Obj.colorHeader obj_hdr color in
    SweepDefs.chunked_set_object_color_some mh obj color obj_hdr;
    match MH.write_word_in_major mh obj_hd new_hdr with
    | None ->
      SpecMajorAlloc.major_write_word_or_same_none mh obj_hd new_hdr
    | Some mh' ->
      SpecMajorAlloc.major_write_word_or_same_some mh mh' obj_hd new_hdr;
      assert (SweepDefs.chunked_set_object_color mh obj color == mh');
      SweepDefs.chunked_is_black_read_header mh' target;
      SweepDefs.chunked_read_header_step mh' target;
      match SweepDefs.chunked_read_header mh' target with
      | None -> assert False
      | Some target_hdr ->
        assert (obj_hd <> target_hd);
        distinct_word_aligned_addrs_disjoint obj_hd target_hd;
        assert (MH.read_word_in_major mh' target_hd == Some target_hdr);
        MHReadFrame.write_word_in_major_preserves_other_read_back
          mh obj_hd new_hdr target_hd target_hdr;
        SweepDefs.chunked_read_header_step mh target;
        assert (SweepDefs.chunked_read_header mh target == Some target_hdr);
        SweepDefs.chunked_color_of_object_some mh target target_hdr;
        assert (Obj.getColor target_hdr == Header.Black);
        SweepDefs.chunked_is_black_from_color mh target

let chunked_set_object_color_preserves_other_black_status
    (mh: MH.major_heap)
    (obj target: obj_addr)
    (color: Header.color_sem)
  : Lemma
      (requires obj <> target)
      (ensures
        SweepDefs.chunked_is_black
          (SweepDefs.chunked_set_object_color mh obj color) target ==
        SweepDefs.chunked_is_black mh target)
  =
  if SweepDefs.chunked_is_black mh target then
    chunked_set_object_color_preserves_other_black mh obj target color
  else if SweepDefs.chunked_is_black
            (SweepDefs.chunked_set_object_color mh obj color) target then begin
    chunked_set_object_color_preserves_other_black_back mh obj target color;
    assert False
  end

let chunked_set_object_color_preserves_other_gray
    (mh: MH.major_heap)
    (obj target: obj_addr)
    (color: Header.color_sem)
  : Lemma
      (requires
        obj <> target /\
        SweepDefs.chunked_color_of_object mh target == Some Header.Gray)
      (ensures
        SweepDefs.chunked_color_of_object
          (SweepDefs.chunked_set_object_color mh obj color) target ==
        Some Header.Gray)
  =
  let target_hd = hd_address target in
  SweepDefs.chunked_read_header_step mh target;
  SweepDefs.chunked_color_of_object_elim mh target Header.Gray;
  match SweepDefs.chunked_read_header mh target with
  | None -> assert False
  | Some target_hdr ->
    assert (Obj.getColor target_hdr == Header.Gray);
    let obj_hd = hd_address obj in
    hd_address_injective obj target;
    match SweepDefs.chunked_read_header mh obj with
    | None ->
      SweepDefs.chunked_set_object_color_none mh obj color
    | Some obj_hdr ->
      let new_hdr = Obj.colorHeader obj_hdr color in
      SweepDefs.chunked_read_header_step mh obj;
      SweepDefs.chunked_set_object_color_some mh obj color obj_hdr;
      MHReadFrame.write_word_in_major_preserves_same_read
        mh obj_hd obj_hdr new_hdr;
      match MH.write_word_in_major mh obj_hd new_hdr with
      | None -> assert False
      | Some mh' ->
        assert (obj_hd <> target_hd);
        distinct_word_aligned_addrs_disjoint obj_hd target_hd;
        assert (MH.read_word_in_major mh target_hd == Some target_hdr);
        MHReadFrame.write_word_in_major_preserves_other_read
          mh obj_hd new_hdr target_hd target_hdr;
        SpecMajorAlloc.major_write_word_or_same_some mh mh' obj_hd new_hdr;
        assert (SweepDefs.chunked_set_object_color mh obj color == mh');
        SweepDefs.chunked_read_header_step mh' target;
        SweepDefs.chunked_color_of_object_some mh' target target_hdr

let chunked_set_object_color_preserves_other_gray_back
    (mh: MH.major_heap)
    (obj target: obj_addr)
    (color: Header.color_sem)
  : Lemma
      (requires
        obj <> target /\
        SweepDefs.chunked_color_of_object
          (SweepDefs.chunked_set_object_color mh obj color) target ==
        Some Header.Gray)
      (ensures SweepDefs.chunked_color_of_object mh target == Some Header.Gray)
  =
  let target_hd = hd_address target in
  let obj_hd = hd_address obj in
  hd_address_injective obj target;
  SweepDefs.chunked_read_header_step mh obj;
  match SweepDefs.chunked_read_header mh obj with
  | None ->
    SweepDefs.chunked_set_object_color_none mh obj color
  | Some obj_hdr ->
    let new_hdr = Obj.colorHeader obj_hdr color in
    SweepDefs.chunked_set_object_color_some mh obj color obj_hdr;
    match MH.write_word_in_major mh obj_hd new_hdr with
    | None ->
      SpecMajorAlloc.major_write_word_or_same_none mh obj_hd new_hdr
    | Some mh' ->
      SpecMajorAlloc.major_write_word_or_same_some mh mh' obj_hd new_hdr;
      assert (SweepDefs.chunked_set_object_color mh obj color == mh');
      SweepDefs.chunked_color_of_object_elim mh' target Header.Gray;
      SweepDefs.chunked_read_header_step mh' target;
      match SweepDefs.chunked_read_header mh' target with
      | None -> assert False
      | Some target_hdr ->
        assert (obj_hd <> target_hd);
        distinct_word_aligned_addrs_disjoint obj_hd target_hd;
        assert (MH.read_word_in_major mh' target_hd == Some target_hdr);
        MHReadFrame.write_word_in_major_preserves_other_read_back
          mh obj_hd new_hdr target_hd target_hdr;
        SweepDefs.chunked_read_header_step mh target;
        assert (SweepDefs.chunked_read_header mh target == Some target_hdr);
        SweepDefs.chunked_color_of_object_some mh target target_hdr

let chunked_make_gray_preserves_other_black
    (mh: MH.major_heap)
    (obj target: obj_addr)
  : Lemma
      (requires
        obj <> target /\
        SweepDefs.chunked_is_black mh target)
      (ensures
        SweepDefs.chunked_is_black
          (MarkDefs.chunked_make_gray mh obj) target)
  =
  MarkDefs.chunked_make_gray_step mh obj;
  chunked_set_object_color_preserves_other_black mh obj target Header.Gray

let chunked_make_gray_preserves_other_black_status
    (mh: MH.major_heap)
    (obj target: obj_addr)
  : Lemma
      (requires obj <> target)
      (ensures
        SweepDefs.chunked_is_black (MarkDefs.chunked_make_gray mh obj) target ==
        SweepDefs.chunked_is_black mh target)
  =
  MarkDefs.chunked_make_gray_step mh obj;
  chunked_set_object_color_preserves_other_black_status mh obj target Header.Gray

let chunked_make_gray_preserves_other_gray_back
    (mh: MH.major_heap)
    (obj target: obj_addr)
  : Lemma
      (requires
        obj <> target /\
        SweepDefs.chunked_color_of_object
          (MarkDefs.chunked_make_gray mh obj) target ==
        Some Header.Gray)
      (ensures SweepDefs.chunked_color_of_object mh target == Some Header.Gray)
  =
  MarkDefs.chunked_make_gray_step mh obj;
  chunked_set_object_color_preserves_other_gray_back mh obj target Header.Gray

let chunked_make_gray_preserves_other_gray
    (mh: MH.major_heap)
    (obj target: obj_addr)
  : Lemma
      (requires
        obj <> target /\
        SweepDefs.chunked_color_of_object mh target == Some Header.Gray)
      (ensures
        SweepDefs.chunked_color_of_object
          (MarkDefs.chunked_make_gray mh obj) target ==
        Some Header.Gray)
  =
  MarkDefs.chunked_make_gray_step mh obj;
  chunked_set_object_color_preserves_other_gray mh obj target Header.Gray

let chunked_make_black_preserves_other_black_status
    (mh: MH.major_heap)
    (obj target: obj_addr)
  : Lemma
      (requires obj <> target)
      (ensures
        SweepDefs.chunked_is_black (MarkDefs.chunked_make_black mh obj) target ==
        SweepDefs.chunked_is_black mh target)
  =
  MarkDefs.chunked_make_black_step mh obj;
  chunked_set_object_color_preserves_other_black_status mh obj target Header.Black

let chunked_make_black_preserves_other_gray
    (mh: MH.major_heap)
    (obj target: obj_addr)
  : Lemma
      (requires
        obj <> target /\
        SweepDefs.chunked_color_of_object mh target == Some Header.Gray)
      (ensures
        SweepDefs.chunked_color_of_object
          (MarkDefs.chunked_make_black mh obj) target ==
        Some Header.Gray)
  =
  MarkDefs.chunked_make_black_step mh obj;
  chunked_set_object_color_preserves_other_gray mh obj target Header.Black

let chunked_make_black_preserves_other_gray_back
    (mh: MH.major_heap)
    (obj target: obj_addr)
  : Lemma
      (requires
        obj <> target /\
        SweepDefs.chunked_color_of_object
          (MarkDefs.chunked_make_black mh obj) target ==
        Some Header.Gray)
      (ensures SweepDefs.chunked_color_of_object mh target == Some Header.Gray)
  =
  MarkDefs.chunked_make_black_step mh obj;
  chunked_set_object_color_preserves_other_gray_back mh obj target Header.Black

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

let rec chunked_push_children_preserves_black
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (obj target: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
  : Lemma
      (requires
        chunked_push_children_preservation_ready mh obj i ws /\
        SweepDefs.chunked_is_black mh target)
      (ensures
        (let (mh', _) = MarkDefs.chunked_push_children mh st obj i ws in
         SweepDefs.chunked_is_black mh' target))
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
        if child = target then begin
          SweepDefs.chunked_is_white_not_black mh target;
          assert False
        end else begin
          chunked_make_gray_preserves_other_black mh child target;
          if U64.v i < U64.v ws then
            chunked_push_children_preserves_black
              (MarkDefs.chunked_make_gray mh child)
              (Seq.cons child st)
              obj target (U64.add i 1UL) ws
        end
      end else if U64.v i < U64.v ws then
        chunked_push_children_preserves_black
          mh st obj target (U64.add i 1UL) ws
    end else if U64.v i < U64.v ws then
      chunked_push_children_preserves_black
        mh st obj target (U64.add i 1UL) ws
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

let chunked_mark_step_marks_head_black
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        chunked_mark_step_preservation_ready mh st)
      (ensures
        (let (mh', _) = MarkDefs.chunked_mark_step mh st in
         SweepDefs.chunked_is_black mh' (Seq.head st)))
  =
  let obj = Seq.head st in
  let st' = Seq.tail st in
  assert (Seq.mem obj (MH.major_objects mh));
  if MarkDefs.chunked_is_no_scan mh obj then begin
    MarkDefs.chunked_mark_step_no_scan mh st;
    chunked_make_black_makes_black mh obj
  end else begin
    let mh_black = MarkDefs.chunked_make_black mh obj in
    let ws = SweepDefs.chunked_wosize_of_object mh obj in
    MarkDefs.chunked_mark_step_scan mh st;
    chunked_make_black_makes_black mh obj;
    chunked_push_children_preserves_black mh_black st' obj obj 1UL ws
  end

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

let rec chunked_mark_aux_preservation_ready
      (mh: MH.major_heap)
      (st: Seq.seq obj_addr)
      (fuel: nat)
    : Tot prop
      (decreases fuel)
    =
    if Seq.length st = 0 then True
    else if fuel = 0 then True
    else
      let fuel_pred : n:nat{n < fuel} = fuel - 1 in
      chunked_mark_step_preservation_ready mh st /\
      (let (mh', st') = MarkDefs.chunked_mark_step mh st in
       chunked_mark_aux_preservation_ready mh' st' fuel_pred)

let rec chunked_mark_aux_preserves_major_objects
      (mh: MH.major_heap)
      (st: Seq.seq obj_addr)
      (fuel: nat)
    : Lemma
        (requires
          MH.well_formed_major_heap mh /\
          chunked_mark_aux_preservation_ready mh st fuel)
        (ensures
          MH.major_objects (MarkDefs.chunked_mark_aux mh st fuel) ==
          MH.major_objects mh)
        (decreases fuel)
    =
    if Seq.length st = 0 then
      MarkDefs.chunked_mark_aux_empty mh st fuel
    else if fuel = 0 then
      MarkDefs.chunked_mark_aux_out_of_fuel mh st
    else begin
      nat_nonzero_pos fuel;
      MarkDefs.chunked_mark_aux_step mh st fuel;
      let (mh', st') = MarkDefs.chunked_mark_step mh st in
      assert (chunked_mark_step_preservation_ready mh st);
      chunked_mark_step_preserves_major_objects mh st;
      chunked_mark_step_preserves_well_formed mh st;
      assert (MH.major_objects mh' == MH.major_objects mh);
      assert (MH.well_formed_major_heap mh');
      assert (chunked_mark_aux_preservation_ready mh' st' (fuel - 1));
      chunked_mark_aux_preserves_major_objects mh' st' (fuel - 1)
    end

let rec chunked_mark_aux_preserves_well_formed
      (mh: MH.major_heap)
      (st: Seq.seq obj_addr)
      (fuel: nat)
    : Lemma
        (requires
          MH.well_formed_major_heap mh /\
          chunked_mark_aux_preservation_ready mh st fuel)
        (ensures
          MH.well_formed_major_heap (MarkDefs.chunked_mark_aux mh st fuel))
        (decreases fuel)
    =
    if Seq.length st = 0 then
      MarkDefs.chunked_mark_aux_empty mh st fuel
    else if fuel = 0 then
      MarkDefs.chunked_mark_aux_out_of_fuel mh st
    else begin
      nat_nonzero_pos fuel;
      MarkDefs.chunked_mark_aux_step mh st fuel;
      let (mh', st') = MarkDefs.chunked_mark_step mh st in
      assert (chunked_mark_step_preservation_ready mh st);
      chunked_mark_step_preserves_well_formed mh st;
      assert (MH.well_formed_major_heap mh');
      assert (chunked_mark_aux_preservation_ready mh' st' (fuel - 1));
      chunked_mark_aux_preserves_well_formed mh' st' (fuel - 1)
    end

let chunked_mark_preservation_ready
      (mh: MH.major_heap)
      (st: Seq.seq obj_addr)
    : GTot prop
    =
    chunked_mark_aux_preservation_ready mh st (heap_size / U64.v mword)

let chunked_mark_preserves_major_objects
      (mh: MH.major_heap)
      (st: Seq.seq obj_addr)
    : Lemma
        (requires
          MH.well_formed_major_heap mh /\
          chunked_mark_preservation_ready mh st)
        (ensures
          MH.major_objects (MarkDefs.chunked_mark mh st) ==
          MH.major_objects mh)
    =
    MarkDefs.chunked_mark_equation mh st;
    chunked_mark_aux_preserves_major_objects
      mh st (heap_size / U64.v mword)

let chunked_mark_preserves_well_formed
      (mh: MH.major_heap)
      (st: Seq.seq obj_addr)
    : Lemma
        (requires
          MH.well_formed_major_heap mh /\
          chunked_mark_preservation_ready mh st)
        (ensures
          MH.well_formed_major_heap (MarkDefs.chunked_mark mh st))
    =
    MarkDefs.chunked_mark_equation mh st;
    chunked_mark_aux_preserves_well_formed
      mh st (heap_size / U64.v mword)
