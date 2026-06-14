module GC.Spec.ChunkedSweepCoalesce.Preservation

module U64 = FStar.UInt64
module Seq = FStar.Seq
module SeqProps = FStar.Seq.Properties

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module MHReadFrame = GC.Spec.MajorHeap.ReadFrame
module Header = GC.Lib.Header
module Obj = GC.Spec.Object
module Fields = GC.Spec.Fields
module Defs = GC.Spec.ChunkedSweepCoalesce.Defs
module MarkDefs = GC.Spec.ChunkedMark.Defs
module SpecMajorAlloc = GC.Spec.MajorAllocator
module ChunkedGraph = GC.Spec.ChunkedMajorGC.Graph
module Pending = GC.Spec.ChunkedSweepCoalesce.PendingRun

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let nat_nonzero_pos (n: nat)
  : Lemma (requires n <> 0) (ensures n > 0)
  = ()

let nat_pred_succ (n: nat)
  : Lemma (requires n > 0) (ensures n == (n - 1) + 1)
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

let seq_mem_eq (#a:eqtype) (s t: Seq.seq a) (x: a)
  : Lemma
      (requires s == t /\ Seq.mem x s)
      (ensures Seq.mem x t)
  =
  assert (t == s);
  assert (Seq.mem x t == Seq.mem x s)

let blue_run_empty_end_at_next_start
    (start: hp_addr)
    (first: obj_addr)
    (wz: nat)
  : Lemma
      (requires U64.v first == U64.v start + U64.v mword)
      (ensures
        U64.v first + wz * U64.v mword ==
        U64.v start + (wz + 1) * U64.v mword)
  =
  FStar.Math.Lemmas.distributivity_add_left wz 1 (U64.v mword);
  FStar.Math.Lemmas.paren_add_right
    (U64.v start) (U64.v mword) (wz * U64.v mword)

let blue_run_extended_end_at_next_start
    (first_blue: U64.t)
    (run_words: nat)
    (start: hp_addr)
    (wz: nat)
  : Lemma
      (requires
        run_words > 0 /\
        U64.v first_blue + (run_words - 1) * U64.v mword == U64.v start)
      (ensures
        U64.v first_blue + (run_words + wz + 1 - 1) * U64.v mword ==
        U64.v start + (wz + 1) * U64.v mword)
  =
  assert (run_words + wz + 1 - 1 == (run_words - 1) + (wz + 1));
  FStar.Math.Lemmas.distributivity_add_left
    (run_words - 1) (wz + 1) (U64.v mword);
  FStar.Math.Lemmas.paren_add_right
    (U64.v first_blue)
    ((run_words - 1) * U64.v mword)
    ((wz + 1) * U64.v mword)

let chunked_fused_aux_nonblack_run_end_at_next_start
    (start: hp_addr)
    (first: obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (wz: U64.t)
    (next_start: hp_addr)
  : Lemma
      (requires
        U64.v first == U64.v start + U64.v mword /\
        U64.v next_start ==
          U64.v start + (U64.v wz + 1) * U64.v mword /\
        (run_words = 0 \/
         U64.v first_blue + (run_words - 1) * U64.v mword == U64.v start))
      (ensures
        (let new_first : U64.t = if run_words = 0 then first else first_blue in
         let new_run = run_words + U64.v wz + 1 in
         new_run = 0 \/
         U64.v new_first + (new_run - 1) * U64.v mword == U64.v next_start))
  =
  let new_first : U64.t = if run_words = 0 then first else first_blue in
  let new_run = run_words + U64.v wz + 1 in
  match run_words with
  | 0 ->
    assert (new_run - 1 == U64.v wz);
    blue_run_empty_end_at_next_start start first (U64.v wz);
    assert (U64.v new_first + (new_run - 1) * U64.v mword ==
            U64.v start + (U64.v wz + 1) * U64.v mword);
    assert (U64.v new_first + (new_run - 1) * U64.v mword ==
            U64.v next_start)
  | _ ->
    assert (run_words > 0);
    assert (U64.v first_blue +
            (run_words - 1) * U64.v mword == U64.v start);
    assert (new_run - 1 == (run_words - 1) + U64.v wz + 1);
    blue_run_extended_end_at_next_start first_blue run_words start (U64.v wz);
    assert (U64.v first_blue + (new_run - 1) * U64.v mword ==
            U64.v start + (U64.v wz + 1) * U64.v mword);
    assert (U64.v first_blue + (new_run - 1) * U64.v mword ==
            U64.v next_start)

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always"
let chunked_fused_aux_nonblack_named_run_before_read
    (start: hp_addr)
    (first: obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (wz: U64.t)
    (next_start: hp_addr)
    (new_first: U64.t)
    (new_run: nat)
    (read_addr: hp_addr)
  : Lemma
      (requires
        U64.v first == U64.v start + U64.v mword /\
        U64.v next_start ==
          U64.v start + (U64.v wz + 1) * U64.v mword /\
        (run_words = 0 \/
         U64.v first_blue + (run_words - 1) * U64.v mword == U64.v start) /\
        new_first == (if run_words = 0 then first else first_blue) /\
        new_run == run_words + U64.v wz + 1 /\
        U64.v read_addr >= U64.v next_start)
      (ensures
        new_run = 0 \/
        U64.v new_first + (new_run - 1) * U64.v mword <= U64.v read_addr)
  =
  chunked_fused_aux_nonblack_run_end_at_next_start
    start first first_blue run_words wz next_start;
  assert (new_run == run_words + U64.v wz + 1);
  assert (new_first == (if run_words = 0 then first else first_blue));
  assert (new_run = 0 \/
          U64.v new_first + (new_run - 1) * U64.v mword ==
            U64.v next_start);
  assert (new_run = 0 \/
          U64.v new_first + (new_run - 1) * U64.v mword <= U64.v read_addr)
#pop-options

let field_addr_two_words_before_next_payload
    (start: hp_addr)
    (i: U64.t{U64.v i >= 1})
    (wz: U64.t)
    (field_addr: hp_addr)
  : Lemma
      (requires
        U64.v i <= U64.v wz /\
        U64.v field_addr == U64.v start + U64.v mword * U64.v i)
      (ensures
        U64.v field_addr + U64.v mword * 2 <=
        U64.v start + (U64.v wz + 2) * U64.v mword)
  =
  assert (U64.v mword == 8);
  assert (U64.v i + 2 <= U64.v wz + 2);
  assert (U64.v field_addr + U64.v mword * 2 ==
          U64.v start + (U64.v i + 2) * U64.v mword);
  assert (U64.v start + (U64.v i + 2) * U64.v mword <=
          U64.v start + (U64.v wz + 2) * U64.v mword)

let chunk_suffix_object_after_field_addr
    (c: MH.heap_chunk)
    (start: hp_addr)
    (next_start: hp_addr)
    (o: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (wz: U64.t)
    (field_addr: hp_addr)
  : Lemma
      (requires
        Seq.mem o (MH.objects_in_chunk_from c next_start) /\
        U64.v next_start == U64.v start + (U64.v wz + 1) * U64.v mword /\
        U64.v i <= U64.v wz /\
        U64.v field_addr == U64.v start + U64.v mword * U64.v i)
      (ensures U64.v field_addr + U64.v mword * 2 <= U64.v o)
  =
  MH.objects_in_chunk_from_addresses_gt_start c next_start o;
  assert (U64.v o > U64.v next_start);
  assert (U64.v o % U64.v mword == 0);
  assert (U64.v next_start % U64.v mword == 0);
  MH.word_aligned_gt_at_least_mword (U64.v o) (U64.v next_start);
  assert (U64.v o >= U64.v next_start + U64.v mword);
  field_addr_two_words_before_next_payload start i wz field_addr;
  FStar.Math.Lemmas.distributivity_add_left (U64.v wz + 1) 1 (U64.v mword);
  FStar.Math.Lemmas.paren_add_right
    (U64.v start) ((U64.v wz + 1) * U64.v mword) (U64.v mword);
  assert ((U64.v wz + 1) + 1 == U64.v wz + 2);
  assert (U64.v next_start + U64.v mword ==
          U64.v start + (U64.v wz + 2) * U64.v mword);
  assert (U64.v field_addr + U64.v mword * 2 <= U64.v o)

let major_write_word_or_same_preserves_other_read
    (mh: MH.major_heap)
    (write_addr: hp_addr)
    (value: U64.t)
    (read_addr: hp_addr)
    (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (U64.v write_addr + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v write_addr))
      (ensures
        MH.read_word_in_major
          (SpecMajorAlloc.major_write_word_or_same mh write_addr value)
          read_addr == Some old)
  =
  MHReadFrame.write_word_in_major_preserves_other_read
    mh write_addr value read_addr old;
  match MH.write_word_in_major mh write_addr value with
  | None ->
    SpecMajorAlloc.major_write_word_or_same_none mh write_addr value
  | Some mh' ->
    SpecMajorAlloc.major_write_word_or_same_some mh mh' write_addr value

let major_write_word_or_same_read_same
    (mh: MH.major_heap)
    (write_addr: hp_addr)
    (value: U64.t)
    (idx: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        MH.lookup_chunk_index mh write_addr == Some idx /\
        MH.word_in_chunk (Seq.index mh idx) write_addr)
      (ensures
        MH.read_word_in_major
          (SpecMajorAlloc.major_write_word_or_same mh write_addr value)
          write_addr == Some value)
  =
  let c = Seq.index mh idx in
  MH.write_word_in_major_at_lookup_index mh write_addr value idx;
  MH.write_word_at_index_preserves_wf mh write_addr value idx;
  let c' = MH.write_word_in_chunk c write_addr value in
  assert (MH.write_word_in_major mh write_addr value ==
          Some (Seq.upd mh idx c'));
  SpecMajorAlloc.major_write_word_or_same_some
    mh (Seq.upd mh idx c') write_addr value;
  MH.read_write_in_chunk_same c write_addr value;
  assert (MH.read_word_in_chunk c' write_addr == value);
  MH.write_word_in_chunk_preserves_word c write_addr value write_addr;
  assert (MH.word_in_chunk c' write_addr);
  MH.lookup_chunk_index_word_in_chunk (Seq.upd mh idx c') write_addr idx;
  assert (MH.lookup_chunk_index (Seq.upd mh idx c') write_addr == Some idx);
  MH.read_word_in_major_at_lookup_index (Seq.upd mh idx c') write_addr idx

let chunked_set_object_color_preserves_self_wosize
    (mh: MH.major_heap)
    (obj: obj_addr)
    (color: Header.color_sem)
    (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Defs.chunked_read_header mh obj == Some hdr)
      (ensures
        Defs.chunked_wosize_of_object
          (Defs.chunked_set_object_color mh obj color)
          obj ==
        Obj.getWosize hdr)
  =
  Defs.chunked_read_header_step mh obj;
  let hd = hd_address obj in
  MH.read_word_in_major_lookup_index mh hd hdr;
  let idx = MH.lookup_chunk_index_value mh hd in
  assert (MH.lookup_chunk_index mh hd == Some idx);
  assert (idx < Seq.length mh);
  assert (MH.word_in_chunk (Seq.index mh idx) hd);
  Defs.chunked_set_object_color_some mh obj color hdr;
  let new_hdr = Obj.colorHeader hdr color in
  Obj.colorHeader_preserves_wosize hdr color;
  major_write_word_or_same_read_same mh hd new_hdr idx;
  let mh' = Defs.chunked_set_object_color mh obj color in
  Defs.chunked_read_header_step mh' obj;
  assert (Defs.chunked_read_header mh' obj == Some new_hdr);
  Defs.chunked_wosize_of_object_some mh' obj new_hdr

let chunked_make_white_preserves_self_wosize
    (mh: MH.major_heap)
    (obj: obj_addr)
    (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Defs.chunked_read_header mh obj == Some hdr)
      (ensures
        Defs.chunked_wosize_of_object
          (Defs.chunked_make_white mh obj)
          obj ==
        Obj.getWosize hdr)
  =
  Defs.chunked_make_white_step mh obj;
  chunked_set_object_color_preserves_self_wosize
    mh obj Header.White hdr

let chunked_make_blue_preserves_self_wosize
    (mh: MH.major_heap)
    (obj: obj_addr)
    (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Defs.chunked_read_header mh obj == Some hdr)
      (ensures
        Defs.chunked_wosize_of_object
          (Defs.chunked_make_blue mh obj)
          obj ==
        Obj.getWosize hdr)
  =
  Defs.chunked_make_blue_step mh obj;
  chunked_set_object_color_preserves_self_wosize
    mh obj Header.Blue hdr

let chunked_set_object_color_preserves_other_read
    (mh: MH.major_heap)
    (obj: obj_addr)
    (color: Header.color_sem)
    (read_addr: hp_addr)
    (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (U64.v (hd_address obj) + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v (hd_address obj)))
      (ensures
        MH.read_word_in_major
          (Defs.chunked_set_object_color mh obj color)
          read_addr == Some old)
  =
  Defs.chunked_read_header_step mh obj;
  match Defs.chunked_read_header mh obj with
  | None ->
    Defs.chunked_set_object_color_none mh obj color
  | Some hdr ->
    Defs.chunked_set_object_color_some mh obj color hdr;
    major_write_word_or_same_preserves_other_read
      mh (hd_address obj) (Obj.colorHeader hdr color) read_addr old

let rec chunked_zero_fields_preserves_read_before
    (mh: MH.major_heap)
    (addr: U64.t)
    (n: nat)
    (read_addr: hp_addr)
    (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        U64.v read_addr + U64.v mword <= U64.v addr)
      (ensures
        MH.read_word_in_major
          (Defs.chunked_zero_fields mh addr n)
          read_addr == Some old)
      (decreases n)
  =
  if n = 0 then
    Defs.chunked_zero_fields_zero mh addr
  else if U64.v addr + U64.v mword > heap_size then
    Defs.chunked_zero_fields_no_room mh addr n
  else if U64.v addr >= heap_size then
    Defs.chunked_zero_fields_out_of_heap mh addr n
  else if U64.v addr % U64.v mword <> 0 then
    Defs.chunked_zero_fields_unaligned mh addr n
  else begin
    assert (n <> 0);
    nat_nonzero_pos n;
    assert (n > 0);
    Defs.chunked_zero_fields_step mh addr n;
    let write_addr : hp_addr = addr in
    let mh' =
      SpecMajorAlloc.major_write_word_or_same mh write_addr 0UL in
    major_write_word_or_same_preserves_other_read
      mh write_addr 0UL read_addr old;
    if U64.v addr + U64.v mword >= pow2 64 then
      ()
    else begin
      let next = U64.uint_to_t (U64.v addr + U64.v mword) in
      assert (U64.v read_addr + U64.v mword <= U64.v next);
      chunked_zero_fields_preserves_read_before
        mh' next (n - 1) read_addr old
    end
  end

let rec chunked_zero_fields_preserves_read_after
    (mh: MH.major_heap)
    (addr: U64.t)
    (n: nat)
    (read_addr: hp_addr)
    (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        U64.v addr + n * U64.v mword <= U64.v read_addr)
      (ensures
        MH.read_word_in_major
          (Defs.chunked_zero_fields mh addr n)
          read_addr == Some old)
      (decreases n)
  =
  if n = 0 then
    Defs.chunked_zero_fields_zero mh addr
  else if U64.v addr + U64.v mword > heap_size then
    Defs.chunked_zero_fields_no_room mh addr n
  else if U64.v addr >= heap_size then
    Defs.chunked_zero_fields_out_of_heap mh addr n
  else if U64.v addr % U64.v mword <> 0 then
    Defs.chunked_zero_fields_unaligned mh addr n
  else begin
    assert (n <> 0);
    nat_nonzero_pos n;
    assert (n > 0);
    Defs.chunked_zero_fields_step mh addr n;
    let write_addr : hp_addr = addr in
    let mh' =
      SpecMajorAlloc.major_write_word_or_same mh write_addr 0UL in
    FStar.Math.Lemmas.lemma_mult_le_right (U64.v mword) 1 n;
    assert (U64.v addr + U64.v mword <= U64.v read_addr);
    major_write_word_or_same_preserves_other_read
      mh write_addr 0UL read_addr old;
    if U64.v addr + U64.v mword >= pow2 64 then
      ()
    else begin
      let next = U64.uint_to_t (U64.v addr + U64.v mword) in
      assert (U64.v next == U64.v addr + U64.v mword);
      nat_pred_succ n;
      assert (n == (n - 1) + 1);
      FStar.Math.Lemmas.distributivity_add_left
        (n - 1) 1 (U64.v mword);
      assert (n * U64.v mword ==
              (n - 1) * U64.v mword + U64.v mword);
      assert (U64.v mword + (n - 1) * U64.v mword ==
              (n - 1) * U64.v mword + U64.v mword);
      FStar.Math.Lemmas.paren_add_right
        (U64.v addr) (U64.v mword) ((n - 1) * U64.v mword);
      assert (U64.v next + (n - 1) * U64.v mword ==
              U64.v addr + n * U64.v mword);
      assert (U64.v next + (n - 1) * U64.v mword <= U64.v read_addr);
      chunked_zero_fields_preserves_read_after
        mh' next (n - 1) read_addr old
    end
  end

let chunked_flush_blue_preserves_read_before
    (mh: MH.major_heap)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
    (read_addr: hp_addr)
    (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        U64.v read_addr + U64.v mword * 2 <= U64.v first_blue)
      (ensures
        MH.read_word_in_major
          (fst (Defs.chunked_flush_blue mh first_blue run_words fp))
          read_addr == Some old)
  =
  if run_words = 0 then
    Defs.chunked_flush_blue_empty mh first_blue fp
  else begin
    assert (run_words <> 0);
    nat_nonzero_pos run_words;
    assert (run_words > 0);
    if U64.v first_blue < U64.v mword ||
       U64.v first_blue >= heap_size ||
       U64.v first_blue % U64.v mword <> 0
    then
      Defs.chunked_flush_blue_invalid mh first_blue run_words fp
    else if run_words - 1 >= pow2 54 then
      Defs.chunked_flush_blue_too_large mh first_blue run_words fp
    else begin
      FStar.Math.Lemmas.pow2_lt_compat 64 54;
      assert (run_words - 1 < pow2 54);
      assert (run_words - 1 < pow2 64);
      Defs.chunked_flush_blue_step mh first_blue run_words fp;
      let fb : obj_addr = first_blue in
      let hd = hd_address fb in
      let wz : nat = run_words - 1 in
      let wz_u64 : Obj.wosize = U64.uint_to_t wz in
      let hdr = Obj.makeHeader wz_u64 Header.Blue 0UL in
      let mh1 = SpecMajorAlloc.major_write_word_or_same mh hd hdr in
      hd_address_spec fb;
      assert (U64.v hd + U64.v mword == U64.v first_blue);
      assert (U64.v read_addr + U64.v mword <= U64.v hd);
      major_write_word_or_same_preserves_other_read
        mh hd hdr read_addr old;
      if wz >= 1 && U64.v hd + U64.v mword * 2 <= heap_size then begin
        let mh2 = SpecMajorAlloc.major_write_word_or_same mh1 fb fp in
        assert (U64.v read_addr + U64.v mword <= U64.v fb);
        major_write_word_or_same_preserves_other_read
          mh1 fb fp read_addr old;
        let zero_start_nat = U64.v fb + U64.v mword in
        if wz >= 2 && zero_start_nat < pow2 64 then begin
          let zero_start = U64.uint_to_t zero_start_nat in
          assert (U64.v read_addr + U64.v mword <= U64.v zero_start);
          chunked_zero_fields_preserves_read_before
            mh2 zero_start (wz - 1) read_addr old
        end
      end
    end
  end

let chunked_flush_blue_preserves_read_after
    (mh: MH.major_heap)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
    (read_addr: hp_addr)
    (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (run_words = 0 \/
         U64.v first_blue + (run_words - 1) * U64.v mword <= U64.v read_addr))
      (ensures
        MH.read_word_in_major
          (fst (Defs.chunked_flush_blue mh first_blue run_words fp))
          read_addr == Some old)
  =
  if run_words = 0 then
    Defs.chunked_flush_blue_empty mh first_blue fp
  else begin
    assert (run_words <> 0);
    nat_nonzero_pos run_words;
    assert (run_words > 0);
    assert (U64.v first_blue + (run_words - 1) * U64.v mword <=
            U64.v read_addr);
    if U64.v first_blue < U64.v mword ||
       U64.v first_blue >= heap_size ||
       U64.v first_blue % U64.v mword <> 0
    then
      Defs.chunked_flush_blue_invalid mh first_blue run_words fp
    else if run_words - 1 >= pow2 54 then
      Defs.chunked_flush_blue_too_large mh first_blue run_words fp
    else begin
      FStar.Math.Lemmas.pow2_lt_compat 64 54;
      assert (run_words - 1 < pow2 54);
      assert (run_words - 1 < pow2 64);
      Defs.chunked_flush_blue_step mh first_blue run_words fp;
      let fb : obj_addr = first_blue in
      let hd = hd_address fb in
      let wz : nat = run_words - 1 in
      let wz_u64 : Obj.wosize = U64.uint_to_t wz in
      let hdr = Obj.makeHeader wz_u64 Header.Blue 0UL in
      let mh1 = SpecMajorAlloc.major_write_word_or_same mh hd hdr in
      hd_address_spec fb;
      assert (U64.v hd + U64.v mword == U64.v fb);
      assert (U64.v fb == U64.v first_blue);
      assert (U64.v fb + wz * U64.v mword <= U64.v read_addr);
      assert (U64.v hd + U64.v mword <= U64.v read_addr);
      major_write_word_or_same_preserves_other_read
        mh hd hdr read_addr old;
      if wz >= 1 && U64.v hd + U64.v mword * 2 <= heap_size then begin
        let mh2 = SpecMajorAlloc.major_write_word_or_same mh1 fb fp in
        FStar.Math.Lemmas.lemma_mult_le_right (U64.v mword) 1 wz;
        assert (U64.v fb + U64.v mword <= U64.v read_addr);
        major_write_word_or_same_preserves_other_read
          mh1 fb fp read_addr old;
        let zero_start_nat = U64.v fb + U64.v mword in
        if wz >= 2 && zero_start_nat < pow2 64 then begin
          let zero_start = U64.uint_to_t zero_start_nat in
          assert (U64.v zero_start == U64.v fb + U64.v mword);
          assert (wz == (wz - 1) + 1);
          FStar.Math.Lemmas.distributivity_add_left
            (wz - 1) 1 (U64.v mword);
          assert (wz * U64.v mword ==
                  (wz - 1) * U64.v mword + U64.v mword);
          assert (U64.v mword + (wz - 1) * U64.v mword ==
                  (wz - 1) * U64.v mword + U64.v mword);
          FStar.Math.Lemmas.paren_add_right
            (U64.v fb) (U64.v mword) ((wz - 1) * U64.v mword);
          assert (U64.v zero_start + (wz - 1) * U64.v mword ==
                  U64.v fb + wz * U64.v mword);
          assert (U64.v zero_start + (wz - 1) * U64.v mword <=
                  U64.v read_addr);
          chunked_zero_fields_preserves_read_after
            mh2 zero_start (wz - 1) read_addr old
        end
      end
    end
  end

let chunked_flush_blue_preserves_other_read
    (mh: MH.major_heap)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
    (read_addr: hp_addr)
    (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (run_words = 0 \/
         U64.v read_addr + U64.v mword * 2 <= U64.v first_blue \/
         U64.v first_blue + (run_words - 1) * U64.v mword <= U64.v read_addr))
      (ensures
        MH.read_word_in_major
          (fst (Defs.chunked_flush_blue mh first_blue run_words fp))
          read_addr == Some old)
  =
  if run_words = 0 then
    Defs.chunked_flush_blue_empty mh first_blue fp
  else if U64.v read_addr + U64.v mword * 2 <= U64.v first_blue then
    chunked_flush_blue_preserves_read_before
      mh first_blue run_words fp read_addr old
  else begin
    assert (U64.v first_blue + (run_words - 1) * U64.v mword <=
            U64.v read_addr);
    chunked_flush_blue_preserves_read_after
      mh first_blue run_words fp read_addr old
  end

let chunked_make_white_preserves_other_read
    (mh: MH.major_heap)
    (obj: obj_addr)
    (read_addr: hp_addr)
    (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (U64.v (hd_address obj) + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v (hd_address obj)))
      (ensures
        MH.read_word_in_major
          (Defs.chunked_make_white mh obj)
          read_addr == Some old)
  =
  Defs.chunked_make_white_step mh obj;
  chunked_set_object_color_preserves_other_read
    mh obj Header.White read_addr old

let chunked_make_blue_preserves_other_read
    (mh: MH.major_heap)
    (obj: obj_addr)
    (read_addr: hp_addr)
    (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (U64.v (hd_address obj) + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v (hd_address obj)))
      (ensures
        MH.read_word_in_major
          (Defs.chunked_make_blue mh obj)
          read_addr == Some old)
  =
  Defs.chunked_make_blue_step mh obj;
  chunked_set_object_color_preserves_other_read
    mh obj Header.Blue read_addr old

let chunked_flush_blue_make_white_preserves_other_read
    (mh: MH.major_heap)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
    (obj: obj_addr)
    (read_addr: hp_addr)
    (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (run_words = 0 \/
         U64.v read_addr + U64.v mword * 2 <= U64.v first_blue \/
         U64.v first_blue + (run_words - 1) * U64.v mword <= U64.v read_addr) /\
        (U64.v (hd_address obj) + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v (hd_address obj)))
      (ensures
        MH.read_word_in_major
          (Defs.chunked_make_white
            (fst (Defs.chunked_flush_blue mh first_blue run_words fp))
            obj)
          read_addr == Some old)
  =
  let (mh', fp') = Defs.chunked_flush_blue mh first_blue run_words fp in
  chunked_flush_blue_preserves_other_read
    mh first_blue run_words fp read_addr old;
  chunked_make_white_preserves_other_read mh' obj read_addr old

let chunked_sweep_object_preserves_other_read
    (mh: MH.major_heap)
    (obj: obj_addr)
    (fp: U64.t)
    (read_addr: hp_addr)
    (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (U64.v (hd_address obj) + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v (hd_address obj)) /\
        (U64.v obj + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v obj))
      (ensures
        MH.read_word_in_major
          (fst (Defs.chunked_sweep_object mh obj fp))
          read_addr == Some old)
  =
  if Defs.chunked_is_infix mh obj then
    Defs.chunked_sweep_object_infix_step mh obj fp
  else if Defs.chunked_is_white mh obj then begin
    Defs.chunked_sweep_object_white_step mh obj fp;
    let ws = Defs.chunked_wosize_of_object mh obj in
    let hd = hd_address obj in
    let mh' =
      if U64.v ws > 0 && U64.v hd + U64.v mword * 2 <= heap_size then
        SpecMajorAlloc.major_write_word_or_same mh obj fp
      else
        mh
    in
    if U64.v ws > 0 && U64.v hd + U64.v mword * 2 <= heap_size then
      major_write_word_or_same_preserves_other_read mh obj fp read_addr old;
    chunked_make_blue_preserves_other_read mh' obj read_addr old
  end else if Defs.chunked_is_black mh obj then begin
    Defs.chunked_sweep_object_black_step mh obj fp;
    chunked_make_white_preserves_other_read mh obj read_addr old
  end else
    Defs.chunked_sweep_object_other_step mh obj fp

let rec chunked_sweep_aux_preserves_other_read
    (mh: MH.major_heap)
    (objs: Seq.seq obj_addr)
    (fp: U64.t)
    (read_addr: hp_addr)
    (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (forall (obj: obj_addr). Seq.mem obj objs ==>
          (U64.v (hd_address obj) + U64.v mword <= U64.v read_addr \/
           U64.v read_addr + U64.v mword <= U64.v (hd_address obj)) /\
          (U64.v obj + U64.v mword <= U64.v read_addr \/
           U64.v read_addr + U64.v mword <= U64.v obj)))
      (ensures
        MH.read_word_in_major
          (fst (Defs.chunked_sweep_aux mh objs fp))
          read_addr == Some old)
      (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then begin
    Defs.chunked_sweep_aux_empty_length mh objs fp
  end else begin
    assert (~(Seq.length objs = 0));
    nat_nonzero_pos (Seq.length objs);
    assert (Seq.length objs > 0);
    let obj = Seq.head objs in
    let tail = Seq.tail objs in
    assert (Seq.length tail < Seq.length objs);
    let (mh', fp') = Defs.chunked_sweep_object mh obj fp in
    chunked_sweep_object_preserves_other_read mh obj fp read_addr old;
    Defs.chunked_sweep_aux_step mh objs fp;
    let aux (o: obj_addr) : Lemma
        (requires Seq.mem o tail)
        (ensures
          (U64.v (hd_address o) + U64.v mword <= U64.v read_addr \/
           U64.v read_addr + U64.v mword <= U64.v (hd_address o)) /\
          (U64.v o + U64.v mword <= U64.v read_addr \/
           U64.v read_addr + U64.v mword <= U64.v o))
      =
      seq_tail_mem objs o
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    chunked_sweep_aux_preserves_other_read mh' tail fp' read_addr old
  end

let rec chunked_fused_aux_read_frame_ready
    (source: MH.major_heap)
    (objs: Seq.seq obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (read_addr: hp_addr)
  : Tot prop
      (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then
    run_words = 0 \/
    U64.v read_addr + U64.v mword * 2 <= U64.v first_blue \/
    U64.v first_blue + (run_words - 1) * U64.v mword <= U64.v read_addr
  else
    let obj = Seq.head objs in
    let rest = Seq.tail objs in
    if Defs.chunked_is_black source obj then
      (run_words = 0 \/
       U64.v read_addr + U64.v mword * 2 <= U64.v first_blue \/
       U64.v first_blue + (run_words - 1) * U64.v mword <= U64.v read_addr) /\
      (U64.v (hd_address obj) + U64.v mword <= U64.v read_addr \/
       U64.v read_addr + U64.v mword <= U64.v (hd_address obj)) /\
      chunked_fused_aux_read_frame_ready source rest 0UL 0 read_addr
    else
      let ws = U64.v (Defs.chunked_wosize_of_object source obj) in
      let new_first : U64.t = if run_words = 0 then obj else first_blue in
      chunked_fused_aux_read_frame_ready
        source rest new_first (run_words + ws + 1) read_addr

let rec chunked_fused_aux_read_frame_ready_from_all_after
    (source: MH.major_heap)
    (objs: Seq.seq obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (read_addr: hp_addr)
  : Lemma
      (requires
        (run_words = 0 \/
         U64.v read_addr + U64.v mword * 2 <= U64.v first_blue) /\
        (forall (obj: obj_addr). Seq.mem obj objs ==>
          U64.v read_addr + U64.v mword * 2 <= U64.v obj))
      (ensures
        chunked_fused_aux_read_frame_ready
          source objs first_blue run_words read_addr)
      (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then
    ()
  else begin
    assert (~(Seq.length objs = 0));
    nat_nonzero_pos (Seq.length objs);
    assert (Seq.length objs > 0);
    let obj = Seq.head objs in
    let rest = Seq.tail objs in
    assert (Seq.length rest < Seq.length objs);
    if Defs.chunked_is_black source obj then begin
      assert (U64.v read_addr + U64.v mword * 2 <= U64.v obj);
      hd_address_spec obj;
      assert (U64.v (hd_address obj) + U64.v mword == U64.v obj);
      assert (U64.v read_addr + U64.v mword <= U64.v (hd_address obj));
      let aux (o: obj_addr) : Lemma
          (requires Seq.mem o rest)
          (ensures U64.v read_addr + U64.v mword * 2 <= U64.v o)
        =
        seq_tail_mem objs o
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
      chunked_fused_aux_read_frame_ready_from_all_after
        source rest 0UL 0 read_addr
    end else begin
      let ws = U64.v (Defs.chunked_wosize_of_object source obj) in
      let new_first : U64.t = if run_words = 0 then obj else first_blue in
      if run_words = 0 then
        assert (U64.v read_addr + U64.v mword * 2 <= U64.v new_first)
      else
        assert (U64.v read_addr + U64.v mword * 2 <= U64.v new_first);
      let aux (o: obj_addr) : Lemma
          (requires Seq.mem o rest)
          (ensures U64.v read_addr + U64.v mword * 2 <= U64.v o)
        =
        seq_tail_mem objs o
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
      chunked_fused_aux_read_frame_ready_from_all_after
        source rest new_first (run_words + ws + 1) read_addr
    end
  end

let word_before_chunk_end_before_read
        (start: hp_addr)
        (chunk_end: nat)
        (read_addr: hp_addr)
      : Lemma
          (requires
            U64.v start + U64.v mword < chunk_end /\
            chunk_end <= U64.v read_addr)
          (ensures U64.v start + U64.v mword <= U64.v read_addr)
      = ()

let header_word_before_read_from_start
        (start: hp_addr)
        (obj: obj_addr)
        (read_addr: hp_addr)
      : Lemma
          (requires
            hd_address obj == start /\
            U64.v start + U64.v mword <= U64.v read_addr)
          (ensures
            U64.v (hd_address obj) + U64.v mword <= U64.v read_addr)
      = ()

let header_word_before_read_from_chunk_end
        (start: hp_addr)
        (obj: obj_addr)
        (chunk_end: nat)
        (read_addr: hp_addr)
      : Lemma
          (requires
            hd_address obj == start /\
            U64.v start + U64.v mword < chunk_end /\
            chunk_end <= U64.v read_addr)
          (ensures
            U64.v (hd_address obj) + U64.v mword <= U64.v read_addr)
      =
      word_before_chunk_end_before_read start chunk_end read_addr;
      header_word_before_read_from_start start obj read_addr

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let rec chunked_fused_aux_read_frame_ready_from_chunk_before
    (source: MH.major_heap)
    (idx: nat{idx < Seq.length source})
    (base start: hp_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (read_addr: hp_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        Pending.pending_run_before_start
          source idx base start first_blue run_words /\
        MH.chunk_end (Seq.index source idx) <= U64.v read_addr /\
        (forall (o: obj_addr).
          Seq.mem o
            (MH.objects_in_chunk_from (Seq.index source idx) start) ==>
          Seq.mem o
            (MH.objects_in_chunk_from (Seq.index source idx) base)) /\
        (forall (o: obj_addr).
          Seq.mem o
            (MH.objects_in_chunk_from (Seq.index source idx) start) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o))
      (ensures
        chunked_fused_aux_read_frame_ready
          source
          (MH.objects_in_chunk_from (Seq.index source idx) start)
          first_blue run_words read_addr)
      (decreases
        Seq.length (MH.objects_in_chunk_from (Seq.index source idx) start))
  =
  let c = Seq.index source idx in
  let objs = MH.objects_in_chunk_from c start in
  if Seq.length objs = 0 then begin
    if run_words = 0 then
      ()
    else begin
      nat_nonzero_pos run_words;
      let rw : pos = run_words in
      Pending.pending_run_before_start_nonempty_elim
        source idx base start first_blue rw;
      assert (U64.v first_blue + (run_words - 1) * U64.v mword ==
              U64.v start);
      assert (U64.v start <= MH.chunk_end c);
      assert (U64.v first_blue + (run_words - 1) * U64.v mword <=
              U64.v read_addr)
    end
  end else begin
    nat_nonzero_pos (Seq.length objs);
    assert (Seq.length objs > 0);
    assert (U64.v start >= MH.chunk_start c);
    assert (U64.v start + U64.v mword < MH.chunk_end c);
    let header = MH.read_word_in_chunk c start in
    let wz = Obj.getWosize header in
    let obj_size_words = U64.v wz + 1 in
    let next_start_nat =
      U64.v start + obj_size_words * U64.v mword in
    assert (next_start_nat <= MH.chunk_end c);
    assert (next_start_nat < pow2 64);
    MH.next_object_start_aligned start obj_size_words;
    assert (next_start_nat % U64.v mword == 0);
    MH.objects_in_chunk_from_cons_step c start;
    let obj = f_address start in
    let rest = Seq.tail objs in
    assert (Seq.length rest < Seq.length objs);
    assert (Seq.head objs == obj);
    f_address_spec start;
    hd_f_roundtrip start;
    assert (hd_address obj == start);
    assert (U64.v obj == U64.v start + U64.v mword);
    assert (Seq.mem obj objs);
    assert (Seq.mem obj (MH.objects_in_chunk_from c base));
    MH.objects_in_chunk_from_member_header_fits c start obj;
    assert (MH.object_wosize_in_chunk c obj == U64.v wz);
    assert (U64.v (Defs.chunked_wosize_of_object source obj) ==
            U64.v wz);
    if Defs.chunked_is_black source obj then begin
      if run_words = 0 then
        ()
      else begin
        nat_nonzero_pos run_words;
        let rw : pos = run_words in
        Pending.pending_run_before_start_nonempty_elim
          source idx base start first_blue rw;
        assert (U64.v first_blue + (run_words - 1) * U64.v mword ==
                U64.v start);
        assert (U64.v first_blue + (run_words - 1) * U64.v mword <=
                U64.v read_addr)
      end;
      header_word_before_read_from_chunk_end
        start obj (MH.chunk_end c) read_addr;
      if next_start_nat >= MH.chunk_end c then begin
        assert (rest == Seq.empty);
        assert (chunked_fused_aux_read_frame_ready
                  source rest 0UL 0 read_addr)
      end else begin
        assert (next_start_nat < heap_size);
        let next_start : hp_addr = U64.uint_to_t next_start_nat in
        assert (rest == MH.objects_in_chunk_from c next_start);
        assert (Seq.length (MH.objects_in_chunk_from c next_start) <
                Seq.length objs);
        let base_mem_tail (o: obj_addr)
          : Lemma
              (requires Seq.mem o (MH.objects_in_chunk_from c next_start))
              (ensures Seq.mem o (MH.objects_in_chunk_from c next_start))
          = ()
        in
        FStar.Classical.forall_intro
          (FStar.Classical.move_requires base_mem_tail);
        let wosize_tail (o: obj_addr)
          : Lemma
              (requires Seq.mem o (MH.objects_in_chunk_from c next_start))
              (ensures
                U64.v (Defs.chunked_wosize_of_object source o) ==
                MH.object_wosize_in_chunk c o)
          =
          assert (Seq.mem o rest);
          seq_tail_mem objs o
        in
        FStar.Classical.forall_intro
          (FStar.Classical.move_requires wosize_tail);
        Pending.pending_run_before_start_empty
          source idx next_start next_start;
        assert (Pending.pending_run_before_start
                  source idx next_start next_start 0UL 0);
        chunked_fused_aux_read_frame_ready_from_chunk_before
          source idx next_start next_start 0UL 0 read_addr
      end
    end else begin
      let new_first : U64.t = if run_words = 0 then obj else first_blue in
      let new_run = run_words + U64.v wz + 1 in
      assert (new_run > 0);
      assert (new_run ==
              run_words + U64.v (Defs.chunked_wosize_of_object source obj) + 1);
      assert (next_start_nat <= U64.v read_addr);
      assert (next_start_nat < heap_size);
      let next_start : hp_addr = U64.uint_to_t next_start_nat in
      if run_words = 0 then
        Pending.nonblack_tail_pending_run_before_start_from_empty
          source idx base start next_start obj wz
      else begin
        nat_nonzero_pos run_words;
        let rw : pos = run_words in
        Pending.nonblack_tail_pending_run_before_start_from_nonempty
          source idx base start next_start obj wz first_blue rw
      end;
      assert (Pending.pending_run_before_start
                source idx base next_start new_first new_run);
      if next_start_nat >= MH.chunk_end c then begin
        assert (rest == Seq.empty);
        assert (new_run <> 0);
        let nr : pos = new_run in
        Pending.pending_run_before_start_nonempty_elim
          source idx base next_start new_first nr;
        assert (U64.v new_first + (new_run - 1) * U64.v mword ==
                U64.v next_start);
        assert (U64.v new_first + (new_run - 1) * U64.v mword <=
                U64.v read_addr);
        assert (chunked_fused_aux_read_frame_ready
                  source Seq.empty new_first new_run read_addr);
        assert (chunked_fused_aux_read_frame_ready
                  source rest new_first new_run read_addr)
      end else begin
        assert (rest == MH.objects_in_chunk_from c next_start);
        assert (Seq.length (MH.objects_in_chunk_from c next_start) <
                Seq.length objs);
        let base_mem_tail (o: obj_addr)
          : Lemma
              (requires Seq.mem o (MH.objects_in_chunk_from c next_start))
              (ensures Seq.mem o (MH.objects_in_chunk_from c base))
          =
          assert (Seq.mem o rest);
          seq_tail_mem objs o
        in
        FStar.Classical.forall_intro
          (FStar.Classical.move_requires base_mem_tail);
        let wosize_tail (o: obj_addr)
          : Lemma
              (requires Seq.mem o (MH.objects_in_chunk_from c next_start))
              (ensures
                U64.v (Defs.chunked_wosize_of_object source o) ==
                MH.object_wosize_in_chunk c o)
          =
          assert (Seq.mem o rest);
          seq_tail_mem objs o
        in
        FStar.Classical.forall_intro
          (FStar.Classical.move_requires wosize_tail);
        chunked_fused_aux_read_frame_ready_from_chunk_before
          source idx base next_start new_first new_run read_addr
      end
    end
  end
#pop-options

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always"
let chunked_fused_aux_read_frame_ready_from_chunk_after
    (source: MH.major_heap)
    (idx: nat{idx < Seq.length source})
    (base start: hp_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (read_addr: hp_addr)
  : Lemma
      (requires
        Pending.pending_run_before_start
          source idx base start first_blue run_words /\
        U64.v read_addr + U64.v mword <=
          MH.chunk_start (Seq.index source idx))
      (ensures
        chunked_fused_aux_read_frame_ready
          source
          (MH.objects_in_chunk_from (Seq.index source idx) start)
          first_blue run_words read_addr)
  =
  let c = Seq.index source idx in
  if run_words = 0 then
    ()
  else begin
    nat_nonzero_pos run_words;
    let rw : pos = run_words in
    Pending.pending_run_before_start_nonempty_elim
      source idx base start first_blue rw;
    let fb : obj_addr = first_blue in
    MH.objects_in_chunk_from_member_in_chunk c base fb;
    assert (U64.v first_blue >= MH.chunk_start c + U64.v mword);
    assert (U64.v read_addr + U64.v mword * 2 <= U64.v first_blue)
  end;
  let objs = MH.objects_in_chunk_from c start in
  let after_objs (o: obj_addr)
    : Lemma
        (requires Seq.mem o objs)
        (ensures U64.v read_addr + U64.v mword * 2 <= U64.v o)
    =
    MH.objects_in_chunk_from_member_in_chunk c start o;
    assert (U64.v o >= MH.chunk_start c + U64.v mword);
    assert (U64.v read_addr + U64.v mword * 2 <= U64.v o)
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires after_objs);
  chunked_fused_aux_read_frame_ready_from_all_after
    source objs first_blue run_words read_addr
#pop-options

let rec chunked_fused_aux_live_read_frame_ready
    (source: MH.major_heap)
    (objs: Seq.seq obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (target: obj_addr)
    (read_addr: hp_addr)
  : Tot prop
      (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then
    False
  else
    let obj = Seq.head objs in
    let rest = Seq.tail objs in
    if obj = target then
      Defs.chunked_is_black source obj /\
      (run_words = 0 \/
       U64.v first_blue + (run_words - 1) * U64.v mword <=
         U64.v read_addr) /\
      (U64.v (hd_address obj) + U64.v mword <= U64.v read_addr \/
       U64.v read_addr + U64.v mword <= U64.v (hd_address obj)) /\
      (forall (o: obj_addr). Seq.mem o rest ==>
        U64.v read_addr + U64.v mword * 2 <= U64.v o)
    else if Defs.chunked_is_black source obj then
      (run_words = 0 \/
       U64.v first_blue + (run_words - 1) * U64.v mword <=
         U64.v read_addr) /\
      (U64.v (hd_address obj) + U64.v mword <= U64.v read_addr \/
       U64.v read_addr + U64.v mword <= U64.v (hd_address obj)) /\
      chunked_fused_aux_live_read_frame_ready
        source rest 0UL 0 target read_addr
    else
      let ws = U64.v (Defs.chunked_wosize_of_object source obj) in
      let new_first : U64.t = if run_words = 0 then obj else first_blue in
      chunked_fused_aux_live_read_frame_ready
        source rest new_first (run_words + ws + 1) target read_addr

let chunked_fused_aux_live_read_frame_ready_seq_eq
    (source: MH.major_heap)
    (s t: Seq.seq obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (target: obj_addr)
    (read_addr: hp_addr)
  : Lemma
      (requires
        s == t /\
        chunked_fused_aux_live_read_frame_ready
          source s first_blue run_words target read_addr)
      (ensures
        chunked_fused_aux_live_read_frame_ready
          source t first_blue run_words target read_addr)
  =
  assert (t == s)

let chunked_fused_aux_live_read_frame_ready_at_head
    (source: MH.major_heap)
    (target: obj_addr)
    (rest: Seq.seq obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (read_addr: hp_addr)
  : Lemma
      (requires
        Defs.chunked_is_black source target /\
        (run_words = 0 \/
         U64.v first_blue + (run_words - 1) * U64.v mword <=
           U64.v read_addr) /\
        (U64.v (hd_address target) + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v (hd_address target)) /\
        (forall (o: obj_addr). Seq.mem o rest ==>
          U64.v read_addr + U64.v mword * 2 <= U64.v o))
      (ensures
        chunked_fused_aux_live_read_frame_ready
          source (Seq.cons target rest) first_blue run_words target read_addr)
  =
  assert (Seq.length (Seq.cons target rest) > 0);
  assert (Seq.head (Seq.cons target rest) == target);
  assert (Seq.equal (Seq.tail (Seq.cons target rest)) rest);
  Seq.lemma_eq_elim (Seq.tail (Seq.cons target rest)) rest;
  assert (Seq.tail (Seq.cons target rest) == rest)

let chunked_fused_aux_live_read_frame_ready_current_head
    (source: MH.major_heap)
    (objs: Seq.seq obj_addr)
    (rest: Seq.seq obj_addr)
    (target: obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (read_addr: hp_addr)
  : Lemma
      (requires
        Seq.length objs > 0 /\
        Seq.head objs == target /\
        Seq.tail objs == rest /\
        Defs.chunked_is_black source target /\
        (run_words = 0 \/
         U64.v first_blue + (run_words - 1) * U64.v mword <=
           U64.v read_addr) /\
        (U64.v (hd_address target) + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v (hd_address target)) /\
        (forall (o: obj_addr). Seq.mem o rest ==>
          U64.v read_addr + U64.v mword * 2 <= U64.v o))
      (ensures
        chunked_fused_aux_live_read_frame_ready
          source objs first_blue run_words target read_addr)
  = ()

let chunked_fused_aux_live_read_frame_ready_black_head
    (source: MH.major_heap)
    (objs: Seq.seq obj_addr)
    (obj: obj_addr)
    (rest: Seq.seq obj_addr)
    (target: obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (read_addr: hp_addr)
  : Lemma
      (requires
        Seq.length objs > 0 /\
        Seq.head objs == obj /\
        Seq.tail objs == rest /\
        obj <> target /\
        Defs.chunked_is_black source obj /\
        (run_words = 0 \/
         U64.v first_blue + (run_words - 1) * U64.v mword <=
           U64.v read_addr) /\
        (U64.v (hd_address obj) + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v (hd_address obj)) /\
        chunked_fused_aux_live_read_frame_ready
          source rest 0UL 0 target read_addr)
      (ensures
        chunked_fused_aux_live_read_frame_ready
          source objs first_blue run_words target read_addr)
  = ()

let chunked_fused_aux_live_read_frame_ready_nonblack_head
    (source: MH.major_heap)
    (objs: Seq.seq obj_addr)
    (obj: obj_addr)
    (rest: Seq.seq obj_addr)
    (target: obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (read_addr: hp_addr)
  : Lemma
      (requires
        Seq.length objs > 0 /\
        Seq.head objs == obj /\
        Seq.tail objs == rest /\
        obj <> target /\
        ~(Defs.chunked_is_black source obj) /\
        (let ws = U64.v (Defs.chunked_wosize_of_object source obj) in
         let new_first : U64.t = if run_words = 0 then obj else first_blue in
         chunked_fused_aux_live_read_frame_ready
           source rest new_first (run_words + ws + 1) target read_addr))
      (ensures
        chunked_fused_aux_live_read_frame_ready
          source objs first_blue run_words target read_addr)
  = ()

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always"
let chunked_fused_aux_live_read_frame_ready_nonblack_head_named_run
    (source: MH.major_heap)
    (objs: Seq.seq obj_addr)
    (obj: obj_addr)
    (rest: Seq.seq obj_addr)
    (target: obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (new_first: U64.t)
    (new_run: nat)
    (read_addr: hp_addr)
  : Lemma
      (requires
        Seq.length objs > 0 /\
        Seq.head objs == obj /\
        Seq.tail objs == rest /\
        obj <> target /\
        ~(Defs.chunked_is_black source obj) /\
        new_first == (if run_words = 0 then obj else first_blue) /\
        new_run ==
          run_words + U64.v (Defs.chunked_wosize_of_object source obj) + 1 /\
        chunked_fused_aux_live_read_frame_ready
          source rest new_first new_run target read_addr)
      (ensures
        chunked_fused_aux_live_read_frame_ready
          source objs first_blue run_words target read_addr)
  =
  assert (new_run ==
          run_words + U64.v (Defs.chunked_wosize_of_object source obj) + 1);
  assert (new_first == (if run_words = 0 then obj else first_blue));
  assert (chunked_fused_aux_live_read_frame_ready
            source rest new_first
            (run_words + U64.v (Defs.chunked_wosize_of_object source obj) + 1)
            target read_addr);
  chunked_fused_aux_live_read_frame_ready_nonblack_head
    source objs obj rest target first_blue run_words read_addr
#pop-options

let rec chunked_fused_aux_read_frame_ready_from_live_target
    (source: MH.major_heap)
    (objs: Seq.seq obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (target: obj_addr)
    (read_addr: hp_addr)
  : Lemma
      (requires
        chunked_fused_aux_live_read_frame_ready
          source objs first_blue run_words target read_addr)
      (ensures
        chunked_fused_aux_read_frame_ready
          source objs first_blue run_words read_addr)
      (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then
    assert False
  else begin
    assert (~(Seq.length objs = 0));
    nat_nonzero_pos (Seq.length objs);
    assert (Seq.length objs > 0);
    let obj = Seq.head objs in
    let rest = Seq.tail objs in
    assert (Seq.length rest < Seq.length objs);
    if obj = target then begin
      assert (Defs.chunked_is_black source obj);
      chunked_fused_aux_read_frame_ready_from_all_after
        source rest 0UL 0 read_addr
    end else if Defs.chunked_is_black source obj then
      chunked_fused_aux_read_frame_ready_from_live_target
        source rest 0UL 0 target read_addr
    else begin
      let ws = U64.v (Defs.chunked_wosize_of_object source obj) in
      let new_first : U64.t = if run_words = 0 then obj else first_blue in
      chunked_fused_aux_read_frame_ready_from_live_target
        source rest new_first (run_words + ws + 1) target read_addr
    end
  end

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let rec chunked_fused_aux_live_read_frame_ready_from_chunk_from
    (source: MH.major_heap)
    (c: MH.heap_chunk)
    (start: hp_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (target: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (field_addr: hp_addr)
    (hdr: U64.t)
  : Lemma
      (requires
        Seq.mem target (MH.objects_in_chunk_from c start) /\
        (forall (o: obj_addr). Seq.mem o (MH.objects_in_chunk_from c start) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk c o) /\
        Defs.chunked_read_header source target == Some hdr /\
        Defs.chunked_is_black source target /\
        U64.v i <= U64.v (Obj.getWosize hdr) /\
        U64.v (Obj.getWosize hdr) == MH.object_wosize_in_chunk c target /\
        U64.v (hd_address target) + U64.v mword * U64.v i +
          U64.v mword <= heap_size /\
        field_addr == U64.add (hd_address target) (U64.mul mword i) /\
        (run_words = 0 \/
         U64.v first_blue + (run_words - 1) * U64.v mword == U64.v start))
      (ensures
        chunked_fused_aux_live_read_frame_ready
          source
          (MH.objects_in_chunk_from c start)
          first_blue
          run_words
          target
          field_addr)
      (decreases MH.chunk_end c - U64.v start)
  =
  assert_spinoff True;
  assert
    (run_words = 0 \/
     U64.v first_blue + (run_words - 1) * U64.v mword == U64.v start);
  if U64.v start < MH.chunk_start c then
    assert False
  else if U64.v start + U64.v mword >= MH.chunk_end c then
    assert False
  else begin
    let header = MH.read_word_in_chunk c start in
    let wz = Obj.getWosize header in
    let obj_size_words = U64.v wz + 1 in
    let start_nat : nat = U64.v start in
    let word_nat : nat = U64.v mword in
    let next_start_nat : nat =
      start_nat + obj_size_words * word_nat in
    assert (next_start_nat ==
            U64.v start + obj_size_words * U64.v mword);
    if next_start_nat > MH.chunk_end c || next_start_nat >= pow2 64 then
      assert False
    else begin
      f_address_spec start;
      let first : obj_addr = f_address start in
      let tail =
        if next_start_nat >= MH.chunk_end c then
          Seq.empty
        else begin
          assert (next_start_nat < heap_size);
          assert (next_start_nat < pow2 64);
          MH.next_object_start_aligned start obj_size_words;
          assert (next_start_nat % U64.v mword == 0);
          let next_start_nat_u : n:nat{n < pow2 64} = next_start_nat in
          let next_start : hp_addr = U64.uint_to_t next_start_nat_u in
          MH.objects_in_chunk_from c next_start
        end
      in
      let objs = MH.objects_in_chunk_from c start in
      assert (U64.v start >= MH.chunk_start c);
      assert (U64.v start + U64.v mword < MH.chunk_end c);
      assert (next_start_nat <= MH.chunk_end c);
      assert (next_start_nat < pow2 64);
      if next_start_nat < MH.chunk_end c then begin
        MH.next_object_start_aligned start obj_size_words;
        assert (next_start_nat % U64.v mword == 0)
      end;
      assert (next_start_nat < MH.chunk_end c ==>
              next_start_nat % U64.v mword == 0);
      MH.objects_in_chunk_from_cons_step c start;
      assert (objs == Seq.cons first tail);
      assert (Seq.length objs > 0);
      assert (Seq.head objs == first);
      assert (Seq.tail objs == tail);
      Fields.mem_cons_lemma target first tail;
      if target = first then begin
        assert (Defs.chunked_is_black source first);
        hd_f_roundtrip start;
        assert (hd_address first == start);
        assert (MH.word_in_chunk c (hd_address first));
        assert (MH.object_wosize_in_chunk c first == U64.v wz);
        assert (U64.v i <= U64.v wz);
        assert (U64.v i >= 1);
        assert (U64.v field_addr ==
                U64.v start + U64.v mword * U64.v i);
        assert (run_words = 0 \/
                U64.v first_blue + (run_words - 1) * U64.v mword <=
                  U64.v field_addr);
        assert (U64.v (hd_address first) + U64.v mword <=
                U64.v field_addr);
        let suffix_after (o: obj_addr) : Lemma
            (requires Seq.mem o tail)
            (ensures U64.v field_addr + U64.v mword * 2 <= U64.v o)
          =
          if next_start_nat >= MH.chunk_end c then
            assert False
          else begin
            let next_start_nat_u : n:nat{n < pow2 64} = next_start_nat in
            let next_start : hp_addr = U64.uint_to_t next_start_nat_u in
            assert (tail == MH.objects_in_chunk_from c next_start);
            assert (next_start_nat ==
                    U64.v start + (U64.v wz + 1) * U64.v mword);
            assert (U64.v i <= U64.v wz);
            chunk_suffix_object_after_field_addr
              c start next_start o i wz field_addr
          end
        in
        FStar.Classical.forall_intro
          (FStar.Classical.move_requires suffix_after);
        assert (Seq.head objs == target);
        chunked_fused_aux_live_read_frame_ready_current_head
          source objs tail target first_blue run_words field_addr
      end else begin
        assert (Seq.mem target tail);
        if next_start_nat >= MH.chunk_end c then
          assert False
        else begin
          assert (next_start_nat < heap_size);
          assert (next_start_nat < pow2 64);
          MH.next_object_start_aligned start obj_size_words;
          assert (next_start_nat % U64.v mword == 0);
          let next_start_nat_u : n:nat{n < pow2 64} = next_start_nat in
          let next_start : hp_addr = U64.uint_to_t next_start_nat_u in
          assert (tail == MH.objects_in_chunk_from c next_start);
          let wosize_match_tail (o: obj_addr)
            : Lemma
                (requires Seq.mem o (MH.objects_in_chunk_from c next_start))
                (ensures
                  U64.v (Defs.chunked_wosize_of_object source o) ==
                  MH.object_wosize_in_chunk c o)
            =
            assert (MH.objects_in_chunk_from c next_start == tail);
            seq_mem_eq (MH.objects_in_chunk_from c next_start) tail o;
            assert (Seq.mem o tail);
            assert (Seq.tail objs == tail);
            seq_tail_mem objs o;
            assert (Seq.mem o objs);
            assert (objs == MH.objects_in_chunk_from c start);
            seq_mem_eq objs (MH.objects_in_chunk_from c start) o
          in
          FStar.Classical.forall_intro
            (FStar.Classical.move_requires wosize_match_tail);
          MH.objects_in_chunk_from_addresses_gt_start c next_start target;
          assert (U64.v target > U64.v next_start);
          hd_address_spec target;
          assert (U64.v (hd_address target) + U64.v mword == U64.v target);
          assert (U64.v field_addr >= U64.v target);
          assert (U64.v field_addr >= U64.v next_start);
          if Defs.chunked_is_black source first then begin
            assert (run_words = 0 \/
                    U64.v first_blue + (run_words - 1) * U64.v mword <=
                      U64.v field_addr);
            hd_f_roundtrip start;
            assert (hd_address first == start);
            assert (U64.v (hd_address first) + U64.v mword <=
                    U64.v field_addr);
            chunked_fused_aux_live_read_frame_ready_from_chunk_from
              source c next_start 0UL 0 target i field_addr hdr;
            chunked_fused_aux_live_read_frame_ready_black_head
              source objs first tail target first_blue run_words field_addr
          end else begin
            let new_first : U64.t =
              if run_words = 0 then first else first_blue in
            let new_run = run_words + U64.v wz + 1 in
            hd_f_roundtrip start;
            assert (hd_address first == start);
            hd_address_spec first;
            assert (U64.v (hd_address first) + U64.v mword == U64.v first);
            assert (U64.v first == U64.v start + U64.v mword);
            assert (U64.v next_start == next_start_nat);
            assert (next_start_nat ==
                    U64.v start + (U64.v wz + 1) * U64.v mword);
            assert (U64.v next_start ==
                    U64.v start + (U64.v wz + 1) * U64.v mword);
            assert (U64.v mword > 0);
            assert (U64.v wz + 1 > 0);
            assert (U64.v next_start > U64.v start);
            assert (U64.v next_start < MH.chunk_end c);
            assert (MH.chunk_end c - U64.v next_start <
                    MH.chunk_end c - U64.v start);
            MH.objects_in_chunk_from_head_mem c start;
            assert (Seq.mem first (MH.objects_in_chunk_from c start));
            assert (MH.object_wosize_in_chunk c first == U64.v wz);
            assert (U64.v (Defs.chunked_wosize_of_object source first) ==
                    MH.object_wosize_in_chunk c first);
            assert (U64.v (Defs.chunked_wosize_of_object source first) ==
                    U64.v wz);
            assert (new_run ==
                    run_words +
                    U64.v (Defs.chunked_wosize_of_object source first) + 1);
            assert_spinoff True;
            assert (run_words = 0 \/
                    U64.v first_blue + (run_words - 1) * U64.v mword ==
                      U64.v start);
            chunked_fused_aux_nonblack_run_end_at_next_start
              start first first_blue run_words wz next_start;
            assert (tail == MH.objects_in_chunk_from c next_start);
            assert (Seq.mem target tail);
            seq_mem_eq tail (MH.objects_in_chunk_from c next_start) target;
            assert (Seq.mem target (MH.objects_in_chunk_from c next_start));
            assert (Defs.chunked_read_header source target == Some hdr);
            assert (Defs.chunked_is_black source target);
            assert (U64.v i <= U64.v (Obj.getWosize hdr));
            assert (U64.v (Obj.getWosize hdr) ==
                    MH.object_wosize_in_chunk c target);
            assert (U64.v (hd_address target) +
                    U64.v mword * U64.v i + U64.v mword <= heap_size);
            assert (field_addr == U64.add (hd_address target) (U64.mul mword i));
            assert (new_first == (if run_words = 0 then first else first_blue));
            assert (new_run == run_words + U64.v wz + 1);
            assert (new_run = 0 \/
                    U64.v new_first + (new_run - 1) * U64.v mword ==
                      U64.v next_start);
            assert (U64.v field_addr >= U64.v next_start);
            if new_run = 0 then
              assert (new_run = 0 \/
                      U64.v new_first + (new_run - 1) * U64.v mword <=
                        U64.v field_addr)
            else begin
              assert (U64.v new_first + (new_run - 1) * U64.v mword ==
                      U64.v next_start);
              assert (U64.v new_first + (new_run - 1) * U64.v mword <=
                      U64.v field_addr);
              assert (new_run = 0 \/
                      U64.v new_first + (new_run - 1) * U64.v mword <=
                        U64.v field_addr)
            end;
            assert (Seq.length (MH.objects_in_chunk_from c next_start) <
                   Seq.length (MH.objects_in_chunk_from c start));
            chunked_fused_aux_live_read_frame_ready_from_chunk_from
              source c next_start new_first new_run target i field_addr hdr;
            assert (chunked_fused_aux_live_read_frame_ready
                      source
                      (MH.objects_in_chunk_from c next_start)
                      new_first new_run target field_addr);
            chunked_fused_aux_live_read_frame_ready_seq_eq
              source (MH.objects_in_chunk_from c next_start) tail
              new_first new_run target field_addr;
            assert (chunked_fused_aux_live_read_frame_ready
                      source tail new_first new_run target field_addr);
            assert (~(Defs.chunked_is_black source first));
            assert (Seq.length objs > 0);
            assert (Seq.head objs == first);
            assert (Seq.tail objs == tail);
            assert (first <> target);
            chunked_fused_aux_live_read_frame_ready_nonblack_head_named_run
              source objs first tail target first_blue run_words
              new_first new_run field_addr
          end
        end
      end
    end
  end

let chunked_fused_aux_live_read_frame_ready_from_chunk
    (source: MH.major_heap)
    (c: MH.heap_chunk)
    (target: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (field_addr: hp_addr)
    (hdr: U64.t)
  : Lemma
      (requires
        Seq.mem target (MH.objects_in_chunk c) /\
        (forall (o: obj_addr). Seq.mem o (MH.objects_in_chunk c) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk c o) /\
        Defs.chunked_read_header source target == Some hdr /\
        Defs.chunked_is_black source target /\
        U64.v i <= U64.v (Obj.getWosize hdr) /\
        U64.v (Obj.getWosize hdr) == MH.object_wosize_in_chunk c target /\
        U64.v (hd_address target) + U64.v mword * U64.v i +
          U64.v mword <= heap_size /\
        field_addr == U64.add (hd_address target) (U64.mul mword i))
      (ensures
        chunked_fused_aux_live_read_frame_ready
          source (MH.objects_in_chunk c) 0UL 0 target field_addr)
  =
  chunked_fused_aux_live_read_frame_ready_from_chunk_from
    source c c.base 0UL 0 target i field_addr hdr
#pop-options

let rec chunked_fused_aux_preserves_other_read
    (source work: MH.major_heap)
    (objs: Seq.seq obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
    (read_addr: hp_addr)
    (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major work read_addr == Some old /\
        chunked_fused_aux_read_frame_ready
          source objs first_blue run_words read_addr)
      (ensures
        MH.read_word_in_major
          (fst (Defs.chunked_fused_aux
            source work objs first_blue run_words fp))
          read_addr == Some old)
      (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then begin
    Defs.chunked_fused_aux_empty_length
      source work objs first_blue run_words fp;
    assert (run_words = 0 \/
            U64.v read_addr + U64.v mword * 2 <= U64.v first_blue \/
            U64.v first_blue + (run_words - 1) * U64.v mword <=
              U64.v read_addr);
    chunked_flush_blue_preserves_other_read
      work first_blue run_words fp read_addr old
  end else begin
    assert (~(Seq.length objs = 0));
    nat_nonzero_pos (Seq.length objs);
    assert (Seq.length objs > 0);
    let obj = Seq.head objs in
    let rest = Seq.tail objs in
    assert (Seq.length rest < Seq.length objs);
    if Defs.chunked_is_black source obj then begin
      Defs.chunked_fused_aux_black_step
        source work objs first_blue run_words fp;
      let (work', fp') =
        Defs.chunked_flush_blue work first_blue run_words fp in
      let work'' = Defs.chunked_make_white work' obj in
      chunked_flush_blue_make_white_preserves_other_read
        work first_blue run_words fp obj read_addr old;
      chunked_fused_aux_preserves_other_read
        source work'' rest 0UL 0 fp' read_addr old
    end else begin
      Defs.chunked_fused_aux_nonblack_step
        source work objs first_blue run_words fp;
      let ws = U64.v (Defs.chunked_wosize_of_object source obj) in
      let new_first : U64.t = if run_words = 0 then obj else first_blue in
      chunked_fused_aux_preserves_other_read
        source work rest new_first (run_words + ws + 1) fp read_addr old
    end
  end

let chunked_fused_aux_preserves_get_field_read_some
    (source work: MH.major_heap)
    (objs: Seq.seq obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (field_addr: hp_addr)
    (old: U64.t)
  : Lemma
      (requires
        U64.v (hd_address obj) + U64.v mword * U64.v i + U64.v mword <=
          heap_size /\
        field_addr == U64.add (hd_address obj) (U64.mul mword i) /\
        MH.read_word_in_major work field_addr == Some old /\
        chunked_fused_aux_read_frame_ready
          source objs first_blue run_words field_addr)
      (ensures
        MarkDefs.chunked_get_field
          (fst (Defs.chunked_fused_aux
            source work objs first_blue run_words fp))
          obj i ==
        MarkDefs.chunked_get_field work obj i)
  =
  let final =
    fst (Defs.chunked_fused_aux source work objs first_blue run_words fp) in
  assert (U64.add (hd_address obj) (U64.mul mword i) == field_addr);
  MarkDefs.chunked_get_field_read_some work obj i old;
  chunked_fused_aux_preserves_other_read
    source work objs first_blue run_words fp field_addr old;
  MarkDefs.chunked_get_field_read_some final obj i old

let chunked_fused_aux_preserves_get_field_from_live_target
    (source work: MH.major_heap)
    (objs: Seq.seq obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (field_addr: hp_addr)
    (old: U64.t)
  : Lemma
      (requires
        U64.v (hd_address obj) + U64.v mword * U64.v i + U64.v mword <=
          heap_size /\
        field_addr == U64.add (hd_address obj) (U64.mul mword i) /\
        MH.read_word_in_major work field_addr == Some old /\
        chunked_fused_aux_live_read_frame_ready
          source objs first_blue run_words obj field_addr)
      (ensures
        MarkDefs.chunked_get_field
          (fst (Defs.chunked_fused_aux
            source work objs first_blue run_words fp))
          obj i ==
        MarkDefs.chunked_get_field work obj i)
  =
  chunked_fused_aux_read_frame_ready_from_live_target
    source objs first_blue run_words obj field_addr;
  chunked_fused_aux_preserves_get_field_read_some
    source work objs first_blue run_words fp obj i field_addr old

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_fused_aux_live_field_data_preserved_from_chunk
  (source: MH.major_heap)
  (idx: nat)
  (fp: U64.t)
  (target: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        idx < Seq.length source /\
        Seq.mem target (MH.objects_in_chunk (Seq.index source idx)) /\
        (forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o) /\
        Defs.chunked_read_header source target == Some hdr /\
        Defs.chunked_is_black source target /\
        U64.v (Obj.getWosize hdr) ==
          MH.object_wosize_in_chunk (Seq.index source idx) target /\
        (let final =
          fst (Defs.chunked_fused_aux
            source source (MH.objects_in_chunk (Seq.index source idx))
            0UL 0 fp) in
         ChunkedGraph.chunked_major_vertex final target))
      (ensures
        (let final =
          fst (Defs.chunked_fused_aux
            source source (MH.objects_in_chunk (Seq.index source idx))
            0UL 0 fp) in
        ChunkedGraph.chunked_major_field_data_preserved source final target))
  =
  let c = Seq.index source idx in
  let objs = MH.objects_in_chunk c in
  let final = fst (Defs.chunked_fused_aux source source objs 0UL 0 fp) in
  let field_data_refined
      (i: U64.t{U64.v i >= 1})
    : Lemma
      (requires U64.v i <=
        U64.v (Defs.chunked_wosize_of_object source target))
      (ensures
        MarkDefs.chunked_get_field source target i ==
        MarkDefs.chunked_get_field final target i)
    =
    Defs.chunked_wosize_of_object_some source target hdr;
    assert (U64.v i <= U64.v (Obj.getWosize hdr));
    MH.objects_in_chunk_member_header_fits c target;
    assert (MH.object_header_size_fits_in_chunk c target);
    assert (MH.word_in_chunk c (hd_address target));
    MH.lookup_chunk_index_word_in_chunk source (hd_address target) idx;
    assert (MH.lookup_chunk_index source (hd_address target) == Some idx);
    MH.lookup_chunk_index_some source (hd_address target) idx;
    assert (MH.chunk_contains_addr c (hd_address target));
    hd_address_spec target;
    assert (U64.v (hd_address target) + U64.v mword == U64.v target);
    FStar.Math.Lemmas.lemma_mult_le_right
      (U64.v mword) (U64.v i)
      (MH.object_wosize_in_chunk c target);
    assert (U64.v mword * U64.v i <=
            U64.v mword * MH.object_wosize_in_chunk c target);
    assert (U64.v target + U64.v mword * U64.v i <=
            U64.v target +
            MH.object_wosize_in_chunk c target * U64.v mword);
    assert (U64.v (hd_address target) +
            U64.v mword * U64.v i + U64.v mword ==
            U64.v target + U64.v mword * U64.v i);
    assert (U64.v (hd_address target) +
            U64.v mword * U64.v i + U64.v mword <=
            U64.v target +
            MH.object_wosize_in_chunk c target * U64.v mword);
    let field_addr : hp_addr =
      U64.add (hd_address target) (U64.mul mword i) in
    assert (U64.v target <= U64.v field_addr);
    assert (U64.v field_addr + U64.v mword ==
            U64.v (hd_address target) +
            U64.v mword * U64.v i + U64.v mword);
    assert (U64.v field_addr + U64.v mword <=
            U64.v target +
            MH.object_wosize_in_chunk c target * U64.v mword);
    MH.major_objects_member_at_index source idx target;
    MH.major_object_payload_word_in_lookup_chunk
      source idx target field_addr;
    MH.read_word_in_major_at_lookup_index source field_addr idx;
    let old = MH.read_word_in_chunk c field_addr in
    assert (MH.read_word_in_major source field_addr == Some old);
    chunked_fused_aux_live_read_frame_ready_from_chunk
      source c target i field_addr hdr;
    chunked_fused_aux_preserves_get_field_from_live_target
      source source objs 0UL 0 fp target i field_addr old;
    assert (MarkDefs.chunked_get_field final target i ==
            MarkDefs.chunked_get_field source target i)
  in
  let field_data (i: U64.t)
    : Lemma
        (ensures
          U64.v i >= 1 /\
          U64.v i <= U64.v (Defs.chunked_wosize_of_object source target) ==>
          MarkDefs.chunked_get_field source target i ==
          MarkDefs.chunked_get_field final target i)
    =
    if U64.v i >= 1 &&
       U64.v i <= U64.v (Defs.chunked_wosize_of_object source target) then begin
      let ii : i':U64.t{U64.v i' >= 1} = i in
      field_data_refined ii;
      assert (MarkDefs.chunked_get_field source target i ==
              MarkDefs.chunked_get_field final target i)
    end
  in
  MH.major_objects_member_at_index source idx target;
  ChunkedGraph.chunked_major_vertex_intro source target;
  FStar.Classical.forall_intro field_data;
  ChunkedGraph.chunked_major_field_data_preserved_intro
    source final target
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_set_object_color_header_effect
    (mh: MH.major_heap)
    (obj: obj_addr)
    (color: Header.color_sem)
    (hdr: U64.t)
  : Lemma
      (requires
        Defs.chunked_read_header mh obj == Some hdr)
      (ensures
        (let new_hdr = Obj.colorHeader hdr color in
        Defs.chunked_read_header
          (Defs.chunked_set_object_color mh obj color)
          obj == Some new_hdr /\
        Obj.getWosize new_hdr == Obj.getWosize hdr /\
        Obj.getTag new_hdr == Obj.getTag hdr /\
        Defs.chunked_wosize_of_object
          (Defs.chunked_set_object_color mh obj color)
          obj ==
        Obj.getWosize hdr /\
        Defs.chunked_tag_of_object
          (Defs.chunked_set_object_color mh obj color)
          obj ==
        Obj.getTag hdr))
  =
  Defs.chunked_read_header_step mh obj;
  let hd = hd_address obj in
  MH.read_word_in_major_lookup_index mh hd hdr;
  let idx = MH.lookup_chunk_index_value mh hd in
  assert (MH.lookup_chunk_index mh hd == Some idx);
  assert (idx < Seq.length mh);
  assert (MH.word_in_chunk (Seq.index mh idx) hd);
  MH.lookup_chunk_index_some mh hd idx;
  Defs.chunked_set_object_color_some mh obj color hdr;
  let new_hdr = Obj.colorHeader hdr color in
  Obj.colorHeader_preserves_wosize hdr color;
  Obj.colorHeader_preserves_tag hdr color;
  let c = Seq.index mh idx in
  let c' = MH.write_word_in_chunk c hd new_hdr in
  MH.write_word_in_major_at_lookup_index mh hd new_hdr idx;
  assert (MH.write_word_in_major mh hd new_hdr == Some (Seq.upd mh idx c'));
  SpecMajorAlloc.major_write_word_or_same_some
    mh (Seq.upd mh idx c') hd new_hdr;
  MH.read_write_in_chunk_same c hd new_hdr;
  assert (MH.read_word_in_chunk c' hd == new_hdr);
  MH.write_word_in_chunk_preserves_word c hd new_hdr hd;
  assert (MH.word_in_chunk c' hd);
  assert (Seq.index (Seq.upd mh idx c') idx == c');
  let no_prior (k: nat{k < idx})
    : Lemma (~(MH.chunk_contains_addr (Seq.index (Seq.upd mh idx c') k) hd))
    =
    assert (Seq.index (Seq.upd mh idx c') k == Seq.index mh k)
  in
  FStar.Classical.forall_intro no_prior;
  MH.read_word_in_major_at_index (Seq.upd mh idx c') hd idx;
  let mh' = Defs.chunked_set_object_color mh obj color in
  Defs.chunked_read_header_step mh' obj;
  assert (Defs.chunked_read_header mh' obj == Some new_hdr);
  Defs.chunked_wosize_of_object_some mh' obj new_hdr;
  Defs.chunked_tag_of_object_some mh' obj new_hdr

let chunked_make_white_header_effect
    (mh: MH.major_heap)
    (obj: obj_addr)
    (hdr: U64.t)
  : Lemma
      (requires
        Defs.chunked_read_header mh obj == Some hdr)
      (ensures
        (let new_hdr = Obj.colorHeader hdr Header.White in
        Defs.chunked_read_header
          (Defs.chunked_make_white mh obj)
          obj == Some new_hdr /\
        Obj.getWosize new_hdr == Obj.getWosize hdr /\
        Obj.getTag new_hdr == Obj.getTag hdr /\
        Defs.chunked_wosize_of_object
          (Defs.chunked_make_white mh obj)
          obj ==
        Obj.getWosize hdr /\
        Defs.chunked_tag_of_object
          (Defs.chunked_make_white mh obj)
          obj ==
        Obj.getTag hdr))
  =
  Defs.chunked_make_white_step mh obj;
  chunked_set_object_color_header_effect mh obj Header.White hdr
#pop-options
