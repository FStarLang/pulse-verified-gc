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
module Defs = GC.Spec.ChunkedSweepCoalesce.Defs
module MarkDefs = GC.Spec.ChunkedMark.Defs
module SpecMajorAlloc = GC.Spec.MajorAllocator

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let nat_nonzero_pos (n: nat)
  : Lemma (requires n <> 0) (ensures n > 0)
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
