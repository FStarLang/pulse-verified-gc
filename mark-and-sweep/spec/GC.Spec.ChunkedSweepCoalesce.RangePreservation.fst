module GC.Spec.ChunkedSweepCoalesce.RangePreservation

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module Defs = GC.Spec.ChunkedSweepCoalesce.Defs
module MarkDefs = GC.Spec.ChunkedMark.Defs
module ChunkedGraph = GC.Spec.ChunkedMajorGC.Graph
module SpecMajorAlloc = GC.Spec.MajorAllocator

#set-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always --warn_error -321"

let nat_nonzero_pos (n: nat)
  : Lemma (requires n <> 0) (ensures n > 0)
  = ()

let same_chunk_ranges (before after: MH.major_heap) : prop =
  Seq.length before == Seq.length after /\
  (forall (i: nat{i < Seq.length before /\ i < Seq.length after}).
    MH.chunk_start (Seq.index after i) ==
      MH.chunk_start (Seq.index before i) /\
    MH.chunk_end (Seq.index after i) ==
      MH.chunk_end (Seq.index before i))

let same_chunk_ranges_refl (mh: MH.major_heap)
  : Lemma (same_chunk_ranges mh mh)
  = ()

let same_chunk_ranges_trans
    (mh0 mh1 mh2: MH.major_heap)
  : Lemma
      (requires same_chunk_ranges mh0 mh1 /\ same_chunk_ranges mh1 mh2)
      (ensures same_chunk_ranges mh0 mh2)
  =
  let ranges (i: nat{i < Seq.length mh0 /\ i < Seq.length mh2})
    : Lemma
        (ensures
          MH.chunk_start (Seq.index mh2 i) ==
            MH.chunk_start (Seq.index mh0 i) /\
          MH.chunk_end (Seq.index mh2 i) ==
            MH.chunk_end (Seq.index mh0 i))
    =
    assert (i < Seq.length mh1);
    assert (i < Seq.length mh2)
  in
  FStar.Classical.forall_intro ranges

let pointer_in_chunk_same_range
    (c0 c1: MH.heap_chunk)
    (v: U64.t)
  : Lemma
      (requires
        MH.chunk_start c1 == MH.chunk_start c0 /\
        MH.chunk_end c1 == MH.chunk_end c0)
      (ensures MH.pointer_in_chunk c0 v == MH.pointer_in_chunk c1 v)
  = ()

#push-options "--z3rlimit 5 --fuel 1 --ifuel 0 --split_queries always"
let rec same_chunk_ranges_preserves_is_major_pointer
    (mh0 mh1: MH.major_heap)
    (v: U64.t)
  : Lemma
      (requires same_chunk_ranges mh0 mh1)
      (ensures MH.is_major_pointer mh0 v == MH.is_major_pointer mh1 v)
      (decreases Seq.length mh0)
  =
  if Seq.length mh0 = 0 then
    assert (Seq.length mh1 = 0)
  else begin
    let hd0 = Seq.head mh0 in
    let tl0 = Seq.tail mh0 in
    let hd1 = Seq.head mh1 in
    let tl1 = Seq.tail mh1 in
    assert (Seq.length mh1 > 0);
    assert (Seq.index mh0 0 == hd0);
    assert (Seq.index mh1 0 == hd1);
    pointer_in_chunk_same_range hd0 hd1 v;
    let tail_ranges (i: nat{i < Seq.length tl0 /\ i < Seq.length tl1})
      : Lemma
          (ensures
            MH.chunk_start (Seq.index tl1 i) ==
              MH.chunk_start (Seq.index tl0 i) /\
            MH.chunk_end (Seq.index tl1 i) ==
              MH.chunk_end (Seq.index tl0 i))
      =
      assert (i + 1 < Seq.length mh0);
      assert (Seq.index tl0 i == Seq.index mh0 (i + 1));
      assert (Seq.index tl1 i == Seq.index mh1 (i + 1))
    in
    FStar.Classical.forall_intro tail_ranges;
    assert (same_chunk_ranges tl0 tl1);
    same_chunk_ranges_preserves_is_major_pointer tl0 tl1 v
  end
#pop-options

#push-options "--z3rlimit 5 --fuel 1 --ifuel 0 --split_queries always"
let rec write_word_in_major_preserves_ranges
    (mh: MH.major_heap)
    (addr: hp_addr)
    (value: U64.t)
  : Lemma
      (ensures
        (match MH.write_word_in_major mh addr value with
        | None -> True
        | Some mh' -> same_chunk_ranges mh mh'))
      (decreases Seq.length mh)
  =
  if Seq.length mh = 0 then
    ()
  else begin
    let c = Seq.head mh in
    let tl = Seq.tail mh in
    if MH.word_in_chunk c addr then begin
      let c' = MH.write_word_in_chunk c addr value in
      MH.write_word_in_chunk_preserves_range c addr value;
      assert (Seq.length (Seq.cons c' tl) == Seq.length mh);
      let ranges (i: nat{i < Seq.length mh /\ i < Seq.length (Seq.cons c' tl)})
        : Lemma
            (ensures
              MH.chunk_start (Seq.index (Seq.cons c' tl) i) ==
                MH.chunk_start (Seq.index mh i) /\
              MH.chunk_end (Seq.index (Seq.cons c' tl) i) ==
                MH.chunk_end (Seq.index mh i))
        =
        if i = 0 then begin
          assert (Seq.index mh i == c);
          assert (Seq.index (Seq.cons c' tl) i == c')
        end else begin
          assert (i <> 0);
          nat_nonzero_pos i;
          assert (i >= 1);
          assert (i - 1 < Seq.length tl);
          let im1 : n:nat{n < Seq.length tl} = i - 1 in
          assert (Seq.index mh i == Seq.index tl im1);
          assert (Seq.index (Seq.cons c' tl) i == Seq.index tl im1)
        end
      in
      FStar.Classical.forall_intro ranges
    end else begin
      write_word_in_major_preserves_ranges tl addr value;
      match MH.write_word_in_major tl addr value with
      | None -> ()
      | Some tl' ->
        assert (Seq.length tl == Seq.length tl');
        assert (Seq.length (Seq.cons c tl') == Seq.length mh);
        let ranges (i: nat{i < Seq.length mh /\ i < Seq.length (Seq.cons c tl')})
          : Lemma
              (ensures
                MH.chunk_start (Seq.index (Seq.cons c tl') i) ==
                  MH.chunk_start (Seq.index mh i) /\
                MH.chunk_end (Seq.index (Seq.cons c tl') i) ==
                  MH.chunk_end (Seq.index mh i))
          =
          if i = 0 then begin
            assert (Seq.index mh i == c);
            assert (Seq.index (Seq.cons c tl') i == c)
          end else begin
            assert (i <> 0);
            nat_nonzero_pos i;
            assert (i >= 1);
            assert (i - 1 < Seq.length tl);
            assert (i - 1 < Seq.length tl');
            let im1 : n:nat{n < Seq.length tl} = i - 1 in
            assert (Seq.index mh i == Seq.index tl im1);
            assert (Seq.index (Seq.cons c tl') i == Seq.index tl' im1)
          end
        in
        FStar.Classical.forall_intro ranges
    end
  end
#pop-options

let major_write_word_or_same_preserves_ranges
    (mh: MH.major_heap)
    (addr: hp_addr)
    (value: U64.t)
  : Lemma
      (ensures
        same_chunk_ranges mh
          (SpecMajorAlloc.major_write_word_or_same mh addr value))
  =
  write_word_in_major_preserves_ranges mh addr value;
  match MH.write_word_in_major mh addr value with
  | None -> same_chunk_ranges_refl mh
  | Some _ -> ()

#push-options "--z3rlimit 5 --fuel 1 --ifuel 0 --split_queries always"
let rec chunked_zero_fields_preserves_ranges
    (mh: MH.major_heap)
    (addr: U64.t)
    (n: nat)
  : Lemma
      (ensures
        same_chunk_ranges mh (Defs.chunked_zero_fields mh addr n))
      (decreases n)
  =
  if n = 0 then begin
    Defs.chunked_zero_fields_zero mh addr;
    assert (Defs.chunked_zero_fields mh addr n == mh);
    same_chunk_ranges_refl mh
  end else if U64.v addr + U64.v mword > heap_size then begin
    Defs.chunked_zero_fields_no_room mh addr n;
    assert (Defs.chunked_zero_fields mh addr n == mh);
    same_chunk_ranges_refl mh
  end else if U64.v addr >= heap_size then begin
    Defs.chunked_zero_fields_out_of_heap mh addr n;
    assert (Defs.chunked_zero_fields mh addr n == mh);
    same_chunk_ranges_refl mh
  end else if U64.v addr % U64.v mword <> 0 then begin
    Defs.chunked_zero_fields_unaligned mh addr n;
    assert (Defs.chunked_zero_fields mh addr n == mh);
    same_chunk_ranges_refl mh
  end else begin
    let mh' =
      SpecMajorAlloc.major_write_word_or_same mh (addr <: hp_addr) 0UL in
    Defs.chunked_zero_fields_step mh addr n;
    major_write_word_or_same_preserves_ranges mh (addr <: hp_addr) 0UL;
    assert (same_chunk_ranges mh mh');
    if U64.v addr + U64.v mword >= pow2 64 then begin
      assert (Defs.chunked_zero_fields mh addr n == mh')
    end else begin
      let next = U64.uint_to_t (U64.v addr + U64.v mword) in
      let final_tail = Defs.chunked_zero_fields mh' next (n - 1) in
      chunked_zero_fields_preserves_ranges mh' next (n - 1);
      assert (same_chunk_ranges mh' final_tail);
      same_chunk_ranges_trans mh mh' final_tail;
      assert (Defs.chunked_zero_fields mh addr n == final_tail)
    end
  end
#pop-options

let chunked_set_object_color_preserves_ranges
    (mh: MH.major_heap)
    (obj: obj_addr)
    (color: GC.Lib.Header.color_sem)
  : Lemma
      (ensures
        same_chunk_ranges mh (Defs.chunked_set_object_color mh obj color))
  =
  match Defs.chunked_read_header mh obj with
  | None ->
    Defs.chunked_set_object_color_none mh obj color;
    same_chunk_ranges_refl mh
  | Some hdr ->
    Defs.chunked_set_object_color_some mh obj color hdr;
    major_write_word_or_same_preserves_ranges
      mh (hd_address obj) (GC.Spec.Object.colorHeader hdr color)

let chunked_make_white_preserves_ranges
    (mh: MH.major_heap)
    (obj: obj_addr)
  : Lemma
      (ensures same_chunk_ranges mh (Defs.chunked_make_white mh obj))
  =
  Defs.chunked_make_white_step mh obj;
  chunked_set_object_color_preserves_ranges mh obj GC.Lib.Header.White

#push-options "--z3rlimit 5 --fuel 1 --ifuel 0 --split_queries always"
let chunked_flush_blue_preserves_ranges
    (mh: MH.major_heap)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
  : Lemma
      (ensures
        same_chunk_ranges mh
          (fst (Defs.chunked_flush_blue mh first_blue run_words fp)))
  =
  if run_words = 0 then begin
    Defs.chunked_flush_blue_empty mh first_blue fp;
    same_chunk_ranges_refl mh
  end
  else if U64.v first_blue < U64.v mword ||
          U64.v first_blue >= heap_size ||
          U64.v first_blue % U64.v mword <> 0 then begin
    Defs.chunked_flush_blue_invalid mh first_blue run_words fp;
    same_chunk_ranges_refl mh
  end
  else begin
    let fb : obj_addr = first_blue in
    let hd = hd_address fb in
    let wz : nat = run_words - 1 in
    if wz >= pow2 54 then begin
      Defs.chunked_flush_blue_too_large mh first_blue run_words fp;
      same_chunk_ranges_refl mh
    end
    else begin
      FStar.Math.Lemmas.pow2_lt_compat 64 54;
      assert (wz < pow2 64);
      let wz_u64 : GC.Spec.Object.wosize = U64.uint_to_t wz in
      let hdr = GC.Spec.Object.makeHeader wz_u64 GC.Lib.Header.Blue 0UL in
      let mh1 = SpecMajorAlloc.major_write_word_or_same mh hd hdr in
      major_write_word_or_same_preserves_ranges mh hd hdr;
      if wz >= 1 && U64.v hd + U64.v mword * 2 <= heap_size then begin
        let mh2 = SpecMajorAlloc.major_write_word_or_same mh1 fb fp in
        major_write_word_or_same_preserves_ranges mh1 fb fp;
        if wz >= 2 && U64.v fb + U64.v mword < pow2 64 then begin
          let zero_start = U64.uint_to_t (U64.v fb + U64.v mword) in
          let mh3 = Defs.chunked_zero_fields mh2 zero_start (wz - 1) in
          Defs.chunked_flush_blue_fst_zero_step mh fb run_words fp;
          chunked_zero_fields_preserves_ranges mh2 zero_start (wz - 1);
          assert (same_chunk_ranges mh2 mh3);
          same_chunk_ranges_trans mh1 mh2
            mh3;
          same_chunk_ranges_trans mh mh1 mh3;
          assert (fst (Defs.chunked_flush_blue mh fb run_words fp) == mh3)
        end else begin
          Defs.chunked_flush_blue_fst_link_step mh fb run_words fp;
          same_chunk_ranges_trans mh mh1 mh2;
          assert (fst (Defs.chunked_flush_blue mh fb run_words fp) == mh2)
        end
      end else begin
        Defs.chunked_flush_blue_fst_header_step mh fb run_words fp;
        assert (fst (Defs.chunked_flush_blue mh fb run_words fp) == mh1)
      end
    end
  end
#pop-options

#push-options "--z3rlimit 5 --fuel 1 --ifuel 0 --split_queries always"
let rec chunked_fused_aux_preserves_ranges
    (source work: MH.major_heap)
    (objs: Seq.seq obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
  : Lemma
      (ensures
        same_chunk_ranges work
          (fst (Defs.chunked_fused_aux
            source work objs first_blue run_words fp)))
      (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then begin
    Defs.chunked_fused_aux_empty_length
      source work objs first_blue run_words fp;
    chunked_flush_blue_preserves_ranges work first_blue run_words fp;
    assert (
      fst (Defs.chunked_fused_aux source work objs first_blue run_words fp) ==
      fst (Defs.chunked_flush_blue work first_blue run_words fp))
  end
  else begin
    let obj = Seq.head objs in
    let rest = Seq.tail objs in
    if Defs.chunked_is_black source obj then begin
      let flushed = Defs.chunked_flush_blue work first_blue run_words fp in
      let work' = fst flushed in
      let fp' = snd flushed in
      let work'' = Defs.chunked_make_white work' obj in
      Defs.chunked_fused_aux_black_step
        source work objs first_blue run_words fp;
      chunked_flush_blue_preserves_ranges work first_blue run_words fp;
      chunked_make_white_preserves_ranges work' obj;
      chunked_fused_aux_preserves_ranges source work'' rest 0UL 0 fp';
      same_chunk_ranges_trans work' work'' 
        (fst (Defs.chunked_fused_aux source work'' rest 0UL 0 fp'));
      same_chunk_ranges_trans work work'
        (fst (Defs.chunked_fused_aux source work'' rest 0UL 0 fp'));
      assert (
        fst (Defs.chunked_fused_aux source work objs first_blue run_words fp) ==
        fst (Defs.chunked_fused_aux source work'' rest 0UL 0 fp'))
    end else begin
      Defs.chunked_fused_aux_nonblack_step
        source work objs first_blue run_words fp;
      let ws = U64.v (Defs.chunked_wosize_of_object source obj) in
      let new_first : U64.t = if run_words = 0 then obj else first_blue in
      chunked_fused_aux_preserves_ranges
        source work rest new_first (run_words + ws + 1) fp;
      assert (
        fst (Defs.chunked_fused_aux source work objs first_blue run_words fp) ==
        fst (Defs.chunked_fused_aux
          source work rest new_first (run_words + ws + 1) fp))
    end
  end
#pop-options

let chunked_fused_aux_pointer_classification_preserved
    (source work: MH.major_heap)
    (objs: Seq.seq obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
  : Lemma
      (ensures
        ChunkedGraph.chunked_major_pointer_classification_preserved
          work
          (fst (Defs.chunked_fused_aux
            source work objs first_blue run_words fp)))
  =
  let final =
    fst (Defs.chunked_fused_aux source work objs first_blue run_words fp) in
  chunked_fused_aux_preserves_ranges
    source work objs first_blue run_words fp;
  let classify (v: U64.t)
    : Lemma
        (ensures
          MarkDefs.chunked_is_pointer_field work v ==
          MarkDefs.chunked_is_pointer_field final v)
    =
    MarkDefs.chunked_is_pointer_field_step work v;
    MarkDefs.chunked_is_pointer_field_step final v;
    same_chunk_ranges_preserves_is_major_pointer work final v
  in
  FStar.Classical.forall_intro classify;
  ChunkedGraph.chunked_major_pointer_classification_preserved_intro work final

#push-options "--z3rlimit 5 --fuel 1 --ifuel 0 --split_queries always"
let rec chunked_fused_sweep_coalesce_chunks_preserves_ranges
    (source_chunks source work: MH.major_heap)
    (fp: U64.t)
  : Lemma
      (ensures
        same_chunk_ranges work
          (fst (Defs.chunked_fused_sweep_coalesce_chunks
            source_chunks source work fp)))
      (decreases Seq.length source_chunks)
  =
  if Seq.length source_chunks = 0 then begin
    Defs.chunked_fused_sweep_coalesce_chunks_empty_length
      source_chunks source work fp;
    same_chunk_ranges_refl work;
    assert (
      fst (Defs.chunked_fused_sweep_coalesce_chunks
        source_chunks source work fp) == work)
  end else begin
    assert (Seq.length source_chunks > 0);
    let c = Seq.head source_chunks in
    let rest = Seq.tail source_chunks in
    assert (Seq.length rest < Seq.length source_chunks);
    let one =
      Defs.chunked_fused_aux source work (MH.objects_in_chunk c) 0UL 0 fp in
    let work' = fst one in
    let fp' = snd one in
    Defs.chunked_fused_sweep_coalesce_chunks_step
      source_chunks source work fp;
    chunked_fused_aux_preserves_ranges
      source work (MH.objects_in_chunk c) 0UL 0 fp;
    chunked_fused_sweep_coalesce_chunks_preserves_ranges
      rest source work' fp';
    same_chunk_ranges_trans work work'
      (fst (Defs.chunked_fused_sweep_coalesce_chunks
        rest source work' fp'));
    assert (
      fst (Defs.chunked_fused_sweep_coalesce_chunks
        source_chunks source work fp) ==
      fst (Defs.chunked_fused_sweep_coalesce_chunks
        rest source work' fp'))
  end
#pop-options

let chunked_fused_sweep_coalesce_preserves_ranges
    (mh: MH.major_heap)
  : Lemma
      (ensures
        same_chunk_ranges mh
          (fst (Defs.chunked_fused_sweep_coalesce mh)))
  =
  Defs.chunked_fused_sweep_coalesce_step mh;
  chunked_fused_sweep_coalesce_chunks_preserves_ranges mh mh mh 0UL

let chunked_fused_sweep_coalesce_chunks_pointer_classification_preserved
    (source_chunks source work: MH.major_heap)
    (fp: U64.t)
  : Lemma
      (ensures
        ChunkedGraph.chunked_major_pointer_classification_preserved
          work
          (fst (Defs.chunked_fused_sweep_coalesce_chunks
            source_chunks source work fp)))
  =
  let final =
    fst (Defs.chunked_fused_sweep_coalesce_chunks source_chunks source work fp) in
  chunked_fused_sweep_coalesce_chunks_preserves_ranges
    source_chunks source work fp;
  let classify (v: U64.t)
    : Lemma
        (ensures
          MarkDefs.chunked_is_pointer_field work v ==
          MarkDefs.chunked_is_pointer_field final v)
    =
    MarkDefs.chunked_is_pointer_field_step work v;
    MarkDefs.chunked_is_pointer_field_step final v;
    same_chunk_ranges_preserves_is_major_pointer work final v
  in
  FStar.Classical.forall_intro classify;
  ChunkedGraph.chunked_major_pointer_classification_preserved_intro work final

let chunked_fused_sweep_coalesce_pointer_classification_preserved
    (mh: MH.major_heap)
  : Lemma
      (ensures
        ChunkedGraph.chunked_major_pointer_classification_preserved
          mh
          (fst (Defs.chunked_fused_sweep_coalesce mh)))
  =
  Defs.chunked_fused_sweep_coalesce_step mh;
  chunked_fused_sweep_coalesce_chunks_pointer_classification_preserved
    mh mh mh 0UL
