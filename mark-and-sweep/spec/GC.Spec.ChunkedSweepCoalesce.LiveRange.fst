module GC.Spec.ChunkedSweepCoalesce.LiveRange

module U64 = FStar.UInt64
module Seq = FStar.Seq
module SeqProps = FStar.Seq.Properties

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module Obj = GC.Spec.Object
module Defs = GC.Spec.ChunkedSweepCoalesce.Defs
module MarkDefs = GC.Spec.ChunkedMark.Defs
module Pres = GC.Spec.ChunkedSweepCoalesce.Preservation
module SeqPres = GC.Spec.ChunkedSweepCoalesce.SequencePreservation
module VertexRange = GC.Spec.ChunkedSweepCoalesce.VertexRange
module LivePres = GC.Spec.ChunkedSweepCoalesce.LivePreservation
module RangePres = GC.Spec.ChunkedSweepCoalesce.RangePreservation
module ChunkedGraph = GC.Spec.ChunkedMajorGC.Graph

#set-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always --warn_error -321"

let u64_ext (x y: U64.t)
  : Lemma (requires U64.v x == U64.v y) (ensures x == y)
  = ()

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let payload_field_address_facts
    (c: MH.heap_chunk)
    (target: obj_addr)
    (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        MH.object_header_size_fits_in_chunk c target /\
        U64.v i <= MH.object_wosize_in_chunk c target)
      (ensures
        (let field_u = U64.add (hd_address target) (U64.mul mword i) in
         U64.v (hd_address target) + U64.v mword * U64.v i +
           U64.v mword <= heap_size /\
         U64.v field_u ==
           U64.v (hd_address target) + U64.v mword * U64.v i /\
         U64.v field_u < heap_size /\
         U64.v field_u % U64.v mword == 0 /\
         U64.v target <= U64.v field_u /\
         U64.v field_u + U64.v mword <=
           U64.v target +
           MH.object_wosize_in_chunk c target * U64.v mword))
  =
  let w = MH.object_wosize_in_chunk c target in
  hd_address_spec target;
  assert (U64.v (hd_address target) + U64.v mword == U64.v target);
  FStar.Math.Lemmas.lemma_mult_le_right (U64.v mword) (U64.v i) w;
  assert (U64.v mword * U64.v i <= U64.v mword * w);
  assert (U64.v (hd_address target) +
          U64.v mword * U64.v i + U64.v mword <=
          U64.v target + w * U64.v mword);
  assert (U64.v (hd_address target) +
          (1 + w) * U64.v mword <= MH.chunk_end c);
  FStar.Math.Lemmas.distributivity_add_left 1 w (U64.v mword);
  assert (1 * U64.v mword == U64.v mword);
  assert ((1 + w) * U64.v mword ==
          U64.v mword + w * U64.v mword);
  assert (U64.v target + w * U64.v mword <= MH.chunk_end c);
  assert (MH.chunk_end c <= heap_size);
  assert (U64.v (hd_address target) +
          U64.v mword * U64.v i + U64.v mword <= heap_size);
  let field_u = U64.add (hd_address target) (U64.mul mword i) in
  assert (U64.v field_u ==
          U64.v (hd_address target) + U64.v mword * U64.v i);
  assert (U64.v field_u < heap_size);
  assert (U64.v mword * U64.v i == U64.v i * U64.v mword);
  assert (U64.v (hd_address target) % U64.v mword == 0);
  FStar.Math.Lemmas.lemma_mod_plus
    (U64.v (hd_address target)) (U64.v i) (U64.v mword);
  assert ((U64.v (hd_address target) +
           U64.v i * U64.v mword) % U64.v mword == 0);
  assert ((U64.v (hd_address target) +
           U64.v mword * U64.v i) % U64.v mword == 0);
  assert (U64.v field_u % U64.v mword == 0);
  assert (U64.v target <= U64.v field_u);
  assert (U64.v field_u + U64.v mword ==
          U64.v (hd_address target) +
          U64.v mword * U64.v i + U64.v mword);
  assert (U64.v field_u + U64.v mword <=
          U64.v target + w * U64.v mword)
#pop-options

let target_suffix_wosize
    (source: MH.major_heap)
    (idx: nat)
    (o: obj_addr)
  : Lemma
      (requires
        idx < Seq.length source /\
        Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) /\
        (forall (j: nat). idx <= j /\ j < Seq.length source ==>
          forall (x: obj_addr).
          Seq.mem x (MH.objects_in_chunk (Seq.index source j)) ==>
          U64.v (Defs.chunked_wosize_of_object source x) ==
          MH.object_wosize_in_chunk (Seq.index source j) x))
      (ensures
        U64.v (Defs.chunked_wosize_of_object source o) ==
        MH.object_wosize_in_chunk (Seq.index source idx) o)
  =
  assert (idx <= idx);
  assert (idx < Seq.length source)

let target_chunk_wosize_all
    (source: MH.major_heap)
    (idx: nat)
  : Lemma
      (requires
        idx < Seq.length source /\
        (forall (j: nat). idx <= j /\ j < Seq.length source ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source j)) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source j) o))
      (ensures
        forall (o: obj_addr).
        Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
        U64.v (Defs.chunked_wosize_of_object source o) ==
        MH.object_wosize_in_chunk (Seq.index source idx) o)
  =
  let f (o: obj_addr)
    : Lemma
        (requires Seq.mem o (MH.objects_in_chunk (Seq.index source idx)))
        (ensures
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o)
    =
    target_suffix_wosize source idx o
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires f)

let suffix_wosize_all
    (source: MH.major_heap)
    (idx: nat)
  : Lemma
      (requires
        idx < Seq.length source /\
        (forall (j: nat). idx <= j /\ j < Seq.length source ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source j)) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source j) o))
      (ensures
        forall (j: nat). idx < j /\ j < Seq.length source ==>
        forall (o: obj_addr).
        Seq.mem o (MH.objects_in_chunk (Seq.index source j)) ==>
        U64.v (Defs.chunked_wosize_of_object source o) ==
        MH.object_wosize_in_chunk (Seq.index source j) o)
  =
  let f (j: nat{idx < j /\ j < Seq.length source})
    : Lemma
        (ensures
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source j)) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source j) o)
    =
    assert (idx <= j);
    assert (j < Seq.length source)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires f)

let prefix_wosize_all
    (source: MH.major_heap)
    (idx: nat)
  : Lemma
      (requires
        idx < Seq.length source /\
        (forall (j: nat). j < idx ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source j)) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source j) o))
      (ensures
        forall (j: nat). j < idx ==>
        forall (o: obj_addr).
        Seq.mem o (MH.objects_in_chunk (Seq.index source j)) ==>
        U64.v (Defs.chunked_wosize_of_object source o) ==
        MH.object_wosize_in_chunk (Seq.index source j) o)
  =
  let f (j: nat{j < idx})
    : Lemma
        (ensures
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source j)) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source j) o)
    =
    assert (j < idx)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires f)

#push-options "--z3rlimit 5 --fuel 1 --ifuel 0 --split_queries always"
let rec chunked_fused_sweep_coalesce_chunks_split_range
    (source work: MH.major_heap)
    (start mid stop: nat)
    (fp: U64.t)
  : Lemma
      (requires start <= mid /\ mid <= stop /\ stop <= Seq.length source)
      (ensures
        (let prefix =
           Defs.chunked_fused_sweep_coalesce_chunks
             (Seq.slice source start mid) source work fp in
         Defs.chunked_fused_sweep_coalesce_chunks
           (Seq.slice source start stop) source work fp ==
         Defs.chunked_fused_sweep_coalesce_chunks
           (Seq.slice source mid stop) source (fst prefix) (snd prefix)))
      (decreases mid - start)
  =
  Seq.lemma_len_slice source start mid;
  Seq.lemma_len_slice source start stop;
  if start = mid then begin
    assert (Seq.length (Seq.slice source start mid) == 0);
    Defs.chunked_fused_sweep_coalesce_chunks_empty_length
      (Seq.slice source start mid) source work fp;
    assert (Defs.chunked_fused_sweep_coalesce_chunks
              (Seq.slice source start mid) source work fp == (work, fp));
    assert (Seq.slice source start stop == Seq.slice source mid stop)
  end else begin
    assert (start < mid);
    assert (start < stop);
    assert (Seq.length (Seq.slice source start mid) > 0);
    assert (Seq.length (Seq.slice source start stop) > 0);
    Seq.lemma_index_slice source start mid 0;
    Seq.lemma_index_slice source start stop 0;
    assert (Seq.head (Seq.slice source start mid) ==
            Seq.index source start);
    assert (Seq.head (Seq.slice source start stop) ==
            Seq.index source start);
    SeqProps.lemma_tail_slice source start mid;
    SeqProps.lemma_tail_slice source start stop;
    assert (Seq.tail (Seq.slice source start mid) ==
            Seq.slice source (start + 1) mid);
    assert (Seq.tail (Seq.slice source start stop) ==
            Seq.slice source (start + 1) stop);
    Defs.chunked_fused_sweep_coalesce_chunks_step
      (Seq.slice source start mid) source work fp;
    Defs.chunked_fused_sweep_coalesce_chunks_step
      (Seq.slice source start stop) source work fp;
    let one =
      Defs.chunked_fused_aux
        source work (MH.objects_in_chunk (Seq.index source start)) 0UL 0 fp in
    let work' = fst one in
    let fp' = snd one in
    chunked_fused_sweep_coalesce_chunks_split_range
      source work' (start + 1) mid stop fp';
    let prefix_tail =
      Defs.chunked_fused_sweep_coalesce_chunks
        (Seq.slice source (start + 1) mid) source work' fp' in
    assert (
      Defs.chunked_fused_sweep_coalesce_chunks
        (Seq.slice source start mid) source work fp ==
      prefix_tail);
    assert (
      Defs.chunked_fused_sweep_coalesce_chunks
        (Seq.slice source start stop) source work fp ==
      Defs.chunked_fused_sweep_coalesce_chunks
        (Seq.slice source (start + 1) stop) source work' fp');
    assert (
      Defs.chunked_fused_sweep_coalesce_chunks
        (Seq.slice source (start + 1) stop) source work' fp' ==
      Defs.chunked_fused_sweep_coalesce_chunks
        (Seq.slice source mid stop) source (fst prefix_tail) (snd prefix_tail))
  end
#pop-options

let slice_all_eq (s: Seq.seq MH.heap_chunk)
  : Lemma (Seq.slice s 0 (Seq.length s) == s)
  =
  Seq.lemma_len_slice s 0 (Seq.length s);
  Seq.lemma_eq_intro (Seq.slice s 0 (Seq.length s)) s

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_fused_sweep_coalesce_prefix_preserves_chunk_wosizes
    (source: MH.major_heap)
    (idx: nat)
    (fp: U64.t)
    (protected: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        idx < Seq.length source /\
        Seq.mem protected (MH.objects_in_chunk (Seq.index source idx)) /\
        (forall (j: nat). j < idx ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source j)) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source j) o))
      (ensures
        (let c = Seq.index source idx in
         let work =
           fst (Defs.chunked_fused_sweep_coalesce_chunks
             (Seq.slice source 0 idx) source source fp) in
         idx < Seq.length work /\
         forall (o: obj_addr). Seq.mem o (MH.objects_in_chunk c) ==>
           MH.object_wosize_in_chunk (Seq.index work idx) o ==
           MH.object_wosize_in_chunk c o))
  =
  let c = Seq.index source idx in
  let work =
    fst (Defs.chunked_fused_sweep_coalesce_chunks
      (Seq.slice source 0 idx) source source fp) in
  RangePres.same_chunk_ranges_refl source;
  assert (MH.objects_in_chunk c == MH.objects_in_chunk_from c c.base);
  VertexRange.chunked_fused_sweep_coalesce_prefix_preserves_objects_from
    source source idx c.base protected fp;
  assert (idx < Seq.length work);
  let wos (o: obj_addr)
    : Lemma
        (requires Seq.mem o (MH.objects_in_chunk c))
        (ensures
          MH.object_wosize_in_chunk (Seq.index work idx) o ==
          MH.object_wosize_in_chunk c o)
    =
    assert (Seq.mem o (MH.objects_in_chunk_from c c.base));
    VertexRange.chunked_fused_sweep_coalesce_prefix_preserves_objects_from
      source source idx c.base o fp
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires wos)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_fused_sweep_coalesce_prefix_live_field_data_preserved
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
        (forall (j: nat). j < idx ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source j)) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source j) o) /\
        Defs.chunked_read_header source target == Some hdr /\
        U64.v (Obj.getWosize hdr) ==
          MH.object_wosize_in_chunk (Seq.index source idx) target)
      (ensures
        (let work =
           fst (Defs.chunked_fused_sweep_coalesce_chunks
             (Seq.slice source 0 idx) source source fp) in
         Defs.chunked_read_header work target == Some hdr /\
         Defs.chunked_wosize_of_object work target == Obj.getWosize hdr /\
         ChunkedGraph.chunked_major_field_data_preserved
           source work target))
  =
  let c = Seq.index source idx in
  let work =
    fst (Defs.chunked_fused_sweep_coalesce_chunks
      (Seq.slice source 0 idx) source source fp) in
  RangePres.same_chunk_ranges_refl source;
  prefix_wosize_all source idx;
  assert (MH.objects_in_chunk c == MH.objects_in_chunk_from c c.base);
  assert (Seq.mem target (MH.objects_in_chunk_from c c.base));
  VertexRange.chunked_fused_sweep_coalesce_prefix_preserves_objects_from
    source source idx c.base target fp;
  assert (MH.well_formed_major_heap work);
  assert (idx < Seq.length work);
  u64_ext (Seq.index work idx).base c.base;
  assert ((Seq.index work idx).base == c.base);
  assert (MH.objects_in_chunk (Seq.index work idx) ==
          MH.objects_in_chunk_from (Seq.index work idx) c.base);
  assert (Seq.mem target (MH.objects_in_chunk (Seq.index work idx)));
  ChunkedGraph.chunked_major_vertex_from_chunk work idx target;
  MH.major_objects_member_at_index source idx target;
  ChunkedGraph.chunked_major_vertex_from_chunk source idx target;

  MH.objects_in_chunk_member_header_fits c target;
  assert (MH.object_header_size_fits_in_chunk c target);
  assert (MH.word_in_chunk c (hd_address target));
  Defs.chunked_read_header_step source target;
  assert (MH.read_word_in_major source (hd_address target) == Some hdr);
  SeqPres.chunked_fused_sweep_coalesce_prefix_preserves_read
    source source idx fp (hd_address target) hdr;
  assert (MH.read_word_in_major work (hd_address target) == Some hdr);
  Defs.chunked_read_header_step work target;
  assert (Defs.chunked_read_header work target == Some hdr);
  Defs.chunked_wosize_of_object_some source target hdr;
  Defs.chunked_wosize_of_object_some work target hdr;

  let field_data (i: U64.t)
    : Lemma
        (ensures
          U64.v i >= 1 /\
          U64.v i <= U64.v (Defs.chunked_wosize_of_object source target) ==>
          MarkDefs.chunked_get_field source target i ==
          MarkDefs.chunked_get_field work target i)
    =
    if U64.v i >= 1 &&
       U64.v i <= U64.v (Defs.chunked_wosize_of_object source target) then begin
      let ii : i':U64.t{U64.v i' >= 1} = i in
      assert (U64.v ii <= U64.v (Obj.getWosize hdr));
      hd_address_spec target;
      assert (U64.v (hd_address target) + U64.v mword == U64.v target);
      FStar.Math.Lemmas.lemma_mult_le_right
        (U64.v mword) (U64.v ii)
        (MH.object_wosize_in_chunk c target);
      assert (U64.v mword * U64.v ii <=
              U64.v mword * MH.object_wosize_in_chunk c target);
      assert (U64.v (hd_address target) +
              U64.v mword * U64.v ii + U64.v mword <=
              U64.v target +
              MH.object_wosize_in_chunk c target * U64.v mword);
      assert (U64.v (hd_address target) +
              (1 + MH.object_wosize_in_chunk c target) *
                U64.v mword <=
              MH.chunk_end c);
      assert (U64.v target == U64.v (hd_address target) + U64.v mword);
      FStar.Math.Lemmas.distributivity_add_left
        1 (MH.object_wosize_in_chunk c target) (U64.v mword);
      assert (1 * U64.v mword == U64.v mword);
      assert ((1 + MH.object_wosize_in_chunk c target) *
                U64.v mword ==
              U64.v mword +
              MH.object_wosize_in_chunk c target * U64.v mword);
      assert (U64.v (hd_address target) +
              U64.v mword +
              MH.object_wosize_in_chunk c target * U64.v mword ==
              U64.v (hd_address target) +
              (U64.v mword +
               MH.object_wosize_in_chunk c target * U64.v mword));
      assert (U64.v (hd_address target) +
              U64.v mword +
              MH.object_wosize_in_chunk c target * U64.v mword ==
              U64.v (hd_address target) +
              (1 + MH.object_wosize_in_chunk c target) *
                U64.v mword);
      assert (U64.v target +
              MH.object_wosize_in_chunk c target * U64.v mword ==
              U64.v (hd_address target) +
              (1 + MH.object_wosize_in_chunk c target) *
                U64.v mword);
      assert (U64.v target +
              MH.object_wosize_in_chunk c target * U64.v mword <=
              MH.chunk_end c);
      assert (MH.chunk_end c <= heap_size);
      assert (U64.v (hd_address target) +
              U64.v mword * U64.v ii < heap_size);
      let field_u = U64.add (hd_address target) (U64.mul mword ii) in
      assert (U64.v field_u ==
              U64.v (hd_address target) + U64.v mword * U64.v ii);
      assert (U64.v field_u < heap_size);
      assert (U64.v mword * U64.v ii == U64.v ii * U64.v mword);
      assert (U64.v (hd_address target) % U64.v mword == 0);
      FStar.Math.Lemmas.lemma_mod_plus
        (U64.v (hd_address target)) (U64.v ii) (U64.v mword);
      assert ((U64.v (hd_address target) +
               U64.v ii * U64.v mword) % U64.v mword == 0);
      assert ((U64.v (hd_address target) +
               U64.v mword * U64.v ii) % U64.v mword == 0);
      assert (U64.v field_u % U64.v mword == 0);
      let field_addr : hp_addr = field_u in
      assert (U64.v target <= U64.v field_addr);
      assert (U64.v field_addr + U64.v mword ==
              U64.v (hd_address target) +
              U64.v mword * U64.v ii + U64.v mword);
      assert (U64.v field_addr + U64.v mword <=
              U64.v target +
              MH.object_wosize_in_chunk c target * U64.v mword);
      MH.lookup_chunk_index_word_in_chunk source (hd_address target) idx;
      MH.major_object_payload_word_in_lookup_chunk
        source idx target field_addr;
      let old = MH.read_word_in_chunk c field_addr in
      MH.read_word_in_major_at_lookup_index source field_addr idx;
      assert (MH.read_word_in_major source field_addr == Some old);
      SeqPres.chunked_fused_sweep_coalesce_prefix_preserves_read
        source source idx fp field_addr old;
      assert (MH.read_word_in_major work field_addr == Some old);
      MarkDefs.chunked_get_field_read_some source target ii old;
      MarkDefs.chunked_get_field_read_some work target ii old;
      assert (MarkDefs.chunked_get_field source target i ==
              MarkDefs.chunked_get_field work target i)
    end
  in
  FStar.Classical.forall_intro field_data;
  ChunkedGraph.chunked_major_field_data_preserved_intro source work target
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_fused_sweep_coalesce_target_suffix_live_field_preserved_work
  (source work: MH.major_heap)
  (idx: nat)
  (fp: U64.t)
  (target: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        MH.well_formed_major_heap work /\
        RangePres.same_chunk_ranges source work /\
        idx < Seq.length source /\
        idx < Seq.length work /\
        (let c = Seq.index source idx in
         MH.chunk_start (Seq.index work idx) == MH.chunk_start c /\
         MH.chunk_end (Seq.index work idx) == MH.chunk_end c /\
         Seq.mem target (MH.objects_in_chunk c) /\
         MH.objects_in_chunk_from (Seq.index work idx) c.base ==
           MH.objects_in_chunk c /\
         (forall (o: obj_addr). Seq.mem o (MH.objects_in_chunk c) ==>
           MH.object_wosize_in_chunk (Seq.index work idx) o ==
           MH.object_wosize_in_chunk c o) /\
         (forall (j: nat). idx <= j /\ j < Seq.length source ==>
           forall (o: obj_addr).
           Seq.mem o (MH.objects_in_chunk (Seq.index source j)) ==>
           U64.v (Defs.chunked_wosize_of_object source o) ==
           MH.object_wosize_in_chunk (Seq.index source j) o) /\
         Defs.chunked_read_header source target == Some hdr /\
         Defs.chunked_read_header work target == Some hdr /\
         Defs.chunked_is_black source target /\
         U64.v (Obj.getWosize hdr) ==
           MH.object_wosize_in_chunk c target /\
         ChunkedGraph.chunked_major_field_data_preserved
           source work target))
      (ensures
        (let c = Seq.index source idx in
         let step =
           Defs.chunked_fused_aux
             source work (MH.objects_in_chunk c) 0UL 0 fp in
         let work' = fst step in
         let fp' = snd step in
         let final =
           fst (Defs.chunked_fused_sweep_coalesce_chunks
             (Seq.slice source (idx + 1) (Seq.length source))
             source work' fp') in
         ChunkedGraph.chunked_major_field_preserved source final target /\
         MarkDefs.chunked_is_no_scan source target ==
         MarkDefs.chunked_is_no_scan final target))
  =
  let c = Seq.index source idx in
  let step =
    Defs.chunked_fused_aux source work (MH.objects_in_chunk c) 0UL 0 fp in
  let work' = fst step in
  let fp' = snd step in
  let final =
    fst (Defs.chunked_fused_sweep_coalesce_chunks
      (Seq.slice source (idx + 1) (Seq.length source)) source work' fp') in

  target_chunk_wosize_all source idx;
  assert (forall (o: obj_addr).
    Seq.mem o (MH.objects_in_chunk c) ==>
    U64.v (Defs.chunked_wosize_of_object source o) ==
    MH.object_wosize_in_chunk c o);
  LivePres.chunked_fused_aux_live_vertex_preserved_from_chunk_work
    source work idx fp target hdr;
  LivePres.chunked_fused_aux_live_wosize_preserved_from_chunk_work
    source work idx fp target hdr;
  LivePres.chunked_fused_aux_live_no_scan_preserved_from_chunk_work
    source work idx fp target hdr;
  RangePres.chunked_fused_aux_preserves_ranges
    source work (MH.objects_in_chunk c) 0UL 0 fp;
  assert (RangePres.same_chunk_ranges work work');
  RangePres.same_chunk_ranges_trans source work work';
  assert (RangePres.same_chunk_ranges source work');
  RangePres.same_chunk_ranges_index source work idx;
  RangePres.same_chunk_ranges_index work work' idx;
  u64_ext (Seq.index work idx).base c.base;
  assert ((Seq.index work idx).base == c.base);
  u64_ext (Seq.index work' idx).base (Seq.index work idx).base;
  assert ((Seq.index work' idx).base == c.base);
  assert (MH.objects_in_chunk (Seq.index work idx) ==
          MH.objects_in_chunk_from (Seq.index work idx) c.base);
  assert (Seq.mem target (MH.objects_in_chunk (Seq.index work idx)));
  ChunkedGraph.chunked_major_vertex_from_chunk work idx target;
  assert (MH.objects_in_chunk (Seq.index work' idx) ==
          MH.objects_in_chunk_from (Seq.index work' idx) c.base);
  assert (Seq.mem target (MH.objects_in_chunk (Seq.index work' idx)));
  ChunkedGraph.chunked_major_vertex_from_chunk work' idx target;

  suffix_wosize_all source idx;
  VertexRange.chunked_fused_sweep_coalesce_suffix_preserves_objects_from
    source work' idx (Seq.index work' idx).base target fp';
  assert (MH.well_formed_major_heap final);
  assert (idx < Seq.length final);
  RangePres.chunked_fused_sweep_coalesce_chunks_preserves_ranges
    (Seq.slice source (idx + 1) (Seq.length source)) source work' fp';
  RangePres.same_chunk_ranges_trans source work' final;
  assert (RangePres.same_chunk_ranges source final);
  RangePres.same_chunk_ranges_index work' final idx;
  u64_ext (Seq.index final idx).base (Seq.index work' idx).base;
  assert ((Seq.index final idx).base == (Seq.index work' idx).base);
  assert (MH.objects_in_chunk (Seq.index final idx) ==
          MH.objects_in_chunk_from
            (Seq.index final idx) (Seq.index work' idx).base);
  assert (Seq.mem target (MH.objects_in_chunk (Seq.index final idx)));
  ChunkedGraph.chunked_major_vertex_from_chunk final idx target;

  Defs.chunked_wosize_of_object_some source target hdr;
  MH.objects_in_chunk_member_header_fits c target;
  assert (MH.object_header_size_fits_in_chunk c target);
  assert (MH.word_in_chunk c (hd_address target));
  RangePres.same_chunk_ranges_word_in_chunk source work idx (hd_address target);
  RangePres.same_chunk_ranges_word_in_chunk work work' idx (hd_address target);
  MH.lookup_chunk_index_word_in_chunk work' (hd_address target) idx;
  let work_hdr = MH.read_word_in_chunk (Seq.index work' idx) (hd_address target) in
  MH.read_word_in_major_at_lookup_index work' (hd_address target) idx;
  assert (MH.read_word_in_major work' (hd_address target) == Some work_hdr);
  SeqPres.chunked_fused_sweep_coalesce_suffix_preserves_read
    source work' idx fp' (hd_address target) work_hdr;
  assert (MH.read_word_in_major final (hd_address target) == Some work_hdr);
  Defs.chunked_read_header_step work' target;
  Defs.chunked_read_header_step final target;
  assert (Defs.chunked_read_header work' target == Some work_hdr);
  assert (Defs.chunked_read_header final target == Some work_hdr);
  Defs.chunked_tag_of_object_some work' target work_hdr;
  Defs.chunked_tag_of_object_some final target work_hdr;
  MarkDefs.chunked_is_no_scan_step work' target;
  MarkDefs.chunked_is_no_scan_step final target;
  assert (MarkDefs.chunked_is_no_scan work' target ==
          MarkDefs.chunked_is_no_scan final target);
  assert (MarkDefs.chunked_is_no_scan source target ==
          MarkDefs.chunked_is_no_scan work' target);
  Defs.chunked_wosize_of_object_some work' target work_hdr;
  Defs.chunked_wosize_of_object_some final target work_hdr;
  assert (Defs.chunked_wosize_of_object source target == Obj.getWosize hdr);
  assert (Defs.chunked_wosize_of_object work' target == Obj.getWosize work_hdr);
  assert (Defs.chunked_wosize_of_object final target == Obj.getWosize work_hdr);
  assert (Defs.chunked_wosize_of_object work' target == Obj.getWosize hdr);
  assert (Defs.chunked_wosize_of_object source target ==
          Defs.chunked_wosize_of_object final target);

  ChunkedGraph.chunked_major_field_data_preserved_elim source work target;
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
      assert (U64.v ii <= U64.v (Obj.getWosize hdr));
      payload_field_address_facts c target ii;
      let field_u = U64.add (hd_address target) (U64.mul mword ii) in
      let field_addr : hp_addr = field_u in

      MH.major_objects_member_at_index work idx target;
      MH.lookup_chunk_index_word_in_chunk work (hd_address target) idx;
      assert (MH.object_wosize_in_chunk (Seq.index work idx) target ==
              MH.object_wosize_in_chunk c target);
      MH.major_object_payload_word_in_lookup_chunk
        work idx target field_addr;
      let old = MH.read_word_in_chunk (Seq.index work idx) field_addr in
      MH.read_word_in_major_at_lookup_index work field_addr idx;
      assert (MH.read_word_in_major work field_addr == Some old);
      Pres.chunked_fused_aux_live_read_frame_ready_from_chunk
        source c target ii field_addr hdr;
      Pres.chunked_fused_aux_read_frame_ready_from_live_target
        source (MH.objects_in_chunk c) 0UL 0 target field_addr;
      Pres.chunked_fused_aux_preserves_other_read
        source work (MH.objects_in_chunk c) 0UL 0 fp field_addr old;
      assert (MH.read_word_in_major work' field_addr == Some old);
      SeqPres.chunked_fused_sweep_coalesce_suffix_preserves_read
        source work' idx fp' field_addr old;
      assert (MH.read_word_in_major final field_addr == Some old);
      MarkDefs.chunked_get_field_read_some work target ii old;
      MarkDefs.chunked_get_field_read_some work' target ii old;
      MarkDefs.chunked_get_field_read_some final target ii old;
      assert (MarkDefs.chunked_get_field source target ii ==
              MarkDefs.chunked_get_field work target ii);
      assert (MarkDefs.chunked_get_field source target i ==
              MarkDefs.chunked_get_field final target i)
    end
  in
  FStar.Classical.forall_intro field_data;
  ChunkedGraph.chunked_major_field_preserved_intro source final target
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_fused_sweep_coalesce_live_field_preserved
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
        (forall (j: nat). j < Seq.length source ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source j)) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source j) o) /\
        Defs.chunked_read_header source target == Some hdr /\
        Defs.chunked_is_black source target /\
        U64.v (Obj.getWosize hdr) ==
          MH.object_wosize_in_chunk (Seq.index source idx) target)
      (ensures
        (let final =
           fst (Defs.chunked_fused_sweep_coalesce_chunks
             source source source fp) in
        ChunkedGraph.chunked_major_field_preserved source final target /\
        MarkDefs.chunked_is_no_scan source target ==
        MarkDefs.chunked_is_no_scan final target))
  =
  let c = Seq.index source idx in
  let prefix =
    Defs.chunked_fused_sweep_coalesce_chunks
      (Seq.slice source 0 idx) source source fp in
  let work = fst prefix in
  let fp0 = snd prefix in
  let step =
    Defs.chunked_fused_aux source work (MH.objects_in_chunk c) 0UL 0 fp0 in
  let work' = fst step in
  let fp' = snd step in
  let composed_final =
    fst (Defs.chunked_fused_sweep_coalesce_chunks
      (Seq.slice source (idx + 1) (Seq.length source))
      source work' fp') in
  let full_final =
    fst (Defs.chunked_fused_sweep_coalesce_chunks source source source fp) in

  let prefix_wos (j: nat{j < idx})
    : Lemma
        (ensures
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source j)) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source j) o)
    =
    assert (j < Seq.length source)
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires prefix_wos);
  let suffix_wos (j: nat{idx <= j /\ j < Seq.length source})
    : Lemma
        (ensures
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source j)) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source j) o)
    =
    assert (j < Seq.length source)
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires suffix_wos);

  chunked_fused_sweep_coalesce_prefix_live_field_data_preserved
    source idx fp target hdr;
  RangePres.same_chunk_ranges_refl source;
  RangePres.chunked_fused_sweep_coalesce_chunks_preserves_ranges
    (Seq.slice source 0 idx) source source fp;
  assert (RangePres.same_chunk_ranges source work);
  RangePres.same_chunk_ranges_index source work idx;
  assert (idx < Seq.length work);
  u64_ext (Seq.index work idx).base c.base;
  assert ((Seq.index work idx).base == c.base);
  assert (MH.objects_in_chunk c == MH.objects_in_chunk_from c c.base);
  VertexRange.chunked_fused_sweep_coalesce_prefix_preserves_objects_from
    source source idx c.base target fp;
  assert (MH.objects_in_chunk_from (Seq.index work idx) c.base ==
          MH.objects_in_chunk c);
  chunked_fused_sweep_coalesce_prefix_preserves_chunk_wosizes
    source idx fp target;
  assert (forall (o: obj_addr). Seq.mem o (MH.objects_in_chunk c) ==>
    MH.object_wosize_in_chunk (Seq.index work idx) o ==
    MH.object_wosize_in_chunk c o);
  assert (Defs.chunked_read_header work target == Some hdr);
  assert (ChunkedGraph.chunked_major_field_data_preserved source work target);

  chunked_fused_sweep_coalesce_target_suffix_live_field_preserved_work
    source work idx fp0 target hdr;
  assert (MarkDefs.chunked_is_no_scan source target ==
          MarkDefs.chunked_is_no_scan composed_final target);

  chunked_fused_sweep_coalesce_chunks_split_range
    source source 0 idx (Seq.length source) fp;
  assert (
    Defs.chunked_fused_sweep_coalesce_chunks
      (Seq.slice source 0 (Seq.length source)) source source fp ==
    Defs.chunked_fused_sweep_coalesce_chunks
      (Seq.slice source idx (Seq.length source)) source work fp0);
  Seq.lemma_len_slice source idx (Seq.length source);
  assert (Seq.length (Seq.slice source idx (Seq.length source)) > 0);
  Seq.lemma_index_slice source idx (Seq.length source) 0;
  assert (Seq.head (Seq.slice source idx (Seq.length source)) == c);
  SeqProps.lemma_tail_slice source idx (Seq.length source);
  assert (Seq.tail (Seq.slice source idx (Seq.length source)) ==
          Seq.slice source (idx + 1) (Seq.length source));
  Defs.chunked_fused_sweep_coalesce_chunks_step
    (Seq.slice source idx (Seq.length source)) source work fp0;
  assert (
    Defs.chunked_fused_sweep_coalesce_chunks
      (Seq.slice source idx (Seq.length source)) source work fp0 ==
    Defs.chunked_fused_sweep_coalesce_chunks
      (Seq.slice source (idx + 1) (Seq.length source)) source work' fp');
  slice_all_eq source;
  assert (
    Defs.chunked_fused_sweep_coalesce_chunks source source source fp ==
    Defs.chunked_fused_sweep_coalesce_chunks
      (Seq.slice source 0 (Seq.length source)) source source fp);
  assert (full_final == composed_final)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_fused_sweep_coalesce_live_subgraph_preserved
  (source: MH.major_heap)
  (fp: U64.t)
  (live: obj_addr -> prop)
  (live_idx: obj_addr -> nat)
  (live_hdr: obj_addr -> U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        (forall (j: nat). j < Seq.length source ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source j)) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source j) o) /\
        (forall (target: obj_addr).
          live target ==>
          live_idx target < Seq.length source /\
          Seq.mem target
            (MH.objects_in_chunk (Seq.index source (live_idx target))) /\
          Defs.chunked_read_header source target == Some (live_hdr target) /\
          Defs.chunked_is_black source target /\
          U64.v (Obj.getWosize (live_hdr target)) ==
            MH.object_wosize_in_chunk
              (Seq.index source (live_idx target)) target))
      (ensures
        (let final =
           fst (Defs.chunked_fused_sweep_coalesce_chunks
             source source source fp) in
         ChunkedGraph.chunked_major_live_subgraph_preserved
           source final live))
  =
  let final =
    fst (Defs.chunked_fused_sweep_coalesce_chunks source source source fp) in
  let fields (target: obj_addr)
    : Lemma
        (requires live target)
        (ensures ChunkedGraph.chunked_major_field_preserved source final target)
    =
    chunked_fused_sweep_coalesce_live_field_preserved
      source (live_idx target) fp target (live_hdr target)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires fields);
  let no_scan (target: obj_addr)
    : Lemma
        (requires live target)
        (ensures
          MarkDefs.chunked_is_no_scan source target ==
          MarkDefs.chunked_is_no_scan final target)
    =
    chunked_fused_sweep_coalesce_live_field_preserved
      source (live_idx target) fp target (live_hdr target)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires no_scan);
  RangePres.chunked_fused_sweep_coalesce_chunks_pointer_classification_preserved
    source source source fp;
  ChunkedGraph.chunked_major_live_subgraph_preserved_from_fields
    source final live
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_fused_sweep_coalesce_live_subgraph_preserved_from_black_membership
  (source: MH.major_heap)
  (fp: U64.t)
  (live: obj_addr -> prop)
  (live_idx: obj_addr -> nat)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        (forall (j: nat). j < Seq.length source ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source j)) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source j) o) /\
        (forall (target: obj_addr).
          live target ==>
          live_idx target < Seq.length source /\
          Seq.mem target
            (MH.objects_in_chunk (Seq.index source (live_idx target))) /\
          Defs.chunked_is_black source target))
      (ensures
        (let final =
           fst (Defs.chunked_fused_sweep_coalesce_chunks
             source source source fp) in
         ChunkedGraph.chunked_major_live_subgraph_preserved
           source final live))
  =
  let final =
    fst (Defs.chunked_fused_sweep_coalesce_chunks source source source fp) in
  let fields (target: obj_addr)
    : Lemma
        (requires live target)
        (ensures ChunkedGraph.chunked_major_field_preserved source final target)
    =
    assert (live_idx target < Seq.length source);
    assert (Seq.mem target
      (MH.objects_in_chunk (Seq.index source (live_idx target))));
    assert (Defs.chunked_is_black source target);
    Defs.chunked_is_black_read_header source target;
    match Defs.chunked_read_header source target with
    | None -> assert False
    | Some hdr ->
      Defs.chunked_wosize_of_object_some source target hdr;
      assert (U64.v (Defs.chunked_wosize_of_object source target) ==
              MH.object_wosize_in_chunk
                (Seq.index source (live_idx target)) target);
      assert (U64.v (Obj.getWosize hdr) ==
              MH.object_wosize_in_chunk
                (Seq.index source (live_idx target)) target);
      chunked_fused_sweep_coalesce_live_field_preserved
        source (live_idx target) fp target hdr
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires fields);
  let no_scan (target: obj_addr)
    : Lemma
        (requires live target)
        (ensures
          MarkDefs.chunked_is_no_scan source target ==
          MarkDefs.chunked_is_no_scan final target)
    =
    assert (live_idx target < Seq.length source);
    assert (Seq.mem target
      (MH.objects_in_chunk (Seq.index source (live_idx target))));
    assert (Defs.chunked_is_black source target);
    Defs.chunked_is_black_read_header source target;
    match Defs.chunked_read_header source target with
    | None -> assert False
    | Some hdr ->
      Defs.chunked_wosize_of_object_some source target hdr;
      assert (U64.v (Defs.chunked_wosize_of_object source target) ==
              MH.object_wosize_in_chunk
                (Seq.index source (live_idx target)) target);
      assert (U64.v (Obj.getWosize hdr) ==
              MH.object_wosize_in_chunk
                (Seq.index source (live_idx target)) target);
      chunked_fused_sweep_coalesce_live_field_preserved
        source (live_idx target) fp target hdr
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires no_scan);
  RangePres.chunked_fused_sweep_coalesce_chunks_pointer_classification_preserved
    source source source fp;
  ChunkedGraph.chunked_major_live_subgraph_preserved_from_fields
    source final live
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_fused_sweep_coalesce_target_suffix_live_field_preserved
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
        (forall (j: nat). idx <= j /\ j < Seq.length source ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source j)) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source j) o) /\
        Defs.chunked_read_header source target == Some hdr /\
        Defs.chunked_is_black source target /\
        U64.v (Obj.getWosize hdr) ==
          MH.object_wosize_in_chunk (Seq.index source idx) target)
      (ensures
        (let c = Seq.index source idx in
         let step =
           Defs.chunked_fused_aux
             source source (MH.objects_in_chunk c) 0UL 0 fp in
         let work = fst step in
         let fp' = snd step in
         let final =
           fst (Defs.chunked_fused_sweep_coalesce_chunks
             (Seq.slice source (idx + 1) (Seq.length source))
             source work fp') in
         ChunkedGraph.chunked_major_field_preserved source final target))
  =
  let c = Seq.index source idx in
  let step =
    Defs.chunked_fused_aux source source (MH.objects_in_chunk c) 0UL 0 fp in
  let work = fst step in
  let fp' = snd step in
  let final =
    fst (Defs.chunked_fused_sweep_coalesce_chunks
      (Seq.slice source (idx + 1) (Seq.length source)) source work fp') in

  target_chunk_wosize_all source idx;
  LivePres.chunked_fused_aux_live_vertex_preserved_from_chunk
    source idx fp target hdr;
  LivePres.chunked_fused_aux_live_wosize_preserved_from_chunk
    source c fp target hdr;
  Pres.chunked_fused_aux_live_field_data_preserved_from_chunk
    source idx fp target hdr;
  RangePres.same_chunk_ranges_refl source;
  RangePres.chunked_fused_aux_preserves_ranges
    source source (MH.objects_in_chunk c) 0UL 0 fp;
  assert (RangePres.same_chunk_ranges source work);
  RangePres.same_chunk_ranges_index source work idx;
  u64_ext (Seq.index work idx).base c.base;
  assert ((Seq.index work idx).base == c.base);
  assert (MH.objects_in_chunk (Seq.index work idx) ==
          MH.objects_in_chunk_from (Seq.index work idx) c.base);
  assert (Seq.mem target (MH.objects_in_chunk (Seq.index work idx)));
  ChunkedGraph.chunked_major_vertex_from_chunk work idx target;
  suffix_wosize_all source idx;
  VertexRange.chunked_fused_sweep_coalesce_suffix_preserves_objects_from
    source work idx (Seq.index work idx).base target fp';
  assert (MH.well_formed_major_heap final);
  assert (idx < Seq.length final);
  RangePres.chunked_fused_sweep_coalesce_chunks_preserves_ranges
    (Seq.slice source (idx + 1) (Seq.length source)) source work fp';
  RangePres.same_chunk_ranges_trans source work final;
  RangePres.same_chunk_ranges_index work final idx;
  u64_ext (Seq.index final idx).base (Seq.index work idx).base;
  assert ((Seq.index final idx).base == (Seq.index work idx).base);
  assert (MH.objects_in_chunk (Seq.index final idx) ==
          MH.objects_in_chunk_from
            (Seq.index final idx) (Seq.index work idx).base);
  assert (Seq.mem target (MH.objects_in_chunk (Seq.index final idx)));
  ChunkedGraph.chunked_major_vertex_from_chunk final idx target;

  Defs.chunked_wosize_of_object_some source target hdr;
  MH.objects_in_chunk_member_header_fits c target;
  assert (MH.object_header_size_fits_in_chunk c target);
  assert (MH.word_in_chunk c (hd_address target));
  RangePres.same_chunk_ranges_word_in_chunk source work idx (hd_address target);
  MH.lookup_chunk_index_word_in_chunk work (hd_address target) idx;
  let work_hdr = MH.read_word_in_chunk (Seq.index work idx) (hd_address target) in
  MH.read_word_in_major_at_lookup_index work (hd_address target) idx;
  assert (MH.read_word_in_major work (hd_address target) == Some work_hdr);
  SeqPres.chunked_fused_sweep_coalesce_suffix_preserves_read
    source work idx fp' (hd_address target) work_hdr;
  assert (MH.read_word_in_major final (hd_address target) == Some work_hdr);
  Defs.chunked_read_header_step work target;
  Defs.chunked_read_header_step final target;
  assert (Defs.chunked_read_header work target == Some work_hdr);
  assert (Defs.chunked_read_header final target == Some work_hdr);
  Defs.chunked_wosize_of_object_some work target work_hdr;
  Defs.chunked_wosize_of_object_some final target work_hdr;
  assert (Defs.chunked_wosize_of_object source target == Obj.getWosize hdr);
  assert (Defs.chunked_wosize_of_object work target == Obj.getWosize work_hdr);
  assert (Defs.chunked_wosize_of_object final target == Obj.getWosize work_hdr);
  assert (Defs.chunked_wosize_of_object work target == Obj.getWosize hdr);
  assert (Defs.chunked_wosize_of_object source target ==
          Defs.chunked_wosize_of_object final target);

  ChunkedGraph.chunked_major_field_data_preserved_elim source work target;
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
      assert (U64.v ii <= U64.v (Obj.getWosize hdr));
      payload_field_address_facts c target ii;
      let field_u = U64.add (hd_address target) (U64.mul mword ii) in
      let field_addr : hp_addr = field_u in
      MH.major_objects_member_at_index source idx target;
      MH.lookup_chunk_index_word_in_chunk source (hd_address target) idx;
      MH.major_object_payload_word_in_lookup_chunk
        source idx target field_addr;
      assert (MH.word_in_chunk c field_addr);
      RangePres.same_chunk_ranges_word_in_chunk source work idx field_addr;
      MH.lookup_chunk_index_word_in_chunk work field_addr idx;
      let old = MH.read_word_in_chunk (Seq.index work idx) field_addr in
      MH.read_word_in_major_at_lookup_index work field_addr idx;
      assert (MH.read_word_in_major work field_addr == Some old);
      SeqPres.chunked_fused_sweep_coalesce_suffix_preserves_read
        source work idx fp' field_addr old;
      assert (MH.read_word_in_major final field_addr == Some old);
      MarkDefs.chunked_get_field_read_some work target ii old;
      MarkDefs.chunked_get_field_read_some final target ii old;
      assert (MarkDefs.chunked_get_field work target ii ==
              MarkDefs.chunked_get_field final target ii);
      assert (MarkDefs.chunked_get_field source target ii ==
              MarkDefs.chunked_get_field work target ii);
      assert (MarkDefs.chunked_get_field source target i ==
              MarkDefs.chunked_get_field final target i)
    end
  in
  FStar.Classical.forall_intro field_data;
  ChunkedGraph.chunked_major_field_preserved_intro source final target
#pop-options
