/// ---------------------------------------------------------------------------
/// GC.Spec.MajorAllocator - Chunk-aware allocation/expansion helpers
/// ---------------------------------------------------------------------------
///
/// This module starts the chunked-major allocation layer by specifying how a
/// fresh active chunk is initialized as one blue free-list block.  It is kept
/// beside the existing dense allocator while the collector is ported.

module GC.Spec.MajorAllocator

module U64 = FStar.UInt64
module MH = GC.Spec.MajorHeap
module Alloc = GC.Spec.Allocator

open GC.Spec.Base
open GC.Spec.Heap

let chunk_word_capacity (c: MH.heap_chunk) : nat =
  c.size / U64.v mword

let fresh_chunk_wosize (c: MH.heap_chunk) : nat =
  chunk_word_capacity c - 1

let fresh_chunk_wosize_fits (c: MH.heap_chunk)
  : Lemma (fresh_chunk_wosize c < pow2 54)
  = assert (c.size < pow2 57);
    FStar.Math.Lemmas.lemma_div_lt c.size 57 3;
    assert (chunk_word_capacity c < pow2 54)

let fresh_chunk_has_block (c: MH.heap_chunk)
  : Lemma (chunk_word_capacity c >= 2)
  = FStar.Math.Lemmas.lemma_div_exact c.size (U64.v mword);
    assert (c.size == chunk_word_capacity c * U64.v mword);
    assert (U64.v mword == 8)

let fresh_chunk_object (c: MH.heap_chunk) : obj_addr =
  fresh_chunk_has_block c;
  assert (U64.v c.base + U64.v mword < heap_size);
  f_address c.base

let fresh_chunk_object_word (c: MH.heap_chunk)
  : Lemma (MH.word_in_chunk c (fresh_chunk_object c))
  = fresh_chunk_has_block c;
    f_address_spec c.base;
    assert (U64.v (fresh_chunk_object c) == U64.v c.base + U64.v mword);
    assert (U64.v (fresh_chunk_object c) + U64.v mword <= MH.chunk_end c)

type fresh_chunk_result (c: MH.heap_chunk) = {
  chunk_out: c2:MH.heap_chunk{MH.word_in_chunk c2 c.base /\
                              MH.word_in_chunk c2 (fresh_chunk_object c)};
  fp_out: obj_addr;
}

let init_fresh_chunk (c: MH.heap_chunk) (next_fp: U64.t)
  : Tot (fresh_chunk_result c)
  = fresh_chunk_wosize_fits c;
    fresh_chunk_has_block c;
    let wz = fresh_chunk_wosize c in
    let hdr = Alloc.make_header (U64.uint_to_t wz) Alloc.blue_bits 0UL in
    assert (MH.word_in_chunk c c.base);
    let c1 = MH.write_word_in_chunk c c.base hdr in
    let obj = fresh_chunk_object c in
    fresh_chunk_object_word c;
    MH.write_word_in_chunk_preserves_word c c.base hdr obj;
    let c2 = MH.write_word_in_chunk c1 obj next_fp in
    MH.write_word_in_chunk_preserves_word c1 obj next_fp c.base;
    MH.write_word_in_chunk_preserves_word c1 obj next_fp obj;
    { chunk_out = c2; fp_out = obj }

let init_fresh_chunk_header (c: MH.heap_chunk) (next_fp: U64.t)
  : Lemma (let r = init_fresh_chunk c next_fp in
           MH.read_word_in_chunk r.chunk_out c.base ==
           Alloc.make_header (U64.uint_to_t (fresh_chunk_wosize c)) Alloc.blue_bits 0UL)
  = fresh_chunk_wosize_fits c;
    let hdr = Alloc.make_header (U64.uint_to_t (fresh_chunk_wosize c)) Alloc.blue_bits 0UL in
    let c1 = MH.write_word_in_chunk c c.base hdr in
    let obj = fresh_chunk_object c in
    fresh_chunk_object_word c;
    MH.write_word_in_chunk_preserves_word c c.base hdr c.base;
    MH.write_word_in_chunk_preserves_word c c.base hdr obj;
    MH.read_write_in_chunk_same c c.base hdr;
    f_address_spec c.base;
    assert (U64.v c.base + U64.v mword <= U64.v obj);
    MH.read_write_in_chunk_different c1 obj c.base next_fp

let init_fresh_chunk_link (c: MH.heap_chunk) (next_fp: U64.t)
  : Lemma (let r = init_fresh_chunk c next_fp in
           r.fp_out == fresh_chunk_object c /\
           MH.read_word_in_chunk r.chunk_out r.fp_out == next_fp)
  = fresh_chunk_wosize_fits c;
    let hdr = Alloc.make_header (U64.uint_to_t (fresh_chunk_wosize c)) Alloc.blue_bits 0UL in
    let c1 = MH.write_word_in_chunk c c.base hdr in
    let obj = fresh_chunk_object c in
    fresh_chunk_object_word c;
    MH.write_word_in_chunk_preserves_word c c.base hdr obj;
    MH.read_write_in_chunk_same c1 obj next_fp
