/// ---------------------------------------------------------------------------
/// GC.Spec.MajorHeap - Pure chunked major-heap model
/// ---------------------------------------------------------------------------
///
/// This module introduces the non-moving chunk abstraction used for heap
/// expansion. It intentionally lives next to the existing dense heap model:
/// existing collectors can keep using GC.Spec.Heap while new expansion proofs
/// are built around active chunk membership.

module GC.Spec.MajorHeap

open FStar.Seq

module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

type chunk_id = nat

type heap_chunk = {
  base: hp_addr;
  size: s:pos{s % U64.v mword == 0 /\ s >= 16 /\ U64.v base + s <= heap_size};
  bytes: b:seq U8.t{Seq.length b == size};
}

type major_heap = seq heap_chunk

let chunk_start (c: heap_chunk) : nat = U64.v c.base

let chunk_end (c: heap_chunk) : nat = U64.v c.base + c.size

let chunk_contains_addr (c: heap_chunk) (addr: U64.t) : Tot bool =
  U64.v addr >= chunk_start c && U64.v addr < chunk_end c

let word_in_chunk (c: heap_chunk) (addr: U64.t) : Tot bool =
  U64.v addr >= chunk_start c && U64.v addr + U64.v mword <= chunk_end c

let obj_addr_in_chunk (c: heap_chunk) (obj: obj_addr) : Tot bool =
  U64.v obj >= chunk_start c + U64.v mword && U64.v obj < chunk_end c

let object_payload_end (obj: obj_addr) (wz: nat) : nat =
  U64.v obj + wz * U64.v mword

let object_fits_in_chunk (c: heap_chunk) (obj: obj_addr) (wz: nat) : Tot bool =
  obj_addr_in_chunk c obj && object_payload_end obj wz <= chunk_end c

let obj_addr_in_chunk_header_word (c: heap_chunk) (obj: obj_addr{obj_addr_in_chunk c obj})
  : Lemma (word_in_chunk c (hd_address obj))
  = hd_address_spec obj

let chunk_offset (c: heap_chunk) (addr: U64.t{chunk_contains_addr c addr}) : nat =
  U64.v addr - chunk_start c

let chunks_disjoint (c1 c2: heap_chunk) : Tot prop =
  chunk_end c1 <= chunk_start c2 \/ chunk_end c2 <= chunk_start c1

let rec chunks_pairwise_disjoint (chunks: major_heap) : Tot prop
  (decreases Seq.length chunks)
  = if Seq.length chunks = 0 then True
    else
      let hd = Seq.head chunks in
      let tl = Seq.tail chunks in
      (forall i. i < Seq.length tl ==> chunks_disjoint hd (Seq.index tl i)) /\
      chunks_pairwise_disjoint tl

let well_formed_major_heap (mh: major_heap) : Tot prop =
  chunks_pairwise_disjoint mh

let rec lookup_chunk (mh: major_heap) (addr: hp_addr) : Tot (option heap_chunk)
  (decreases Seq.length mh)
  = if Seq.length mh = 0 then None
    else
      let c = Seq.head mh in
      if chunk_contains_addr c addr then Some c else lookup_chunk (Seq.tail mh) addr

let add_chunk (mh: major_heap) (c: heap_chunk) : major_heap =
  Seq.cons c mh

let lookup_add_chunk_hit (mh: major_heap) (c: heap_chunk)
                          (addr: hp_addr{chunk_contains_addr c addr})
  : Lemma (lookup_chunk (add_chunk mh c) addr == Some c)
  = assert (Seq.head (add_chunk mh c) == c)

let lookup_add_chunk_miss (mh: major_heap) (c: heap_chunk)
                           (addr: hp_addr{~(chunk_contains_addr c addr)})
  : Lemma (lookup_chunk (add_chunk mh c) addr == lookup_chunk mh addr)
  = assert (Seq.head (add_chunk mh c) == c);
    assert (Seq.equal (Seq.tail (add_chunk mh c)) mh);
    if chunk_contains_addr c addr then assert False else ()

let read_word_in_chunk (c: heap_chunk) (addr: hp_addr{word_in_chunk c addr}) : U64.t =
  let off = chunk_offset c addr in
  combine_bytes
    (Seq.index c.bytes off)
    (Seq.index c.bytes (off + 1))
    (Seq.index c.bytes (off + 2))
    (Seq.index c.bytes (off + 3))
    (Seq.index c.bytes (off + 4))
    (Seq.index c.bytes (off + 5))
    (Seq.index c.bytes (off + 6))
    (Seq.index c.bytes (off + 7))

let write_word_in_chunk (c: heap_chunk) (addr: hp_addr{word_in_chunk c addr}) (value: U64.t)
  : heap_chunk =
  let off = chunk_offset c addr in
  let bytes = Seq.upd c.bytes off (uint64_to_uint8 value) in
  let bytes = Seq.upd bytes (off + 1) (uint64_to_uint8 (U64.shift_right value 8ul)) in
  let bytes = Seq.upd bytes (off + 2) (uint64_to_uint8 (U64.shift_right value 16ul)) in
  let bytes = Seq.upd bytes (off + 3) (uint64_to_uint8 (U64.shift_right value 24ul)) in
  let bytes = Seq.upd bytes (off + 4) (uint64_to_uint8 (U64.shift_right value 32ul)) in
  let bytes = Seq.upd bytes (off + 5) (uint64_to_uint8 (U64.shift_right value 40ul)) in
  let bytes = Seq.upd bytes (off + 6) (uint64_to_uint8 (U64.shift_right value 48ul)) in
  let bytes = Seq.upd bytes (off + 7) (uint64_to_uint8 (U64.shift_right value 56ul)) in
  { c with bytes = bytes }

let read_word_in_major (mh: major_heap) (addr: hp_addr) : Tot (option U64.t) =
  match lookup_chunk mh addr with
  | None -> None
  | Some c ->
    if word_in_chunk c addr then Some (read_word_in_chunk c addr) else None

let rec write_word_in_major (mh: major_heap) (addr: hp_addr) (value: U64.t)
  : Tot (option major_heap) (decreases Seq.length mh)
  = if Seq.length mh = 0 then None
    else
      let c = Seq.head mh in
      let tl = Seq.tail mh in
      if word_in_chunk c addr then
        Some (Seq.cons (write_word_in_chunk c addr value) tl)
      else
        match write_word_in_major tl addr value with
        | None -> None
        | Some tl' -> Some (Seq.cons c tl')

let read_word_add_chunk_hit (mh: major_heap) (c: heap_chunk)
                            (addr: hp_addr{word_in_chunk c addr})
  : Lemma (read_word_in_major (add_chunk mh c) addr == Some (read_word_in_chunk c addr))
  = lookup_add_chunk_hit mh c addr

let read_word_add_chunk_miss (mh: major_heap) (c: heap_chunk)
                             (addr: hp_addr{~(chunk_contains_addr c addr)})
  : Lemma (read_word_in_major (add_chunk mh c) addr == read_word_in_major mh addr)
  = lookup_add_chunk_miss mh c addr

let rec lookup_chunk_contains (mh: major_heap) (addr: hp_addr) (c: heap_chunk)
  : Lemma (requires lookup_chunk mh addr == Some c)
          (ensures chunk_contains_addr c addr)
          (decreases Seq.length mh)
  = if Seq.length mh = 0 then
      assert False
    else
      let hd = Seq.head mh in
      if chunk_contains_addr hd addr then
        assert (hd == c)
      else
        lookup_chunk_contains (Seq.tail mh) addr c
