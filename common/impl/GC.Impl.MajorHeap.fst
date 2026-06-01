(*
   GC.Impl.MajorHeap -- range-owned representation for chunked major heaps.

   This module is intentionally side-by-side with GC.Impl.Heap.  It owns only
   the active major chunks as pts_to_range resources; inactive gaps in the
   virtual address space are left unowned.
*)

module GC.Impl.MajorHeap

#lang-pulse

open Pulse.Lib.Pervasives

module Base = GC.Spec.Base
module MH = GC.Spec.MajorHeap
module SpecHeap = GC.Spec.Heap
module Heap = GC.Impl.Heap
module PTR = Pulse.Lib.Array.PtsToRange
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq

noeq
type major_heap_t = {
  data : array U8.t;
  size : n:SZ.t{SZ.v n == Base.heap_size};
}

let heap_as_major (h: Heap.heap_t) : major_heap_t =
  { data = h.data; size = h.size }

let chunk_range (h: major_heap_t) (c: MH.heap_chunk) : slprop =
  PTR.pts_to_range h.data (MH.chunk_start c) (MH.chunk_end c) c.bytes

let rec chunk_ranges (h: major_heap_t) (mh: MH.major_heap)
  : Tot slprop (decreases Seq.length mh)
  = if Seq.length mh = 0 then emp
    else
      let c = Seq.head mh in
      chunk_range h c ** chunk_ranges h (Seq.tail mh)

let is_major_heap (h: major_heap_t) (mh: MH.major_heap) : slprop =
  chunk_ranges h mh **
  pure (SZ.v h.size == Base.heap_size /\ MH.well_formed_major_heap mh)

let inactive_prefix (h: major_heap_t) (s: Base.heap) : slprop =
  PTR.pts_to_range h.data 0 (U64.v Base.zero_addr) (Seq.slice s 0 (U64.v Base.zero_addr))

let is_single_chunk_major (h: major_heap_t) (s: Base.heap) : slprop =
  chunk_range h (MH.single_chunk_of_heap s) **
  pure (SZ.v h.size == Base.heap_size /\
        MH.well_formed_major_heap (MH.single_chunk_major_heap s))

ghost
fn heap_to_single_major (h: Heap.heap_t)
  requires Heap.is_heap h 's
  ensures inactive_prefix (heap_as_major h) 's **
          is_single_chunk_major (heap_as_major h) 's
{
  let mh = heap_as_major h;
  unfold (Heap.is_heap h 's);
  PTR.pts_to_range_intro h.data 1.0R 's;
  PTR.pts_to_range_prop h.data;
  assert (pure (length h.data == Base.heap_size));
  rewrite each (length h.data) as Base.heap_size;
  PTR.pts_to_range_split h.data 0 (U64.v Base.zero_addr) Base.heap_size;
  with prefix major. assert (
    PTR.pts_to_range h.data 0 (U64.v Base.zero_addr) prefix **
    PTR.pts_to_range h.data (U64.v Base.zero_addr) Base.heap_size major **
    pure (prefix == Seq.slice 's 0 (U64.v Base.zero_addr) /\
          major == Seq.slice 's (U64.v Base.zero_addr) (Seq.length 's)));
  assert (pure (h.data == mh.data));
  rewrite each h.data as mh.data;
  rewrite each prefix as Seq.slice 's 0 (U64.v Base.zero_addr);
  fold (inactive_prefix mh 's);
  assert (pure (Seq.length 's == Base.heap_size));
  assert (pure (major == (MH.single_chunk_of_heap 's).bytes));
  rewrite each major as (MH.single_chunk_of_heap 's).bytes;
  fold (chunk_range mh (MH.single_chunk_of_heap 's));
  MH.single_chunk_major_heap_wf 's;
  fold (is_single_chunk_major mh 's);
  assert (pure (mh == heap_as_major h));
  rewrite each mh as heap_as_major h
}

let offset_sizet (addr: Base.hp_addr) (k: nat{U64.v addr + k < Base.heap_size})
  : (r:SZ.t{SZ.v r == U64.v addr + k})
  = SZ.fits_u64_implies_fits (U64.v addr + k);
    SZ.uint_to_t (U64.v addr + k)

fn read_word_in_chunk (h: major_heap_t)
                      (addr: Base.hp_addr)
                      (#c: Ghost.erased (c0:MH.heap_chunk{MH.word_in_chunk c0 addr}))
  requires chunk_range h (Ghost.reveal c)
  returns v: U64.t
  ensures chunk_range h (Ghost.reveal c) **
          pure (v == MH.read_word_in_chunk (Ghost.reveal c) addr)
{
  let i0 = offset_sizet addr 0;
  let i1 = offset_sizet addr 1;
  let i2 = offset_sizet addr 2;
  let i3 = offset_sizet addr 3;
  let i4 = offset_sizet addr 4;
  let i5 = offset_sizet addr 5;
  let i6 = offset_sizet addr 6;
  let i7 = offset_sizet addr 7;
  assert (pure (MH.chunk_start (Ghost.reveal c) <= SZ.v i0));
  assert (pure (SZ.v i7 < MH.chunk_end (Ghost.reveal c)));
  assert (pure (SZ.v i0 < MH.chunk_end (Ghost.reveal c)));
  assert (pure (SZ.v i1 < MH.chunk_end (Ghost.reveal c)));
  assert (pure (SZ.v i2 < MH.chunk_end (Ghost.reveal c)));
  assert (pure (SZ.v i3 < MH.chunk_end (Ghost.reveal c)));
  assert (pure (SZ.v i4 < MH.chunk_end (Ghost.reveal c)));
  assert (pure (SZ.v i5 < MH.chunk_end (Ghost.reveal c)));
  assert (pure (SZ.v i6 < MH.chunk_end (Ghost.reveal c)));
  unfold (chunk_range h (Ghost.reveal c));
  let b0 = PTR.pts_to_range_index h.data i0;
  let b1 = PTR.pts_to_range_index h.data i1;
  let b2 = PTR.pts_to_range_index h.data i2;
  let b3 = PTR.pts_to_range_index h.data i3;
  let b4 = PTR.pts_to_range_index h.data i4;
  let b5 = PTR.pts_to_range_index h.data i5;
  let b6 = PTR.pts_to_range_index h.data i6;
  let b7 = PTR.pts_to_range_index h.data i7;
  let v = SpecHeap.combine_bytes b0 b1 b2 b3 b4 b5 b6 b7;
  assert (pure (SZ.v i0 - MH.chunk_start (Ghost.reveal c) == MH.chunk_offset (Ghost.reveal c) addr));
  assert (pure (SZ.v i1 - MH.chunk_start (Ghost.reveal c) == MH.chunk_offset (Ghost.reveal c) addr + 1));
  assert (pure (SZ.v i2 - MH.chunk_start (Ghost.reveal c) == MH.chunk_offset (Ghost.reveal c) addr + 2));
  assert (pure (SZ.v i3 - MH.chunk_start (Ghost.reveal c) == MH.chunk_offset (Ghost.reveal c) addr + 3));
  assert (pure (SZ.v i4 - MH.chunk_start (Ghost.reveal c) == MH.chunk_offset (Ghost.reveal c) addr + 4));
  assert (pure (SZ.v i5 - MH.chunk_start (Ghost.reveal c) == MH.chunk_offset (Ghost.reveal c) addr + 5));
  assert (pure (SZ.v i6 - MH.chunk_start (Ghost.reveal c) == MH.chunk_offset (Ghost.reveal c) addr + 6));
  assert (pure (SZ.v i7 - MH.chunk_start (Ghost.reveal c) == MH.chunk_offset (Ghost.reveal c) addr + 7));
  fold (chunk_range h (Ghost.reveal c));
  v
}

fn write_word_in_chunk (h: major_heap_t)
                       (addr: Base.hp_addr)
                       (v: U64.t)
                       (#c: Ghost.erased (c0:MH.heap_chunk{MH.word_in_chunk c0 addr}))
  requires chunk_range h (Ghost.reveal c)
  ensures PTR.pts_to_range h.data
            (MH.chunk_start (Ghost.reveal c))
            (MH.chunk_end (Ghost.reveal c))
            (MH.write_word_in_chunk (Ghost.reveal c) addr v).bytes
{
  let i0 = offset_sizet addr 0;
  let i1 = offset_sizet addr 1;
  let i2 = offset_sizet addr 2;
  let i3 = offset_sizet addr 3;
  let i4 = offset_sizet addr 4;
  let i5 = offset_sizet addr 5;
  let i6 = offset_sizet addr 6;
  let i7 = offset_sizet addr 7;
  assert (pure (MH.chunk_start (Ghost.reveal c) <= SZ.v i0));
  assert (pure (SZ.v i7 < MH.chunk_end (Ghost.reveal c)));
  assert (pure (SZ.v i0 < MH.chunk_end (Ghost.reveal c)));
  assert (pure (SZ.v i1 < MH.chunk_end (Ghost.reveal c)));
  assert (pure (SZ.v i2 < MH.chunk_end (Ghost.reveal c)));
  assert (pure (SZ.v i3 < MH.chunk_end (Ghost.reveal c)));
  assert (pure (SZ.v i4 < MH.chunk_end (Ghost.reveal c)));
  assert (pure (SZ.v i5 < MH.chunk_end (Ghost.reveal c)));
  assert (pure (SZ.v i6 < MH.chunk_end (Ghost.reveal c)));
  assert (pure (SZ.v i0 - MH.chunk_start (Ghost.reveal c) == MH.chunk_offset (Ghost.reveal c) addr));
  assert (pure (SZ.v i1 - MH.chunk_start (Ghost.reveal c) == MH.chunk_offset (Ghost.reveal c) addr + 1));
  assert (pure (SZ.v i2 - MH.chunk_start (Ghost.reveal c) == MH.chunk_offset (Ghost.reveal c) addr + 2));
  assert (pure (SZ.v i3 - MH.chunk_start (Ghost.reveal c) == MH.chunk_offset (Ghost.reveal c) addr + 3));
  assert (pure (SZ.v i4 - MH.chunk_start (Ghost.reveal c) == MH.chunk_offset (Ghost.reveal c) addr + 4));
  assert (pure (SZ.v i5 - MH.chunk_start (Ghost.reveal c) == MH.chunk_offset (Ghost.reveal c) addr + 5));
  assert (pure (SZ.v i6 - MH.chunk_start (Ghost.reveal c) == MH.chunk_offset (Ghost.reveal c) addr + 6));
  assert (pure (SZ.v i7 - MH.chunk_start (Ghost.reveal c) == MH.chunk_offset (Ghost.reveal c) addr + 7));
  let b0 = SpecHeap.uint64_to_uint8 v;
  let b1 = SpecHeap.uint64_to_uint8 (U64.shift_right v 8ul);
  let b2 = SpecHeap.uint64_to_uint8 (U64.shift_right v 16ul);
  let b3 = SpecHeap.uint64_to_uint8 (U64.shift_right v 24ul);
  let b4 = SpecHeap.uint64_to_uint8 (U64.shift_right v 32ul);
  let b5 = SpecHeap.uint64_to_uint8 (U64.shift_right v 40ul);
  let b6 = SpecHeap.uint64_to_uint8 (U64.shift_right v 48ul);
  let b7 = SpecHeap.uint64_to_uint8 (U64.shift_right v 56ul);
  unfold (chunk_range h (Ghost.reveal c));
  with s0. assert (
    PTR.pts_to_range h.data (MH.chunk_start (Ghost.reveal c)) (MH.chunk_end (Ghost.reveal c)) s0 **
    pure (s0 == (Ghost.reveal c).bytes));
  PTR.pts_to_range_upd h.data i0 b0;
  with s1. assert (
    PTR.pts_to_range h.data (MH.chunk_start (Ghost.reveal c)) (MH.chunk_end (Ghost.reveal c)) s1 **
    pure (s1 == Seq.upd s0 (MH.chunk_offset (Ghost.reveal c) addr) b0));
  PTR.pts_to_range_upd h.data i1 b1;
  with s2. assert (
    PTR.pts_to_range h.data (MH.chunk_start (Ghost.reveal c)) (MH.chunk_end (Ghost.reveal c)) s2 **
    pure (s2 == Seq.upd s1 (MH.chunk_offset (Ghost.reveal c) addr + 1) b1));
  PTR.pts_to_range_upd h.data i2 b2;
  with s3. assert (
    PTR.pts_to_range h.data (MH.chunk_start (Ghost.reveal c)) (MH.chunk_end (Ghost.reveal c)) s3 **
    pure (s3 == Seq.upd s2 (MH.chunk_offset (Ghost.reveal c) addr + 2) b2));
  PTR.pts_to_range_upd h.data i3 b3;
  with s4. assert (
    PTR.pts_to_range h.data (MH.chunk_start (Ghost.reveal c)) (MH.chunk_end (Ghost.reveal c)) s4 **
    pure (s4 == Seq.upd s3 (MH.chunk_offset (Ghost.reveal c) addr + 3) b3));
  PTR.pts_to_range_upd h.data i4 b4;
  with s5. assert (
    PTR.pts_to_range h.data (MH.chunk_start (Ghost.reveal c)) (MH.chunk_end (Ghost.reveal c)) s5 **
    pure (s5 == Seq.upd s4 (MH.chunk_offset (Ghost.reveal c) addr + 4) b4));
  PTR.pts_to_range_upd h.data i5 b5;
  with s6. assert (
    PTR.pts_to_range h.data (MH.chunk_start (Ghost.reveal c)) (MH.chunk_end (Ghost.reveal c)) s6 **
    pure (s6 == Seq.upd s5 (MH.chunk_offset (Ghost.reveal c) addr + 5) b5));
  PTR.pts_to_range_upd h.data i6 b6;
  with s7. assert (
    PTR.pts_to_range h.data (MH.chunk_start (Ghost.reveal c)) (MH.chunk_end (Ghost.reveal c)) s7 **
    pure (s7 == Seq.upd s6 (MH.chunk_offset (Ghost.reveal c) addr + 6) b6));
  PTR.pts_to_range_upd h.data i7 b7;
  with s8. assert (
    PTR.pts_to_range h.data (MH.chunk_start (Ghost.reveal c)) (MH.chunk_end (Ghost.reveal c)) s8 **
    pure (s8 == Seq.upd s7 (MH.chunk_offset (Ghost.reveal c) addr + 7) b7));
  assert (pure (s8 == (MH.write_word_in_chunk (Ghost.reveal c) addr v).bytes));
  assert (pure (MH.chunk_start (MH.write_word_in_chunk (Ghost.reveal c) addr v) == MH.chunk_start (Ghost.reveal c)));
  assert (pure (MH.chunk_end (MH.write_word_in_chunk (Ghost.reveal c) addr v) == MH.chunk_end (Ghost.reveal c)));
  assert (pure (MH.chunk_start (Ghost.reveal c) == MH.chunk_start (MH.write_word_in_chunk (Ghost.reveal c) addr v)));
  assert (pure (MH.chunk_end (Ghost.reveal c) == MH.chunk_end (MH.write_word_in_chunk (Ghost.reveal c) addr v)));
  rewrite each s8 as (MH.write_word_in_chunk (Ghost.reveal c) addr v).bytes
}
