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
