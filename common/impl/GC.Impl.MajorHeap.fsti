(*
   GC.Impl.MajorHeap -- range-owned representation for chunked major heaps.

   The interface exposes the ownership predicates and accessors needed by the
   allocator and single-chunk migration wrappers while keeping lower-level proof
   plumbing implementation-private.
 *)

module GC.Impl.MajorHeap

#lang-pulse

open Pulse.Lib.Pervasives

module Base = GC.Spec.Base
module MH = GC.Spec.MajorHeap
module Heap = GC.Impl.Heap
module OR = Pulse.Lib.OnRange
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

let chunk_range_at (h: major_heap_t) (mh: MH.major_heap) (i: nat) : slprop =
  if i < Seq.length mh then chunk_range h (Seq.index mh i) else emp

let indexed_chunk_ranges (h: major_heap_t) (mh: MH.major_heap) : slprop =
  OR.on_range (chunk_range_at h mh) 0 (Seq.length mh)

let is_indexed_major_heap (h: major_heap_t) (mh: MH.major_heap) : slprop =
  indexed_chunk_ranges h mh **
  pure (SZ.v h.size == Base.heap_size /\
        length h.data == Base.heap_size /\
        MH.well_formed_major_heap mh)

let inactive_prefix (h: major_heap_t) (s: Base.heap) : slprop =
  PTR.pts_to_range h.data 0 (U64.v Base.zero_addr) (Seq.slice s 0 (U64.v Base.zero_addr))

val chunk_range_at_in_bounds :
  h:major_heap_t -> mh:MH.major_heap -> i:nat ->
  Lemma (requires i < Seq.length mh)
          (ensures chunk_range_at h mh i == chunk_range h (Seq.index mh i))

val chunk_range_at_update_same :
  h:major_heap_t -> mh:MH.major_heap ->
  i:nat{i < Seq.length mh} -> c:MH.heap_chunk ->
  Lemma (chunk_range_at h (Seq.upd mh i c) i == chunk_range h c)

ghost
fn heap_to_single_indexed_major (h: Heap.heap_t)
  requires Heap.is_heap h 's
  ensures inactive_prefix (heap_as_major h) 's **
          is_indexed_major_heap (heap_as_major h) (MH.single_chunk_major_heap 's)

ghost
fn single_indexed_major_to_heap_as (h: Heap.heap_t) (s: Base.heap)
  requires inactive_prefix (heap_as_major h) s **
           is_indexed_major_heap (heap_as_major h) (MH.single_chunk_major_heap s)
  ensures Heap.is_heap h s

ghost
fn prepend_chunk_to_indexed_major (h: major_heap_t)
                                  (#mh: Ghost.erased MH.major_heap)
                                  (#c: Ghost.erased MH.heap_chunk)
  requires chunk_range h (Ghost.reveal c) **
           is_indexed_major_heap h (Ghost.reveal mh) **
           pure (MH.chunk_disjoint_from_all (Ghost.reveal c) (Ghost.reveal mh))
  ensures is_indexed_major_heap h (MH.add_chunk (Ghost.reveal mh) (Ghost.reveal c))

fn read_word_in_chunk (h: major_heap_t)
                      (addr: Base.hp_addr)
                      (#c: Ghost.erased (c0:MH.heap_chunk{MH.word_in_chunk c0 addr}))
  requires chunk_range h (Ghost.reveal c)
  returns v: U64.t
  ensures chunk_range h (Ghost.reveal c) **
          pure (v == MH.read_word_in_chunk (Ghost.reveal c) addr)

fn write_word_in_chunk (h: major_heap_t)
                       (addr: Base.hp_addr)
                       (v: U64.t)
                       (#c: Ghost.erased (c0:MH.heap_chunk{MH.word_in_chunk c0 addr}))
  requires chunk_range h (Ghost.reveal c)
  ensures chunk_range h (MH.write_word_in_chunk (Ghost.reveal c) addr v)

fn write_word_in_indexed_major_at_lookup_index
  (h: major_heap_t)
  (addr: Base.hp_addr)
  (v: U64.t)
  (i: nat)
  (#mh: Ghost.erased (mh0:MH.major_heap{i < Seq.length mh0 /\
                                        MH.lookup_chunk_index mh0 addr == Some i /\
                                        MH.word_in_chunk (Seq.index mh0 i) addr}))
  requires is_indexed_major_heap h (Ghost.reveal mh)
  ensures is_indexed_major_heap h
            (Seq.upd (Ghost.reveal mh) i
              (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh) i) addr v)) **
          pure (MH.write_word_in_major (Ghost.reveal mh) addr v ==
            Some (Seq.upd (Ghost.reveal mh) i
              (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh) i) addr v)))
