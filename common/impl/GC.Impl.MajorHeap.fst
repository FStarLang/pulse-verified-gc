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
module OR = Pulse.Lib.OnRange
module PTR = Pulse.Lib.Array.PtsToRange
module SZ = FStar.SizeT
module T = Pulse.Lib.Trade.Util
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq
module SeqProps = FStar.Seq.Properties

let major_as_heap (h: major_heap_t) : Heap.heap_t =
  { data = h.data; size = h.size }

let rec chunk_ranges (h: major_heap_t) (mh: MH.major_heap)
  : Tot slprop (decreases Seq.length mh)
  = if Seq.length mh = 0 then emp
    else
      let c = Seq.head mh in
      chunk_range h c ** chunk_ranges h (Seq.tail mh)

let chunk_range_at_in_bounds (h: major_heap_t) (mh: MH.major_heap) (i: nat)
  : Lemma (requires i < Seq.length mh)
          (ensures chunk_range_at h mh i == chunk_range h (Seq.index mh i))
  = ()

let chunk_range_at_update_same (h: major_heap_t) (mh: MH.major_heap)
                               (i: nat{i < Seq.length mh}) (c: MH.heap_chunk)
  : Lemma (chunk_range_at h (Seq.upd mh i c) i == chunk_range h c)
  = assert (Seq.length (Seq.upd mh i c) == Seq.length mh);
    assert (Seq.index (Seq.upd mh i c) i == c)

let chunk_range_at_update_diff (h: major_heap_t) (mh: MH.major_heap)
                               (i: nat{i < Seq.length mh}) (c: MH.heap_chunk)
                               (k: nat{k < Seq.length mh /\ k <> i})
  : Lemma (chunk_range_at h (Seq.upd mh i c) k == chunk_range_at h mh k)
  = assert (Seq.length (Seq.upd mh i c) == Seq.length mh);
    assert (Seq.index (Seq.upd mh i c) k == Seq.index mh k)

let chunk_range_at_add_chunk_head (h: major_heap_t) (mh: MH.major_heap) (c: MH.heap_chunk)
  : Lemma (chunk_range_at h (MH.add_chunk mh c) 0 == chunk_range h c)
  = assert (Seq.length (MH.add_chunk mh c) > 0);
    assert (Seq.index (MH.add_chunk mh c) 0 == c)

let chunk_range_at_add_chunk_tail (h: major_heap_t) (mh: MH.major_heap)
                                  (c: MH.heap_chunk) (k: nat{k < Seq.length mh})
  : Lemma (chunk_range_at h (MH.add_chunk mh c) (k + 1) == chunk_range_at h mh k)
  = assert (Seq.length (MH.add_chunk mh c) == Seq.length mh + 1);
    assert (k + 1 < Seq.length (MH.add_chunk mh c));
    assert (Seq.index (MH.add_chunk mh c) (k + 1) == Seq.index mh k)

let chunk_ranges_cons_eq (h: major_heap_t) (mh: MH.major_heap) (c: MH.heap_chunk)
  : Lemma (chunk_ranges h (Seq.cons c mh) == chunk_range h c ** chunk_ranges h mh)
  = assert (Seq.length (Seq.cons c mh) > 0);
    assert (Seq.head (Seq.cons c mh) == c);
    assert (Seq.equal (Seq.tail (Seq.cons c mh)) mh);
    Seq.lemma_eq_elim (Seq.tail (Seq.cons c mh)) mh

let is_major_heap (h: major_heap_t) (mh: MH.major_heap) : slprop =
  chunk_ranges h mh **
  pure (SZ.v h.size == Base.heap_size /\
        length h.data == Base.heap_size /\
        MH.well_formed_major_heap mh)

let is_single_chunk_major (h: major_heap_t) (s: Base.heap) : slprop =
  chunk_range h (MH.single_chunk_of_heap s) **
  pure (SZ.v h.size == Base.heap_size /\
        length h.data == Base.heap_size /\
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

ghost
fn heap_to_single_indexed_major (h: Heap.heap_t)
  requires Heap.is_heap h 's
  ensures inactive_prefix (heap_as_major h) 's **
          is_indexed_major_heap (heap_as_major h) (MH.single_chunk_major_heap 's)
{
  heap_to_single_major h;
  let mh = heap_as_major h;
  assert (pure (mh == heap_as_major h));
  rewrite each (heap_as_major h) as mh;
  unfold (is_single_chunk_major mh 's);
  assert (pure (Seq.length (MH.single_chunk_major_heap 's) == 1));
  assert (pure (Seq.index (MH.single_chunk_major_heap 's) 0 == MH.single_chunk_of_heap 's));
  chunk_range_at_in_bounds mh (MH.single_chunk_major_heap 's) 0;
  rewrite
    (chunk_range mh (MH.single_chunk_of_heap 's))
  as
    (chunk_range_at mh (MH.single_chunk_major_heap 's) 0);
  OR.on_range_singleton_intro (chunk_range_at mh (MH.single_chunk_major_heap 's)) 0;
  fold (indexed_chunk_ranges mh (MH.single_chunk_major_heap 's));
  fold (is_indexed_major_heap mh (MH.single_chunk_major_heap 's));
  assert (pure (mh == heap_as_major h));
  rewrite each mh as heap_as_major h
}

ghost
fn single_indexed_major_to_heap (h: major_heap_t) (s: Base.heap)
  requires inactive_prefix h s **
           is_indexed_major_heap h (MH.single_chunk_major_heap s)
  ensures Heap.is_heap (major_as_heap h) s
{
  unfold (is_indexed_major_heap h (MH.single_chunk_major_heap s));
  assert (pure (SZ.v h.size == Base.heap_size));
  assert (pure (Seq.length (MH.single_chunk_major_heap s) == 1));
  unfold (indexed_chunk_ranges h (MH.single_chunk_major_heap s));
  OR.on_range_singleton_elim ()
    #(chunk_range_at h (MH.single_chunk_major_heap s))
    #0
    #1;
  chunk_range_at_in_bounds h (MH.single_chunk_major_heap s) 0;
  rewrite
    (chunk_range_at h (MH.single_chunk_major_heap s) 0)
  as
    (chunk_range h (MH.single_chunk_of_heap s));
  unfold (inactive_prefix h s);
  unfold (chunk_range h (MH.single_chunk_of_heap s));
  with prefix major. assert (
    PTR.pts_to_range h.data 0 (U64.v Base.zero_addr) prefix **
    PTR.pts_to_range h.data (U64.v Base.zero_addr) Base.heap_size major **
    pure (prefix == Seq.slice s 0 (U64.v Base.zero_addr) /\
          major == (MH.single_chunk_of_heap s).bytes));
  assert (pure (major == Seq.slice s (U64.v Base.zero_addr) (Seq.length s)));
  SeqProps.lemma_split s (U64.v Base.zero_addr);
  assert (pure (Seq.append prefix major == s));
  PTR.pts_to_range_join h.data 0 (U64.v Base.zero_addr) Base.heap_size;
  rewrite
    (PTR.pts_to_range h.data 0 Base.heap_size (Seq.append prefix major))
  as
    (PTR.pts_to_range h.data 0 (length h.data) s);
  PTR.pts_to_range_elim h.data 1.0R s;
  assert (pure ((major_as_heap h).data == h.data));
  assert (pure ((major_as_heap h).size == h.size));
  fold (Heap.is_heap (major_as_heap h) s)
}

ghost
fn single_indexed_major_to_heap_as (h: Heap.heap_t) (s: Base.heap)
  requires inactive_prefix (heap_as_major h) s **
           is_indexed_major_heap (heap_as_major h) (MH.single_chunk_major_heap s)
  ensures Heap.is_heap h s
{
  single_indexed_major_to_heap (heap_as_major h) s;
  assert (pure (major_as_heap (heap_as_major h) == h));
  rewrite
    (Heap.is_heap (major_as_heap (heap_as_major h)) s)
  as
    (Heap.is_heap h s)
}

ghost
fn prepend_chunk_range (h: major_heap_t)
                       (#mh: Ghost.erased MH.major_heap)
                       (#c: Ghost.erased MH.heap_chunk)
  requires chunk_range h (Ghost.reveal c) **
           chunk_ranges h (Ghost.reveal mh)
  ensures chunk_ranges h (MH.add_chunk (Ghost.reveal mh) (Ghost.reveal c))
{
  chunk_ranges_cons_eq h (Ghost.reveal mh) (Ghost.reveal c);
  rewrite
    (chunk_range h (Ghost.reveal c) **
     chunk_ranges h (Ghost.reveal mh))
  as
    (chunk_ranges h (Seq.cons (Ghost.reveal c) (Ghost.reveal mh)));
  assert (pure (Seq.cons (Ghost.reveal c) (Ghost.reveal mh) == MH.add_chunk (Ghost.reveal mh) (Ghost.reveal c)));
  rewrite each (Seq.cons (Ghost.reveal c) (Ghost.reveal mh)) as MH.add_chunk (Ghost.reveal mh) (Ghost.reveal c)
}

ghost
fn split_prepended_chunk_range (h: major_heap_t)
                              (#mh: Ghost.erased MH.major_heap)
                              (#c: Ghost.erased MH.heap_chunk)
  requires chunk_ranges h (MH.add_chunk (Ghost.reveal mh) (Ghost.reveal c))
  ensures chunk_range h (Ghost.reveal c) **
          chunk_ranges h (Ghost.reveal mh)
{
  assert (pure (Seq.cons (Ghost.reveal c) (Ghost.reveal mh) == MH.add_chunk (Ghost.reveal mh) (Ghost.reveal c)));
  rewrite
    (chunk_ranges h (MH.add_chunk (Ghost.reveal mh) (Ghost.reveal c)))
  as
    (chunk_ranges h (Seq.cons (Ghost.reveal c) (Ghost.reveal mh)));
  chunk_ranges_cons_eq h (Ghost.reveal mh) (Ghost.reveal c);
  rewrite
    (chunk_ranges h (Seq.cons (Ghost.reveal c) (Ghost.reveal mh)))
  as
    (chunk_range h (Ghost.reveal c) **
     chunk_ranges h (Ghost.reveal mh))
}

ghost
fn prepend_chunk_to_major (h: major_heap_t)
                          (#mh: Ghost.erased MH.major_heap)
                          (#c: Ghost.erased MH.heap_chunk)
  requires chunk_range h (Ghost.reveal c) **
           is_major_heap h (Ghost.reveal mh) **
           pure (MH.chunk_disjoint_from_all (Ghost.reveal c) (Ghost.reveal mh))
  ensures is_major_heap h (MH.add_chunk (Ghost.reveal mh) (Ghost.reveal c))
{
  unfold (is_major_heap h (Ghost.reveal mh));
  assert (pure (SZ.v h.size == Base.heap_size));
  assert (pure (MH.well_formed_major_heap (Ghost.reveal mh)));
  MH.add_chunk_preserves_wf (Ghost.reveal mh) (Ghost.reveal c);
  prepend_chunk_range h #mh #c;
  fold (is_major_heap h (MH.add_chunk (Ghost.reveal mh) (Ghost.reveal c)))
}

ghost
fn shift_chunk_range_after_prepend (h: major_heap_t)
                                   (#mh: Ghost.erased MH.major_heap)
                                   (#c: Ghost.erased MH.heap_chunk)
                                   (k: nat{k < Seq.length (Ghost.reveal mh)})
  requires chunk_range_at h (Ghost.reveal mh) k
  ensures chunk_range_at h (MH.add_chunk (Ghost.reveal mh) (Ghost.reveal c)) (k + 1)
{
  chunk_range_at_add_chunk_tail h (Ghost.reveal mh) (Ghost.reveal c) k;
  rewrite
    (chunk_range_at h (Ghost.reveal mh) k)
  as
    (chunk_range_at h (MH.add_chunk (Ghost.reveal mh) (Ghost.reveal c)) (k + 1))
}

ghost
fn prepend_chunk_to_indexed_major (h: major_heap_t)
                                  (#mh: Ghost.erased MH.major_heap)
                                  (#c: Ghost.erased MH.heap_chunk)
  requires chunk_range h (Ghost.reveal c) **
           is_indexed_major_heap h (Ghost.reveal mh) **
           pure (MH.chunk_disjoint_from_all (Ghost.reveal c) (Ghost.reveal mh))
  ensures is_indexed_major_heap h (MH.add_chunk (Ghost.reveal mh) (Ghost.reveal c))
{
  unfold (is_indexed_major_heap h (Ghost.reveal mh));
  unfold (indexed_chunk_ranges h (Ghost.reveal mh));
  assert (pure (SZ.v h.size == Base.heap_size));
  assert (pure (MH.well_formed_major_heap (Ghost.reveal mh)));
  MH.add_chunk_preserves_wf (Ghost.reveal mh) (Ghost.reveal c);
  chunk_range_at_add_chunk_head h (Ghost.reveal mh) (Ghost.reveal c);
  rewrite
    (chunk_range h (Ghost.reveal c))
  as
    (chunk_range_at h (MH.add_chunk (Ghost.reveal mh) (Ghost.reveal c)) 0);
  ghost
  fn shift_old_chunk (k: nat{0 <= k /\ k < Seq.length (Ghost.reveal mh)})
    requires chunk_range_at h (Ghost.reveal mh) k
    ensures chunk_range_at h (MH.add_chunk (Ghost.reveal mh) (Ghost.reveal c)) (k + 1)
  {
    shift_chunk_range_after_prepend h #mh #c k
  };
  OR.on_range_weaken_and_shift
    (chunk_range_at h (Ghost.reveal mh))
    (chunk_range_at h (MH.add_chunk (Ghost.reveal mh) (Ghost.reveal c)))
    1 0 (Seq.length (Ghost.reveal mh))
    shift_old_chunk;
  OR.on_range_cons
    0
    #(chunk_range_at h (MH.add_chunk (Ghost.reveal mh) (Ghost.reveal c)))
    #_
    #_;
  fold (indexed_chunk_ranges h (MH.add_chunk (Ghost.reveal mh) (Ghost.reveal c)));
  fold (is_indexed_major_heap h (MH.add_chunk (Ghost.reveal mh) (Ghost.reveal c)))
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
  ensures chunk_range h (MH.write_word_in_chunk (Ghost.reveal c) addr v)
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
  MH.write_word_in_chunk_preserves_range (Ghost.reveal c) addr v;
  assert (pure (MH.chunk_start (MH.write_word_in_chunk (Ghost.reveal c) addr v) == MH.chunk_start (Ghost.reveal c)));
  assert (pure (MH.chunk_end (MH.write_word_in_chunk (Ghost.reveal c) addr v) == MH.chunk_end (Ghost.reveal c)));
  assert (pure (MH.chunk_start (Ghost.reveal c) == MH.chunk_start (MH.write_word_in_chunk (Ghost.reveal c) addr v)));
  assert (pure (MH.chunk_end (Ghost.reveal c) == MH.chunk_end (MH.write_word_in_chunk (Ghost.reveal c) addr v)));
  rewrite
    (PTR.pts_to_range h.data (MH.chunk_start (Ghost.reveal c)) (MH.chunk_end (Ghost.reveal c)) s8)
  as
    (PTR.pts_to_range h.data
       (MH.chunk_start (MH.write_word_in_chunk (Ghost.reveal c) addr v))
       (MH.chunk_end (MH.write_word_in_chunk (Ghost.reveal c) addr v))
       (MH.write_word_in_chunk (Ghost.reveal c) addr v).bytes);
  fold (chunk_range h (MH.write_word_in_chunk (Ghost.reveal c) addr v))
}

fn read_word_in_prepended_chunk (h: major_heap_t)
                                (addr: Base.hp_addr)
                                (#mh: Ghost.erased MH.major_heap)
                                (#c: Ghost.erased (c0:MH.heap_chunk{MH.word_in_chunk c0 addr}))
  requires chunk_ranges h (MH.add_chunk (Ghost.reveal mh) (Ghost.reveal c))
  returns v: U64.t
  ensures chunk_ranges h (MH.add_chunk (Ghost.reveal mh) (Ghost.reveal c)) **
          pure (v == MH.read_word_in_chunk (Ghost.reveal c) addr)
{
  split_prepended_chunk_range h #mh #(Ghost.hide (Ghost.reveal c));
  let v = read_word_in_chunk h addr #c;
  prepend_chunk_range h #mh #(Ghost.hide (Ghost.reveal c));
  v
}

fn write_word_in_prepended_chunk (h: major_heap_t)
                                 (addr: Base.hp_addr)
                                 (v: U64.t)
                                 (#mh: Ghost.erased MH.major_heap)
                                 (#c: Ghost.erased (c0:MH.heap_chunk{MH.word_in_chunk c0 addr}))
  requires chunk_ranges h (MH.add_chunk (Ghost.reveal mh) (Ghost.reveal c))
  ensures chunk_ranges h (MH.add_chunk (Ghost.reveal mh) (MH.write_word_in_chunk (Ghost.reveal c) addr v))
{
  split_prepended_chunk_range h #mh #(Ghost.hide (Ghost.reveal c));
  write_word_in_chunk h addr v #c;
  prepend_chunk_range h #mh #(Ghost.hide (MH.write_word_in_chunk (Ghost.reveal c) addr v))
}

fn read_word_at_chunk_index (h: major_heap_t)
                            (addr: Base.hp_addr)
                            (i: nat)
                            (#mh: Ghost.erased (mh0:MH.major_heap{i < Seq.length mh0 /\
                                                                   MH.word_in_chunk (Seq.index mh0 i) addr}))
  requires indexed_chunk_ranges h (Ghost.reveal mh)
  returns v: U64.t
  ensures indexed_chunk_ranges h (Ghost.reveal mh) **
          pure (v == MH.read_word_in_chunk (Seq.index (Ghost.reveal mh) i) addr)
{
  unfold (indexed_chunk_ranges h (Ghost.reveal mh));
  OR.on_range_focus i #(chunk_range_at h (Ghost.reveal mh)) #0 #(Seq.length (Ghost.reveal mh));
  chunk_range_at_in_bounds h (Ghost.reveal mh) i;
  rewrite
    (chunk_range_at h (Ghost.reveal mh) i)
  as
    (chunk_range h (Seq.index (Ghost.reveal mh) i));
  let v = read_word_in_chunk h addr #(Ghost.hide (Seq.index (Ghost.reveal mh) i));
  chunk_range_at_in_bounds h (Ghost.reveal mh) i;
  rewrite
    (chunk_range h (Seq.index (Ghost.reveal mh) i))
  as
    (chunk_range_at h (Ghost.reveal mh) i);
  T.elim _ _;
  fold (indexed_chunk_ranges h (Ghost.reveal mh));
  v
}

fn read_word_in_major_at_chunk_index
  (h: major_heap_t)
  (addr: Base.hp_addr)
  (i: nat)
  (#mh: Ghost.erased (mh0:MH.major_heap{i < Seq.length mh0 /\
                                         MH.word_in_chunk (Seq.index mh0 i) addr /\
                                         (forall (k:nat). k < i ==> ~(MH.chunk_contains_addr (Seq.index mh0 k) addr))}))
  requires indexed_chunk_ranges h (Ghost.reveal mh)
  returns v: U64.t
  ensures indexed_chunk_ranges h (Ghost.reveal mh) **
          pure (MH.read_word_in_major (Ghost.reveal mh) addr == Some v)
{
  let v = read_word_at_chunk_index h addr i #(Ghost.hide (Ghost.reveal mh));
  MH.read_word_in_major_at_index (Ghost.reveal mh) addr i;
  v
}

fn read_word_in_indexed_major_at_chunk_index
  (h: major_heap_t)
  (addr: Base.hp_addr)
  (i: nat)
  (#mh: Ghost.erased (mh0:MH.major_heap{i < Seq.length mh0 /\
                                         MH.word_in_chunk (Seq.index mh0 i) addr /\
                                         (forall (k:nat). k < i ==> ~(MH.chunk_contains_addr (Seq.index mh0 k) addr))}))
  requires is_indexed_major_heap h (Ghost.reveal mh)
  returns v: U64.t
  ensures is_indexed_major_heap h (Ghost.reveal mh) **
          pure (MH.read_word_in_major (Ghost.reveal mh) addr == Some v)
{
  unfold (is_indexed_major_heap h (Ghost.reveal mh));
  let v = read_word_in_major_at_chunk_index h addr i #mh;
  fold (is_indexed_major_heap h (Ghost.reveal mh));
  v
}

fn read_word_in_indexed_major_at_lookup_index
  (h: major_heap_t)
  (addr: Base.hp_addr)
  (i: nat)
  (#mh: Ghost.erased (mh0:MH.major_heap{i < Seq.length mh0 /\
                                        MH.lookup_chunk_index mh0 addr == Some i /\
                                        MH.word_in_chunk (Seq.index mh0 i) addr}))
  requires is_indexed_major_heap h (Ghost.reveal mh)
  returns v: U64.t
  ensures is_indexed_major_heap h (Ghost.reveal mh) **
          pure (MH.read_word_in_major (Ghost.reveal mh) addr == Some v)
{
  MH.lookup_chunk_index_some (Ghost.reveal mh) addr i;
  let v = read_word_in_indexed_major_at_chunk_index h addr i
    #(Ghost.hide (Ghost.reveal mh));
  v
}

fn write_word_at_chunk_index (h: major_heap_t)
                             (addr: Base.hp_addr)
                             (v: U64.t)
                             (i: nat)
                             (#mh: Ghost.erased (mh0:MH.major_heap{i < Seq.length mh0 /\
                                                                    MH.word_in_chunk (Seq.index mh0 i) addr}))
  requires indexed_chunk_ranges h (Ghost.reveal mh)
  ensures indexed_chunk_ranges h
            (Seq.upd (Ghost.reveal mh) i
              (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh) i) addr v))
{
  assert (pure (Seq.length (Seq.upd (Ghost.reveal mh) i
    (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh) i) addr v)) ==
    Seq.length (Ghost.reveal mh)));
  unfold (indexed_chunk_ranges h (Ghost.reveal mh));
  OR.on_range_get i #(chunk_range_at h (Ghost.reveal mh)) #0 #(Seq.length (Ghost.reveal mh));
  chunk_range_at_in_bounds h (Ghost.reveal mh) i;
  rewrite
    (chunk_range_at h (Ghost.reveal mh) i)
  as
    (chunk_range h (Seq.index (Ghost.reveal mh) i));
  write_word_in_chunk h addr v #(Ghost.hide (Seq.index (Ghost.reveal mh) i));
  chunk_range_at_update_same h (Ghost.reveal mh) i
    (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh) i) addr v);
  rewrite
    (chunk_range h (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh) i) addr v))
  as
    (chunk_range_at h
      (Seq.upd (Ghost.reveal mh) i
        (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh) i) addr v))
      i);
  assert (pure (forall k. 0 <= k /\ k < i ==>
    chunk_range_at h (Ghost.reveal mh) k ==
    chunk_range_at h
      (Seq.upd (Ghost.reveal mh) i
        (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh) i) addr v))
      k));
  OR.on_range_frame
    (chunk_range_at h (Ghost.reveal mh))
    (chunk_range_at h
      (Seq.upd (Ghost.reveal mh) i
        (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh) i) addr v)))
    0 i;
  rewrite
    (OR.on_range (chunk_range_at h (Ghost.reveal mh)) 0 i)
  as
    (OR.on_range
      (chunk_range_at h
        (Seq.upd (Ghost.reveal mh) i
          (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh) i) addr v)))
      0 i);
  assert (pure (forall k. i + 1 <= k /\ k < Seq.length (Ghost.reveal mh) ==>
    chunk_range_at h (Ghost.reveal mh) k ==
    chunk_range_at h
      (Seq.upd (Ghost.reveal mh) i
        (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh) i) addr v))
      k));
  OR.on_range_frame
    (chunk_range_at h (Ghost.reveal mh))
    (chunk_range_at h
      (Seq.upd (Ghost.reveal mh) i
        (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh) i) addr v)))
    (i + 1)
    (Seq.length (Ghost.reveal mh));
  rewrite
    (OR.on_range (chunk_range_at h (Ghost.reveal mh)) (i + 1) (Seq.length (Ghost.reveal mh)))
  as
    (OR.on_range
      (chunk_range_at h
        (Seq.upd (Ghost.reveal mh) i
          (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh) i) addr v)))
      (i + 1)
      (Seq.length (Ghost.reveal mh)));
  OR.on_range_put 0 i (Seq.length (Ghost.reveal mh))
    #(chunk_range_at h
      (Seq.upd (Ghost.reveal mh) i
        (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh) i) addr v)));
  rewrite each (Seq.length (Ghost.reveal mh)) as
    Seq.length (Seq.upd (Ghost.reveal mh) i
      (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh) i) addr v));
  fold (indexed_chunk_ranges h
    (Seq.upd (Ghost.reveal mh) i
      (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh) i) addr v)))
}

fn write_word_in_major_at_chunk_index
  (h: major_heap_t)
  (addr: Base.hp_addr)
  (v: U64.t)
  (i: nat)
  (#mh: Ghost.erased (mh0:MH.major_heap{i < Seq.length mh0 /\
                                         MH.word_in_chunk (Seq.index mh0 i) addr /\
                                         (forall (k:nat). k < i ==> ~(MH.word_in_chunk (Seq.index mh0 k) addr))}))
  requires indexed_chunk_ranges h (Ghost.reveal mh)
  ensures indexed_chunk_ranges h
            (Seq.upd (Ghost.reveal mh) i
              (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh) i) addr v)) **
          pure (MH.write_word_in_major (Ghost.reveal mh) addr v ==
            Some (Seq.upd (Ghost.reveal mh) i
              (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh) i) addr v)))
{
  MH.write_word_in_major_at_index (Ghost.reveal mh) addr v i;
  write_word_at_chunk_index h addr v i #(Ghost.hide (Ghost.reveal mh));
}

fn write_word_in_indexed_major_at_chunk_index
  (h: major_heap_t)
  (addr: Base.hp_addr)
  (v: U64.t)
  (i: nat)
  (#mh: Ghost.erased (mh0:MH.major_heap{i < Seq.length mh0 /\
                                         MH.word_in_chunk (Seq.index mh0 i) addr /\
                                         (forall (k:nat). k < i ==> ~(MH.word_in_chunk (Seq.index mh0 k) addr))}))
  requires is_indexed_major_heap h (Ghost.reveal mh)
  ensures is_indexed_major_heap h
            (Seq.upd (Ghost.reveal mh) i
              (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh) i) addr v)) **
          pure (MH.write_word_in_major (Ghost.reveal mh) addr v ==
            Some (Seq.upd (Ghost.reveal mh) i
              (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh) i) addr v)))
{
  unfold (is_indexed_major_heap h (Ghost.reveal mh));
  assert (pure (SZ.v h.size == Base.heap_size));
  assert (pure (MH.well_formed_major_heap (Ghost.reveal mh)));
  MH.write_word_at_index_preserves_wf (Ghost.reveal mh) addr v i;
  write_word_in_major_at_chunk_index h addr v i #mh;
  fold (is_indexed_major_heap h
    (Seq.upd (Ghost.reveal mh) i
      (MH.write_word_in_chunk (Seq.index (Ghost.reveal mh) i) addr v)))
}

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
{
  MH.lookup_chunk_index_some (Ghost.reveal mh) addr i;
  assert (pure (forall (k:nat). k < i ==>
    ~(MH.word_in_chunk (Seq.index (Ghost.reveal mh) k) addr)));
  MH.write_word_in_major_at_lookup_index (Ghost.reveal mh) addr v i;
  write_word_in_indexed_major_at_chunk_index h addr v i
    #(Ghost.hide (Ghost.reveal mh))
}
