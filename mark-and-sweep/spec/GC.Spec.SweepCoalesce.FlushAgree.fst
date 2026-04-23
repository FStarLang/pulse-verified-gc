/// ---------------------------------------------------------------------------
/// GC.Spec.SweepCoalesceFinal — Lemmas for sweep-coalesce composition
/// ---------------------------------------------------------------------------
///
/// Provides:
///   1. read_word_bytes_agree        — Word agreement implies byte agreement
///   2. heaps_word_agree_implies_equal — Full word agreement implies heap equality
///   3. flush_blue_pair_agree        — flush_blue result is heap-independent
///                                     (modulo outside-range agreement)

module GC.Spec.SweepCoalesce.FlushAgree

open FStar.Seq
open FStar.Mul

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Lib.Header

module SpecCoalesce = GC.Spec.Coalesce
module SCH = GC.Spec.SweepCoalesce.Helpers
module HeapGraph = GC.Spec.HeapGraph
module Alloc = GC.Spec.Allocator
module ML = FStar.Math.Lemmas

#set-options "--split_queries always --z3rlimit 50 --fuel 1 --ifuel 1"

/// ===========================================================================
/// Helper: write_word byte at addr+k depends only on the value v,
/// not on the input heap.
/// ===========================================================================

/// After write_word_spec, both write_word results are chains of Seq.upd
/// writing the same decomposition of v. At position addr+k, the chain
/// produces the k-th byte of v regardless of the base heap.
#push-options "--z3rlimit 20"
let write_word_byte_at (g1 g2: heap) (addr: hp_addr) (v: U64.t) (k: nat{k < 8})
  : Lemma (Seq.index (write_word g1 addr v) (U64.v addr + k) ==
           Seq.index (write_word g2 addr v) (U64.v addr + k))
  = write_word_spec g1 addr v;
    write_word_spec g2 addr v
#pop-options

/// ===========================================================================
/// Lemma 1: read_word_bytes_agree
/// ===========================================================================

/// If two heaps agree at a word-aligned address (read_word), then they
/// agree at each of the 8 individual bytes.
///
/// Proof: write_word_id says write_word g addr (read_word g addr) == g.
/// So Seq.index g (addr+k) == Seq.index (write_word g addr v) (addr+k).
/// And write_word_byte_at says the byte at addr+k depends only on v.

#push-options "--z3rlimit 20"
let read_word_bytes_agree (h1 h2: heap) (addr: hp_addr) (k: nat{k < 8})
  : Lemma
    (requires read_word h1 addr == read_word h2 addr)
    (ensures Seq.index h1 (U64.v addr + k) == Seq.index h2 (U64.v addr + k))
  = let v = read_word h1 addr in
    SCH.write_word_id h1 addr;
    SCH.write_word_id h2 addr;
    // h1 == write_word h1 addr v, h2 == write_word h2 addr v
    write_word_byte_at h1 h2 addr v k
#pop-options

/// ===========================================================================
/// Lemma 2: heaps_word_agree_implies_equal
/// ===========================================================================

/// If two heaps agree at every word-aligned address, they are equal.
///
/// Proof: every byte index i can be written as a + k where a = i - (i%8)
/// is word-aligned and k = i%8 < 8. Then read_word_bytes_agree gives
/// byte equality at i.

let heaps_word_agree_implies_equal (h1 h2: heap)
  : Lemma
    (requires forall (addr: hp_addr). read_word h1 addr == read_word h2 addr)
    (ensures h1 == h2)
  = let aux (i: nat{i < heap_size})
      : Lemma (Seq.index h1 i == Seq.index h2 i)
      = let a = i - i % 8 in
        assert (a % 8 == 0);
        assert (a >= 0 /\ a < heap_size);
        let addr : hp_addr = U64.uint_to_t a in
        read_word_bytes_agree h1 h2 addr (i % 8)
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_elim h1 h2

/// ===========================================================================
/// Helpers for flush_blue determinism
/// ===========================================================================

/// Two different hp_addrs are at least 8 bytes apart
/// (both are multiples of 8, and different multiples differ by >= 8).
private let aligned_neq_disjoint (x y: hp_addr)
  : Lemma (requires x <> y)
          (ensures U64.v x + U64.v mword <= U64.v y \/
                   U64.v y + U64.v mword <= U64.v x)
  = assert (U64.v x % 8 == 0 /\ U64.v y % 8 == 0);
    // x and y are distinct multiples of 8, so |x-y| >= 8
    ()

/// write_word preserves word-level agreement at any hp_addr a:
/// if a is the written address, both results have v;
/// otherwise, the original agreement is preserved.
private let write_word_agree_at
    (h1 h2: heap) (addr: hp_addr) (v: U64.t) (a: hp_addr)
  : Lemma
    (requires a == addr \/ read_word h1 a == read_word h2 a)
    (ensures read_word (write_word h1 addr v) a ==
             read_word (write_word h2 addr v) a)
  = if a = addr then begin
      read_write_same h1 addr v;
      read_write_same h2 addr v
    end else begin
      aligned_neq_disjoint a addr;
      read_write_different h1 addr a v;
      read_write_different h2 addr a v
    end

/// ===========================================================================
/// zero_fields pair agreement
/// ===========================================================================

/// If two heaps agree at position a (or a is inside the zeroed range),
/// then after zero_fields the results also agree at a.
///
/// Inside range: both get 0UL (from the write at each position).
/// Outside range: agreement is preserved through each write_word step.
#push-options "--z3rlimit 20"
private let rec zero_fields_agree_pair
    (h1 h2: heap) (start: U64.t) (n: nat) (a: hp_addr)
  : Lemma
    (requires
      (U64.v start + n * U64.v mword <= heap_size /\
       U64.v start % U64.v mword == 0 /\
       U64.v a >= U64.v start /\
       U64.v a < U64.v start + n * U64.v mword) \/
      read_word h1 a == read_word h2 a)
    (ensures read_word (Alloc.zero_fields h1 start n) a ==
             read_word (Alloc.zero_fields h2 start n) a)
    (decreases n)
  = if n = 0 then ()
    else if U64.v start + 8 > heap_size then ()
    else if U64.v start >= heap_size then ()
    else if U64.v start % 8 <> 0 then ()
    else begin
      let start_hp : hp_addr = start in
      let h1' = write_word h1 start_hp 0UL in
      let h2' = write_word h2 start_hp 0UL in
      if U64.v start + 8 >= pow2 64 then
        // zero_fields returns h1'/h2' after one write
        write_word_agree_at h1 h2 start_hp 0UL a
      else begin
        let next = U64.uint_to_t (U64.v start + 8) in
        if a = start_hp then begin
          // a == start: both have 0UL after the write
          read_write_same h1 start_hp 0UL;
          read_write_same h2 start_hp 0UL;
          // Now h1' and h2' agree at a; use "outside" path in IH
          zero_fields_agree_pair h1' h2' next (n - 1) a
        end else begin
          // a <> start
          // Check if a was in the inside range
          if U64.v start + n * 8 <= heap_size &&
             U64.v start % 8 = 0 &&
             U64.v a >= U64.v start &&
             U64.v a < U64.v start + n * 8
          then begin
            // a is inside [start, start+n*8), a <> start, both aligned
            // => a >= start + 8 = next, and a < start + n*8 = next + (n-1)*8
            // Use first disjunct in IH
            zero_fields_agree_pair h1' h2' next (n - 1) a
          end else begin
            // a is outside; h1,h2 agree at a
            // write at start doesn't affect a since a <> start
            write_word_agree_at h1 h2 start_hp 0UL a;
            // h1',h2' agree at a; use second disjunct in IH
            zero_fields_agree_pair h1' h2' next (n - 1) a
          end
        end
      end
    end
#pop-options

/// ===========================================================================
/// zero_fields read within: zeroed position reads 0
/// (Reproduces private lemma from GC.Spec.Coalesce)
/// ===========================================================================

#push-options "--z3rlimit 20"
private let rec my_zero_fields_read_within
    (g: heap) (start: U64.t) (n: nat) (addr: hp_addr)
  : Lemma
    (requires
      U64.v start + n * U64.v mword <= heap_size /\
      U64.v start % U64.v mword == 0 /\
      U64.v addr >= U64.v start /\
      U64.v addr < U64.v start + n * U64.v mword /\
      U64.v addr % U64.v mword == 0)
    (ensures read_word (Alloc.zero_fields g start n) addr == 0UL)
    (decreases n)
  = if n = 0 then ()
    else begin
      assert (U64.v start + 8 <= heap_size);
      assert (U64.v start < heap_size);
      assert (U64.v start % 8 == 0);
      let g' = write_word g (start <: hp_addr) 0UL in
      if U64.v addr = U64.v start then begin
        read_write_same g (start <: hp_addr) 0UL;
        if U64.v start + 8 >= pow2 64 then ()
        else begin
          let next = U64.uint_to_t (U64.v start + 8) in
          SpecCoalesce.zero_fields_preserves_before g' next (n - 1) addr
        end
      end else begin
        assert (U64.v start + 8 < pow2 64);
        let next = U64.uint_to_t (U64.v start + 8) in
        read_write_different g (start <: hp_addr) addr 0UL;
        my_zero_fields_read_within g' next (n - 1) addr
      end
    end
#pop-options

/// ===========================================================================
/// flush_blue field 1 spec: after flush with rw >= 2, field 1 = fp
/// (Reproduces private lemma from GC.Spec.Coalesce)
/// ===========================================================================

#push-options "--z3rlimit 20 --fuel 2"
private let my_flush_blue_field1
    (g: heap) (fb: obj_addr) (rw: nat) (fp: U64.t)
  : Lemma
    (requires
      rw >= 2 /\
      rw - 1 < pow2 54 /\
      U64.v (hd_address fb) + rw * U64.v mword <= heap_size)
    (ensures read_word (fst (SpecCoalesce.flush_blue g fb rw fp)) fb == fp)
  = let hd = hd_address fb in
    hd_address_spec fb;
    let wz = rw - 1 in
    assert (wz >= 1);
    ML.pow2_lt_compat 64 54;
    let wz_u64 : wosize = U64.uint_to_t wz in
    let hdr = makeHeader wz_u64 Blue 0UL in
    let g1 = write_word g hd hdr in
    assert (U64.v hd + U64.v mword * 2 <= heap_size);
    assert (U64.v (hd_address fb) + U64.v mword * (U64.v 1UL + 1) <= heap_size);
    let field1_addr : hp_addr = U64.add (hd_address fb) (U64.mul mword 1UL) in
    assert (U64.v field1_addr == U64.v fb);
    read_write_different g hd field1_addr hdr;
    let g2 = HeapGraph.set_field g1 fb 1UL fp in
    read_write_same g1 field1_addr fp;
    let zero_start_nat = U64.v fb + U64.v mword in
    if wz >= 2 && zero_start_nat < pow2 64 then begin
      let zero_start = U64.uint_to_t zero_start_nat in
      assert (U64.v field1_addr + U64.v mword <= U64.v zero_start);
      SpecCoalesce.zero_fields_preserves_before g2 zero_start (wz - 1) field1_addr
    end else ()
#pop-options

/// ===========================================================================
/// flush_blue zero fields spec: after flush with rw >= 3, fields 2+ are 0
/// (Reproduces private lemma from GC.Spec.Coalesce)
/// ===========================================================================

#push-options "--z3rlimit 20 --fuel 2"
private let my_flush_blue_field_zero
    (g: heap) (fb: obj_addr) (rw: nat) (fp: U64.t) (a: hp_addr)
  : Lemma
    (requires
      rw >= 3 /\
      rw - 1 < pow2 54 /\
      U64.v (hd_address fb) + rw * U64.v mword <= heap_size /\
      U64.v a >= U64.v fb + U64.v mword /\
      U64.v a < U64.v fb + (rw - 1) * U64.v mword /\
      U64.v a % U64.v mword == 0)
    (ensures read_word (fst (SpecCoalesce.flush_blue g fb rw fp)) a == 0UL)
  = let hd = hd_address fb in
    hd_address_spec fb;
    let wz = rw - 1 in
    assert (wz >= 2);
    ML.pow2_lt_compat 64 54;
    let wz_u64 : wosize = U64.uint_to_t wz in
    let hdr = makeHeader wz_u64 Blue 0UL in
    let g1 = write_word g hd hdr in
    assert (wz >= 1 /\ U64.v hd + U64.v mword * 2 <= heap_size);
    assert (U64.v (hd_address fb) + U64.v mword * (U64.v 1UL + 1) <= heap_size);
    let g2 = HeapGraph.set_field g1 fb 1UL fp in
    let zero_start_nat = U64.v fb + U64.v mword in
    assert (zero_start_nat < pow2 64);
    let zero_start = U64.uint_to_t zero_start_nat in
    assert (U64.v a >= U64.v zero_start);
    assert (U64.v a < U64.v zero_start + (wz - 1) * U64.v mword);
    my_zero_fields_read_within g2 zero_start (wz - 1) a
#pop-options

/// ===========================================================================
/// Lemma 3 (private): flush_blue_word_agree
/// ===========================================================================

/// For any hp_addr a, flush_blue h1 and flush_blue h2 produce the same
/// word at a, provided h1 and h2 agree outside the flush range.
///
/// Outside: flush_blue_preserves_outside + input agreement.
/// Inside header: flush_blue_header_spec (both produce same header).
/// Inside field 1: my_flush_blue_field1 (both produce fp).
/// Inside zero range: my_flush_blue_field_zero (both produce 0UL).

#push-options "--z3rlimit 20 --fuel 2"
private let flush_blue_word_agree
    (h1 h2: heap) (fb: U64.t) (rw: nat) (fp: U64.t) (a: hp_addr)
  : Lemma
    (requires
      (rw > 0 ==>
        (U64.v fb >= U64.v mword /\
         U64.v fb < heap_size /\
         U64.v fb % U64.v mword == 0 /\
         rw - 1 < pow2 54 /\
         U64.v fb - U64.v mword + rw * U64.v mword <= heap_size)) /\
      ((rw = 0 \/
        U64.v a + U64.v mword <= U64.v fb - U64.v mword \/
        U64.v a >= U64.v fb - U64.v mword + rw * U64.v mword) ==>
       read_word h1 a == read_word h2 a))
    (ensures read_word (fst (SpecCoalesce.flush_blue h1 fb rw fp)) a ==
             read_word (fst (SpecCoalesce.flush_blue h2 fb rw fp)) a)
  = if rw = 0 then ()
    else begin
      // fb is a valid obj_addr
      let fb_obj : obj_addr = fb in
      let hd = hd_address fb_obj in
      hd_address_spec fb_obj;
      let hd_nat = U64.v fb - U64.v mword in
      let range_end = hd_nat + rw * U64.v mword in
      if U64.v a + U64.v mword <= hd_nat || U64.v a >= range_end then begin
        // --- Outside case ---
        // flush_blue_preserves_outside: each result equals its input
        SpecCoalesce.flush_blue_preserves_outside h1 fb rw fp a;
        SpecCoalesce.flush_blue_preserves_outside h2 fb rw fp a
        // And inputs agree by hypothesis
      end else begin
        // --- Inside case: a in [hd, hd + rw*8) ---
        if U64.v a = hd_nat then begin
          // a == hd_address(fb): both produce the same merged header
          SpecCoalesce.flush_blue_header_spec h1 fb_obj rw fp;
          SpecCoalesce.flush_blue_header_spec h2 fb_obj rw fp
        end else if U64.v a = U64.v fb then begin
          // a == fb: both produce fp at field 1
          // rw >= 2 follows from: a = fb, a >= hd, a <> hd, both aligned => a >= hd + 8 = fb
          // and a < hd + rw*8, so fb < fb - 8 + rw*8, giving 8 < rw*8, so rw >= 2
          assert (rw >= 2);
          my_flush_blue_field1 h1 fb_obj rw fp;
          my_flush_blue_field1 h2 fb_obj rw fp
        end else begin
          // a > fb and in range: zero fields region
          // a >= fb + 8 (since a > fb and both aligned)
          // a < hd + rw*8 = fb - 8 + rw*8 = fb + (rw-1)*8
          // rw >= 3 (since a >= fb + 8 and a < fb + (rw-1)*8 => 8 < (rw-1)*8 => rw > 2)
          assert (U64.v a >= U64.v fb + U64.v mword);
          assert (U64.v a < U64.v fb + (rw - 1) * U64.v mword);
          assert (rw >= 3);
          my_flush_blue_field_zero h1 fb_obj rw fp a;
          my_flush_blue_field_zero h2 fb_obj rw fp a
        end
      end
    end
#pop-options

/// ===========================================================================
/// Lemma 4: flush_blue_pair_agree
/// ===========================================================================

/// If two heaps agree at all word-aligned addresses outside the flush_blue
/// range, then flush_blue produces identical results for both heaps.
///
/// This combines:
/// - flush_blue_word_agree (word-level agreement at every position)
/// - heaps_word_agree_implies_equal (word agreement → heap equality)
/// - flush_blue_snd_heap_independent (snd is heap-independent)

#push-options "--z3rlimit 20"
let flush_blue_pair_agree (h1 h2: heap) (fb: U64.t) (rw: nat) (fp: U64.t)
  : Lemma
    (requires
      (rw > 0 ==>
        (U64.v fb >= U64.v mword /\
         U64.v fb < heap_size /\
         U64.v fb % U64.v mword == 0 /\
         rw - 1 < pow2 54 /\
         U64.v fb - U64.v mword + rw * U64.v mword <= heap_size)) /\
      (forall (a: hp_addr).
        (rw = 0 \/
         U64.v a + U64.v mword <= U64.v fb - U64.v mword \/
         U64.v a >= U64.v fb - U64.v mword + rw * U64.v mword) ==>
        read_word h1 a == read_word h2 a))
    (ensures SpecCoalesce.flush_blue h1 fb rw fp ==
             SpecCoalesce.flush_blue h2 fb rw fp)
  = // 1. Show fst heaps agree at every word position
    let g1 = fst (SpecCoalesce.flush_blue h1 fb rw fp) in
    let g2 = fst (SpecCoalesce.flush_blue h2 fb rw fp) in
    let word_agree (a: hp_addr)
      : Lemma (read_word g1 a == read_word g2 a)
      = flush_blue_word_agree h1 h2 fb rw fp a
    in
    FStar.Classical.forall_intro word_agree;

    // 2. Lengths preserved (both are heaps, so length == heap_size)
    SpecCoalesce.flush_blue_preserves_length h1 fb rw fp;
    SpecCoalesce.flush_blue_preserves_length h2 fb rw fp;

    // 3. Word agreement → heap equality for fst
    heaps_word_agree_implies_equal g1 g2;

    // 4. snd is heap-independent
    SCH.flush_blue_snd_heap_independent h1 h2 fb rw fp
#pop-options
