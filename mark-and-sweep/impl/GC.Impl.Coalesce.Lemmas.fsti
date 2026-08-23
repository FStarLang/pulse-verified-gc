(*
   Pure F* bridge lemmas for the coalesce implementation.
   Bridges between spec-level coalesce definitions and the imperative loop.
*)

module GC.Impl.Coalesce.Lemmas

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Coalesce
module Alloc = GC.Spec.Allocator
module HeapGraph = GC.Spec.HeapGraph
module Header = GC.Lib.Header

/// ---------------------------------------------------------------------------
/// Objects walk advance lemma
/// ---------------------------------------------------------------------------

/// Objects walk advances by (wosize + 1) * mword  
val objects_advance (start: hp_addr) (g: heap)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      Seq.length (objects start g) > 0)
    (ensures (
      let hdr = read_word g start in
      let wz = getWosize hdr in
      let next_nat = U64.v start + (U64.v wz + 1) * U64.v mword in
      next_nat <= heap_size /\
      next_nat < pow2 64 /\
      (next_nat < heap_size ==>
        Seq.equal (Seq.tail (objects start g)) (objects (U64.uint_to_t next_nat) g)) /\
      (next_nat >= heap_size ==>
        Seq.equal (Seq.tail (objects start g)) Seq.empty)))

/// ---------------------------------------------------------------------------
/// Coalesce step lemmas for the imperative loop
/// ---------------------------------------------------------------------------
/// When objects zero_addr g is non-empty, f_address zero_addr is in it
val objects_mem_at_zero (g: heap)
  : Lemma
    (requires Seq.length g == heap_size /\ Seq.length (objects zero_addr g) > 0)
    (ensures Seq.mem (f_address zero_addr) (objects zero_addr g))
/// zero_fields one-step unfolding
val zero_fields_step
  (g: heap) (addr: U64.t) (n: nat)
  : Lemma
    (requires
      n > 0 /\
      U64.v addr % 8 == 0 /\
      U64.v addr + 8 <= heap_size /\
      U64.v addr + 8 < pow2 64 /\
      Seq.length g == heap_size)
    (ensures
      Alloc.zero_fields g addr n ==
        Alloc.zero_fields (write_word g addr 0UL) (U64.uint_to_t (U64.v addr + 8)) (n - 1))

/// flush_blue suffix preservation: reads at addresses >= end of run are unchanged
val flush_blue_suffix_preserved
  (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (cursor: nat)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      (run_words > 0 ==>
        U64.v first_blue >= U64.v mword /\
        U64.v first_blue < heap_size /\
        U64.v first_blue % U64.v mword == 0 /\
        U64.v first_blue - U64.v mword + run_words * U64.v mword == cursor))
    (ensures (
      let (g', _) = flush_blue g first_blue run_words fp in
      forall (addr: hp_addr). U64.v addr >= cursor ==>
        read_word g' addr == read_word g addr))

/// Bridge: impl makeHeader == spec makeHeader (same value, different defs)
val makeHeader_bridge (wz: wosize) (c: color) (tag: U64.t{U64.v tag < 256})
  : Lemma (GC.Impl.Object.makeHeader wz c tag == GC.Spec.Object.makeHeader wz c tag)

/// Bridge: set_field g fb 1UL fp == write_word g fb fp (for obj_addr fb)
val set_field_1_eq_write_word
  (g: heap) (fb: obj_addr) (fp: U64.t)
  : Lemma
    (requires U64.v (hd_address fb) + U64.v mword * 2 <= heap_size)
    (ensures HeapGraph.set_field g fb 1UL fp == write_word g fb fp)
/// Bridge lemmas: flush_blue equals chain of write operations for each branch.
/// Split into three lemmas to avoid refined-type scoping issues.

/// Case wz=0 (rw=1): just header write, no link
val flush_blue_impl_wz0
  (g: heap) (fb: obj_addr) (fp: U64.t) (g1: heap)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      U64.v fb - U64.v mword + 1 * U64.v mword <= heap_size /\
      g1 == write_word g (hd_address fb) (makeHeader 0UL Header.Blue 0UL))
    (ensures flush_blue g fb 1 fp == (g1, fp))

/// Case wz=1 (rw=2): header + link, no zeroing
val flush_blue_impl_wz1
  (g: heap) (fb: obj_addr) (fp: U64.t) (g1 g2: heap)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      U64.v fb - U64.v mword + 2 * U64.v mword <= heap_size /\
      g1 == write_word g (hd_address fb) (makeHeader 1UL Header.Blue 0UL) /\
      Seq.length g1 == heap_size /\
      g2 == write_word g1 fb fp)
    (ensures flush_blue g fb 2 fp == (g2, fb))

/// Case wz>=2 (rw>=3): header + link + zeroing
val flush_blue_impl_wz_ge2
  (g: heap) (fb: obj_addr) (wz: wosize{U64.v wz >= 2}) (fp: U64.t) (g1 g2 g3: heap)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      U64.v fb - U64.v mword + (U64.v wz + 1) * U64.v mword <= heap_size /\
      g1 == write_word g (hd_address fb) (makeHeader wz Header.Blue 0UL) /\
      Seq.length g1 == heap_size /\
      g2 == write_word g1 fb fp /\
      Seq.length g2 == heap_size /\
      U64.v fb + U64.v mword < pow2 64 /\
      g3 == Alloc.zero_fields g2 (U64.add fb mword) (U64.v wz - 1))
    (ensures flush_blue g fb (U64.v wz + 1) fp == (g3, fb))
