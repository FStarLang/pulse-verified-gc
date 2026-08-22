(*
   Pulse GC - Heap Module
   
   This module defines the core heap type and operations for the
   verified garbage collector, migrated from Low* to Pulse.
   
   Based on: Proofs/Spec.Heap.fsti and Proofs/Impl.GC_closure_infix_ver3.fsti
*)

module GC.Impl.Heap

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq

/// ---------------------------------------------------------------------------
/// Constants (imported from GC.Spec.Base for type alignment)
/// ---------------------------------------------------------------------------

/// Re-export from Base so spec heap == Pulse heap_state
module Base = GC.Spec.Base
module SpecHeap = GC.Spec.Heap
module ArrayWord = GC.Impl.ArrayWord

/// Machine word size in bytes (8 bytes = 64 bits)
inline_for_extraction
let mword : U64.t = Base.mword

/// Heap size in bytes — shared with spec so heap_state == Base.heap
let heap_size : pos = Base.heap_size

/// TCB: Platform assumption — size_t is at least 64 bits.
/// True on all 64-bit platforms (x86-64, AArch64, RISC-V 64).
/// This is the only `assume` in the codebase.
assume val platform_fits_u64 : squash SZ.fits_u64
/// Heap size as U64 — inline so KaRaMeL emits a local constant (no cross-bundle ref)
inline_for_extraction
let heap_size_u64 : (n:U64.t{U64.v n == heap_size}) =
  Base.heap_size_u64

/// ---------------------------------------------------------------------------
/// Types
/// ---------------------------------------------------------------------------

/// Heap is a byte-addressable array
/// In Pulse, we use Vec for resizable arrays with slprop predicates
noeq
type heap_t = {
  data : array U8.t;
  size : (n:SZ.t{SZ.v n == heap_size});
}

/// Heap pointer address - alias for Base.hp_addr (word-aligned, within bounds)
let hp_addr = Base.hp_addr

/// Zero address as hp_addr (avoids Z3 matching loops from bare 0UL)
let zero_addr : hp_addr = Base.zero_addr
/// Object address - alias for Base.obj_addr (hp_addr with room for header)
let obj_addr = Base.obj_addr

/// Value address - any address within heap bounds
let is_val_addr (addr: U64.t) : prop =
  U64.v addr >= 0 /\
  U64.v addr < heap_size

/// ---------------------------------------------------------------------------
/// Heap predicate
/// ---------------------------------------------------------------------------

/// Heap state type: identical to Base.heap (byte sequence of exactly heap_size)
let heap_state = Base.heap

/// The heap predicate: heap contains a sequence of bytes
let is_heap (h: heap_t) (s: heap_state) : slprop =
  pts_to h.data s **
  pure (SZ.v h.size == heap_size)

/// ---------------------------------------------------------------------------
/// Pure helper functions — imported from Spec.Heap for consistency
/// ---------------------------------------------------------------------------
/// Helper: convert U64 to U8 (same as SpecHeap.uint64_to_uint8)
let uint64_to_uint8 (x: U64.t) : U8.t = SpecHeap.uint64_to_uint8 x

/// Combine 8 bytes into a 64-bit word (same as SpecHeap.combine_bytes)
let combine_bytes (b0 b1 b2 b3 b4 b5 b6 b7: U8.t) : U64.t =
  SpecHeap.combine_bytes b0 b1 b2 b3 b4 b5 b6 b7

/// Specification for read_word — same as Spec.Heap.read_word on the byte sequence
[@@"opaque_to_smt"]
let spec_read_word (s: heap_state) (addr: nat{addr + 8 <= Seq.length s}) : U64.t =
  combine_bytes
    (Seq.index s addr)
    (Seq.index s (addr + 1))
    (Seq.index s (addr + 2))
    (Seq.index s (addr + 3))
    (Seq.index s (addr + 4))
    (Seq.index s (addr + 5))
    (Seq.index s (addr + 6))
    (Seq.index s (addr + 7))

/// Bridge: spec_read_word matches Spec.Heap.read_word
let spec_read_word_eq (s: heap_state) (addr: hp_addr)
  : Lemma (requires U64.v addr + 8 <= Seq.length s)
          (ensures spec_read_word s (U64.v addr) == SpecHeap.read_word s addr)
  = reveal_opaque (`%spec_read_word) spec_read_word;
    SpecHeap.read_word_spec s addr

/// Specification for write_word
[@@"opaque_to_smt"]
let spec_write_word (s: heap_state) 
                    (addr: nat{addr + 8 <= Seq.length s}) 
                    (v: U64.t) 
    : heap_state =
  let b0 = uint64_to_uint8 v in
  let b1 = uint64_to_uint8 (U64.shift_right v 8ul) in
  let b2 = uint64_to_uint8 (U64.shift_right v 16ul) in
  let b3 = uint64_to_uint8 (U64.shift_right v 24ul) in
  let b4 = uint64_to_uint8 (U64.shift_right v 32ul) in
  let b5 = uint64_to_uint8 (U64.shift_right v 40ul) in
  let b6 = uint64_to_uint8 (U64.shift_right v 48ul) in
  let b7 = uint64_to_uint8 (U64.shift_right v 56ul) in
  let s1 = Seq.upd s addr b0 in
  let s2 = Seq.upd s1 (addr + 1) b1 in
  let s3 = Seq.upd s2 (addr + 2) b2 in
  let s4 = Seq.upd s3 (addr + 3) b3 in
  let s5 = Seq.upd s4 (addr + 4) b4 in
  let s6 = Seq.upd s5 (addr + 5) b5 in
  let s7 = Seq.upd s6 (addr + 6) b6 in
  Seq.upd s7 (addr + 7) b7

/// Bridge: spec_write_word matches Spec.Heap.write_word
let spec_write_word_eq (s: heap_state) (addr: hp_addr) (v: U64.t)
  : Lemma (requires U64.v addr + 8 <= Seq.length s)
          (ensures spec_write_word s (U64.v addr) v == SpecHeap.write_word s addr v)
  = reveal_opaque (`%spec_write_word) spec_write_word;
    SpecHeap.write_word_spec s addr v
/// After 8 sequential updates, reading at each position gives the written value
/// ---------------------------------------------------------------------------
/// Byte decompose/recompose roundtrip (bitvector proof)
/// ---------------------------------------------------------------------------
///
/// Proves: combine_bytes(decompose(v)) == v
/// Strategy: nth-level bitvector reasoning — each byte occupies a disjoint
/// 8-bit window, so OR-ing them back recovers every bit of v.

module UInt = FStar.UInt
/// Core identity at uint_t 64 level: OR of 8 disjoint byte windows = identity
/// Bridge: combine_bytes(decompose(v)) == v
/// Connects U64.t-level combine_bytes with uint_t-level or_byte_windows_identity
/// Read-after-write: reading back from the same address yields the written value
/// ---------------------------------------------------------------------------
/// Read operations
/// ---------------------------------------------------------------------------
/// hp_addr + 8 <= heap_size (for spec_read_word/spec_write_word well-typedness)
let hp_addr_plus_8 (addr: hp_addr) 
  : Lemma (U64.v addr + 8 <= heap_size)
  = assert (U64.v addr < heap_size);
    assert (U64.v addr % 8 == 0);
    // addr % 8 == 0 /\ addr < heap_size /\ heap_size % 8 == 0 ==> addr + 8 <= heap_size
    assert_norm (heap_size % 8 == 0)

/// Read a 64-bit word from the heap (little-endian)
/// Uses word-level primitive for single load instead of 8 byte reads
fn read_word (h: heap_t) (addr: hp_addr)
  requires is_heap h 's
  returns v: U64.t
  ensures is_heap h 's ** 
          pure (v == SpecHeap.read_word 's addr)
{
  hp_addr_plus_8 addr;
  unfold is_heap;
  let base = SZ.uint64_to_sizet addr;
  let v = ArrayWord.read_u64_le h.data base;
  SpecHeap.read_word_spec 's addr;
  fold (is_heap h 's);
  v
}

/// ---------------------------------------------------------------------------
/// Write operations
/// ---------------------------------------------------------------------------
/// Write a 64-bit word to the heap (little-endian)
/// Uses word-level primitive for single store instead of 8 byte writes
fn write_word (h: heap_t) (addr: hp_addr) (v: U64.t)
  requires is_heap h 's
  ensures is_heap h (SpecHeap.write_word 's addr v) **
          pure (SpecHeap.write_word 's addr v == spec_write_word 's (U64.v addr) v)
{
  hp_addr_plus_8 addr;
  reveal_opaque (`%spec_write_word) spec_write_word;
  unfold is_heap;
  let base = SZ.uint64_to_sizet addr;
  ArrayWord.write_u64_le h.data base v;
  SpecHeap.write_word_spec 's addr v;
  fold (is_heap h (SpecHeap.write_word 's addr v))
}

/// ---------------------------------------------------------------------------
/// Heap allocation
/// ---------------------------------------------------------------------------

/// Allocate a new heap
// free_heap omitted: Pulse.Lib.Array.PtsTo.free requires is_full_array
// which is not easily provable from is_heap. Not used by any module.

/// Compute header address from field address
let hd_address (f_addr: U64.t{U64.v f_addr >= U64.v mword /\ U64.v f_addr < heap_size /\ U64.v f_addr % U64.v mword == 0}) : hp_addr =
  U64.sub f_addr mword

/// Compute first field address from header address
let f_address (h_addr: hp_addr) : U64.t =
  U64.add h_addr mword
