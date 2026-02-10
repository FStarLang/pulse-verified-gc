(*
   Pulse GC - Heap Module
   
   This module defines the core heap type and operations for the
   verified garbage collector, migrated from Low* to Pulse.
   
   Based on: Proofs/Spec.Heap.fsti and Proofs/Impl.GC_closure_infix_ver3.fsti
*)

module Pulse.Lib.GC.Heap

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq

/// ---------------------------------------------------------------------------
/// Constants
/// ---------------------------------------------------------------------------

/// Machine word size in bytes (8 bytes = 64 bits)
let mword : U64.t = 8UL

/// Heap size in bytes (configurable, default 1MB)
let heap_size : pos = 1048576  // 1MB = 1024 * 1024

/// Heap size as SizeT
let heap_size_sz : SZ.t = SZ.uint_to_t heap_size

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

/// Heap pointer address - must be word-aligned and within bounds
let is_hp_addr (addr: U64.t) : prop =
  U64.v addr >= 0 /\
  U64.v addr < heap_size /\
  U64.v addr % U64.v mword == 0

type hp_addr = addr:U64.t{is_hp_addr addr}

/// Value address - any address within heap bounds
let is_val_addr (addr: U64.t) : prop =
  U64.v addr >= 0 /\
  U64.v addr < heap_size

type val_addr = addr:U64.t{is_val_addr addr}

/// ---------------------------------------------------------------------------
/// Heap predicate
/// ---------------------------------------------------------------------------

/// The heap predicate: heap contains a sequence of bytes
let is_heap (h: heap_t) (s: Seq.seq U8.t) : slprop =
  pts_to h.data s **
  pure (Seq.length s == heap_size /\ SZ.v h.size == heap_size)

/// ---------------------------------------------------------------------------
/// Pure helper functions (must be defined before fn definitions)
/// ---------------------------------------------------------------------------

/// Helper: convert U8 to U64
let uint8_to_uint64 (x: U8.t) : U64.t = 
  U64.uint_to_t (U8.v x)

/// Helper: convert U64 to U8 (truncate to low 8 bits)
let uint64_to_uint8 (x: U64.t) : U8.t =
  U8.uint_to_t (U64.v x % 256)

/// Combine 8 bytes into a 64-bit word (little-endian)
let combine_bytes (b0 b1 b2 b3 b4 b5 b6 b7: U8.t) : U64.t =
  let open U64 in
  let v0 = uint8_to_uint64 b0 in
  let v1 = uint8_to_uint64 b1 <<^ 8ul in
  let v2 = uint8_to_uint64 b2 <<^ 16ul in
  let v3 = uint8_to_uint64 b3 <<^ 24ul in
  let v4 = uint8_to_uint64 b4 <<^ 32ul in
  let v5 = uint8_to_uint64 b5 <<^ 40ul in
  let v6 = uint8_to_uint64 b6 <<^ 48ul in
  let v7 = uint8_to_uint64 b7 <<^ 56ul in
  v0 |^ v1 |^ v2 |^ v3 |^ v4 |^ v5 |^ v6 |^ v7

/// Specification for read_word
let spec_read_word (s: Seq.seq U8.t{Seq.length s >= 8}) (addr: nat{addr + 8 <= Seq.length s}) : U64.t =
  let b0 = Seq.index s addr in
  let b1 = Seq.index s (addr + 1) in
  let b2 = Seq.index s (addr + 2) in
  let b3 = Seq.index s (addr + 3) in
  let b4 = Seq.index s (addr + 4) in
  let b5 = Seq.index s (addr + 5) in
  let b6 = Seq.index s (addr + 6) in
  let b7 = Seq.index s (addr + 7) in
  combine_bytes b0 b1 b2 b3 b4 b5 b6 b7

/// Specification for write_word
let spec_write_word (s: Seq.seq U8.t{Seq.length s >= 8}) 
                    (addr: nat{addr + 8 <= Seq.length s}) 
                    (v: U64.t) 
    : Seq.seq U8.t =
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

/// Seq.upd/index roundtrip for non-overlapping writes
let upd_index_same (s: Seq.seq U8.t) (i: nat{i < Seq.length s}) (v: U8.t)
  : Lemma (Seq.index (Seq.upd s i v) i == v) = ()

let upd_index_diff (s: Seq.seq U8.t) (i j: nat{i < Seq.length s /\ j < Seq.length s /\ i <> j}) (v: U8.t)
  : Lemma (Seq.index (Seq.upd s i v) j == Seq.index s j) = ()

/// After 8 sequential updates, reading at each position gives the written value
let spec_write_read_byte (s: Seq.seq U8.t{Seq.length s >= 8}) 
                         (addr: nat{addr + 8 <= Seq.length s})
                         (v: U64.t) (k: nat{k < 8})
  : Lemma (Seq.index (spec_write_word s addr v) (addr + k) ==
           (match k with
            | 0 -> uint64_to_uint8 v
            | 1 -> uint64_to_uint8 (U64.shift_right v 8ul)
            | 2 -> uint64_to_uint8 (U64.shift_right v 16ul)
            | 3 -> uint64_to_uint8 (U64.shift_right v 24ul)
            | 4 -> uint64_to_uint8 (U64.shift_right v 32ul)
            | 5 -> uint64_to_uint8 (U64.shift_right v 40ul)
            | 6 -> uint64_to_uint8 (U64.shift_right v 48ul)
            | _ -> uint64_to_uint8 (U64.shift_right v 56ul)))
  = ()

/// Read-after-write: reading back from the same address yields the written value
#push-options "--z3rlimit 50"
let read_write_same (s: Seq.seq U8.t{Seq.length s >= 8}) 
                    (addr: nat{addr + 8 <= Seq.length s}) 
                    (v: U64.t)
  : Lemma (spec_read_word (spec_write_word s addr v) addr == v)
  = spec_write_read_byte s addr v 0;
    spec_write_read_byte s addr v 1;
    spec_write_read_byte s addr v 2;
    spec_write_read_byte s addr v 3;
    spec_write_read_byte s addr v 4;
    spec_write_read_byte s addr v 5;
    spec_write_read_byte s addr v 6;
    spec_write_read_byte s addr v 7;
    // After showing each byte reads back correctly, 
    // combine_bytes ∘ decompose = identity follows by SMT
    admit()  // TODO: bitvector roundtrip (combine ∘ decompose = id)
#pop-options

/// ---------------------------------------------------------------------------
/// Read operations
/// ---------------------------------------------------------------------------

/// Read a single byte from the heap
fn read_byte (h: heap_t) (addr: val_addr)
  requires is_heap h 's
  returns v: U8.t
  ensures is_heap h 's ** pure (v == Seq.index 's (U64.v addr))
{
  unfold is_heap;
  let idx = SZ.uint64_to_sizet addr;
  let v = h.data.(idx);
  fold (is_heap h 's);
  v
}

/// Read a 64-bit word from the heap (little-endian)
/// Reads 8 consecutive bytes and combines them
fn read_word (h: heap_t) (addr: hp_addr)
  requires is_heap h 's
  returns v: U64.t
  ensures is_heap h 's ** 
          pure (v == spec_read_word 's (U64.v addr))
{
  unfold is_heap;
  let base = SZ.uint64_to_sizet addr;
  
  // Read 8 bytes
  let b0 = h.data.(base);
  let b1 = h.data.(SZ.add base 1sz);
  let b2 = h.data.(SZ.add base 2sz);
  let b3 = h.data.(SZ.add base 3sz);
  let b4 = h.data.(SZ.add base 4sz);
  let b5 = h.data.(SZ.add base 5sz);
  let b6 = h.data.(SZ.add base 6sz);
  let b7 = h.data.(SZ.add base 7sz);
  
  // Combine into 64-bit word (little-endian)
  let v = combine_bytes b0 b1 b2 b3 b4 b5 b6 b7;
  
  fold (is_heap h 's);
  v
}

/// ---------------------------------------------------------------------------
/// Write operations
/// ---------------------------------------------------------------------------

/// Write a single byte to the heap
fn write_byte (h: heap_t) (addr: val_addr) (v: U8.t)
  requires is_heap h 's
  ensures is_heap h (Seq.upd 's (U64.v addr) v)
{
  unfold is_heap;
  let idx = SZ.uint64_to_sizet addr;
  h.data.(idx) <- v;
  fold (is_heap h (Seq.upd 's (U64.v addr) v))
}

/// Write a 64-bit word to the heap (little-endian)
fn write_word (h: heap_t) (addr: hp_addr) (v: U64.t)
  requires is_heap h 's
  ensures is_heap h (spec_write_word 's (U64.v addr) v)
{
  unfold is_heap;
  let base = SZ.uint64_to_sizet addr;
  
  // Split into 8 bytes (little-endian)
  let b0 = uint64_to_uint8 v;
  let b1 = uint64_to_uint8 (U64.shift_right v 8ul);
  let b2 = uint64_to_uint8 (U64.shift_right v 16ul);
  let b3 = uint64_to_uint8 (U64.shift_right v 24ul);
  let b4 = uint64_to_uint8 (U64.shift_right v 32ul);
  let b5 = uint64_to_uint8 (U64.shift_right v 40ul);
  let b6 = uint64_to_uint8 (U64.shift_right v 48ul);
  let b7 = uint64_to_uint8 (U64.shift_right v 56ul);
  
  // Write 8 bytes
  h.data.(base) <- b0;
  h.data.(SZ.add base 1sz) <- b1;
  h.data.(SZ.add base 2sz) <- b2;
  h.data.(SZ.add base 3sz) <- b3;
  h.data.(SZ.add base 4sz) <- b4;
  h.data.(SZ.add base 5sz) <- b5;
  h.data.(SZ.add base 6sz) <- b6;
  h.data.(SZ.add base 7sz) <- b7;
  
  fold (is_heap h (spec_write_word 's (U64.v addr) v))
}

/// ---------------------------------------------------------------------------
/// Heap allocation
/// ---------------------------------------------------------------------------

/// Allocate a new heap
fn alloc_heap (_: unit)
  requires emp
  returns h: heap_t
  ensures is_heap h (Seq.create heap_size 0uy)
{
  let data = alloc 0uy heap_size_sz;
  let h : heap_t = { data; size = heap_size_sz };
  rewrite each data as h.data;
  fold (is_heap h (Seq.create (SZ.v heap_size_sz) 0uy));
  rewrite (is_heap h (Seq.create (SZ.v heap_size_sz) 0uy))
       as (is_heap h (Seq.create heap_size 0uy));
  h
}

/// Free a heap
fn free_heap (h: heap_t)
  requires exists* s. is_heap h s
  ensures emp
{
  unfold is_heap;
  free h.data
}

/// ---------------------------------------------------------------------------
/// Address arithmetic helpers
/// ---------------------------------------------------------------------------

/// Compute header address from field address
/// field_addr = header_addr + mword, so header_addr = field_addr - mword
let hd_address (f_addr: U64.t{U64.v f_addr >= U64.v mword}) : hp_addr =
  U64.sub f_addr mword

/// Compute first field address from header address
let f_address (h_addr: hp_addr) : U64.t =
  U64.add h_addr mword

/// Check if address is word-aligned
let is_word_aligned (addr: U64.t) : bool =
  U64.rem addr mword = 0UL
