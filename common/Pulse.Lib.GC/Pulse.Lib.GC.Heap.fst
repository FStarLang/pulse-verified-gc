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
/// Constants (imported from Pulse.Spec.GC.Base for type alignment)
/// ---------------------------------------------------------------------------

/// Re-export from Base so spec heap == Pulse heap_state
module Base = Pulse.Spec.GC.Base
module SpecHeap = Pulse.Spec.GC.Heap

/// Machine word size in bytes (8 bytes = 64 bits)
let mword : U64.t = Base.mword

/// Heap size in bytes — shared with spec so heap_state == Base.heap
let heap_size : pos = Base.heap_size

/// Platform assumption: size_t is at least 64 bits (true on all 64-bit platforms)
assume val platform_fits_u64 : squash SZ.fits_u64

/// Heap size as SizeT
let heap_size_sz : (n:SZ.t{SZ.v n == heap_size}) = 
  SZ.fits_u64_implies_fits heap_size;
  SZ.uint_to_t heap_size

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

/// Predicate form for backward compatibility
let is_hp_addr (addr: U64.t) : prop =
  U64.v addr >= 0 /\
  U64.v addr < heap_size /\
  U64.v addr % U64.v mword == 0

/// Object address - alias for Base.obj_addr (hp_addr with room for header)
let obj_addr = Base.obj_addr

/// Value address - any address within heap bounds
let is_val_addr (addr: U64.t) : prop =
  U64.v addr >= 0 /\
  U64.v addr < heap_size

type val_addr = addr:U64.t{is_val_addr addr}

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

/// Helper: convert U8 to U64 (same as SpecHeap.uint8_to_uint64)
let uint8_to_uint64 (x: U8.t) : U64.t = SpecHeap.uint8_to_uint64 x

/// Helper: convert U64 to U8 (same as SpecHeap.uint64_to_uint8)
let uint64_to_uint8 (x: U64.t) : U8.t = SpecHeap.uint64_to_uint8 x

/// Combine 8 bytes into a 64-bit word (same as SpecHeap.combine_bytes)
let combine_bytes (b0 b1 b2 b3 b4 b5 b6 b7: U8.t) : U64.t =
  SpecHeap.combine_bytes b0 b1 b2 b3 b4 b5 b6 b7

/// Specification for read_word — same as Spec.Heap.read_word on the byte sequence
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
  = SpecHeap.read_word_spec s addr

/// Specification for write_word
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

/// Seq.upd/index roundtrip for non-overlapping writes
let upd_index_same (s: Seq.seq U8.t) (i: nat{i < Seq.length s}) (v: U8.t)
  : Lemma (Seq.index (Seq.upd s i v) i == v) = ()

let upd_index_diff (s: Seq.seq U8.t) (i j: nat{i < Seq.length s /\ j < Seq.length s /\ i <> j}) (v: U8.t)
  : Lemma (Seq.index (Seq.upd s i v) j == Seq.index s j) = ()

/// After 8 sequential updates, reading at each position gives the written value
#push-options "--z3rlimit 50"
let spec_write_read_byte (s: heap_state) 
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
#pop-options

/// ---------------------------------------------------------------------------
/// Byte decompose/recompose roundtrip (bitvector proof)
/// ---------------------------------------------------------------------------
///
/// Proves: combine_bytes(decompose(v)) == v
/// Strategy: nth-level bitvector reasoning — each byte occupies a disjoint
/// 8-bit window, so OR-ing them back recovers every bit of v.

module UInt = FStar.UInt

/// nth of 255: bit i is set iff i >= 56 (i.e., in the low byte)
private let nth_255 (i: nat{i < 64})
  : Lemma (UInt.nth #64 255 i == (i >= 56))
  = assert_norm (pow2 8 - 1 == 255);
    UInt.logand_mask #64 255 8;
    UInt.pow2_nth_lemma #64 8 i

/// Byte k of w, shifted back: has bit i = nth w i in window [56-8k, 64-8k)
private let byte_term_nth (w: UInt.uint_t 64) (s: nat{s < 64 /\ s % 8 == 0}) (i: nat{i < 64})
  : Lemma (
      let masked = UInt.logand #64 (UInt.shift_right #64 w s) 255 in
      let term = UInt.shift_left #64 masked s in
      UInt.nth #64 term i == (if (56 - s) <= i && i < (64 - s) then UInt.nth #64 w i else false))
  = let shifted = UInt.shift_right #64 w s in
    let masked = UInt.logand #64 shifted 255 in
    if i >= 64 - s then
      UInt.shift_left_lemma_1 #64 masked s i
    else begin
      UInt.shift_left_lemma_2 #64 masked s i;
      let j = i + s in
      UInt.logand_definition #64 shifted 255 j;
      nth_255 j;
      if j < 56 then ()
      else UInt.shift_right_lemma_2 #64 w s j
    end

/// Pure uint_t 64 version of the OR chain (left-associative, matching |^ )
private let or_bytes (t0 t1 t2 t3 t4 t5 t6 t7: UInt.uint_t 64) : UInt.uint_t 64 =
  let open UInt in
  logor #64 (logor #64 (logor #64 (logor #64 (logor #64 (logor #64 (logor #64 t0 t1) t2) t3) t4) t5) t6) t7

/// Unfold left-associative OR chain for bit i
private let or_bytes_nth (t0 t1 t2 t3 t4 t5 t6 t7: UInt.uint_t 64) (i: nat{i < 64})
  : Lemma (UInt.nth #64 (or_bytes t0 t1 t2 t3 t4 t5 t6 t7) i ==
           (UInt.nth #64 t0 i || UInt.nth #64 t1 i || UInt.nth #64 t2 i || UInt.nth #64 t3 i ||
            UInt.nth #64 t4 i || UInt.nth #64 t5 i || UInt.nth #64 t6 i || UInt.nth #64 t7 i))
  = UInt.logor_definition #64 t0 t1 i;
    UInt.logor_definition #64 (UInt.logor #64 t0 t1) t2 i;
    UInt.logor_definition #64 (UInt.logor #64 (UInt.logor #64 t0 t1) t2) t3 i;
    UInt.logor_definition #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 t0 t1) t2) t3) t4 i;
    UInt.logor_definition #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 t0 t1) t2) t3) t4) t5 i;
    UInt.logor_definition #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 t0 t1) t2) t3) t4) t5) t6 i;
    UInt.logor_definition #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 t0 t1) t2) t3) t4) t5) t6) t7 i

/// Core identity at uint_t 64 level: OR of 8 disjoint byte windows = identity
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
private let or_byte_windows_identity (w: UInt.uint_t 64)
  : Lemma (
    let t0 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 0) 255) 0 in
    let t1 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 8) 255) 8 in
    let t2 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 16) 255) 16 in
    let t3 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 24) 255) 24 in
    let t4 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 32) 255) 32 in
    let t5 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 40) 255) 40 in
    let t6 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 48) 255) 48 in
    let t7 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 56) 255) 56 in
    or_bytes t0 t1 t2 t3 t4 t5 t6 t7 == w)
  = let t0 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 0) 255) 0 in
    let t1 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 8) 255) 8 in
    let t2 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 16) 255) 16 in
    let t3 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 24) 255) 24 in
    let t4 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 32) 255) 32 in
    let t5 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 40) 255) 40 in
    let t6 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 48) 255) 48 in
    let t7 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 56) 255) 56 in
    let aux (i: nat{i < 64}) : Lemma (UInt.nth #64 (or_bytes t0 t1 t2 t3 t4 t5 t6 t7) i == UInt.nth #64 w i) =
      byte_term_nth w 0 i; byte_term_nth w 8 i; byte_term_nth w 16 i; byte_term_nth w 24 i;
      byte_term_nth w 32 i; byte_term_nth w 40 i; byte_term_nth w 48 i; byte_term_nth w 56 i;
      or_bytes_nth t0 t1 t2 t3 t4 t5 t6 t7 i
    in
    FStar.Classical.forall_intro aux;
    UInt.nth_lemma #64 (or_bytes t0 t1 t2 t3 t4 t5 t6 t7) w
#pop-options

/// Bridge: combine_bytes(decompose(v)) == v
/// Connects U64.t-level combine_bytes with uint_t-level or_byte_windows_identity
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"
let combine_decompose_identity (v: U64.t)
  : Lemma (combine_bytes
    (uint64_to_uint8 v)
    (uint64_to_uint8 (U64.shift_right v 8ul))
    (uint64_to_uint8 (U64.shift_right v 16ul))
    (uint64_to_uint8 (U64.shift_right v 24ul))
    (uint64_to_uint8 (U64.shift_right v 32ul))
    (uint64_to_uint8 (U64.shift_right v 40ul))
    (uint64_to_uint8 (U64.shift_right v 48ul))
    (uint64_to_uint8 (U64.shift_right v 56ul))
    == v)
  = let w = U64.v v in
    assert_norm (pow2 8 == 256);
    // Bridge: x % 256 == logand x 255 (connects uint64_to_uint8 with logand)
    UInt.logand_mask #64 w 8;
    UInt.logand_mask #64 (UInt.shift_right #64 w 8) 8;
    UInt.logand_mask #64 (UInt.shift_right #64 w 16) 8;
    UInt.logand_mask #64 (UInt.shift_right #64 w 24) 8;
    UInt.logand_mask #64 (UInt.shift_right #64 w 32) 8;
    UInt.logand_mask #64 (UInt.shift_right #64 w 40) 8;
    UInt.logand_mask #64 (UInt.shift_right #64 w 48) 8;
    UInt.logand_mask #64 (UInt.shift_right #64 w 56) 8;
    or_byte_windows_identity w
#pop-options

/// Read-after-write: reading back from the same address yields the written value
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"
let read_write_same (s: heap_state)
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
    combine_decompose_identity v
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

/// hp_addr + 8 <= heap_size (for spec_read_word/spec_write_word well-typedness)
let hp_addr_plus_8 (addr: hp_addr) 
  : Lemma (U64.v addr + 8 <= heap_size)
  = assert (U64.v addr < heap_size);
    assert (U64.v addr % 8 == 0);
    // addr % 8 == 0 /\ addr < heap_size /\ heap_size % 8 == 0 ==> addr + 8 <= heap_size
    assert_norm (heap_size % 8 == 0)

/// Read a 64-bit word from the heap (little-endian)
/// Reads 8 consecutive bytes and combines them
fn read_word (h: heap_t) (addr: hp_addr)
  requires is_heap h 's
  returns v: U64.t
  ensures is_heap h 's ** 
          pure (v == spec_read_word 's (U64.v addr))
{
  hp_addr_plus_8 addr;
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
  
  assert (pure (
    b0 == Seq.index 's (U64.v addr) /\
    b1 == Seq.index 's (U64.v addr + 1) /\
    b2 == Seq.index 's (U64.v addr + 2) /\
    b3 == Seq.index 's (U64.v addr + 3) /\
    b4 == Seq.index 's (U64.v addr + 4) /\
    b5 == Seq.index 's (U64.v addr + 5) /\
    b6 == Seq.index 's (U64.v addr + 6) /\
    b7 == Seq.index 's (U64.v addr + 7)
  ));
  
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
  hp_addr_plus_8 addr;
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
#push-options "--z3rlimit 50"
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
#pop-options

// free_heap omitted: Pulse.Lib.Array.PtsTo.free requires is_full_array
// which is not easily provable from is_heap. Not used by any module.

/// ---------------------------------------------------------------------------
/// Address arithmetic helpers
/// ---------------------------------------------------------------------------

/// Compute header address from field address
/// field_addr = header_addr + mword, so header_addr = field_addr - mword
let hd_address (f_addr: U64.t{U64.v f_addr >= U64.v mword /\ U64.v f_addr < heap_size /\ U64.v f_addr % U64.v mword == 0}) : hp_addr =
  U64.sub f_addr mword

/// Compute first field address from header address
let f_address (h_addr: hp_addr) : U64.t =
  U64.add h_addr mword

/// Check if address is word-aligned
let is_word_aligned (addr: U64.t) : bool =
  U64.rem addr mword = 0UL
