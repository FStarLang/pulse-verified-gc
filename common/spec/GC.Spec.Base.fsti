/// ---------------------------------------------------------------------------
/// GC.Spec.Base - Foundational types for verified GC
/// ---------------------------------------------------------------------------
///
/// This module provides the core types used throughout the GC specification:
/// - Machine word constants
/// - Heap type (byte-addressable sequence)
/// - Address types (word-aligned pointers)

module GC.Spec.Base

open FStar.Seq
open FStar.Mul

module U64 = FStar.UInt64
module U8 = FStar.UInt8

/// ---------------------------------------------------------------------------
/// Machine Constants
/// ---------------------------------------------------------------------------

/// Machine word size in bytes (8 for 64-bit)
inline_for_extraction
let mword : U64.t = 8UL

/// Heap size in bytes (abstract — proofs work for any word-aligned size up to pow2 57)
/// The pow2 57 bound ensures h_addr + (1+wosize)*mword doesn't overflow U64.
/// Minimum 16 bytes (header + one field) to hold at least one object.
val heap_size : n:pos{n % U64.v mword == 0 /\ n >= 16 /\ n <= pow2 57 /\ n < pow2 64}

/// Heap size as U64 — left as an extern so the runtime can configure it.
val heap_size_u64 : n:U64.t{U64.v n == heap_size}

/// ---------------------------------------------------------------------------
/// Heap Type
/// ---------------------------------------------------------------------------

/// Heap is a byte-addressable array of fixed size
let heap = h:seq U8.t{Seq.length h == heap_size}

/// ---------------------------------------------------------------------------
/// Address Types
/// ---------------------------------------------------------------------------

/// Word-aligned address within heap bounds
let hp_addr = a:U64.t{
  U64.v a >= 0 /\ 
  U64.v a < heap_size /\ 
  U64.v a % U64.v mword == 0
}

/// 32-bit variant for compatibility
let hp_addr_32 = a:FStar.UInt32.t{
  FStar.UInt32.v a >= 0 /\ 
  FStar.UInt32.v a < heap_size /\ 
  FStar.UInt32.v a % 8 == 0
}

/// Zero address is a valid hp_addr
inline_for_extraction
let zero_addr : hp_addr = 0UL

/// Object address: hp_addr with room for header before it (>= 8)
/// Used for all operations that access object headers via hd_address
type obj_addr = a:hp_addr{U64.v a >= U64.v mword}

/// Alias for backward compatibility
let val_addr = obj_addr

/// ---------------------------------------------------------------------------
/// Address Predicates
/// ---------------------------------------------------------------------------

/// Check if a value is a valid heap pointer address
val is_hp_addr (a: U64.t) : bool

/// Check if address has room for header
val is_val_addr (a: U64.t) : bool

/// ---------------------------------------------------------------------------
/// Address Arithmetic Lemmas
/// ---------------------------------------------------------------------------

/// Sum of word-aligned values is word-aligned
val sum_of_aligned_is_aligned (x: U64.t{U64.v x % U64.v mword == 0})
                               (y: U64.t{U64.v y % U64.v mword == 0})
  : Lemma (ensures (U64.v x + U64.v y) % U64.v mword == 0)

/// Product with mword is word-aligned (when no overflow)
val mult_mword_aligned (x: U64.t{U64.v x * U64.v mword < pow2 64})
  : Lemma (ensures U64.v (U64.mul x mword) % U64.v mword == 0)

/// ---------------------------------------------------------------------------
/// Utility Types
/// ---------------------------------------------------------------------------

/// Stack-heap pair (result of operations that modify both)
let stack_heap_pair = seq U64.t & heap

/// Heap with free list pointer
let heap_fp_pair = heap & hp_addr
