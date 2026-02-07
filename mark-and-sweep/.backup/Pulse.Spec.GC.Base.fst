/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.Base - Foundational types for verified GC
/// ---------------------------------------------------------------------------
///
/// This module provides the core types used throughout the GC specification:
/// - Machine word constants
/// - Heap type (byte-addressable sequence)
/// - Address types (word-aligned pointers)
///
/// Ported from: Proofs/Spec.Heap.fsti

module Pulse.Spec.GC.Base

open FStar.Seq
open FStar.Mul

module U64 = FStar.UInt64
module U8 = FStar.UInt8

/// ---------------------------------------------------------------------------
/// Machine Constants
/// ---------------------------------------------------------------------------

/// Machine word size in bytes (8 for 64-bit)
let mword : U64.t = 8UL

/// Heap size in bytes (must be multiple of mword)
/// Can be adjusted for different configurations
let heap_size : pos = 1024

/// Validate heap size is word-aligned
let heap_size_aligned : squash (heap_size % U64.v mword == 0) = ()

/// ---------------------------------------------------------------------------
/// Heap Type
/// ---------------------------------------------------------------------------

/// Heap is a byte-addressable array of fixed size
type heap = h:seq U8.t{Seq.length h == heap_size}

/// ---------------------------------------------------------------------------
/// Address Types
/// ---------------------------------------------------------------------------

/// Word-aligned address within heap bounds
/// Used for object headers and pointer fields
type hp_addr = a:U64.t{
  U64.v a >= 0 /\ 
  U64.v a < heap_size /\ 
  U64.v a % U64.v mword == 0
}

/// 32-bit variant for compatibility
type hp_addr_32 = a:FStar.UInt32.t{
  FStar.UInt32.v a >= 0 /\ 
  FStar.UInt32.v a < heap_size /\ 
  FStar.UInt32.v a % 8 == 0
}

/// Zero address is a valid hp_addr (used as starting point for object enumeration)
let zero_addr : hp_addr = 0UL

/// Value address: hp_addr with room for header before it
/// Points to first field of an object (header is at addr - mword)
type val_addr = a:hp_addr{U64.v a >= U64.v mword}

/// ---------------------------------------------------------------------------
/// Address Predicates
/// ---------------------------------------------------------------------------

/// Check if a value is a valid heap pointer address
let is_hp_addr (a: U64.t) : bool =
  U64.v a < heap_size && U64.v a % U64.v mword = 0

/// Check if address has room for header
let is_val_addr (a: U64.t) : bool =
  is_hp_addr a && U64.v a >= U64.v mword

/// ---------------------------------------------------------------------------
/// Address Arithmetic Lemmas
/// ---------------------------------------------------------------------------

/// Sum of word-aligned values is word-aligned
let sum_of_aligned_is_aligned (x: U64.t{U64.v x % U64.v mword == 0})
                               (y: U64.t{U64.v y % U64.v mword == 0})
  : Lemma (ensures (U64.v x + U64.v y) % U64.v mword == 0) = ()

/// Product with mword is word-aligned (when no overflow)
let mult_mword_aligned (x: U64.t{U64.v x * U64.v mword < pow2 64})
  : Lemma (ensures U64.v (U64.mul x mword) % U64.v mword == 0) = ()

/// ---------------------------------------------------------------------------
/// Utility Types
/// ---------------------------------------------------------------------------

/// Stack-heap pair (result of operations that modify both)
type stack_heap_pair = seq U64.t & heap

/// Heap with free list pointer
type heap_fp_pair = heap & hp_addr
