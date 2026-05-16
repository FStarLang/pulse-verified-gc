/// ---------------------------------------------------------------------------
/// GC.Spec.Base - Foundational types for verified GC
/// ---------------------------------------------------------------------------
///
/// This module provides the core types used throughout the GC specification:
/// - Machine word constants
/// - Heap type (byte-addressable sequence)
/// - Address types (word-aligned pointers)
///
/// Ported from: Proofs/Spec.Heap.fsti

module GC.Spec.Base

open FStar.Seq

module U64 = FStar.UInt64
module U8 = FStar.UInt8

/// ---------------------------------------------------------------------------
/// Machine Constants (implementations from ZeroAddr extern)
/// ---------------------------------------------------------------------------

let heap_size : n:pos{n % U64.v mword == 0 /\ n >= 16 /\ n < pow2 57 /\ n < pow2 64} =
  GC.Spec.ZeroAddr.heap_size

let heap_size_u64 : n:U64.t{U64.v n == heap_size} =
  GC.Spec.ZeroAddr.heap_size_u64

/// ---------------------------------------------------------------------------
/// Heap Base Address (implementation)
/// ---------------------------------------------------------------------------

let zero_addr : a:hp_addr{U64.v a + U64.v mword < heap_size} =
  GC.Spec.ZeroAddr.zero_addr_ok ();
  GC.Spec.ZeroAddr.zero_addr

/// ---------------------------------------------------------------------------
/// Address Predicates (implementations)
/// ---------------------------------------------------------------------------

let is_hp_addr (a: U64.t) : bool =
  U64.v a < heap_size && U64.v a % U64.v mword = 0

let is_val_addr (a: U64.t) : bool =
  is_hp_addr a && U64.v a >= U64.v mword

let is_val_addr_spec (a: U64.t)
  : Lemma (ensures is_val_addr a <==>
                   (U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword == 0))
  = ()

/// ---------------------------------------------------------------------------
/// Address Arithmetic Lemmas (implementations)
/// ---------------------------------------------------------------------------

let sum_of_aligned_is_aligned (x: U64.t{U64.v x % U64.v mword == 0})
                               (y: U64.t{U64.v y % U64.v mword == 0})
  : Lemma (ensures (U64.v x + U64.v y) % U64.v mword == 0) = ()

let mult_mword_aligned (x: U64.t{U64.v x * U64.v mword < pow2 64})
  : Lemma (ensures U64.v (U64.mul x mword) % U64.v mword == 0) = ()
