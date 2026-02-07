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
/// Machine Constants (implementations)
/// ---------------------------------------------------------------------------

let heap_size : n:pos{n % U64.v mword == 0 /\ n < pow2 64} = 1024

/// ---------------------------------------------------------------------------
/// Address Predicates (implementations)
/// ---------------------------------------------------------------------------

let is_hp_addr (a: U64.t) : bool =
  U64.v a < heap_size && U64.v a % U64.v mword = 0

let is_val_addr (a: U64.t) : bool =
  is_hp_addr a && U64.v a >= U64.v mword

/// ---------------------------------------------------------------------------
/// Address Arithmetic Lemmas (implementations)
/// ---------------------------------------------------------------------------

let sum_of_aligned_is_aligned (x: U64.t{U64.v x % U64.v mword == 0})
                               (y: U64.t{U64.v y % U64.v mword == 0})
  : Lemma (ensures (U64.v x + U64.v y) % U64.v mword == 0) = ()

let mult_mword_aligned (x: U64.t{U64.v x * U64.v mword < pow2 64})
  : Lemma (ensures U64.v (U64.mul x mword) % U64.v mword == 0) = ()
