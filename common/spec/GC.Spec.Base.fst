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

let zero_addr_above_2048 () : Lemma (U64.v zero_addr >= 2048) =
  GC.Spec.ZeroAddr.zero_addr_above_minor_size ()

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

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let mk_hp_addr a =
  assert (a < pow2 64);
  U64.uint_to_t a
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let aligned_plus_mul8 base k =
  FStar.Math.Lemmas.lemma_mod_add_distr base (k * 8) 8;
  FStar.Math.Lemmas.multiple_modulo_lemma k 8
#pop-options
