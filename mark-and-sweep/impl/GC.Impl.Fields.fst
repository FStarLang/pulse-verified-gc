(*
   Pulse GC - Fields Module
   
   This module provides field access operations for objects:
   - Reading successors (pointer fields)
   - Object enumeration helpers
   
   Based on: Proofs/Impl.GC_closure_infix_ver3.fst (read_succ_impl)
*)

module GC.Impl.Fields

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module ML = FStar.Math.Lemmas

/// ---------------------------------------------------------------------------
/// Pure helper lemmas for overflow checking
/// ---------------------------------------------------------------------------

/// Lemma: mword is 8
let lemma_mword_is_8 () : Lemma (U64.v mword == 8) = ()

/// Lemma: i <= 2^54-1 implies i*8 < 2^64
let lemma_field_offset_no_overflow (i: nat)
  : Lemma (requires i <= pow2 54 - 1)
          (ensures i * 8 < pow2 64)
= 
  // i <= 2^54 - 1, so i * 8 <= (2^54 - 1) * 8 < 2^54 * 8 = 2^57 < 2^64
  ML.pow2_lt_compat 64 57;
  assert (pow2 57 <= pow2 64)

/// Lemma: address + offset fits in U64 when both are bounded
let lemma_address_add_no_overflow (addr: nat) (offset: nat)
  : Lemma (requires addr < heap_size /\ offset <= pow2 57)
          (ensures addr + offset < pow2 64)
=
  // heap_size <= pow2 57, offset <= pow2 57, so sum < pow2 57 + pow2 57 = pow2 58 < pow2 64
  ML.pow2_lt_compat 64 58;
  ML.pow2_double_sum 57;
  assert (addr + offset < pow2 58)

/// Lemma: (1 + wz) * 8 doesn't overflow for valid wosize
let lemma_object_size_no_overflow (wz: nat)
  : Lemma (requires wz <= pow2 54 - 1)
          (ensures (1 + wz) * 8 <= pow2 57 /\ (1 + wz) * 8 < pow2 64)
=
  // (1 + wz) <= 2^54, so (1 + wz) * 8 <= 2^54 * 8 = 2^57 < 2^64
  ML.pow2_lt_compat 64 57;
  assert ((1 + wz) * 8 <= pow2 57)

/// Lemma: h_addr word-aligned and i*8 is multiple of 8 => (h_addr + i*8) is word-aligned
let lemma_field_addr_aligned (h_addr: nat) (i: nat)
  : Lemma (requires h_addr % 8 == 0)
          (ensures (h_addr + i * 8) % 8 == 0)
= 
  FStar.Math.Lemmas.lemma_mod_plus_distr_l h_addr (i * 8) 8;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r i 8 8

/// ---------------------------------------------------------------------------
/// Field Address Computation
/// ---------------------------------------------------------------------------

/// Compute address of field i (1-indexed, 0 is header) - pure version
/// Precondition: i is in valid range and result doesn't overflow
let field_address_pure (h_addr: hp_addr) (i: U64.t{U64.v i >= 1 /\ U64.v i <= pow2 54 - 1})
  : Pure U64.t
    (requires True)
    (ensures fun addr -> U64.v addr == spec_field_address (U64.v h_addr) (U64.v i))
=
  lemma_field_offset_no_overflow (U64.v i);
  let offset = U64.mul i mword in
  lemma_address_add_no_overflow (U64.v h_addr) (U64.v offset);
  U64.add h_addr offset
/// ---------------------------------------------------------------------------
/// Field Read Operations
/// ---------------------------------------------------------------------------

/// Read field i of object at h_addr
/// Requires: field address is within heap bounds (< heap_size)
fn read_field (heap: heap_t) (h_addr: hp_addr) (i: U64.t)
  requires is_heap heap 's ** 
           pure (U64.v i >= 1 /\ 
                 U64.v i <= pow2 54 - 1 /\
                 spec_field_address (U64.v h_addr) (U64.v i) + 8 <= heap_size)
  returns v: U64.t
  ensures is_heap heap 's **
          pure (U64.v i >= 1 /\
                spec_field_address (U64.v h_addr) (U64.v i) + 8 <= Seq.length 's /\
                v == spec_read_word 's (spec_field_address (U64.v h_addr) (U64.v i)))
{
  lemma_mword_is_8 ();
  
  // Use the pure function directly to get the postcondition
  let addr = field_address_pure h_addr i;
  
  // Now addr has the postcondition from field_address_pure
  assert (pure (U64.v addr == spec_field_address (U64.v h_addr) (U64.v i)));
  assert (pure (U64.v addr == U64.v h_addr + U64.v i * 8));
  
  // Now prove alignment
  lemma_field_addr_aligned (U64.v h_addr) (U64.v i);
  assert (pure ((U64.v h_addr + U64.v i * 8) % 8 == 0));
  assert (pure (U64.v addr % 8 == 0));
  
  // Prove bounds
  assert (pure (U64.v addr >= 0));
  assert (pure (U64.v addr < heap_size));
  
  let addr_hp : hp_addr = addr;
  
  let v = read_word heap addr_hp;
  spec_read_word_eq 's addr_hp;
  v
}
/// ---------------------------------------------------------------------------
/// Pointer Check
/// ---------------------------------------------------------------------------

/// Check if a value is a valid heap pointer
fn is_pointer (v: U64.t)
  requires emp
  returns b: bool
  ensures emp ** pure (b <==> (U64.v v >= U64.v zero_addr + U64.v mword /\ 
                               U64.v v < heap_size /\ 
                               U64.v v % U64.v mword == 0))
{
  // Lower bound: zero_addr + mword (in spec zero_addr=0, so this is 8;
  // at deployment zero_addr is the heap base address)
  let lo = U64.add zero_addr mword;
  if (U64.lt v lo) {
    false
  } else {
    // Check within heap bounds
    if (U64.gte v heap_size_u64) {
      false
    } else {
      // Check word-aligned
      let rem = U64.rem v mword;
      U64.eq rem 0UL
    }
  }
}

/// ---------------------------------------------------------------------------
/// Successor Iteration
/// ---------------------------------------------------------------------------
/// ---------------------------------------------------------------------------
/// Object Validation
/// ---------------------------------------------------------------------------
/// ---------------------------------------------------------------------------
/// Next Object Address
/// ---------------------------------------------------------------------------
