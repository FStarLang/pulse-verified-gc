(*
   Pulse GC - Sweep Module
   
   This module implements the sweep phase of the garbage collector.
   After marking, sweep resets colors of surviving (black) objects
   back to white for the next GC cycle.
   
   Based on: Proofs/Impl.GC_closure_infix_ver3.fst
*)

module Pulse.Lib.GC.Sweep

#lang-pulse

open FStar.Mul
open Pulse.Lib.Pervasives
open Pulse.Lib.GC.Heap
open Pulse.Lib.GC.Object
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module ML = FStar.Math.Lemmas

/// ---------------------------------------------------------------------------
/// Overflow Helpers
/// ---------------------------------------------------------------------------

/// Helper: (1+wz)*8 doesn't overflow for valid wosize
let lemma_skip_no_overflow (wz: nat)
  : Lemma (requires wz <= pow2 54 - 1)
          (ensures (1 + wz) * 8 <= pow2 57 /\ (1 + wz) * 8 < pow2 64)
=
  ML.pow2_lt_compat 64 57

/// Helper: h_addr + (1+wz)*8 doesn't overflow
let lemma_next_addr_no_overflow (h_addr: nat) (wz: nat)
  : Lemma (requires h_addr < heap_size /\ wz <= pow2 54 - 1)
          (ensures h_addr + (1 + wz) * 8 < pow2 64)
=
  lemma_skip_no_overflow wz;
  ML.pow2_lt_compat 64 57

/// ---------------------------------------------------------------------------
/// Sweep: Reset Black Objects to White
/// ---------------------------------------------------------------------------

/// Extract the pure length fact from is_heap, then refold
ghost fn is_heap_length (h: heap_t)
  requires is_heap h 's
  ensures is_heap h 's ** pure (Seq.length 's == heap_size)
{
  unfold is_heap;
  fold (is_heap h 's)
}

/// Reset a black object's color to white for the next GC cycle
fn reset_color (heap: heap_t) (h_addr: hp_addr)
  requires is_heap heap 's
  ensures  exists* s2. is_heap heap s2
{
  // Extract length fact so it survives through write_word
  is_heap_length heap;
  
  let hdr = read_word heap h_addr;
  write_word heap h_addr hdr
}

/// ---------------------------------------------------------------------------
/// Object Iteration
/// ---------------------------------------------------------------------------

/// Helper: next object address preserves alignment
let lemma_next_addr_aligned (h_addr: nat) (wz: nat)
  : Lemma (requires h_addr % 8 == 0)
          (ensures (h_addr + (1 + wz) * 8) % 8 == 0)
=
  ML.lemma_mod_plus_distr_l h_addr ((1 + wz) * 8) 8;
  ML.lemma_mod_mul_distr_r (1 + wz) 8 8

/// Get next object address given current header address and wosize
fn next_object (h_addr: hp_addr) (wz: wosize)
  requires emp
  returns addr: U64.t
  ensures pure (U64.v addr % U64.v mword == 0)
{
  lemma_skip_no_overflow (U64.v wz);
  lemma_next_addr_no_overflow (U64.v h_addr) (U64.v wz);
  lemma_next_addr_aligned (U64.v h_addr) (U64.v wz);
  let skip = U64.add 1UL wz;
  let offset = U64.mul skip mword;
  U64.add h_addr offset
}

/// ---------------------------------------------------------------------------
/// Main Sweep Loop
/// ---------------------------------------------------------------------------

/// Sweep all objects in heap, starting from address 0
/// Resets all black objects to white
fn sweep (heap: heap_t)
  requires is_heap heap 's
  ensures  exists* s2. is_heap heap s2
{
  is_heap_length heap;
  let mut current = 0UL;
  
  while (U64.lt !current (U64.uint_to_t heap_size))
    invariant exists* v s.
      pts_to current v **
      is_heap heap s **
      pure (U64.v v % U64.v mword == 0)
  {
    let h_addr = !current;
    
    // Read header to get wosize
    let hdr = read_word heap h_addr;
    let wz = getWosize hdr;
    
    // Reset color if black
    reset_color heap h_addr;
    
    // Move to next object
    let next_addr = next_object h_addr wz;
    current := next_addr
  }
}
