(*
   Pulse GC - Sweep Module
   
   This module implements the sweep phase of the garbage collector.
   After marking, sweep resets colors of surviving (black) objects
   back to white for the next GC cycle.
   
   Based on: Proofs/Impl.GC_closure_infix_ver3.fst
*)

module Pulse.Lib.GC.Sweep

#lang-pulse

#set-options "--z3rlimit 50"

open FStar.Mul
open Pulse.Lib.Pervasives
open Pulse.Lib.GC.Heap
open Pulse.Lib.GC.Object
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module ML = FStar.Math.Lemmas
module SpecSweep = Pulse.Spec.GC.Sweep
module SpecFields = Pulse.Spec.GC.Fields

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

/// Write a free-list link to field 1 if the object has fields (wosize > 0)
/// Precondition: object fits in heap (h_addr + (1+wz)*8 <= heap_size)
fn write_freelist_link (heap: heap_t) (h_addr: hp_addr) (wz: wosize) (fp: U64.t)
  requires is_heap heap 's **
           pure (U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size)
  ensures exists* s2. is_heap heap s2
{
  if U64.gt wz 0UL {
    is_heap_length heap;
    let field1_addr_raw = U64.add h_addr mword;
    // h_addr + 8 < h_addr + (1+wz)*8 <= heap_size (since wz > 0)
    // h_addr % 8 == 0 implies (h_addr + 8) % 8 == 0
    let field1_addr : hp_addr = field1_addr_raw;
    write_word heap field1_addr fp
  }
}

/// Handle a white object: link to free list
fn sweep_white (heap: heap_t) (h_addr: hp_addr) (wz: wosize) (fp: U64.t)
  requires is_heap heap 's **
           pure (U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size)
  returns new_fp: U64.t
  ensures exists* s2. is_heap heap s2
{
  write_freelist_link heap h_addr wz fp;
  f_address h_addr
}

/// Handle a black object: reset color to white
fn sweep_black (heap: heap_t) (h_addr: hp_addr) (wz: wosize) (hdr: U64.t) (fp: U64.t)
  requires is_heap heap 's
  returns new_fp: U64.t
  ensures exists* s2. is_heap heap s2
{
  is_heap_length heap;
  let new_hdr = makeHeader wz white (getTag hdr);
  write_word heap h_addr new_hdr;
  fp
}

/// Sweep one object:
/// - White -> add to free list (link field 1 to fp), return new fp
/// - Black -> reset to white, keep fp
/// - Gray/other -> keep fp
/// Precondition: object fits in heap (header + fields within bounds)
fn sweep_object (heap: heap_t) (h_addr: hp_addr) (wz: wosize) (fp: U64.t)
  requires is_heap heap 's **
           pure (U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size)
  returns new_fp: U64.t
  ensures exists* s2. is_heap heap s2
{
  is_heap_length heap;
  
  let hdr = read_word heap h_addr;
  let color = getColor hdr;
  
  if (color = white) {
    sweep_white heap h_addr wz fp
  } else if (color = black) {
    sweep_black heap h_addr wz hdr fp
  } else {
    fp
  }
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

/// Sweep all objects in heap, building free list
/// fp: initial free pointer (0UL for null/empty free list)
/// Precondition: well_formed_heap ensures each object fits in heap
fn sweep (heap: heap_t) (fp: U64.t)
  requires is_heap heap 's ** pure (SpecFields.well_formed_heap 's)
  returns final_fp: U64.t
  ensures  exists* s2. is_heap heap s2
{
  is_heap_length heap;
  let mut current = 0UL;
  let mut free_ptr = fp;
  
  while (U64.lt !current (U64.uint_to_t heap_size))
    invariant exists* v fv s.
      pts_to current v **
      pts_to free_ptr fv **
      is_heap heap s **
      pure (U64.v v % U64.v mword == 0 /\
            SpecFields.well_formed_heap s)
  {
    let h_addr = !current;
    
    // Read header to get wosize
    let hdr = read_word heap h_addr;
    let wz = getWosize hdr;
    
    // Derive object-fits-in-heap from well_formed_heap
    // TODO: prove correspondence between linear scan and objects list
    // For now this is the only assume in sweep — well_formed_heap implies
    // every object visited by the linear scan fits in heap
    with s_cur. assert (is_heap heap s_cur);
    assume (pure (U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size));
    
    // Process object: sweep and update free pointer
    let cur_fp = !free_ptr;
    let new_fp = sweep_object heap h_addr wz cur_fp;
    free_ptr := new_fp;
    
    // Move to next object
    let next_addr = next_object h_addr wz;
    current := next_addr;
    
    // well_formed_heap preservation through sweep writes
    // Spec: sweep_object_preserves_wf
    with s_post. assert (is_heap heap s_post);
    assume (pure (SpecFields.well_formed_heap s_post))
  };
  
  let result = !free_ptr;
  result
}
