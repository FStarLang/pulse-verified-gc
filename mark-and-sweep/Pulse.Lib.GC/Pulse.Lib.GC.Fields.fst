(*
   Pulse GC - Fields Module
   
   This module provides field access operations for objects:
   - Reading successors (pointer fields)
   - Object enumeration helpers
   
   Based on: Proofs/Impl.GC_closure_infix_ver3.fst (read_succ_impl)
*)

module Pulse.Lib.GC.Fields

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.GC.Heap
open Pulse.Lib.GC.Object
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq

/// ---------------------------------------------------------------------------
/// Field Address Computation
/// ---------------------------------------------------------------------------

/// Compute address of field i (1-indexed, 0 is header)
fn field_address (h_addr: hp_addr) (i: U64.t)
  requires pure (U64.v i >= 1)
  returns addr: U64.t
  ensures pure (U64.v addr == U64.v h_addr + U64.v i * U64.v mword)
{
  let offset = U64.mul i mword;
  U64.add h_addr offset
}

/// ---------------------------------------------------------------------------
/// Field Read Operations
/// ---------------------------------------------------------------------------

/// Read field i of object at h_addr
fn read_field (heap: heap_t) (h_addr: hp_addr) (i: U64.t)
  requires is_heap heap 's ** pure (U64.v i >= 1)
  returns v: U64.t
  ensures is_heap heap 's
{
  let addr = field_address h_addr i;
  read_word heap addr
}

/// Read successor pointer at field i
/// This is the core operation for graph traversal
fn read_succ (heap: heap_t) (h_addr: hp_addr) (i: U64.t)
  requires is_heap heap 's ** pure (U64.v i >= 1)
  returns succ: U64.t
  ensures is_heap heap 's
{
  // Read the field value
  let v = read_field heap h_addr i;
  
  // The field contains a pointer to another object's first field
  // Return the header address
  v
}

/// ---------------------------------------------------------------------------
/// Pointer Check
/// ---------------------------------------------------------------------------

/// Check if a value is a valid heap pointer
fn is_pointer (v: U64.t)
  requires emp
  returns b: bool
  ensures emp ** pure (b <==> (U64.v v > 0 /\ 
                               U64.v v < heap_size /\ 
                               U64.v v % U64.v mword == 0))
{
  // Check non-null
  if U64.eq v 0UL then {
    false
  } else {
    // Check within heap bounds
    if U64.gte v (U64.uint_to_t heap_size) then {
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

/// Get all successors of an object (for mark phase)
/// Returns the number of successors found and processes each
fn for_each_successor (heap: heap_t) (h_addr: hp_addr) (wz: wosize)
                       (callback: hp_addr -> stt unit (requires emp) (ensures fun _ -> emp))
  requires is_heap heap 's
  ensures  is_heap heap 's
{
  let mut i = 1UL;
  
  while (U64.lte !i wz)
    invariant exists* vi s.
      pts_to i vi **
      is_heap heap s **
      pure (U64.v vi >= 1 /\ U64.v vi <= U64.v wz + 1)
  {
    let curr_i = !i;
    
    // Read field value
    let v = read_field heap h_addr curr_i;
    
    // Check if it's a pointer
    let is_ptr = is_pointer v;
    
    if is_ptr then {
      // Get header address of pointed object
      let succ_h_addr = hd_address v;
      
      // Call the callback
      callback succ_h_addr
    };
    
    i := U64.add curr_i 1UL
  }
}

/// ---------------------------------------------------------------------------
/// Object Validation
/// ---------------------------------------------------------------------------

/// Check if an address contains a valid object header
fn is_valid_header (heap: heap_t) (h_addr: hp_addr)
  requires is_heap heap 's
  returns b: bool
  ensures is_heap heap 's
{
  // Read header
  let hdr = read_word heap h_addr;
  let wz = getWosize hdr;
  let t = getTag hdr;
  
  // Check that object fits in heap
  let obj_end = U64.add h_addr (U64.mul (U64.add 1UL wz) mword);
  
  if U64.gt obj_end (U64.uint_to_t heap_size) then {
    false
  } else {
    // Check tag is valid (0-255)
    U64.lte t 255UL
  }
}

/// ---------------------------------------------------------------------------
/// Next Object Address
/// ---------------------------------------------------------------------------

/// Compute address of next object given current object's header address
fn next_object_addr (heap: heap_t) (h_addr: hp_addr)
  requires is_heap heap 's
  returns addr: U64.t
  ensures is_heap heap 's
{
  let hdr = read_word heap h_addr;
  let wz = getWosize hdr;
  
  // Skip header (1 word) + fields (wz words)
  let skip = U64.add 1UL wz;
  let offset = U64.mul skip mword;
  U64.add h_addr offset
}
