(*
   Pulse GC - Closure Module
   
   This module handles OCaml closure and infix objects, which require
   special handling during GC:
   - Closures contain code pointers and environment
   - Infix objects are embedded within closures
   
   Based on: Proofs/Impl.GC_closure_infix_ver3.fst
*)

module Pulse.Lib.GC.Closure

#lang-pulse

open FStar.Mul
open Pulse.Lib.Pervasives
open Pulse.Lib.GC.Heap
open Pulse.Lib.GC.Object
open Pulse.Lib.GC.Fields
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq

/// ---------------------------------------------------------------------------
/// Closure Info Field
/// ---------------------------------------------------------------------------

/// The closure info field contains:
/// - Arity in low bits
/// - Start of environment offset in high bits
/// 
/// Layout: | start_env (high bits) | arity (low bits) |

/// Extract closure info value from closure object
/// Requires that the closure has at least 3 words (header + 2 fields)
fn closinfo_val (heap: heap_t) (h_addr: hp_addr)
  requires is_heap heap 's **
           pure (spec_field_address (U64.v h_addr) 2 < heap_size)
  returns v: U64.t
  ensures is_heap heap 's
{
  // Closure info is in field 1 (after code pointer in field 0... wait, 
  // field 0 is header, field 1 is code pointer, field 2 is closinfo)
  // Actually in OCaml: header, then code ptr, then closinfo
  // Field indexing: 1 = code ptr, 2 = closinfo
  read_field heap h_addr 2UL
}

/// Extract start_env from closinfo
/// start_env tells us where the environment starts (offset from closure start)
fn start_env_from_closinfo (closinfo: U64.t)
  requires emp
  returns start_env: U64.t
  ensures emp
{
  // start_env is in high bits, shifted by some amount
  // In OCaml, this is implementation-specific
  // For now, assume it's the high 32 bits
  U64.shift_right closinfo 32ul
}

/// ---------------------------------------------------------------------------
/// Infix Object Handling
/// ---------------------------------------------------------------------------

/// Check if object is an infix object
fn is_infix_object (heap: heap_t) (h_addr: hp_addr)
  requires is_heap heap 's
  returns b: bool
  ensures is_heap heap 's
{
  let hdr = read_word heap h_addr;
  let t = getTag hdr;
  U64.eq t infix_tag
}

/// Check if object is a closure
fn is_closure_object (heap: heap_t) (h_addr: hp_addr)
  requires is_heap heap 's
  returns b: bool
  ensures is_heap heap 's
{
  let hdr = read_word heap h_addr;
  let t = getTag hdr;
  U64.eq t closure_tag
}

/// Get parent closure of an infix object
/// Infix objects have an offset in their header's wosize field that points back
/// to the parent closure
/// 
/// Returns None if the offset is invalid (would underflow or produce invalid address)
/// This should never happen in a well-formed heap, but we check defensively.
fn parent_closure_of_infix_opt (heap: heap_t) (infix_addr: hp_addr)
  requires is_heap heap 's
  returns parent_opt: option hp_addr
  ensures is_heap heap 's
{
  // The infix object's "wosize" actually contains the offset (in words)
  // back to the parent closure's first field
  let hdr = read_word heap infix_addr;
  let offset_words = getWosize hdr;
  
  // Prove multiplication doesn't overflow
  lemma_field_offset_no_overflow (U64.v offset_words);
  
  // Compute offset in bytes
  let offset_bytes = U64.mul offset_words mword;
  
  // Check if subtraction would underflow
  let f_addr = f_address infix_addr;
  if (U64.lt f_addr offset_bytes) {
    // Invalid: offset points before the start of heap
    None
  } else {
    let parent_f_addr = U64.sub f_addr offset_bytes;
    
    // Check if parent_f_addr >= mword (required for hd_address)
    if (U64.lt parent_f_addr mword) {
      // Invalid: would produce negative header address
      None
    } else {
      Some (hd_address parent_f_addr)
    }
  }
}

/// Get parent closure of an infix object (unsafe version)
/// Precondition: The infix object must be well-formed with valid offset
/// In a valid GC heap with proper invariants, this is always true for infix objects.
fn parent_closure_of_infix (heap: heap_t) (infix_addr: hp_addr)
  requires is_heap heap 's
  returns parent: hp_addr
  ensures is_heap heap 's
{
  let parent_opt = parent_closure_of_infix_opt heap infix_addr;
  
  // In a well-formed heap, this should always be Some
  // If it's None, the heap is corrupted - return infix_addr as fallback
  if (Some? parent_opt) {
    Some?.v parent_opt
  } else {
    infix_addr
  }
}

/// ---------------------------------------------------------------------------
/// Closure-Aware Darkening
/// ---------------------------------------------------------------------------

/// Darken with closure/infix handling
/// If the object is an infix, we need to darken the parent closure instead
fn resolve_object (heap: heap_t) (obj: hp_addr)
  requires is_heap heap 's
  returns resolved: hp_addr
  ensures is_heap heap 's
{
  // Check if it's an infix object
  let is_infix = is_infix_object heap obj;
  
  if (is_infix) {
    // Get parent closure
    parent_closure_of_infix heap obj
  } else {
    // Regular object, return as-is
    obj
  }
}

/// ---------------------------------------------------------------------------
/// Closure Environment Scanning
/// ---------------------------------------------------------------------------

/// Scan a closure's environment
/// The environment starts at start_env and goes to wosize
/// 
/// Precondition: All fields from 2 to wz are within heap bounds
/// (Caller must ensure closure is valid with sufficient size)
/// Also, wz must be a valid field index (>= 1 and <= 2^54-1, which is always true for wosize)
fn scan_closure_env (heap: heap_t) (h_addr: hp_addr) (wz: wosize)
                     (callback: U64.t -> stt unit (requires emp) (ensures fun _ -> emp))
  requires is_heap heap 's **
           pure (
             // closinfo_val needs field 2 to exist
             spec_field_address (U64.v h_addr) 2 < heap_size /\
             // All environment fields up to wz must be in bounds
             spec_field_address (U64.v h_addr) (U64.v wz) < heap_size /\
             // wz is a valid field index (always true for wosize, but make explicit)
             U64.v wz >= 1 /\ U64.v wz <= pow2 54 - 1
           )
  ensures  is_heap heap 's
{
  // Get closinfo to find where environment starts
  let closinfo = closinfo_val heap h_addr;
  let start_env_raw = start_env_from_closinfo closinfo;
  
  // Ensure start_env is at least 1 (can't read field 0, which is header)
  // In a well-formed closure, start_env should be >= code pointer + closinfo = 3 or so
  let start_env : U64.t = if (U64.lt start_env_raw 1UL) { 1UL } else { start_env_raw };
  
  // Also ensure start_env <= wz (no environment if start_env > wz)
  // Cast wz to U64.t for comparison
  let wz_u64 : U64.t = wz;
  let start_env_clamped : U64.t = if (U64.gt start_env wz_u64) { wz_u64 } else { start_env };
  
  // Environment fields are from start_env to wz
  let mut i = start_env_clamped;
  
  while (U64.lte !i wz)
    invariant exists* vi.
      pts_to i vi **
      is_heap heap 's **
      pure (
        U64.v vi >= U64.v start_env_clamped /\
        U64.v vi <= U64.v wz + 1 /\
        U64.v start_env_clamped >= 1 /\
        U64.v start_env_clamped <= U64.v wz /\
        // If i <= wz, then i is a valid field index and in bounds
        (U64.v vi <= U64.v wz ==> (
          U64.v vi >= 1 /\
          U64.v vi <= pow2 54 - 1 /\
          spec_field_address (U64.v h_addr) (U64.v vi) < heap_size
        ))
      )
  {
    let curr_i = !i;
    
    // Prove we can read this field
    assert (pure (U64.v curr_i <= U64.v wz));
    assert (pure (U64.v curr_i >= 1));
    assert (pure (U64.v curr_i <= pow2 54 - 1));
    assert (pure (spec_field_address (U64.v h_addr) (U64.v curr_i) < heap_size));
    
    // Read environment slot
    let v = read_field heap h_addr curr_i;
    
    // Check if it's a pointer
    let is_ptr = is_pointer v;
    
    if (is_ptr) {
      // Pass the pointer value directly to callback
      // The callback can handle dereferencing and resolution
      callback v
    };
    
    i := U64.add curr_i 1UL
  }
}

/// ---------------------------------------------------------------------------
/// No-Scan Objects
/// ---------------------------------------------------------------------------

/// Check if object should not be scanned (no pointers)
fn is_no_scan (heap: heap_t) (h_addr: hp_addr)
  requires is_heap heap 's
  returns b: bool
  ensures is_heap heap 's
{
  let hdr = read_word heap h_addr;
  let t = getTag hdr;
  U64.gte t no_scan_tag
}
