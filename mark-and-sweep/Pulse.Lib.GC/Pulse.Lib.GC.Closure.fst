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
fn closinfo_val (heap: heap_t) (h_addr: hp_addr)
  requires is_heap heap 's
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
fn parent_closure_of_infix (heap: heap_t) (infix_addr: hp_addr)
  requires is_heap heap 's
  returns parent: hp_addr
  ensures is_heap heap 's
{
  // The infix object's "wosize" actually contains the offset (in words)
  // back to the parent closure's first field
  let hdr = read_word heap infix_addr;
  let offset_words = getWosize hdr;
  
  // Compute parent's field address
  let offset_bytes = U64.mul offset_words mword;
  let parent_f_addr = U64.sub (f_address infix_addr) offset_bytes;
  
  // Get parent's header address
  hd_address parent_f_addr
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
fn scan_closure_env (heap: heap_t) (h_addr: hp_addr) (wz: wosize)
                     (callback: hp_addr -> stt unit (requires emp) (ensures fun _ -> emp))
  requires is_heap heap 's
  ensures  is_heap heap 's
{
  // Get closinfo to find where environment starts
  let closinfo = closinfo_val heap h_addr;
  let start_env = start_env_from_closinfo closinfo;
  
  // Environment fields are from start_env to wz
  let mut i = start_env;
  
  while (U64.lte !i wz)
    invariant exists* vi s.
      pts_to i vi **
      is_heap heap s
  {
    let curr_i = !i;
    
    // Read environment slot
    let v = read_field heap h_addr curr_i;
    
    // Check if it's a pointer
    let is_ptr = is_pointer v;
    
    if (is_ptr) {
      // Get header address and resolve (handle infix)
      let succ_h_addr = hd_address v;
      let resolved = resolve_object heap succ_h_addr;
      
      // Call callback on resolved object
      callback resolved
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
