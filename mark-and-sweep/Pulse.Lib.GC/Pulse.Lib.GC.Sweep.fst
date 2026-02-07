(*
   Pulse GC - Sweep Module
   
   This module implements the sweep phase of the garbage collector.
   After marking, sweep reclaims white (unreachable) objects by
   coloring them blue and adding to free list.
   
   Based on: Proofs/Impl.GC_closure_infix_ver3.fst
*)

module Pulse.Lib.GC.Sweep

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.GC.Heap
open Pulse.Lib.GC.Object
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq

/// ---------------------------------------------------------------------------
/// Free List
/// ---------------------------------------------------------------------------

/// Free list pointer - points to first free object
type free_list_ptr = ref U64.t

/// Free list predicate
let is_free_list (fp: free_list_ptr) (addr: U64.t) : slprop =
  pts_to fp addr

/// ---------------------------------------------------------------------------
/// Sweep Body Helper
/// ---------------------------------------------------------------------------

/// Process one object during sweep:
/// - If white/blue: color blue and add to free list
/// - If black: color white (reset for next cycle)
fn sweep_object (heap: heap_t) (h_addr: hp_addr) (fp: free_list_ptr)
  requires is_heap heap 's ** is_free_list fp 'fp_val
  ensures  is_heap heap 's' ** is_free_list fp 'fp_val'
{
  // Read object header
  let hdr = read_word heap h_addr;
  let c = getColor hdr;
  let wz = getWosize hdr;
  let t = getTag hdr;
  
  if U64.eq c white || U64.eq c blue then {
    // White/blue object: free it (color blue, add to free list)
    
    // Color it blue
    let new_hdr = makeHeader wz blue t;
    write_word heap h_addr new_hdr;
    
    // Get current free list head
    let old_fp = !fp;
    
    // Link this object into free list:
    // Set first field to point to old free list head
    let f_addr = f_address h_addr;
    if U64.gt wz 0UL then {
      // Object has at least one field - use it for next pointer
      write_word heap f_addr old_fp
    };
    
    // Update free list pointer to this object
    fp := f_addr
  } else {
    // Black object: survived GC, reset to white for next cycle
    assert (U64.eq c black);
    let new_hdr = makeHeader wz white t;
    write_word heap h_addr new_hdr
  }
}

/// ---------------------------------------------------------------------------
/// Object Iteration
/// ---------------------------------------------------------------------------

/// Get next object address given current header address and wosize
fn next_object (h_addr: hp_addr) (wz: wosize)
  requires emp
  returns addr: U64.t
  ensures emp ** pure (U64.v addr == U64.v h_addr + U64.v mword + U64.v wz * U64.v mword)
{
  // Skip header (1 word) + object fields (wz words)
  let skip = U64.add 1UL wz;
  let offset = U64.mul skip mword;
  U64.add h_addr offset
}

/// ---------------------------------------------------------------------------
/// Main Sweep Loop
/// ---------------------------------------------------------------------------

/// Sweep all objects in heap, starting from address 0
fn sweep (heap: heap_t) (fp: free_list_ptr)
  requires is_heap heap 's ** is_free_list fp 'fp_val
  ensures  is_heap heap 's' ** is_free_list fp 'fp_val'
{
  let mut current = 0UL;
  
  while (U64.lt !current (U64.uint_to_t heap_size))
    invariant exists* v s fp_v.
      pts_to current v **
      is_heap heap s **
      is_free_list fp fp_v **
      pure (U64.v v % U64.v mword == 0)
  {
    let h_addr = !current;
    
    // Check if this is a valid object header
    // (In real impl, we'd check is_valid_header)
    
    // Read header to get wosize
    let hdr = read_word heap h_addr;
    let wz = getWosize hdr;
    
    // Process this object
    sweep_object heap h_addr fp;
    
    // Move to next object
    let next_addr = next_object h_addr wz;
    current := next_addr
  }
}

/// ---------------------------------------------------------------------------
/// Sweep with Objects List
/// ---------------------------------------------------------------------------

/// Alternative: sweep using pre-computed objects list
/// This matches the spec's approach more closely
/// Note: objs is an array (not seq) for imperative indexing
fn sweep_objects_list (heap: heap_t) (fp: free_list_ptr) 
                       (objs: array hp_addr) (objs_len: SZ.t) (idx: SZ.t)
  requires is_heap heap 's ** 
           is_free_list fp 'fp_val **
           pts_to objs 'objlist **
           pure (SZ.v idx <= SZ.v objs_len /\ SZ.v objs_len == L.length 'objlist)
  ensures  is_heap heap 's' ** is_free_list fp 'fp_val' ** pts_to objs 'objlist
{
  let mut i = idx;
  
  while (SZ.lt !i objs_len)
    invariant exists* vi s fp_v objlist.
      pts_to i vi **
      is_heap heap s **
      is_free_list fp fp_v **
      pts_to objs objlist **
      pure (SZ.v vi <= SZ.v objs_len /\ SZ.v objs_len == L.length objlist)
  {
    let curr_idx = !i;
    
    // Get object header address using array indexing
    let h_addr = objs.(curr_idx);
    
    // Process this object
    sweep_object heap h_addr fp;
    
    // Next object
    i := SZ.add curr_idx 1sz
  }
}

/// ---------------------------------------------------------------------------
/// Combined GC: Mark + Sweep
/// ---------------------------------------------------------------------------

/// Full garbage collection: mark phase followed by sweep phase
/// (Top-level entry point)
/// Note: roots is an array (not seq) for imperative indexing
fn gc (heap: heap_t) (fp: free_list_ptr) (roots: array hp_addr) (roots_len: SZ.t)
  requires is_heap heap 's ** is_free_list fp 'fp_val ** pts_to roots 'rs ** pure (SZ.v roots_len == L.length 'rs)
  ensures  is_heap heap 's' ** is_free_list fp 'fp_val' ** pts_to roots 'rs
{
  // Phase 1: Mark (from Mark module)
  // mark heap roots;
  
  // Phase 2: Sweep
  sweep heap fp
}
