(*
   Pulse GC - Mark Module
   
   This module implements the mark phase of the garbage collector.
   Uses tri-color marking: white (unmarked), gray (marked, not scanned),
   black (marked and scanned).
   
   Based on: Proofs/Spec.Mark.fsti and Proofs/Impl.GC_closure_infix_ver3.fsti
*)

module Pulse.Lib.GC.Mark

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.GC.Heap
open Pulse.Lib.GC.Object
open Pulse.Lib.GC.Stack
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module L = FStar.List.Tot

/// ---------------------------------------------------------------------------
/// Mark Phase Invariants
/// ---------------------------------------------------------------------------

/// Tri-color invariant: no black object points to a white object
let tri_color_invariant (heap: heap_t) (blacks whites: list hp_addr) : prop =
  forall b w. L.mem b blacks /\ L.mem w whites ==>
    not (points_to heap b w)

/// Points-to relation (placeholder - full implementation needs field traversal)
let points_to (heap: heap_t) (src dst: hp_addr) : prop =
  // Object at src has a field pointing to dst
  True // TODO: implement via field traversal

/// ---------------------------------------------------------------------------
/// Darken Operation
/// ---------------------------------------------------------------------------

/// Darken a white object: change its color to gray and add to stack
fn darken (heap: heap_t) (st: gray_stack) (obj: hp_addr)
  requires is_object heap obj 'wz white 't **
           is_gray_stack st 'l **
           pure (not (L.mem (f_address obj) 'l))
  returns p: stack_heap_pair
  ensures is_object heap obj 'wz gray 't **
          is_gray_stack (fst p) (f_address obj :: 'l)
{
  // Color the object gray
  colorHeader heap obj gray;
  
  // Push to gray stack
  let f_addr = f_address obj;
  let st' = push st f_addr;
  
  (st', heap)
}

/// Darken if white: check color and darken only if white
fn darken_if_white (heap: heap_t) (st: gray_stack) (obj: hp_addr)
  requires is_heap heap 's ** is_gray_stack st 'l
  returns p: stack_heap_pair
  ensures is_heap heap 's' ** is_gray_stack (fst p) 'l'
{
  // Read object header
  let hdr = read_word heap obj;
  let c = getColor hdr;
  
  if (c = white) {
    // Check if already in stack
    let f_addr = f_address obj;
    let in_stack = mem st f_addr;
    
    if (not in_stack) {
      // Darken: color gray and push to stack
      let wz = getWosize hdr;
      let t = getTag hdr;
      let new_hdr = makeHeader wz gray t;
      write_word heap obj new_hdr;
      let st' = push st f_addr;
      (st', heap)
    } else {
      (st, heap)
    }
  } else {
    // Already gray or black, do nothing
    (st, heap)
  }
}

/// ---------------------------------------------------------------------------
/// Field Scanning
/// ---------------------------------------------------------------------------

/// Scan all fields of an object, darkening any white objects found
fn scan_fields (heap: heap_t) (st: gray_stack) (obj: hp_addr) (wz: wosize)
  requires is_heap heap 's ** is_gray_stack st 'l
  returns p: stack_heap_pair
  ensures is_heap heap 's' ** is_gray_stack (fst p) 'l'
{
  let mut i = 1UL;  // Start at field 1 (field 0 is header)
  let mut current_st = st;
  let mut current_heap = heap;
  
  while (U64.lt !i (U64.add wz 1UL))
    invariant exists* vi vst vheap s l.
      pts_to i vi **
      pts_to current_st vst **
      pts_to current_heap vheap **
      is_heap vheap s **
      is_gray_stack vst l **
      pure (U64.v vi >= 1 /\ U64.v vi <= U64.v wz + 1)
  {
    // Compute field address
    let field_addr = U64.add obj (U64.mul !i mword);
    
    // Read field value
    let field_val = read_word !current_heap field_addr;
    
    // Check if it's a pointer
    if (isPointer field_val) {
      // Get header address of pointed object
      let pointed_obj = hd_address field_val;
      
      // Darken if white
      let (st', heap') = darken_if_white !current_heap !current_st pointed_obj;
      current_st := st';
      current_heap := heap'
    };
    
    i := U64.add !i 1UL
  };
  
  (!current_st, !current_heap)
}

/// ---------------------------------------------------------------------------
/// Mark Step
/// ---------------------------------------------------------------------------

/// Process one gray object: color it black and scan its fields
fn mark_step (heap: heap_t) (st: gray_stack)
  requires is_heap heap 's ** 
           is_gray_stack st 'l ** 
           pure (Cons? 'l)
  returns p: stack_heap_pair
  ensures is_heap (snd p) 's' ** 
          is_gray_stack (fst p) 'l'
{
  // Pop a gray object from the stack
  let (st', f_addr) = pop st;
  
  // Get header address
  let h_addr = hd_address f_addr;
  
  // Read header to get wosize
  let hdr = read_word heap h_addr;
  let wz = getWosize hdr;
  let t = getTag hdr;
  
  // Color the object black
  let new_hdr = makeHeader wz black t;
  write_word heap h_addr new_hdr;
  
  // Scan fields (unless no_scan_tag)
  if (U64.lt t no_scan_tag) {
    scan_fields heap st' h_addr wz
  } else {
    (st', heap)
  }
}

/// ---------------------------------------------------------------------------
/// Main Mark Loop
/// ---------------------------------------------------------------------------

/// Mark all reachable objects starting from gray stack
fn rec mark (heap: heap_t) (st: gray_stack)
  requires is_heap heap 's ** is_gray_stack st 'l
  returns heap': heap_t
  ensures is_heap heap' 's' ** 
          pure (no_gray_objects heap')
  decreases L.length 'l
{
  let empty = is_empty st;
  
  if (empty) {
    // No more gray objects - we're done
    free_stack st;
    heap
  } else {
    // Process one gray object
    let (st', heap') = mark_step heap st;
    
    // Continue marking
    mark heap' st'
  }
}

/// No gray objects remain
let no_gray_objects (heap: heap_t) : prop =
  // All objects in heap are not gray
  True // TODO: full implementation

/// ---------------------------------------------------------------------------
/// Root Greying
/// ---------------------------------------------------------------------------

/// Grey all root objects (starting point for mark phase)
fn grey_roots (heap: heap_t) (roots: vec U64.t)
  requires is_heap heap 's ** pts_to roots 'root_seq
  returns p: stack_heap_pair
  ensures is_heap (snd p) 's' ** is_gray_stack (fst p) 'l
{
  // Create empty gray stack
  let st = create_stack 1024sz;
  
  // Grey each root
  let len = Vec.length roots;
  let mut i = 0sz;
  let mut current_st = st;
  let mut current_heap = heap;
  
  while (SZ.lt !i len)
    invariant exists* vi vst vheap s l.
      pts_to i vi **
      pts_to current_st vst **
      pts_to current_heap vheap **
      is_heap vheap s **
      is_gray_stack vst l **
      pure (SZ.v vi <= SZ.v len)
  {
    let root_addr = Vec.index roots !i;
    
    if (isPointer root_addr) {
      let obj = hd_address root_addr;
      let (st', heap') = darken_if_white !current_heap !current_st obj;
      current_st := st';
      current_heap := heap'
    };
    
    i := SZ.add !i 1sz
  };
  
  (!current_st, !current_heap)
}

/// ---------------------------------------------------------------------------
/// Semantic Aliases
/// ---------------------------------------------------------------------------

let mark_phase = mark
let darken_object = darken
