(*
   Pulse GC - Top-Level Module
   
   This module provides the top-level garbage collection entry point,
   combining mark and sweep phases.
   
   Based on: Proofs/Impl.GC_closure_infix_ver3.fst
*)

module Pulse.Lib.GC

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.GC.Heap
open Pulse.Lib.GC.Object
open Pulse.Lib.GC.Stack
open Pulse.Lib.GC.Fields
open Pulse.Lib.GC.Closure
open Pulse.Lib.GC.Sweep
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module L = FStar.List.Tot

/// ---------------------------------------------------------------------------
/// GC State
/// ---------------------------------------------------------------------------

/// Complete GC state
noeq
type gc_state = {
  heap : heap_t;
  stack : gray_stack;
  free_list : free_list_ptr;
}

/// GC state predicate
let is_gc_state (gc: gc_state) (s: Seq.seq U8.t) (st: list U64.t) (fp: U64.t) : slprop =
  is_heap gc.heap s **
  is_gray_stack gc.stack st **
  is_free_list gc.free_list fp

/// ---------------------------------------------------------------------------
/// Root Greying
/// ---------------------------------------------------------------------------

/// Grey a single root object
fn grey_root (heap: heap_t) (st: gray_stack) (root: hp_addr)
  requires is_heap heap 's ** is_gray_stack st 'l
  ensures  is_heap heap 's' ** is_gray_stack st 'l'
{
  // Check if already grey or black
  let hdr = read_word heap root;
  let c = getColor hdr;
  
  if (U64.eq c white) {
    // Color it grey
    let wz = getWosize hdr;
    let t = getTag hdr;
    let new_hdr = makeHeader wz gray t;
    write_word heap root new_hdr;
    
    // Push to stack
    let f_addr = f_address root;
    push st f_addr
  }
}

/// Grey all roots
/// Note: roots is an array, not a seq, to enable imperative indexing
fn grey_roots (heap: heap_t) (st: gray_stack) (roots: array hp_addr) (roots_len: SZ.t)
  requires is_heap heap 's ** is_gray_stack st 'l ** pts_to roots 'rs ** pure (SZ.v roots_len == L.length 'rs)
  ensures  is_heap heap 's' ** is_gray_stack st 'l' ** pts_to roots 'rs
{
  let mut i = 0sz;
  
  while (SZ.lt !i roots_len)
    invariant exists* vi s l rs.
      pts_to i vi **
      is_heap heap s **
      is_gray_stack st l **
      pts_to roots rs **
      pure (SZ.v vi <= SZ.v roots_len /\ SZ.v roots_len == L.length rs)
  {
    let curr_i = !i;
    
    // Get root at index using array indexing
    let root = roots.(curr_i);
    
    // Grey this root
    grey_root heap st root;
    
    i := SZ.add curr_i 1sz
  }
}

/// ---------------------------------------------------------------------------
/// Mark Phase (Complete)
/// ---------------------------------------------------------------------------

/// Full mark phase: process grey stack until empty
fn mark_phase (heap: heap_t) (st: gray_stack)
  requires is_heap heap 's ** is_gray_stack st 'l
  ensures  is_heap heap 's' ** is_gray_stack st 'l' ** pure (Nil? 'l')
{
  while (not (is_empty st))
    invariant exists* s l.
      is_heap heap s **
      is_gray_stack st l
  {
    // Pop a grey object
    let (st', f_addr) = pop st;
    let h_addr = hd_address f_addr;
    
    // Read header
    let hdr = read_word heap h_addr;
    let wz = getWosize hdr;
    let t = getTag hdr;
    
    // Color it black
    let black_hdr = makeHeader wz black t;
    write_word heap h_addr black_hdr;
    
    // Check if we need to scan fields
    let should_scan = U64.lt t no_scan_tag;
    
    if (should_scan) {
      // Check if it's a closure
      let is_clos = U64.eq t closure_tag;
      
      if (is_clos) {
        // Scan closure environment
        scan_closure_env heap h_addr wz fn succ {
          // Darken successor if white
          let succ_hdr = read_word heap succ;
          let succ_c = getColor succ_hdr;
          
          if (U64.eq succ_c white) {
            grey_root heap st succ
          }
        }
      } else {
        // Scan all fields
        for_each_successor heap h_addr wz fn succ {
          // Resolve infix objects
          let resolved = resolve_object heap succ;
          
          // Darken if white
          let resolved_hdr = read_word heap resolved;
          let resolved_c = getColor resolved_hdr;
          
          if (U64.eq resolved_c white) {
            grey_root heap st resolved
          }
        }
      }
    }
  }
}

/// ---------------------------------------------------------------------------
/// Full GC
/// ---------------------------------------------------------------------------

/// Main garbage collection entry point
/// 1. Grey all roots
/// 2. Mark (process grey stack)
/// 3. Sweep (reclaim white objects)
/// Note: roots must be an array with length roots_len
fn collect (gc: gc_state) (roots: array hp_addr) (roots_len: SZ.t)
  requires is_gc_state gc 's 'st 'fp ** pts_to roots 'rs ** pure (SZ.v roots_len == L.length 'rs)
  ensures  is_gc_state gc 's' 'st' 'fp' ** pts_to roots 'rs
{
  // Phase 1: Grey roots
  grey_roots gc.heap gc.stack roots roots_len;
  
  // Phase 2: Mark
  mark_phase gc.heap gc.stack;
  
  // Phase 3: Sweep
  sweep gc.heap gc.free_list
}

/// ---------------------------------------------------------------------------
/// Allocation (Bonus)
/// ---------------------------------------------------------------------------

/// Allocate from free list
fn alloc (gc: gc_state) (wz: wosize) (t: tag)
  requires is_gc_state gc 's 'st 'fp
  returns result: option hp_addr
  ensures is_gc_state gc 's' 'st 'fp'
{
  // Get free list head
  let fp = !(gc.free_list);
  
  if (U64.eq fp 0UL) {
    // No free memory
    None
  } else {
    // Get header address from field address
    let h_addr = hd_address fp;
    
    // Read header to get available size
    let hdr = read_word gc.heap h_addr;
    let avail_wz = getWosize hdr;
    
    if (U64.lt avail_wz wz) {
      // Not enough space in this block
      // (Real impl would search free list)
      None
    } else {
      // Use this block
      // Update free list to next free block
      let next_fp = read_field gc.heap h_addr 1UL;
      gc.free_list := next_fp;
      
      // Initialize object header (color white, ready for use)
      let new_hdr = makeHeader wz white t;
      write_word gc.heap h_addr new_hdr;
      
      Some h_addr
    }
  }
}
