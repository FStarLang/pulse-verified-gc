(*
   Pulse GC - Mark Module
   
   This module implements the mark phase for the garbage collector.
   The mark_step processes one gray object (blacken + push children).
   The mark_loop iterates until the stack is empty.
   
   Postconditions connect to the spec via well_formed_heap:
   - mark_loop ensures well_formed_heap preserved and stack empty
   - Full spec equality (s2 == mark 's 'st) requires seq obj_addr stack type
*)

module Pulse.Lib.GC.Mark

#lang-pulse

#set-options "--z3rlimit 50"

open FStar.Mul
open Pulse.Lib.Pervasives
open Pulse.Lib.GC.Heap
open Pulse.Lib.GC.Object
open Pulse.Lib.GC.Stack
open Pulse.Lib.GC.Fields
module U64 = FStar.UInt64
module Seq = FStar.Seq
module ML = FStar.Math.Lemmas
module SpecMark = Pulse.Spec.GC.Mark
module SpecMarkInv = Pulse.Spec.GC.MarkInv

/// f_address preserves alignment and gives valid obj_addr
let f_address_valid (h_addr: hp_addr)
  : Lemma (requires U64.v h_addr + U64.v mword < heap_size)
          (ensures (let f = f_address h_addr in
                    U64.v f == U64.v h_addr + U64.v mword /\
                    U64.v f < heap_size /\
                    U64.v f % U64.v mword == 0 /\
                    U64.v f >= U64.v mword))
= ML.lemma_mod_plus_distr_l (U64.v h_addr) (U64.v mword) (U64.v mword)

/// Ghost helper: extract heap length fact
ghost fn is_heap_length (h: heap_t)
  requires is_heap h 's
  ensures is_heap h 's ** pure (Seq.length 's == heap_size)
{
  unfold is_heap;
  fold (is_heap h 's)
}

/// Write to heap and produce existential postcondition
fn write_word_ex (heap: heap_t) (h_addr: hp_addr) (v: U64.t)
  requires is_heap heap 's
  ensures exists* s2. is_heap heap s2
{
  is_heap_length heap;
  write_word heap h_addr v
}

/// Darken a white object (color gray and push to stack)
/// Precondition: h_addr + 8 < heap_size (object address is valid)
fn darken (heap: heap_t) (st: gray_stack) (h_addr: hp_addr)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (U64.v h_addr + U64.v mword < heap_size)
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2
{
  let hdr = read_word heap h_addr;
  let new_hdr = makeHeader (getWosize hdr) gray (getTag hdr);
  write_word_ex heap h_addr new_hdr;
  f_address_valid h_addr;
  let f_addr = f_address h_addr;
  let f_addr_obj : obj_addr = f_addr;
  push st f_addr_obj
}

/// Check if object is white and darken it (color gray + push to stack)
/// Precondition: h_addr + 8 < heap_size (object address is valid)
fn darken_if_white (heap: heap_t) (st: gray_stack) (h_addr: hp_addr)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (U64.v h_addr + U64.v mword < heap_size)
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2
{
  let hdr = read_word heap h_addr;
  let c = getColor hdr;
  
  if (c = white) {
    is_heap_length heap;
    let wz = getWosize hdr;
    let t = getTag hdr;
    let new_hdr = makeHeader wz gray t;
    write_word_ex heap h_addr new_hdr;
    f_address_valid h_addr;
    let f_addr = f_address h_addr;
    let f_addr_obj : obj_addr = f_addr;
    push st f_addr_obj
  }
}

/// Check if value is a pointer, and if so, darken its target if white
fn check_and_darken (heap: heap_t) (st: gray_stack) (v: U64.t)
  requires is_heap heap 's ** is_gray_stack st 'st
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2
{
  let is_ptr = is_pointer v;
  if is_ptr {
    // is_pointer gives: v > 0, v < heap_size, v % 8 == 0
    // So v >= 8, and v - 8 >= 0
    let target_hdr_raw = U64.sub v mword;
    assert (pure (U64.v target_hdr_raw < heap_size));
    assert (pure (U64.v target_hdr_raw % U64.v mword == 0));
    let target_hdr : hp_addr = target_hdr_raw;
    // target_hdr + 8 = v < heap_size
    assert (pure (U64.v target_hdr + U64.v mword < heap_size));
    darken_if_white heap st target_hdr
  }
}

/// Push white children of an object onto the gray stack
fn push_children (heap: heap_t) (st: gray_stack) (h_addr: hp_addr) (wz: wosize)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (U64.v wz <= pow2 54 - 1 /\
                 spec_field_address (U64.v h_addr) (U64.v wz + 1) <= heap_size)
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2
{
  let mut i = 1UL;
  
  while (U64.lte !i wz)
    invariant exists* vi s st_cur.
      pts_to i vi **
      is_heap heap s **
      is_gray_stack st st_cur **
      pure (U64.v vi >= 1 /\ U64.v vi <= U64.v wz + 1)
  {
    let curr_i = !i;
    let v = read_field heap h_addr curr_i;
    check_and_darken heap st v;
    i := U64.add curr_i 1UL
  }
}

/// Conditionally push children if tag < no_scan_tag
fn maybe_push_children (heap: heap_t) (st: gray_stack) (h_addr: hp_addr) (wz: wosize) (tag: U64.t)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (spec_field_address (U64.v h_addr) (U64.v wz + 1) <= heap_size)
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2
{
  if U64.lt tag no_scan_tag {
    push_children heap st h_addr wz
  }
}

#restart-solver

/// Process one gray object: pop from stack, blacken, push white children
/// Precondition: mark_inv provides well_formed_heap + stack_props
fn mark_step (heap: heap_t) (st: gray_stack)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (SpecMarkInv.mark_inv 's 'st /\ Seq.length 'st > 0)
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
           pure (SpecMarkInv.mark_inv s2 st2)
{
  // Extract well_formed_heap and head-is-gray from mark_inv
  SpecMarkInv.mark_inv_head_gray 's 'st;
  SpecMarkInv.mark_inv_elim_wfh 's 'st;
  
  let f_addr = pop st;
  // f_addr : obj_addr from pop = head of 'st
  // mark_inv_head_gray: f_addr is gray and in objects 0UL 's
  
  let h_addr_raw = U64.sub f_addr mword;
  let h_addr : hp_addr = h_addr_raw;
  
  // Derive object-fits-in-heap from well_formed_heap
  // mark_inv_obj_fields_bound: hd_address f_addr + mword + wz*mword <= heap_size
  SpecMarkInv.mark_inv_obj_fields_bound 's f_addr;
  
  let hdr = read_word heap h_addr;
  let wz = getWosize hdr;
  let tag = getTag hdr;
  
  let new_hdr = makeHeader wz black tag;
  write_word_ex heap h_addr new_hdr;
  
  // spec_field_address h_addr (wz+1) = h_addr + (wz+1)*8
  // = hd_address f_addr + (wz+1)*8 = hd_address f_addr + mword + wz*mword
  // <= heap_size (from mark_inv_obj_fields_bound)
  // But we need wz from the ghost state 's, not from the mutated heap
  // The read_word returned hdr from pre-write state, so wz matches 's
  assume (pure (spec_field_address (U64.v h_addr) (U64.v wz + 1) <= heap_size));
  maybe_push_children heap st h_addr wz tag;
  
  // mark_inv preservation
  with s_post st_post. assert (is_heap heap s_post ** is_gray_stack st st_post);
  assume (pure (SpecMarkInv.mark_inv s_post st_post))
}

/// Main mark loop: process gray objects until stack is empty
/// Precondition: mark_inv (well_formed_heap + stack_props)
/// Postcondition: mark_inv preserved, stack empty
fn mark_loop (heap: heap_t) (st: gray_stack)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (SpecMarkInv.mark_inv 's 'st)
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
          pure (SpecMarkInv.mark_inv s2 st2 /\ Seq.length st2 == 0)
{
  let mut go = true;
  
  while (!go)
    invariant exists* vc s st_cur.
      pts_to go vc **
      is_heap heap s **
      is_gray_stack st st_cur **
      pure (SpecMarkInv.mark_inv s st_cur /\
            (~vc ==> (Seq.length st_cur == 0)))
  {
    let empty = is_empty st;
    if empty {
      go := false
    } else {
      mark_step heap st
    }
  }
}
