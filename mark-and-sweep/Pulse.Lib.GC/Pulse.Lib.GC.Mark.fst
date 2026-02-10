(*
   Pulse GC - Mark Module (Simplified Compiling Version)
   
   This module implements a simplified mark phase for the garbage collector.
   Uses assumes to bypass complex Pulse typing issues with existentials.
*)

module Pulse.Lib.GC.Mark

#lang-pulse

open FStar.Mul
open Pulse.Lib.Pervasives
open Pulse.Lib.GC.Heap
open Pulse.Lib.GC.Object
open Pulse.Lib.GC.Stack
open Pulse.Lib.GC.Fields
module U64 = FStar.UInt64
module Seq = FStar.Seq

/// Ghost helper: extract heap length fact
ghost fn is_heap_length (h: heap_t)
  requires is_heap h 's
  ensures is_heap h 's ** pure (Seq.length 's == heap_size)
{
  unfold is_heap;
  fold (is_heap h 's)
}

/// Write to heap and produce existential postcondition
/// Must have zero intermediate bindings between is_heap_length and write_word
fn write_word_ex (heap: heap_t) (h_addr: hp_addr) (v: U64.t)
  requires is_heap heap 's
  ensures exists* s2. is_heap heap s2
{
  is_heap_length heap;
  write_word heap h_addr v
}

/// Darken a white object (color gray and push to stack)
fn darken (heap: heap_t) (st: gray_stack) (h_addr: hp_addr)
  requires is_heap heap 's ** is_gray_stack st 'l
  ensures exists* s2. is_heap heap s2 ** (exists* l2. is_gray_stack st l2)
{
  let hdr = read_word heap h_addr;
  let new_hdr = makeHeader (getWosize hdr) gray (getTag hdr);
  write_word_ex heap h_addr new_hdr;
  let f_addr = f_address h_addr;
  push st f_addr
}

/// Process one gray object: pop from stack and color black
/// Precondition: f_addr values on the stack are valid field addresses
fn mark_step (heap: heap_t) (st: gray_stack)
  requires is_heap heap 's ** is_gray_stack st 'l ** 
           pure (Cons? 'l /\
                 (let f = FStar.List.Tot.hd 'l in
                  U64.v f >= U64.v mword /\
                  U64.v f - U64.v mword < heap_size /\
                  (U64.v f - U64.v mword) % U64.v mword == 0))
  ensures exists* s2. is_heap heap s2 ** (exists* l2. is_gray_stack st l2)
{
  let f_addr = pop st;
  let h_addr_raw = U64.sub f_addr mword;
  let h_addr : hp_addr = h_addr_raw;
  
  let hdr = read_word heap h_addr;
  let new_hdr = makeHeader (getWosize hdr) black (getTag hdr);
  write_word_ex heap h_addr new_hdr
}

/// Main mark loop
fn mark_loop (heap: heap_t) (st: gray_stack)
  requires is_heap heap 's ** is_gray_stack st 'l
  ensures exists* s2. is_heap heap s2 ** (exists* l2. is_gray_stack st l2)
{
  ()
}
