(*
   Pulse GC - Stack Module
   
   This module defines the gray stack used during the mark phase.
   Gray objects are objects that have been marked but not yet scanned.
   
   Based on: Proofs/Spec.Mark.fsti stack operations
*)

module Pulse.Lib.GC.Stack

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Vec
open Pulse.Lib.GC.Heap
open Pulse.Lib.GC.Object
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module L = FStar.List.Tot

/// ---------------------------------------------------------------------------
/// Gray Stack Type
/// ---------------------------------------------------------------------------

/// The gray stack holds field addresses of gray objects
/// (objects marked but not yet scanned)
type gray_stack = vec U64.t

/// ---------------------------------------------------------------------------
/// Stack Predicate
/// ---------------------------------------------------------------------------

/// Stack properties:
/// - All elements are valid field addresses (>= mword, < heap_size)
/// - All elements are word-aligned
/// - No duplicates (vertex set property)
let stack_props (l: list U64.t) : prop =
  (forall x. L.mem x l ==> U64.v x >= U64.v mword /\ U64.v x < heap_size) /\
  (forall x. L.mem x l ==> U64.v x % U64.v mword == 0) /\
  (forall x. L.mem x l ==> L.count x l == 1)  // No duplicates

/// Gray stack predicate: stack contains list of gray object field addresses
let is_gray_stack (st: gray_stack) (l: list U64.t) : slprop =
  exists* s.
    pts_to st s **
    pure (Seq.seq_to_list s == l /\ stack_props l)

/// ---------------------------------------------------------------------------
/// Stack Operations
/// ---------------------------------------------------------------------------

/// Create an empty gray stack
fn create_stack (capacity: SZ.t{SZ.v capacity > 0})
  requires emp
  returns st: gray_stack
  ensures is_gray_stack st []
{
  let st = Vec.alloc 0UL capacity;
  fold (is_gray_stack st []);
  st
}

/// Check if stack is empty
fn is_empty (st: gray_stack)
  requires is_gray_stack st 'l
  returns b: bool
  ensures is_gray_stack st 'l ** pure (b <==> ('l == []))
{
  unfold is_gray_stack;
  let len = Vec.length st;
  fold (is_gray_stack st 'l);
  len = 0sz
}

/// Get stack length
fn stack_length (st: gray_stack)
  requires is_gray_stack st 'l
  returns n: SZ.t
  ensures is_gray_stack st 'l ** pure (SZ.v n == L.length 'l)
{
  unfold is_gray_stack;
  let len = Vec.length st;
  fold (is_gray_stack st 'l);
  len
}

/// Push a field address onto the gray stack
/// Precondition: address is valid and not already in stack
fn push (st: gray_stack) (addr: U64.t)
  requires is_gray_stack st 'l ** 
           pure (U64.v addr >= U64.v mword /\ 
                 U64.v addr < heap_size /\
                 U64.v addr % U64.v mword == 0 /\
                 not (L.mem addr 'l))
  returns st': gray_stack
  ensures is_gray_stack st' (addr :: 'l)
{
  unfold is_gray_stack;
  let st' = Vec.push st addr;
  fold (is_gray_stack st' (addr :: 'l));
  st'
}

/// Pop a field address from the gray stack
/// Precondition: stack is non-empty
fn pop (st: gray_stack)
  requires is_gray_stack st 'l ** pure (Cons? 'l)
  returns p: (gray_stack & U64.t)
  ensures is_gray_stack (fst p) (L.tl 'l) ** 
          pure (snd p == L.hd 'l)
{
  unfold is_gray_stack;
  let (st', v) = Vec.pop st;
  fold (is_gray_stack st' (L.tl 'l));
  (st', v)
}

/// Peek at top of stack without removing
fn peek (st: gray_stack)
  requires is_gray_stack st 'l ** pure (Cons? 'l)
  returns v: U64.t
  ensures is_gray_stack st 'l ** pure (v == L.hd 'l)
{
  unfold is_gray_stack;
  let len = Vec.length st;
  let v = Vec.index st (SZ.sub len 1sz);
  fold (is_gray_stack st 'l);
  v
}

/// Check if address is in stack
fn mem (st: gray_stack) (addr: U64.t)
  requires is_gray_stack st 'l
  returns b: bool
  ensures is_gray_stack st 'l ** pure (b <==> L.mem addr 'l)
{
  unfold is_gray_stack;
  let len = Vec.length st;
  let mut i = 0sz;
  let mut found = false;
  
  while (SZ.lt !i len && not !found)
    invariant exists* vi vfound.
      pts_to i vi **
      pts_to found vfound **
      pure (SZ.v vi <= SZ.v len /\
            (vfound <==> (exists j. j < SZ.v vi /\ L.index 'l j == addr)))
  {
    let v = Vec.index st !i;
    if (v = addr) {
      found := true
    };
    i := SZ.add !i 1sz
  };
  
  fold (is_gray_stack st 'l);
  !found
}

/// Free the gray stack
fn free_stack (st: gray_stack)
  requires exists* l. is_gray_stack st l
  ensures emp
{
  unfold is_gray_stack;
  Vec.free st
}

/// ---------------------------------------------------------------------------
/// Stack-Heap Pair Type
/// ---------------------------------------------------------------------------

/// Result type for operations that modify both stack and heap
type stack_heap_pair = gray_stack & heap_t
