(*
   Pulse GC - Stack Module
   
   This module defines the gray stack used during the mark phase.
   Gray objects are objects that have been marked but not yet scanned.
   
   Based on: Proofs/Spec.Mark.fsti stack operations
*)

module Pulse.Lib.GC.Stack

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Reference
open Pulse.Lib.GC.Heap
open Pulse.Lib.GC.Object
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module L = FStar.List.Tot

/// ---------------------------------------------------------------------------
/// Gray Stack Type
/// ---------------------------------------------------------------------------

/// The gray stack holds field addresses of gray objects
/// (objects marked but not yet scanned)
/// Implementation: mutable reference to a list
type gray_stack = ref (list U64.t)

/// ---------------------------------------------------------------------------
/// Stack Predicate
/// ---------------------------------------------------------------------------

/// Gray stack predicate: stack contains list of gray object field addresses
let is_gray_stack (st: gray_stack) (l: list U64.t) : slprop =
  pts_to st l

/// ---------------------------------------------------------------------------
/// Stack Operations
/// ---------------------------------------------------------------------------

/// Create an empty gray stack
fn create_stack ()
  requires emp
  returns st: gray_stack
  ensures is_gray_stack st []
{
  let st = alloc #(list U64.t) [];
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
  let l = !st;
  fold (is_gray_stack st 'l);
  Nil? l
}

/// Push a field address onto the gray stack
fn push (st: gray_stack) (addr: U64.t)
  requires is_gray_stack st 'l
  ensures is_gray_stack st (addr :: 'l)
{
  unfold is_gray_stack;
  let old = !st;
  st := addr :: old;
  fold (is_gray_stack st (addr :: 'l))
}

/// Pop a field address from the gray stack
/// Precondition: stack is non-empty
fn pop (st: gray_stack)
  requires is_gray_stack st 'l ** pure (Cons? 'l)
  returns v: U64.t
  ensures exists* tl. is_gray_stack st tl ** pure ('l == v :: tl)
{
  unfold is_gray_stack;
  let l = !st;
  rewrite (pts_to st l) as (pts_to st 'l);
  match l {
    hd :: tl -> {
      st := tl;
      fold (is_gray_stack st tl);
      hd
    }
  }
}

/// ---------------------------------------------------------------------------
/// Stack-Heap Pair Type
/// ---------------------------------------------------------------------------

/// Result type for operations that modify both stack and heap
type stack_heap_pair = gray_stack & heap_t
