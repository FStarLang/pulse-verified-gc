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
module Seq = FStar.Seq

/// ---------------------------------------------------------------------------
/// Gray Stack Type
/// ---------------------------------------------------------------------------

/// The gray stack holds object addresses (obj_addr) of gray objects
/// (objects marked but not yet scanned).
/// Using obj_addr enables direct use of spec functions (stack_props, mark, etc.)
type gray_stack = ref (Seq.seq obj_addr)

/// ---------------------------------------------------------------------------
/// Stack Predicate
/// ---------------------------------------------------------------------------

/// Gray stack predicate: stack contains seq of gray object addresses
let is_gray_stack (st: gray_stack) (s: Seq.seq obj_addr) : slprop =
  pts_to st s

/// ---------------------------------------------------------------------------
/// Stack Operations
/// ---------------------------------------------------------------------------

/// Create an empty gray stack
fn create_stack ()
  requires emp
  returns st: gray_stack
  ensures is_gray_stack st (Seq.empty #obj_addr)
{
  let st = alloc #(Seq.seq obj_addr) (Seq.empty #obj_addr);
  fold (is_gray_stack st (Seq.empty #obj_addr));
  st
}

/// Check if stack is empty
fn is_empty (st: gray_stack)
  requires is_gray_stack st 's
  returns b: bool
  ensures is_gray_stack st 's ** pure (b <==> (Seq.length 's == 0))
{
  unfold is_gray_stack;
  let s = !st;
  fold (is_gray_stack st 's);
  Seq.length s = 0
}

/// Push an object address onto the gray stack
fn push (st: gray_stack) (addr: obj_addr)
  requires is_gray_stack st 's
  ensures is_gray_stack st (Seq.cons addr 's)
{
  unfold is_gray_stack;
  let old = !st;
  st := Seq.cons addr old;
  fold (is_gray_stack st (Seq.cons addr 's))
}

/// Pop an object address from the gray stack
/// Precondition: stack is non-empty
fn pop (st: gray_stack)
  requires is_gray_stack st 's ** pure (Seq.length 's > 0)
  returns v: obj_addr
  ensures exists* tl. is_gray_stack st tl ** pure ('s == Seq.cons v tl)
{
  unfold is_gray_stack;
  let s = !st;
  rewrite (pts_to st s) as (pts_to st 's);
  let hd = Seq.head s;
  let tl = Seq.tail s;
  st := tl;
  fold (is_gray_stack st tl);
  hd
}

/// ---------------------------------------------------------------------------
/// Stack-Heap Pair Type
/// ---------------------------------------------------------------------------

/// Result type for operations that modify both stack and heap
type stack_heap_pair = gray_stack & heap_t
