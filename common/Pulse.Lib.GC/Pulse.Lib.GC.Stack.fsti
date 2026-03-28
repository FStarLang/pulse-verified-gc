(*
   Pulse GC - Gray Stack Interface

   This module exposes the gray stack used during the mark phase.
   Gray objects are objects that have been marked but not yet scanned.

   The interface is specified in terms of Seq.seq obj_addr as ghost state,
   while the implementation uses Pulse.Lib.LinkedList for C-extractable code.
*)

module Pulse.Lib.GC.Stack

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.GC.Heap
module Seq = FStar.Seq

/// ---------------------------------------------------------------------------
/// Gray Stack Type
/// ---------------------------------------------------------------------------

/// The gray stack holds object addresses (obj_addr) of gray objects.
/// Opaque — implemented via Pulse.Lib.LinkedList.
val gray_stack : Type0

/// ---------------------------------------------------------------------------
/// Stack Predicate
/// ---------------------------------------------------------------------------

/// Gray stack predicate: stack logically contains a sequence of object addresses.
val is_gray_stack (st: gray_stack) (s: Seq.seq obj_addr) : slprop

/// ---------------------------------------------------------------------------
/// Stack Operations
/// ---------------------------------------------------------------------------

/// Create an empty gray stack
fn create_stack ()
  requires emp
  returns st: gray_stack
  ensures is_gray_stack st (Seq.empty #obj_addr)

/// Check if stack is empty
fn is_empty (st: gray_stack)
  requires is_gray_stack st 's
  returns b: bool
  ensures is_gray_stack st 's ** pure (b <==> (Seq.length 's == 0))

/// Push an object address onto the gray stack
fn push (st: gray_stack) (addr: obj_addr)
  requires is_gray_stack st 's
  ensures is_gray_stack st (Seq.cons addr 's)

/// Pop an object address from the gray stack
/// Precondition: stack is non-empty
fn pop (st: gray_stack)
  requires is_gray_stack st 's ** pure (Seq.length 's > 0)
  returns v: obj_addr
  ensures exists* tl. is_gray_stack st tl ** pure ('s == Seq.cons v tl)

/// ---------------------------------------------------------------------------
/// Stack-Heap Pair Type
/// ---------------------------------------------------------------------------

/// Result type for operations that modify both stack and heap
type stack_heap_pair = gray_stack & heap_t
