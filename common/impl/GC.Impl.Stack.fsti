(*
   Pulse GC - Gray Stack Interface

   Gray stack backed by a caller-provided fixed-capacity array.
   The stack grows downward: elements occupy the tail of the array.

   The interface is specified in terms of Seq.seq obj_addr as ghost state.
   Push requires remaining capacity; if capacity >= heap_size / mword,
   the GC invariant guarantees push never fails (at most one entry per object).
*)

module GC.Impl.Stack

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Impl.Heap
module Seq = FStar.Seq
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module U64 = FStar.UInt64

/// ---------------------------------------------------------------------------
/// Gray Stack Type
/// ---------------------------------------------------------------------------

/// Opaque gray stack type, backed by a Vec U64.t.
val gray_stack : Type0

/// The maximum number of elements the stack can hold (ghost).
val stack_capacity (st: gray_stack) : GTot nat

/// ---------------------------------------------------------------------------
/// Stack Predicate
/// ---------------------------------------------------------------------------

/// Gray stack predicate: stack logically contains a sequence of object addresses.
val is_gray_stack (st: gray_stack) (s: Seq.seq obj_addr) : slprop

/// ---------------------------------------------------------------------------
/// Stack Operations
/// ---------------------------------------------------------------------------

/// Create a gray stack from a caller-provided vector.
/// The caller passes the capacity as a runtime SZ.t (Vec.length is ghost).
fn create_stack (storage: V.vec U64.t) (cap: SZ.t)
  requires V.pts_to storage 'init **
           pure (V.length storage == SZ.v cap /\ SZ.v cap > 0 /\
                 V.is_full_vec storage)
  returns st: gray_stack
  ensures is_gray_stack st (Seq.empty #obj_addr) **
          pure (stack_capacity st == SZ.v cap)

/// Destroy the gray stack and reclaim the backing vector.
fn destroy_stack (st: gray_stack)
  requires is_gray_stack st 's
  returns storage: V.vec U64.t
  ensures exists* contents. V.pts_to storage contents **
          pure (V.length storage == stack_capacity st /\
                V.is_full_vec storage)

/// Check if stack is empty
fn is_empty (st: gray_stack)
  requires is_gray_stack st 's
  returns b: bool
  ensures is_gray_stack st 's ** pure (b <==> (Seq.length 's == 0))

/// Check if stack is full (no more capacity)
fn is_full (st: gray_stack)
  requires is_gray_stack st 's
  returns b: bool
  ensures is_gray_stack st 's ** pure (b <==> (Seq.length 's == stack_capacity st))

/// Return the current number of elements on the stack
fn stack_len (st: gray_stack)
  requires is_gray_stack st 's
  returns n: SZ.t
  ensures is_gray_stack st 's ** pure (SZ.v n == Seq.length 's)

/// Push an object address onto the gray stack.
/// Precondition: stack has remaining capacity.
fn push (st: gray_stack) (addr: obj_addr)
  requires is_gray_stack st 's ** pure (Seq.length 's < stack_capacity st)
  ensures is_gray_stack st (Seq.cons addr 's)

/// Pop an object address from the gray stack.
/// Precondition: stack is non-empty.
fn pop (st: gray_stack)
  requires is_gray_stack st 's ** pure (Seq.length 's > 0)
  returns v: obj_addr
  ensures exists* tl. is_gray_stack st tl ** pure ('s == Seq.cons v tl)
