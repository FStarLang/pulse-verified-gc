(*
   Pulse GC - Stack Module

   Gray stack implemented using Pulse.Lib.LinkedList for C extraction.
   The interface exposes Seq.seq obj_addr as ghost state; internally
   we maintain a ref (llist obj_addr) and bridge via Seq.seq_of_list.
*)

module Pulse.Lib.GC.Stack

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Reference
open Pulse.Lib.LinkedList
open Pulse.Lib.GC.Heap
module Seq = FStar.Seq
module L = FStar.List.Tot

/// ---------------------------------------------------------------------------
/// Gray Stack Type
/// ---------------------------------------------------------------------------

/// A mutable reference to a linked list of obj_addr
type gray_stack = ref (llist obj_addr)

/// ---------------------------------------------------------------------------
/// Stack Predicate
/// ---------------------------------------------------------------------------

/// Bridge between the linked list (ghost: list) and the interface (ghost: Seq.seq).
let is_gray_stack (st: gray_stack) (s: Seq.seq obj_addr) : slprop =
  exists* (ll: llist obj_addr) (l: list obj_addr).
    pts_to st ll **
    is_list ll l **
    pure (s == Seq.seq_of_list l)

/// ---------------------------------------------------------------------------
/// Helper lemmas for Seq ↔ list conversion
/// ---------------------------------------------------------------------------

let seq_of_list_nil ()
  : Lemma (Seq.seq_of_list #obj_addr [] == Seq.empty #obj_addr)
  = Seq.lemma_seq_of_list_induction #obj_addr []

let seq_of_list_cons (x: obj_addr) (l: list obj_addr)
  : Lemma (Seq.seq_of_list (x :: l) == Seq.cons x (Seq.seq_of_list l))
  = Seq.lemma_seq_of_list_induction (x :: l)

let seq_of_list_length (l: list obj_addr)
  : Lemma (Seq.length (Seq.seq_of_list l) == L.length l)
  = ()  // follows from the refinement on seq_of_list

let seq_of_list_empty_iff (l: list obj_addr)
  : Lemma ((l == []) <==> (Seq.length (Seq.seq_of_list l) == 0))
  = seq_of_list_length l

let seq_of_list_nonempty (l: list obj_addr)
  : Lemma (requires Seq.length (Seq.seq_of_list l) > 0)
          (ensures Cons? l)
  = seq_of_list_length l

/// ---------------------------------------------------------------------------
/// Stack Operations
/// ---------------------------------------------------------------------------

/// Create an empty gray stack
fn create_stack ()
  requires emp
  returns st: gray_stack
  ensures is_gray_stack st (Seq.empty #obj_addr)
{
  let ll = create obj_addr;
  let st = alloc ll;
  seq_of_list_nil ();
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
  with ll l. _;
  let curr = !st;
  rewrite (is_list ll l) as (is_list curr l);
  let b = Pulse.Lib.LinkedList.is_empty curr;
  seq_of_list_empty_iff l;
  rewrite (is_list curr l) as (is_list ll l);
  fold (is_gray_stack st 's);
  b
}

/// Push an object address onto the gray stack
fn push (st: gray_stack) (addr: obj_addr)
  requires is_gray_stack st 's
  ensures is_gray_stack st (Seq.cons addr 's)
{
  unfold is_gray_stack;
  with ll l. _;
  let curr = !st;
  rewrite (is_list ll l) as (is_list curr l);
  let new_ll = cons addr curr;
  st := new_ll;
  seq_of_list_cons addr l;
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
  with ll l. _;
  seq_of_list_nonempty l;
  let curr = !st;
  rewrite (is_list ll l) as (is_list curr l);
  let r = Pulse.Lib.LinkedList.pop curr;
  let new_ll = fst r;
  let v = snd r;
  rewrite (is_list (fst r) (L.tl l)) as (is_list new_ll (L.tl l));
  st := new_ll;
  seq_of_list_cons v (L.tl l);
  fold (is_gray_stack st (Seq.seq_of_list (L.tl l)));
  v
}
