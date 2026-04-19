(*
   Pulse GC - Gray Stack (Array-backed)

   Fixed-capacity stack backed by a Vec U64.t. The stack grows downward:
   elements occupy positions [top..cap) in the array, where `top` is
   the index of the most recently pushed element.

   Mapping: s[i] = contents[top + i]  (direct, no reversal needed)
   - Push: decrement top, write addr at new top
   - Pop:  read at top, increment top
   - Empty when top == cap
   - Full  when top == 0
*)

module GC.Impl.Stack

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Impl.Heap
module Seq = FStar.Seq
module V = Pulse.Lib.Vec
module B = Pulse.Lib.Box
module SZ = FStar.SizeT

/// ---------------------------------------------------------------------------
/// Gray Stack Type
/// ---------------------------------------------------------------------------

noeq type gray_stack_rec = {
  storage: V.vec U64.t;
  top: B.box SZ.t;
  cap: SZ.t;  // cached V.length storage for runtime access
}

let gray_stack = gray_stack_rec

let stack_capacity (st: gray_stack) : GTot nat = SZ.v st.cap

/// ---------------------------------------------------------------------------
/// Stack Predicate
/// ---------------------------------------------------------------------------

/// The stack occupies array positions [top..cap). Element at index `top`
/// is the most recently pushed (top of stack). The logical Seq `s` maps
/// directly: s[i] = contents[top + i].
let is_gray_stack (st: gray_stack) (s: Seq.seq obj_addr) : slprop =
  exists* (t: SZ.t) (contents: Seq.seq U64.t).
    B.pts_to st.top t **
    V.pts_to st.storage contents **
    pure (
      SZ.v st.cap > 0 /\
      V.length st.storage == SZ.v st.cap /\
      V.is_full_vec st.storage /\
      Seq.length contents == SZ.v st.cap /\
      SZ.v t + Seq.length s == SZ.v st.cap /\
      SZ.v t <= SZ.v st.cap /\
      (forall (i:nat). i < Seq.length s ==>
        (Seq.index s i <: U64.t) == Seq.index contents (SZ.v t + i))
    )

/// ---------------------------------------------------------------------------
/// Helper Lemmas (pure F*)
/// ---------------------------------------------------------------------------

/// After writing addr at position top-1, the new stack view is Seq.cons addr old_s.
let push_stack_lemma
  (contents: Seq.seq U64.t) (top: nat) (cap: nat) (addr: obj_addr) (s: Seq.seq obj_addr)
  : Lemma
    (requires
      top > 0 /\
      top + Seq.length s == cap /\
      Seq.length contents == cap /\
      (forall (i:nat). i < Seq.length s ==>
        (Seq.index s i <: U64.t) == Seq.index contents (top + i)))
    (ensures (
      let contents' = Seq.upd contents (top - 1) (addr <: U64.t) in
      let s' = Seq.cons addr s in
      (top - 1) + Seq.length s' == cap /\
      Seq.length contents' == cap /\
      (forall (i:nat). i < Seq.length s' ==>
        (Seq.index s' i <: U64.t) == Seq.index contents' ((top - 1) + i))))
  = let contents' = Seq.upd contents (top - 1) (addr <: U64.t) in
    let s' = Seq.cons addr s in
    let aux (i:nat{i < Seq.length s'})
      : Lemma ((Seq.index s' i <: U64.t) == Seq.index contents' ((top - 1) + i))
      = if i = 0 then ()
        else begin
          // s'[i] = s[i-1] and contents'[top-1+i] = contents[top-1+i] (since top-1+i ≠ top-1)
          assert ((top - 1) + i == top + (i - 1));
          assert (top + (i - 1) <> top - 1)
        end
    in
    FStar.Classical.forall_intro aux

/// After pop, the tail of the logical stack corresponds to contents[top+1..].
let pop_stack_lemma
  (contents: Seq.seq U64.t) (top: nat) (cap: nat) (s: Seq.seq obj_addr)
  : Lemma
    (requires
      Seq.length s > 0 /\
      top + Seq.length s == cap /\
      Seq.length contents == cap /\
      (forall (i:nat). i < Seq.length s ==>
        (Seq.index s i <: U64.t) == Seq.index contents (top + i)))
    (ensures (
      let v = Seq.head s in
      let tl = Seq.tail s in
      (v <: U64.t) == Seq.index contents top /\
      (top + 1) + Seq.length tl == cap /\
      (forall (i:nat). i < Seq.length tl ==>
        (Seq.index tl i <: U64.t) == Seq.index contents ((top + 1) + i)) /\
      s == Seq.cons v tl))
  = let tl = Seq.tail s in
    let aux (i:nat{i < Seq.length tl})
      : Lemma ((Seq.index tl i <: U64.t) == Seq.index contents ((top + 1) + i))
      = // tail s = slice s 1 len, so index tl i = index s (i+1)
        assert (Seq.index tl i == Seq.index s (i + 1));
        assert ((top + 1) + i == top + (i + 1))
    in
    FStar.Classical.forall_intro aux;
    // s == cons (head s) (tail s)
    Seq.lemma_split s 1

/// ---------------------------------------------------------------------------
/// Stack Operations
/// ---------------------------------------------------------------------------

fn create_stack (storage: V.vec U64.t) (cap: SZ.t)
  requires V.pts_to storage 'init **
           pure (V.length storage == SZ.v cap /\ SZ.v cap > 0 /\
                 V.is_full_vec storage)
  returns st: gray_stack
  ensures is_gray_stack st (Seq.empty #obj_addr) **
          pure (stack_capacity st == SZ.v cap)
{
  V.pts_to_len storage;
  let top_box = B.alloc cap;
  let st : gray_stack = { storage = storage; top = top_box; cap = cap };
  rewrite (B.pts_to top_box cap) as (B.pts_to st.top cap);
  rewrite (V.pts_to storage 'init) as (V.pts_to st.storage 'init);
  fold (is_gray_stack st (Seq.empty #obj_addr));
  st
}

fn destroy_stack (st: gray_stack)
  requires is_gray_stack st 's
  returns storage: V.vec U64.t
  ensures exists* contents. V.pts_to storage contents **
          pure (V.length storage == stack_capacity st /\
                V.is_full_vec storage)
{
  unfold is_gray_stack;
  with t contents. _;
  B.free st.top;
  st.storage
}

fn is_empty (st: gray_stack)
  requires is_gray_stack st 's
  returns b: bool
  ensures is_gray_stack st 's ** pure (b <==> (Seq.length 's == 0))
{
  unfold is_gray_stack;
  with t contents. _;
  let top_val = B.op_Bang st.top;
  let b = (top_val = st.cap);
  fold (is_gray_stack st 's);
  b
}

fn is_full (st: gray_stack)
  requires is_gray_stack st 's
  returns b: bool
  ensures is_gray_stack st 's ** pure (b <==> (Seq.length 's == stack_capacity st))
{
  unfold is_gray_stack;
  with t contents. _;
  let top_val = B.op_Bang st.top;
  let b = (top_val = 0sz);
  fold (is_gray_stack st 's);
  b
}

fn stack_len (st: gray_stack)
  requires is_gray_stack st 's
  returns n: SZ.t
  ensures is_gray_stack st 's ** pure (SZ.v n == Seq.length 's)
{
  unfold is_gray_stack;
  with t contents. _;
  let top_val = B.op_Bang st.top;
  let n = SZ.sub st.cap top_val;
  fold (is_gray_stack st 's);
  n
}

#push-options "--z3rlimit 20"
fn push (st: gray_stack) (addr: obj_addr)
  requires is_gray_stack st 's ** pure (Seq.length 's < stack_capacity st)
  ensures is_gray_stack st (Seq.cons addr 's)
{
  unfold is_gray_stack;
  with t contents. _;
  let top_val = B.op_Bang st.top;
  let new_top = SZ.sub top_val 1sz;
  V.op_Array_Assignment st.storage new_top (addr <: U64.t);
  B.op_Colon_Equals st.top new_top;
  push_stack_lemma contents (SZ.v top_val) (SZ.v st.cap) addr 's;
  fold (is_gray_stack st (Seq.cons addr 's))
}
#pop-options

#push-options "--z3rlimit 20"
fn pop (st: gray_stack)
  requires is_gray_stack st 's ** pure (Seq.length 's > 0)
  returns v: obj_addr
  ensures exists* tl. is_gray_stack st tl ** pure ('s == Seq.cons v tl)
{
  unfold is_gray_stack;
  with t contents. _;
  let top_val = B.op_Bang st.top;
  let v_raw = V.op_Array_Access st.storage top_val;
  let new_top = SZ.add top_val 1sz;
  B.op_Colon_Equals st.top new_top;
  pop_stack_lemma contents (SZ.v top_val) (SZ.v st.cap) 's;
  fold (is_gray_stack st (Seq.tail 's));
  v_raw
}
#pop-options
