/// Test file demonstrating the seq_mem lemmas work with U64.t sequences
/// as used in Pulse.Spec.GC.Mark

module Pulse.Spec.GC.SeqMemLemmas.Test

open FStar.Seq
open FStar.UInt64
module U64 = FStar.UInt64

open Pulse.Spec.GC.SeqMemLemmas

/// Test 1: seq_mem_cons_tail with U64.t
/// Matches the usage at Mark.fst line 505
let test_cons_tail_u64 (v: U64.t) (st: seq U64.t) (addr: U64.t)
  : Lemma 
    (requires Seq.mem addr st)
    (ensures (let st'' = Seq.cons v st in Seq.mem addr st''))
  = 
  let st'' = Seq.cons v st in
  seq_mem_cons_tail v addr st

/// Test 2: seq_mem_cons_head with U64.t
let test_cons_head_u64 (v: U64.t) (st: seq U64.t)
  : Lemma (ensures Seq.mem v (Seq.cons v st))
  = 
  seq_mem_cons_head v st

/// Test 3: Combined usage - both v and existing elements are members
let test_combined (v: U64.t) (st: seq U64.t) (addr: U64.t)
  : Lemma 
    (requires Seq.mem addr st)
    (ensures (let st' = Seq.cons v st in 
              Seq.mem v st' /\     // v is in the new sequence
              Seq.mem addr st'))   // addr is still in the new sequence
  =
  let st' = Seq.cons v st in
  seq_mem_cons_head v st;
  seq_mem_cons_tail v addr st

/// Test 4: Multiple cons operations preserve membership
let test_multiple_cons (v1 v2: U64.t) (st: seq U64.t) (addr: U64.t)
  : Lemma
    (requires Seq.mem addr st)
    (ensures (let st' = Seq.cons v1 st in
              let st'' = Seq.cons v2 st' in
              Seq.mem addr st''))
  =
  let st' = Seq.cons v1 st in
  seq_mem_cons_tail v1 addr st;
  let st'' = Seq.cons v2 st' in
  seq_mem_cons_tail v2 addr st'
