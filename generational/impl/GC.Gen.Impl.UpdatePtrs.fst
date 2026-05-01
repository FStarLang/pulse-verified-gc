/// ---------------------------------------------------------------------------
/// GC.Gen.Impl.UpdatePtrs — Rewrite roots after promotion
/// ---------------------------------------------------------------------------
///
/// Implements rewrite_roots: for each root that is a minor pointer with a
/// forwarding entry, replace it with the new major-heap address.

module GC.Gen.Impl.UpdatePtrs

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Gen.Base
open GC.Impl.Heap
module PromoteSpec = GC.Gen.Promote

/// ---------------------------------------------------------------------------
/// Pure helper: compute rewrite for a single value
/// ---------------------------------------------------------------------------

/// Compute what rewrite_root does, purely in terms of the array contents
let rewrite_root_arr (farr: Seq.seq U64.t) (v: U64.t) : GTot U64.t =
  if Seq.length farr = fwd_array_size &&
     U64.v v >= 8 && U64.v v < minor_heap_size && U64.v v % 8 = 0 then
    let idx = U64.v v / 8 in
    let fv = Seq.index farr idx in
    if fv <> 0UL then fv else v
  else v

/// Connection lemma: rewrite_root_arr matches rewrite_root when represents_fwd holds
let rewrite_root_arr_spec (farr: Seq.seq U64.t)
                          (fwd: PromoteSpec.forwarding_map) (v: U64.t)
  : Lemma (requires Seq.length farr == fwd_array_size /\ represents_fwd farr fwd)
          (ensures rewrite_root_arr farr v == PromoteSpec.rewrite_root v fwd) =
  ()

/// Safe wrapper: compute the result of rewriting at a given index
let rewrite_at_spec (rs: Seq.seq U64.t) (farr: Seq.seq U64.t) (iv: nat) : GTot (Seq.seq U64.t) =
  if iv < Seq.length rs && Seq.length farr = fwd_array_size
  then Seq.upd rs iv (rewrite_root_arr farr (Seq.index rs iv))
  else rs

/// ---------------------------------------------------------------------------
/// Rewrite one root at a given index (factored out for clean branch merging)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
inline_for_extraction
fn rewrite_at_index (roots: array U64.t) (fwd_arr: array U64.t) (iv: SZ.t)
  requires pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pure (SZ.v iv < Seq.length 'rs /\
                 Seq.length 'farr == fwd_array_size)
  ensures exists* rs2.
    pts_to roots rs2 **
    pts_to fwd_arr 'farr **
    pure (rs2 == rewrite_at_spec 'rs 'farr (SZ.v iv))
{
  let r = roots.(iv);
  if U64.gte r 8UL {
    if U64.lt r minor_heap_size_u64 {
      if U64.eq (U64.rem r 8UL) 0UL {
        let idx = SZ.uint64_to_sizet (U64.div r 8UL);
        let fwd_val = fwd_arr.(idx);
        if U64.eq fwd_val 0UL {
          roots.(iv) <- r
        } else {
          roots.(iv) <- fwd_val
        }
      } else {
        roots.(iv) <- r
      }
    } else {
      roots.(iv) <- r
    }
  } else {
    roots.(iv) <- r
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// Rewrite roots loop
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"
inline_for_extraction
fn rewrite_roots_impl
  (roots: array U64.t)
  (fwd_arr: array U64.t)
  (n: SZ.t)
  requires pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pure (SZ.v n == Seq.length 'rs /\
                 Seq.length 'farr == fwd_array_size /\
                 represents_fwd 'farr 'fwd)
  ensures exists* rs2.
    pts_to roots rs2 **
    pts_to fwd_arr 'farr **
    pure (Seq.length rs2 == Seq.length 'rs /\
          rs2 == PromoteSpec.rewrite_roots 'rs 'fwd)
{
  let mut i = 0sz;
  while (SZ.lt !i n)
    invariant exists* rs_i iv.
      pts_to roots rs_i **
      pts_to fwd_arr 'farr **
      R.pts_to i iv **
      pure (SZ.v iv <= Seq.length 'rs /\
            SZ.v n == Seq.length 'rs /\
            Seq.length rs_i == Seq.length 'rs /\
            Seq.length 'farr == fwd_array_size /\
            represents_fwd 'farr 'fwd /\
            (forall (j: nat). j < SZ.v iv ==>
              Seq.index rs_i j == PromoteSpec.rewrite_root (Seq.index 'rs j) 'fwd) /\
            (forall (j: nat). j >= SZ.v iv /\ j < Seq.length 'rs ==>
              Seq.index rs_i j == Seq.index 'rs j))
  {
    let iv = !i;
    rewrite_at_index roots fwd_arr iv;
    rewrite_root_arr_spec 'farr 'fwd (Seq.index 'rs (SZ.v iv));
    i := SZ.add iv 1sz
  };
  // After loop: iv == n, so forall j < n. Seq.index rs_final j == rewrite_root ...
  // Bind the array witness and establish the connection
  with rs_final. assert (pts_to roots rs_final);
  assert (pure (Seq.length rs_final == Seq.length 'rs));
  assert (pure (forall (j: nat). j < Seq.length 'rs ==>
    Seq.index rs_final j == PromoteSpec.rewrite_root (Seq.index 'rs j) 'fwd));
  PromoteSpec.rewrite_roots_pointwise 'rs 'fwd rs_final;
  PromoteSpec.rewrite_roots_length 'rs 'fwd
}
#pop-options
