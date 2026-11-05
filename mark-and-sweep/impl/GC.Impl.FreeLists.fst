(*
   Pulse GC - Free-list heads

   The allocator state is an array of `n_lists` list heads, one per size class
   (GC.Spec.FreeLists).  This module holds the operations on the array itself.
*)

module GC.Impl.FreeLists

#lang-pulse

#set-options "--fuel 0 --ifuel 0 --z3rlimit 12"

open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Seq = FStar.Seq
module SC = GC.Spec.SizeClass
module FLs = GC.Spec.FreeLists

/// The list of a block of wosize `w` (`GC.Spec.SizeClass.size_class`).
inline_for_extraction
let class_of (w: U64.t) : (c: SZ.t{SZ.v c == SC.size_class (U64.v w) /\ SZ.v c < SC.n_lists}) =
  SC.n_small_u64_v ();
  if U64.gte w 1UL && U64.lte w SC.n_small_u64
  then begin
    SC.size_class_lt (U64.v w);
    FStar.SizeT.fits_at_least_16 (U64.v w);
    SZ.uint64_to_sizet w
  end
  else 0sz

/// Empty every list: all heads become 0.
fn clear_heads (heads: array U64.t)
  requires pts_to heads 'fls ** pure (Seq.length 'fls == SC.n_lists)
  ensures pts_to heads FLs.fls_empty
{
  SC.n_lists_sz_v ();
  let mut i = 0sz;
  while (SZ.lt !i SC.n_lists_sz)
    invariant exists* vi s.
      R.pts_to i vi **
      pts_to heads s **
      pure (SZ.v vi <= SC.n_lists /\ Seq.length s == SC.n_lists /\
            (forall (j: nat). j < SZ.v vi ==> Seq.index s j == 0UL))
    decreases (SC.n_lists - SZ.v !i)
  {
    let vi = !i;
    heads.(vi) <- 0UL;
    i := SZ.add vi 1sz
  };
  with s. assert (pts_to heads s);
  assert (pure (Seq.equal s FLs.fls_empty));
  rewrite (pts_to heads s) as (pts_to heads FLs.fls_empty)
}
