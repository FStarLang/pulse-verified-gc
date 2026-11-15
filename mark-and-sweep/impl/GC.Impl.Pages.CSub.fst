/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.CSub - a range of an array as an array of its own
/// ---------------------------------------------------------------------------
///
/// A chunk of the parallel sweep owns a range of the heap's bytes and a
/// range of the chunks' records (a `pts_to_range`).  To read and write a
/// heap word with the word primitives of `GC.Impl.ArrayWord`, which take a
/// whole array, the range is cut out as an array of its own with Pulse's
/// `Pulse.Lib.Array.Core.sub` (a pointer addition in C), and given back at
/// the end.  `sub_rest` is what the cut leaves of the array: nothing, as a
/// mask.

module GC.Impl.Pages.CSub

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsToRange

module A = Pulse.Lib.Array
module AC = Pulse.Lib.Array.Core
module APT = Pulse.Lib.Array.PtsTo
module SZ = FStar.SizeT
module Seq = FStar.Seq

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// What cutting `[i, j)` out of `a` as `d` leaves of `a`.
let sub_rest (#t: Type0) (a: A.array t) (i j: nat) (d: A.array t) : slprop =
  exists* (v: Seq.seq (option t)) (m: nat -> prop).
    AC.pts_to_mask a v m **
    pure (i <= j /\ j <= AC.length a /\ d == AC.gsub a i j /\ Seq.length v == AC.length a /\
          (forall (k: nat). ~(m k)))

/// Cut the range `[i, j)` of `a` out as an array.
fn range_sub (#t: Type0) (a: A.array t) (i: SZ.t) (j: erased nat) (#s: erased (Seq.seq t))
  requires pts_to_range a (SZ.v i) j s
  returns d: A.array t
  ensures A.pts_to d s ** sub_rest a (SZ.v i) j d
{
  pts_to_range_prop a;
  unfold_pts_to_range a (SZ.v i) j s;
  with s0. assert (AC.pts_to_mask (AC.gsub a (SZ.v i) j) s0 (fun _ -> True));
  AC.gsub_elim a (SZ.v i) j;
  with v0. assert (AC.pts_to_mask a v0 (fun k -> SZ.v i <= k /\ k < j /\ True));
  let d = AC.sub a i j;
  with vs ms. assert (AC.pts_to_mask d vs ms);
  APT.from_mask d;
  with s1. assert (A.pts_to d s1);
  assert (pure (Seq.equal s1 s));
  rewrite (A.pts_to d s1) as (A.pts_to d s);
  fold (sub_rest a (SZ.v i) j d);
  d
}

/// Give the array cut out back to its range.
ghost fn range_unsub (#t: Type0) (a: A.array t) (i j: nat) (d: A.array t) (#s: erased (Seq.seq t))
  requires A.pts_to d s ** sub_rest a i j d
  ensures pts_to_range a i j s
{
  unfold sub_rest;
  with v m. assert (AC.pts_to_mask a v m);
  APT.to_mask d;
  with sv. assert (AC.pts_to_mask d sv (fun _ -> True));
  rewrite (AC.pts_to_mask d sv (fun _ -> True)) as (AC.pts_to_mask (AC.gsub a i j) sv (fun _ -> True));
  AC.return_sub a #1.0R #v #sv #m #(fun _ -> True) #i #j;
  with v1. assert (AC.pts_to_mask a v1 (fun k -> m k \/ (i <= k /\ k < j /\ True)));
  AC.gsub_intro a i j;
  with s2. assert (AC.pts_to_mask (AC.gsub a i j) s2 (fun k -> m (k + i) \/ (i <= k + i /\ k + i < j /\ True)));
  fold_pts_to_range a i j #1.0R #s2 s #(fun k -> m (k + i) \/ (i <= k + i /\ k + i < j /\ True))
}

/// The same range, named by equal bounds.
ghost fn range_idx (#t: Type0) (a: A.array t) (#i #j: nat) (i' j': nat) (#s: Seq.seq t)
  requires pts_to_range a i j s ** pure (i == i' /\ j == j')
  ensures pts_to_range a i' j' s
{
  rewrite (pts_to_range a i j s) as (pts_to_range a i' j' s)
}

/// `s`'s elements `[i, j)`, or nothing when they are not in `s`.
noextract
let tsl (#t: Type0) (s: Seq.seq t) (i j: nat) : Seq.seq t =
  if i <= j && j <= Seq.length s then Seq.slice s i j else Seq.empty

/// An array as three ranges: `[0, i)`, `[i, j)` and `[j, n)`.
ghost fn split3 (#t: Type0) (a: A.array t) (i j: nat) (#s: Seq.seq t)
  requires A.pts_to a s ** pure (i <= j /\ j <= Seq.length s)
  ensures pts_to_range a 0 i (tsl s 0 i) ** pts_to_range a i j (tsl s i j) **
          pts_to_range a j (Seq.length s) (tsl s j (Seq.length s)) **
          pure (AC.length a == Seq.length s)
{
  APT.pts_to_len a;
  pts_to_range_intro a 1.0R s;
  rewrite (pts_to_range a 0 (AC.length a) s) as (pts_to_range a 0 (Seq.length s) s);
  pts_to_range_split a 0 i (Seq.length s);
  with s1 s2. assert (pts_to_range a 0 i s1 ** pts_to_range a i (Seq.length s) s2);
  pts_to_range_split a i j (Seq.length s);
  with s3 s4. assert (pts_to_range a i j s3 ** pts_to_range a j (Seq.length s) s4);
  assert (pure (Seq.equal s3 (tsl s i j)));
  assert (pure (Seq.equal s1 (tsl s 0 i)));
  rewrite (pts_to_range a 0 i s1) as (pts_to_range a 0 i (tsl s 0 i));
  assert (pure (Seq.equal s4 (tsl s j (Seq.length s))));
  rewrite (pts_to_range a i j s3) as (pts_to_range a i j (tsl s i j));
  rewrite (pts_to_range a j (Seq.length s) s4) as (pts_to_range a j (Seq.length s) (tsl s j (Seq.length s)))
}

/// Three ranges back into the array.
ghost fn join3 (#t: Type0) (a: A.array t) (i j n: nat) (#s1 #s2 #s3: Seq.seq t)
  requires pts_to_range a 0 i s1 ** pts_to_range a i j s2 ** pts_to_range a j n s3 ** pure (n == AC.length a)
  ensures A.pts_to a (Seq.append s1 (Seq.append s2 s3))
{
  pts_to_range_join a i j n;
  pts_to_range_join a 0 i n;
  rewrite (pts_to_range a 0 n (Seq.append s1 (Seq.append s2 s3)))
       as (pts_to_range a 0 (AC.length a) (Seq.append s1 (Seq.append s2 s3)));
  pts_to_range_elim a 1.0R (Seq.append s1 (Seq.append s2 s3))
}
