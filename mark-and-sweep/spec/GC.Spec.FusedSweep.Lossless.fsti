/// ---------------------------------------------------------------------------
/// GC.Spec.FusedSweep.Lossless - the sweep loses no free space
/// ---------------------------------------------------------------------------
///
/// The fused sweep (`GC.Spec.FusedSweep.fused_sweep_coalesce`) frees the dead
/// (non-black) blocks of the marked heap `g0` and merges neighbouring free
/// blocks.  This module states, word by word and in total, that it loses
/// nothing doing so:
///
///   * a word of the result lies in a free (blue) block exactly when it lay in
///     a dead block of `g0` (`blue_covered` / `dead_covered`);
///   * the free space of the result, in words, is the dead space of `g0`;
///   * no two free blocks of the result are adjacent;
///   * every live (black) block of `g0` is a white block of the result, at the
///     same address and size.
///
/// These are the clauses that `GC.Spec.Coalesce.Correct.coalesce_correct`
/// stated of the two-pass sweep+coalesce, with the swept heap `sweep g0`
/// replaced by `g0` itself: the swept heap's blue blocks were exactly `g0`'s
/// non-black ones, at the same sizes, and its white blocks `g0`'s black ones.

module GC.Spec.FusedSweep.Lossless

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module FS = GC.Spec.FusedSweep
module FSI = GC.Spec.FusedSweep.Inv
module W = GC.Spec.Walk

/// ---------------------------------------------------------------------------
/// Extents and coverage
/// ---------------------------------------------------------------------------

/// The walk position immediately above x.
let next_pos (g: heap) (x: obj_addr) : GTot nat =
  U64.v (hd_address x) + whsize g x * U64.v mword

/// y sits directly above x, with no gap.
let adjacent (g: heap) (x y: obj_addr) : prop =
  next_pos g x == U64.v (hd_address y)

/// p lies within x's header-and-fields extent.
let in_extent (g: heap) (x: obj_addr) (p: nat) : prop =
  U64.v (hd_address x) <= p /\ p < next_pos g x

/// p is covered by some blue (free) object.
let blue_covered (g: heap) (p: nat) : prop =
  exists (x: obj_addr).
    Seq.mem x (objects zero_addr g) /\ is_blue x g /\ in_extent g x p

/// p is covered by some dead (non-black) object.
let dead_covered (g: heap) (p: nat) : prop =
  exists (x: obj_addr).
    Seq.mem x (objects zero_addr g) /\ ~(is_black x g) /\ in_extent g x p

/// ---------------------------------------------------------------------------
/// Free and dead space
/// ---------------------------------------------------------------------------

/// Total whole size (header plus fields, in words) of the objects of `objs`
/// that satisfy `pr`.
let rec space (g: heap) (pr: obj_addr -> GTot bool) (objs: seq obj_addr)
  : GTot nat (decreases Seq.length objs) =
  if Seq.length objs = 0 then 0
  else
    let x = Seq.head objs in
    (if pr x then whsize g x else 0) + space g pr (Seq.tail objs)

/// Total whole size of the blue objects of the walk.
let total_free_space (g: heap) : GTot nat =
  space g (fun x -> is_blue x g) (objects zero_addr g)

/// Total whole size of the dead (non-black) objects of the walk.
let total_dead_space (g: heap) : GTot nat =
  space g (fun x -> not (is_black x g)) (objects zero_addr g)

/// ---------------------------------------------------------------------------
/// The statement
/// ---------------------------------------------------------------------------

let sweep_lossless (g0 g: heap) : prop =
  total_free_space g == total_dead_space g0 /\
  (forall (p: nat). p < heap_size ==> (blue_covered g p <==> dead_covered g0 p)) /\
  (forall (x y: obj_addr).
     Seq.mem x (objects zero_addr g) /\ Seq.mem y (objects zero_addr g) /\
     is_blue x g /\ is_blue y g /\ adjacent g x y ==> False) /\
  (forall (x: obj_addr).
     Seq.mem x (objects zero_addr g0) /\ is_black x g0 ==>
     Seq.mem x (objects zero_addr g) /\ is_white x g /\
     wosize_of_object x g == wosize_of_object x g0)

/// The sweep leaves the walk ending where it ended.
val fused_sweep_walk_end (g0: heap) (fp: U64.t)
  : Lemma (requires FSI.sweep_pre g0 fp)
          (ensures W.walk_end (fst (FS.fused_sweep_coalesce g0 fp)) zero_addr ==
                   W.walk_end g0 zero_addr)

/// Every word of a dead block of `g0` is in a free block of the result.
val fused_dead_covered (g0: heap) (fp: U64.t) (x: obj_addr) (p: nat)
  : Lemma (requires FSI.sweep_pre g0 fp /\
                    Seq.mem x (objects zero_addr g0) /\ ~(is_black x g0) /\ in_extent g0 x p)
          (ensures blue_covered (fst (FS.fused_sweep_coalesce g0 fp)) p)

/// **The sweep is lossless.**
val fused_sweep_lossless (g0: heap) (fp: U64.t)
  : Lemma (requires FSI.sweep_pre g0 fp)
          (ensures sweep_lossless g0 (fst (FS.fused_sweep_coalesce g0 fp)))
