/// ---------------------------------------------------------------------------
/// GC.Spec.FusedSweep.Facts - corollaries at the heap the collector produces
/// ---------------------------------------------------------------------------
///
/// The statements below are about `GC.Spec.FusedSweep.fused_sweep_coalesce`,
/// the pass `GC.Impl.collect_with_roots` runs, under the mark postcondition and
/// the free list the previous cycle left.  Each is a corollary of the sweep's
/// end lemma (`GC.Spec.FusedSweep.End.sweep_post`).

module GC.Spec.FusedSweep.Facts

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module FS = GC.Spec.FusedSweep
module FSE = GC.Spec.FusedSweep.End
module Corr = GC.Spec.Correctness
module Part = GC.Spec.Partition
module W = GC.Spec.Walk

#set-options "--fuel 0 --ifuel 0 --z3rlimit 30"

/// **The free list the collector leaves is exact**: it holds exactly the free
/// blocks with room for a link -- in address order (`fl_ascending`).
let fused_exact (h_init h_mark: heap) (roots: seq obj_addr) (fp: U64.t)
  : Lemma
    (requires Corr.mark_post h_init h_mark roots fp /\ FLA.fl_ascending h_init fp)
    (ensures (let r = FS.fused_sweep_coalesce h_mark fp in
              FL.fl_exact (fst r) (snd r) /\ FLA.fl_ascending (fst r) (snd r)))
  = let r = FS.fused_sweep_coalesce h_mark fp in
    Corr.fused_post_gen h_init h_mark roots fp;
    FSE.sweep_post_elim h_mark (fst r) (snd r);
    FLA.fl_ascending_exact (fst r) (snd r)

/// **The partition, at the heap the collector produces**: live words, plus the
/// words on the free list, plus the fragments, are exactly the heap the walk
/// covers.  Nothing free has been lost track of.
let fused_partition (h_init h_mark: heap) (roots: seq obj_addr) (fp: U64.t)
  : Lemma
    (requires Corr.mark_post h_init h_mark roots fp /\ FLA.fl_ascending h_init fp)
    (ensures (
      let r = FS.fused_sweep_coalesce h_mark fp in
      let g' = fst r in
      let objs = objects zero_addr g' in
      U64.v zero_addr
      + (Part.white_whsize g' objs
         + Part.onchain_whsize g' (snd r) objs
         + Part.frag_whsize g' objs) * U64.v mword
      == W.walk_end g' zero_addr))
  = let r = FS.fused_sweep_coalesce h_mark fp in
    fused_exact h_init h_mark roots fp;
    Corr.fused_post_gen h_init h_mark roots fp;
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires (FSE.sweep_post_white_or_blue h_mark (fst r) (snd r)));
    Part.heap_partition_strong (fst r) (snd r)

/// **The sweep is correct**: every live object stays where it was, white, with
/// its size, tag and fields; every dead block lies inside a free block; every
/// free block holds only dead blocks; no two free blocks are adjacent; every
/// block of the result is a live object or free.
let fused_sweep_correct (h_init h_mark: heap) (roots: seq obj_addr) (fp: U64.t)
  : Lemma
    (requires Corr.mark_post h_init h_mark roots fp /\ FLA.fl_ascending h_init fp)
    (ensures (
      let g' = fst (FS.fused_sweep_coalesce h_mark fp) in
      (forall (x: obj_addr). Seq.mem x (objects zero_addr h_mark) /\ is_black x h_mark ==>
         FSE.survives h_mark g' x) /\
      (forall (x: obj_addr). Seq.mem x (objects zero_addr h_mark) /\ ~(is_black x h_mark) ==>
         (exists (y: obj_addr). Seq.mem y (objects zero_addr g') /\ is_blue y g' /\
                                FSE.inside h_mark g' x y)) /\
      (forall (x y: obj_addr). Seq.mem y (objects zero_addr g') /\ is_blue y g' /\
         Seq.mem x (objects zero_addr h_mark) /\ FSE.inside h_mark g' x y ==>
         ~(is_black x h_mark)) /\
      (forall (x y: obj_addr). Seq.mem x (objects zero_addr g') /\ Seq.mem y (objects zero_addr g') /\
         is_blue x g' /\ is_blue y g' ==> ~(FSE.adjacent g' x y)) /\
      (forall (x: obj_addr). Seq.mem x (objects zero_addr g') ==>
         Seq.mem x (objects zero_addr h_mark) /\ (is_white x g' \/ is_blue x g'))))
  = let r = FS.fused_sweep_coalesce h_mark fp in
    Corr.fused_post_gen h_init h_mark roots fp;
    FSE.sweep_post_elim h_mark (fst r) (snd r);
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires (FSE.sweep_post_white_or_blue h_mark (fst r) (snd r)))
