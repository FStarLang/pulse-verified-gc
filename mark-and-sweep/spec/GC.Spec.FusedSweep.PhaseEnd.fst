module GC.Spec.FusedSweep.PhaseEnd

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.FusedSweep.Phase

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module FLA = GC.Spec.FreeList.Ascending
module FSE = GC.Spec.FusedSweep.End
module FStep = GC.Spec.FusedSweep.Step
module AC = GC.Spec.Allocator.Cursor
module Oom = GC.Spec.Allocator.Oom
module FL = GC.Spec.FreeList

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// The colour predicates of an object are those of its header.
let colour_of (g: heap) (x: obj_addr)
  : Lemma (let q = hd_address x in
           (is_black x g <==> black_at g q) /\ (is_blue x g <==> blue_at g q) /\
           U64.v (wosize_of_object x g) == wz_at g q /\
           tag_of_object x g == getTag (read_word g q))
  = color_of_object_spec x g;
    is_black_iff x g; is_blue_iff x g;
    wosize_of_object_spec x g; tag_of_object_spec x g

/// A live object of `g0` is a black object of the reference heap, with the
/// same header.
#push-options "--z3rlimit 30"
let live_in_ref (g0 g1: heap) (x: obj_addr)
  : Lemma (requires keeps_live g0 g1 /\ Seq.mem x (objects zero_addr g0) /\ is_black x g0)
          (ensures Seq.mem x (objects zero_addr g1) /\ is_black x g1 /\
                   wosize_of_object x g1 == wosize_of_object x g0 /\
                   tag_of_object x g1 == tag_of_object x g0)
  = W.objects_mem_iff g0 zero_addr x;
    W.objects_mem_iff g1 zero_addr x;
    W.hd_address_pos x;
    colour_of g0 x; colour_of g1 x;
    keeps_live_elim g0 g1 (hd_address x)
#pop-options

#push-options "--z3rlimit 30"
let sweeping_end g0 g1 g fp st =
  FSE.sweep_done_post g1 g fp;
  FSE.sweep_post_elim g1 g fp;
  let wb (x: obj_addr)
    : Lemma (requires Seq.mem x (objects zero_addr g))
            (ensures is_white x g \/ is_blue x g)
    = FSE.sweep_post_white_or_blue g1 g fp x in
  FStar.Classical.forall_intro (FStar.Classical.move_requires wb);
  let live (x: obj_addr)
    : Lemma (requires Seq.mem x (objects zero_addr g0) /\ is_black x g0)
            (ensures Seq.mem x (objects zero_addr g) /\ is_white x g /\
                     wosize_of_object x g == wosize_of_object x g0 /\
                     tag_of_object x g == tag_of_object x g0)
    = live_in_ref g0 g1 x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires live)
#pop-options

#push-options "--z3rlimit 30"
let sweeping_oom_no_fit g0 g1 g fp st wz tag =
  sweep_inv_elim g1 g fp st;
  AC.alloc_phase_fields g fp (GC.Spec.Phase.Sweeping st) wz tag;
  FLA.fl_ascending_valid g fp;
  FLA.fl_ascending_exact g fp;
  GC.Spec.FusedSweep.Edit.part1_holds g;
  Oom.alloc_spec_oom_no_fit g fp wz tag
#pop-options
