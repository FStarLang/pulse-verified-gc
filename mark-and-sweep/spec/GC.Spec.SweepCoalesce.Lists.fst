/// ---------------------------------------------------------------------------
/// GC.Spec.SweepCoalesce.Lists - the fused sweep, building the size lists
/// ---------------------------------------------------------------------------
///
/// The same pass as `GC.Spec.SweepCoalesce.Defs.fused_aux`, except that each
/// flushed run is pushed on the list of its class rather than on the one free
/// list.  The flush is `GC.Spec.Coalesce.flush_blue` itself, handed the head of
/// that list: the heap writes are exactly the single-list pass's, with a
/// different value in the run's link word.  Every list starts empty, so the
/// lists handed in are ignored, as the single list is today.

module GC.Spec.SweepCoalesce.Lists

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.SizeClass
open GC.Spec.FreeLists

module SpecCoalesce = GC.Spec.Coalesce

/// The list a run of `run_words` words (header included) goes on.
let run_class (run_words: nat) : nat =
  if run_words >= 2 then size_class (run_words - 1) else 0

/// Flush a pending run onto the list of its class.
let flush_blue_lists (g: heap) (first_blue: U64.t) (run_words: nat) (fls: fl_state)
  : GTot (heap & fl_state)
  = let c = run_class run_words in
    let (g', fp') = SpecCoalesce.flush_blue g first_blue run_words (fls_head fls c) in
    (g', fls_set fls c fp')

/// The fused pass over the remaining objects.
let rec fused_aux_lists (g0: heap) (g: heap) (objs: seq obj_addr)
    (fb: U64.t) (rw: nat) (fls: fl_state)
  : GTot (heap & fl_state) (decreases Seq.length objs)
  = if Seq.length objs = 0 then
      flush_blue_lists g fb rw fls
    else
      let obj = Seq.head objs in
      let rest = Seq.tail objs in
      if is_black obj g0 then
        let (g', fls') = flush_blue_lists g fb rw fls in
        let g'' = makeWhite obj g' in
        fused_aux_lists g0 g'' rest 0UL 0 fls'
      else
        let ws = U64.v (wosize_of_object obj g0) in
        let new_fb : U64.t = if rw = 0 then obj else fb in
        fused_aux_lists g0 g rest new_fb (rw + ws + 1) fls

/// The whole pass: every list starts empty.
let fused_sweep_coalesce_lists (g: heap) : GTot (heap & fl_state) =
  fused_aux_lists g g (objects zero_addr g) 0UL 0 fls_empty
