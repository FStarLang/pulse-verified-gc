(*
   Pulse GC - the fused sweep

   One pass over the heap that whitens survivors, frees garbage, merges
   adjacent free blocks and keeps the free list -- headed by `fp`, kept
   across collections and edited in place -- exact and in address order.
   It computes exactly `GC.Spec.FusedSweep.fused_sweep_coalesce`.
*)

module GC.Impl.FusedSweepCoalesce

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
module U64 = FStar.UInt64
module FS = GC.Spec.FusedSweep
module FSI = GC.Spec.FusedSweep.Inv

/// Precondition: the marked heap's walk covers it and the free list is exact
/// and ascending (`FSI.sweep_pre`).  Postcondition: the result is the spec's.
fn fused_sweep_coalesce (heap: heap_t) (fp: U64.t)
  requires is_heap heap 's ** pure (FSI.sweep_pre 's fp)
  returns new_fp: U64.t
  ensures exists* s2. is_heap heap s2 **
    pure ((s2, new_fp) == FS.fused_sweep_coalesce 's fp)
