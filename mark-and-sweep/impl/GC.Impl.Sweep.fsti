(*
   Pulse GC - Sweep Module Interface

   Exports the sweep entry point for the sweep phase.
*)

module GC.Impl.Sweep

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
module U64 = FStar.UInt64
module Seq = FStar.Seq
module SpecSweep = GC.Spec.Sweep
module SpecFields = GC.Spec.Fields
module SpecObject = GC.Spec.Object
module SI = GC.Spec.SweepInv

/// Sweep phase: reset black objects to white, build free list.
/// Returns new free pointer.
fn sweep (heap: heap_t) (fp: U64.t)
  requires is_heap heap 's ** pure (SpecFields.well_formed_heap 's /\
                                     Seq.length (SpecFields.objects zero_addr 's) > 0 /\
                                     SI.heap_objects_dense 's /\
                                     SI.fp_valid fp 's /\
                                     SI.no_gray_objects 's)
  returns final_fp: U64.t
  ensures exists* s2. is_heap heap s2 **
    pure (SpecFields.well_formed_heap s2 /\
          (forall (x: obj_addr). Seq.mem x (SpecFields.objects zero_addr s2) ==>
            (SpecObject.is_white x s2 \/ SpecObject.is_blue x s2)) /\
          (s2, final_fp) == SpecSweep.sweep 's fp)
