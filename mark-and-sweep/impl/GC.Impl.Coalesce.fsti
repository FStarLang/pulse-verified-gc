(*
   Pulse GC - Coalesce Module Interface

   Exports the coalesce entry point that merges adjacent free (blue) objects
   into larger free blocks, reducing heap fragmentation.
   Called after sweep, before returning the free list pointer.
*)

module GC.Impl.Coalesce

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
module U64 = FStar.UInt64
module Seq = FStar.Seq
module SpecCoalesce = GC.Spec.Coalesce
module SpecFields = GC.Spec.Fields
module SpecObject = GC.Spec.Object
module SI = GC.Spec.SweepInv

/// Coalesce pass: merge adjacent blue (free) objects into larger blocks.
/// Builds a fresh free list (starting from 0UL/null).
/// Returns the new free list head pointer.
///
/// Precondition: post_sweep heap (well_formed + all objects white or blue)
///               + objects list is non-empty + heap_objects_dense
/// Postcondition: coalesced heap matches spec, preserves wf, all objects white or blue
fn coalesce (heap: heap_t)
  requires is_heap heap 's **
           pure (SpecCoalesce.post_sweep_strong 's /\
                 Seq.length (SpecFields.objects zero_addr 's) > 0 /\
                 SI.heap_objects_dense 's)
  returns new_fp: U64.t
  ensures exists* s2. is_heap heap s2 **
    pure (SpecFields.well_formed_heap s2 /\
          (forall (x: obj_addr). Seq.mem x (SpecFields.objects zero_addr s2) ==>
            (SpecObject.is_white x s2 \/ SpecObject.is_blue x s2)) /\
          (s2, new_fp) == SpecCoalesce.coalesce 's)
