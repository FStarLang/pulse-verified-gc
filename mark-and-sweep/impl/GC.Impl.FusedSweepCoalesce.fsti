(*
   Pulse GC - Fused Sweep+Coalesce Module Interface

   Exports the fused_sweep_coalesce entry point that combines sweep and
   coalesce into a single pass over the heap. Replaces the two-pass
   sweep-then-coalesce approach.
*)

module GC.Impl.FusedSweepCoalesce

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
module U64 = FStar.UInt64
module Seq = FStar.Seq
module Defs = GC.Spec.SweepCoalesce.Defs
module SpecFields = GC.Spec.Fields
module SpecObject = GC.Spec.Object
module SI = GC.Spec.SweepInv

/// Fused sweep+coalesce pass: walk all objects, whiten survivors,
/// merge adjacent free blocks, and build a fresh free list.
/// Returns the new free list head pointer.
///
/// Precondition: well_formed heap, no gray objects (mark phase complete),
///               objects list is non-empty + dense
/// Postcondition: result matches the fused_sweep_coalesce spec
fn fused_sweep_coalesce (heap: heap_t)
  requires is_heap heap 's **
           pure (SpecFields.well_formed_heap 's /\
                 Seq.length (SpecFields.objects zero_addr 's) > 0 /\
                 SI.heap_objects_dense 's /\
                 (forall (x: obj_addr).
                   Seq.mem x (SpecFields.objects zero_addr 's) ==>
                   ~(SpecObject.is_gray x 's)))
  returns new_fp: U64.t
  ensures exists* s2. is_heap heap s2 **
    pure ((s2, new_fp) == Defs.fused_sweep_coalesce 's)
