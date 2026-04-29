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

/// Flush a pending blue run: write merged header, link, and zero remaining fields.
/// Shared helper used by both coalesce and fused_sweep_coalesce.
fn flush_blue_impl (heap: heap_t) (fb: U64.t) (rw: U64.t) (fp: U64.t)
  requires is_heap heap 's **
           pure (Seq.length 's == heap_size /\
                 (U64.v rw > 0 ==>
                   U64.v rw < pow2 54 /\
                   U64.v fb >= U64.v mword /\
                   U64.v fb < heap_size /\
                   U64.v fb % U64.v mword == 0 /\
                   U64.v fb - U64.v mword + op_Star (U64.v rw) (U64.v mword) <= heap_size))
  returns res: (U64.t & U64.t)
  ensures exists* s2. is_heap heap s2 **
           pure ((s2, snd res) == SpecCoalesce.flush_blue 's fb (U64.v rw) fp /\
                 fst res == 0UL /\
                 Seq.length s2 == heap_size)
