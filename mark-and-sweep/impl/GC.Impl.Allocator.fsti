(*
   Pulse GC - Allocator Module Interface

   First-fit free-list allocator for the verified GC.
   Takes the heap and current free-list head, returns updated heap
   and new free-list head along with the allocated object address.
*)

module GC.Impl.Allocator

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
module U64 = FStar.UInt64
module Seq = FStar.Seq
module SpecAlloc = GC.Spec.Allocator
module SpecFields = GC.Spec.Fields
module SpecObject = GC.Spec.Object
module SI = GC.Spec.SweepInv

/// Allocate an object of wosize words from the free list.
///
/// Parameters:
///   heap: mutable heap array
///   fp: current free-list head (obj_addr of first free block, or 0UL)
///   wosize: number of words needed (bumped to 1 if 0)
///
/// Returns: (new_fp, obj_addr)
///   new_fp: updated free-list head
///   obj_addr: allocated object address, or 0UL if out of memory
///
/// Postcondition ties the result to the pure spec alloc_spec.
fn allocate (heap: heap_t) (fp: U64.t) (wosize: U64.t)
  requires is_heap heap 's **
           pure (SpecFields.well_formed_heap 's)
  returns res: (U64.t & U64.t)
  ensures exists* s2. is_heap heap s2 **
    pure (let spec_res = SpecAlloc.alloc_spec 's fp (U64.v wosize) in
          s2 == spec_res.heap_out /\
          fst res == spec_res.fp_out /\
          snd res == spec_res.obj_out)

/// Initialize the heap as one large free block.
///
/// The entire heap becomes a single blue object with wosize = (heap_size/8) - 1.
/// Its first field is set to 0 (end of free list).
///
/// Returns the initial free-list pointer (= mword = 8).
fn init_heap (heap: heap_t)
  requires is_heap heap 's
  returns fp: U64.t
  ensures exists* s2. is_heap heap s2 **
    pure ((s2, fp) == SpecAlloc.init_heap_spec 's)
