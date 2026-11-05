(*
   Pulse GC - Allocator Module Interface

   Free-list allocator for the verified GC.
   Takes the heap and the array of free-list heads (one per size class),
   updates both, and returns the allocated object address.
*)

module GC.Impl.Allocator

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
module SpecBase = GC.Spec.Base
module U64 = FStar.UInt64
module Seq = FStar.Seq
module SpecAlloc = GC.Spec.Allocator
module SpecFields = GC.Spec.Fields
module SpecObject = GC.Spec.Object
module SI = GC.Spec.SweepInv
module AllocLemmas = GC.Spec.Allocator.Lemmas
module SAL = GC.Spec.Allocator.Lists
module FLs = GC.Spec.FreeLists
module SC = GC.Spec.SizeClass

/// Initialize the heap as one large free block, on the list of its class.
///
/// The entire heap becomes a single blue object with wosize = (heap_size/8) - 1.
/// Its first field is set to 0 (end of free list); every other list is empty.
fn init_heap (heap: heap_t) (heads: array U64.t)
  requires is_heap heap 's ** pts_to heads 'fls **
           pure (Seq.length 'fls == SC.n_lists)
  ensures exists* s2 fls2. is_heap heap s2 ** pts_to heads fls2 **
    pure ((s2, fls2) == SAL.init_heap_lists_spec 's)

/// Allocate an object of wosize words from the free lists.
///
/// Parameters:
///   heap: mutable heap array
///   heads: the free-list heads, one per size class (GC.Spec.FreeLists);
///          updated in place
///   wosize: number of words needed
///
/// Returns the allocated object address, or 0UL if out of memory.
///
/// Postcondition ties the result to the pure spec alloc_lists_spec.
fn allocate (heap: heap_t) (heads: array U64.t) (wosize: U64.t)
  requires is_heap heap 's ** pts_to heads 'fls **
           // The allocator is never asked for a zero-word block: `gen_alloc`
           // requires wosize > 0, `promote_one` guards `wosize = 0` before
           // calling, and the C bridge's major path maps a request of 0 to 1
           // before calling (verified_gc/alloc_gen.c) -- OCaml represents a
           // zero-length block as a static Atom, never a heap allocation.
           // Stating it here lets the implementation drop the 0 -> 1 bump,
           // which was a compare-and-select on every major allocation for a
           // case that cannot occur.
           pure (SpecFields.well_formed_heap 's /\
                 U64.v wosize >= 1 /\
                 Seq.length 'fls == SC.n_lists)
  returns obj: U64.t
  ensures exists* s2 fls2. is_heap heap s2 ** pts_to heads fls2 **
    pure (let spec_res = SAL.alloc_lists_spec 's 'fls (U64.v wosize) in
          s2 == spec_res.heap_out /\
          fls2 == spec_res.fls_out /\
          obj == spec_res.obj_out)

/// Allocate with weaker precondition: only requires well_formed_heap_part1
/// + valid, terminating free lists. Suitable for use during promotion where
/// full well_formed_heap (part2: pointer closure) may be temporarily violated.
///
/// The implementation is identical to `allocate` — the allocator only reads
/// headers and free-list links, never inspecting object pointer fields.

fn allocate_part1 (heap: heap_t) (heads: array U64.t) (wosize: U64.t)
  requires is_heap heap 's ** pts_to heads 'fls **
           pure (SpecFields.well_formed_heap_part1 's /\
                 FLs.fls_valid 's 'fls /\
                 FLs.fls_terminates 's 'fls /\
                 U64.v wosize >= 1 /\
                 Seq.length 'fls == SC.n_lists)
  returns obj: U64.t
  ensures exists* s2 fls2. is_heap heap s2 ** pts_to heads fls2 **
    pure (let spec_res = SAL.alloc_lists_spec 's 'fls (U64.v wosize) in
          s2 == spec_res.heap_out /\
          fls2 == spec_res.fls_out /\
          obj == spec_res.obj_out)
