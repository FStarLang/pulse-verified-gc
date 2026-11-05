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
module OT = GC.Spec.ObjectTable

/// Initialize the heap as one large free block, on the list of its class.
///
/// The entire heap becomes a single blue object with wosize = (heap_size/8) - 1.
/// Its first field is set to 0 (end of free list); every other list is empty.
/// The object-start table `tbl` (GC.Spec.ObjectTable) is rebuilt for the
/// resulting heap.
fn init_heap (heap: heap_t) (heads: array U64.t) (tbl: array U64.t)
  requires is_heap heap 's ** pts_to heads 'fls ** pts_to tbl 't **
           pure (Seq.length 'fls == SC.n_lists /\ Seq.length 't == OT.n_windows)
  ensures exists* s2 fls2 t2. is_heap heap s2 ** pts_to heads fls2 ** pts_to tbl t2 **
    pure ((s2, fls2) == SAL.init_heap_lists_spec 's /\ OT.table_matches s2 t2)

/// The object-start table of the heap as it is (one walk).
fn table_rebuild (heap: heap_t) (tbl: array U64.t)
  requires is_heap heap 's ** pts_to tbl 't ** pure (Seq.length 't == OT.n_windows)
  ensures exists* t2. is_heap heap 's ** pts_to tbl t2 ** pure (OT.table_matches 's t2)

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
///
/// `tbl` is the object-start table (GC.Spec.ObjectTable): the entries of the
/// boundaries inside the new object are set to its header, unless the entry
/// past them names a block below it (`OT.alloc_table`).  With valid free
/// lists this keeps the table sound (`OT.table_sound`, the invariant), and
/// exact whenever it was (`OT.table_ok`).
fn allocate (heap: heap_t) (heads: array U64.t) (tbl: array U64.t) (wosize: U64.t)
  requires is_heap heap 's ** pts_to heads 'fls ** pts_to tbl 't **
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
                 Seq.length 'fls == SC.n_lists /\
                 Seq.length 't == OT.n_windows)
  returns obj: U64.t
  ensures exists* s2 fls2 t2. is_heap heap s2 ** pts_to heads fls2 ** pts_to tbl t2 **
    pure (let spec_res = SAL.alloc_lists_spec 's 'fls (U64.v wosize) in
          s2 == spec_res.heap_out /\
          fls2 == spec_res.fls_out /\
          obj == spec_res.obj_out /\
          t2 == OT.alloc_table 't obj (U64.v wosize) /\
          Seq.length t2 == OT.n_windows /\
          (OT.table_sound 's 't /\ FLs.fls_valid 's 'fls /\ FLs.fls_terminates 's 'fls ==>
           OT.table_sound s2 t2) /\
          (OT.table_ok 's 't /\ FLs.fls_valid 's 'fls /\ FLs.fls_terminates 's 'fls ==>
           OT.table_ok s2 t2))

/// Allocate with weaker precondition: only requires well_formed_heap_part1
/// + valid, terminating free lists. Suitable for use during promotion where
/// full well_formed_heap (part2: pointer closure) may be temporarily violated.
///
/// The implementation is identical to `allocate` — the allocator only reads
/// headers and free-list links, never inspecting object pointer fields.

fn allocate_part1 (heap: heap_t) (heads: array U64.t) (tbl: array U64.t) (wosize: U64.t)
  requires is_heap heap 's ** pts_to heads 'fls ** pts_to tbl 't **
           pure (SpecFields.well_formed_heap_part1 's /\
                 FLs.fls_valid 's 'fls /\
                 FLs.fls_terminates 's 'fls /\
                 U64.v wosize >= 1 /\
                 Seq.length 'fls == SC.n_lists /\
                 Seq.length 't == OT.n_windows)
  returns obj: U64.t
  ensures exists* s2 fls2 t2. is_heap heap s2 ** pts_to heads fls2 ** pts_to tbl t2 **
    pure (let spec_res = SAL.alloc_lists_spec 's 'fls (U64.v wosize) in
          s2 == spec_res.heap_out /\
          fls2 == spec_res.fls_out /\
          obj == spec_res.obj_out /\
          t2 == OT.alloc_table 't obj (U64.v wosize) /\
          Seq.length t2 == OT.n_windows /\
          (OT.table_sound 's 't ==> OT.table_sound s2 t2) /\
          (OT.table_ok 's 't ==> OT.table_ok s2 t2))
