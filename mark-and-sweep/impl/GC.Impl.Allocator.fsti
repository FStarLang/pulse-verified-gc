(*
   Pulse GC - Allocator Module Interface

   First-fit free-list allocator for the verified GC.
   Takes the heap, the current free-list head and the collector's phase,
   returns updated heap and new free-list head along with the allocated
   object address; the phase (its sweep state) is updated in place.
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
module AC = GC.Spec.Allocator.Cursor
module FS = GC.Spec.FusedSweep
module R = Pulse.Lib.Reference
open GC.Spec.Phase

/// ---------------------------------------------------------------------------
/// The collector's phase
/// ---------------------------------------------------------------------------

/// The collector's phase (`GC.Spec.Phase.gc_phase`) as the C state holds it:
/// a kind -- 0 idle, otherwise sweeping -- and the sweep state, which only
/// means something while sweeping.
type phase_state = {
  ps_kind          : U64.t;
  ps_cursor        : U64.t;
  ps_swept_tail    : U64.t;
  ps_last_fragment : U64.t;
}

/// The phase a `phase_state` stands for.
noextract
let phase_of (v: phase_state) : gc_phase =
  if v.ps_kind = 0UL then Idle
  else Sweeping { FS.cursor = v.ps_cursor;
                  FS.swept_tail = v.ps_swept_tail;
                  FS.last_fragment = v.ps_last_fragment }

/// `r` holds the phase `ph`.
let is_phase (r: R.ref phase_state) (ph: gc_phase) : slprop =
  exists* (v: phase_state). R.pts_to r v ** pure (phase_of v == ph)

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

/// Allocate an object of wosize words from the free list, at the collector's
/// phase (OCaml's `caml_alloc_shr`).
///
/// Parameters:
///   heap: mutable heap array
///   fp: current free-list head (obj_addr of first free block, or 0UL)
///   phase: the collector's phase.  The header's colour is the one the phase
///          gives the address the search chose (`caml_allocation_color`):
///          white when idle; while sweeping, black in front of the cursor and
///          white behind it.  While sweeping, an allocation that takes
///          `swept_tail`'s own cell off the list moves `swept_tail` back.
///   wosize: number of words needed
///   tag: the allocated header's tag (`caml_alloc_shr (wosize, tag)`); the
///        header is written once, with the colour and this tag
///
/// Returns: (new_fp, obj_addr)
///   new_fp: updated free-list head
///   obj_addr: allocated object address, or 0UL if out of memory
///
/// The allocator reads only headers and free-list links, and checks every
/// address it follows, so it needs nothing of the heap: in particular not
/// pointer closure, which promotion temporarily breaks.  The postcondition
/// ties the result to the pure spec `alloc_phase`; at `Idle` that is
/// `alloc_spec` (`AC.alloc_phase_idle`).  The phase record's cached
/// `swept_tail` is updated in place (`AC.phase_after_alloc`); idle, the phase
/// stays `Idle`.
fn allocate (heap: heap_t) (fp: U64.t) (phase: R.ref phase_state)
            (wosize: U64.t) (tag: U64.t{U64.v tag < 256})
  requires is_heap heap 's ** is_phase phase 'ph **
           // The allocator is never asked for a zero-word block: `gen_alloc`
           // requires wosize > 0, `promote_one` guards `wosize = 0` before
           // calling, and the C bridge's major path maps a request of 0 to 1
           // before calling (verified_gc/alloc_gen.c) -- OCaml represents a
           // zero-length block as a static Atom, never a heap allocation.
           // Stating it here lets the implementation drop the 0 -> 1 bump,
           // which was a compare-and-select on every major allocation for a
           // case that cannot occur.
           pure (U64.v wosize >= 1)
  returns res: (U64.t & U64.t)
  ensures exists* s2. is_heap heap s2 **
    is_phase phase (AC.phase_after_alloc 's fp (U64.v wosize) 'ph) **
    pure (let spec_res = AC.alloc_phase 's fp 'ph (U64.v wosize) tag in
          s2 == spec_res.heap_out /\
          fst res == spec_res.fp_out /\
          snd res == spec_res.obj_out)
