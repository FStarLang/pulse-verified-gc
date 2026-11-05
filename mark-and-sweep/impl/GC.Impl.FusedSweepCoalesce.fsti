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
module SPI = GC.Spec.SweepPhase.Intrinsic
module SL = GC.Spec.SweepPhase.Slice

/// The sweep state as the implementation holds it: three words.
let mk_st (c t f: U64.t) : FS.sweep_state = { FS.cursor = c; FS.swept_tail = t; FS.last_fragment = f }

/// Precondition: the marked heap's walk covers it and the free list is exact
/// and ascending (`FSI.sweep_pre`).  Postcondition: the result is the spec's.
fn fused_sweep_coalesce (heap: heap_t) (fp: U64.t)
  requires is_heap heap 's ** pure (FSI.sweep_pre 's fp)
  returns new_fp: U64.t
  ensures exists* s2. is_heap heap s2 **
    pure ((s2, new_fp) == FS.fused_sweep_coalesce 's fp)

/// The result of a slice, as the spec's (`GC.Spec.SweepPhase.Slice.sweep_slice`):
/// `r` is the new cursor, `swept_tail`, `last_fragment` and free-list head.
let slice_matches (g: GC.Spec.Base.heap) (fp: U64.t) (c t f: U64.t) (budget: U64.t)
    (g': GC.Spec.Base.heap) (r: U64.t & U64.t & U64.t & U64.t) : prop =
  let (c', t', f', fp') = r in
  SL.sweep_slice g fp (mk_st c t f) (U64.v budget) == (g', fp', mk_st c' t' f')

/// The heap is in the sweep phase at cursor `c`
/// (`GC.Spec.SweepPhase.Intrinsic.sweep_inv_incremental`), and `t`, `f` are the
/// caches derived from it (`SPI.state_at`).
let slice_pre (g: GC.Spec.Base.heap) (fp: U64.t) (c t f: U64.t) : prop =
  SPI.sweep_inv_incremental g fp c /\ mk_st c t f == SPI.state_at g c

/// **One slice of the incremental sweep**: whole steps from the sweep state
/// `(c, t, f)` until the blocks swept add up to at least `budget` words
/// (headers included), or the cursor reaches the end of the heap.  The heap
/// is in the sweep phase at `c`, and `t`, `f` are its derived caches.  The
/// result is exactly the spec's slice; the step is the one the stop-the-world
/// pass runs.
fn sweep_slice_impl (heap: heap_t) (c t f fp budget: U64.t)
  requires is_heap heap 's ** pure (slice_pre 's fp c t f)
  returns r: (U64.t & U64.t & U64.t & U64.t)
  ensures exists* s2. is_heap heap s2 ** pure (slice_matches 's fp c t f budget s2 r)
