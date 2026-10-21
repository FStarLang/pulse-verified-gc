(*
   Pulse GC - Parallel sweep, one segment (specification only)

   The OCaml runtime owns the worker threads; each worker calls
   sweep_segment on its own segment [lo, hi) of the heap.  This is the
   Pulse counterpart of the model's per-segment function
   GC.Spec.SweepPar.sweep_segment (see docs/parallel-sweep-phase1.md, §7).

   The heap representation is GC.Impl.Heap's: a byte array (heap_t.data)
   whose contents are a GC.Spec.Base.heap.  The whole-heap predicate is
   is_heap, a full pts_to on the array; a segment owns only its range, as
   a pts_to_range on the same array.
*)

module GC.Impl.SweepSegment

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsToRange
open GC.Impl.Heap
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq
module SP = GC.Spec.SweepPar

/// ---------------------------------------------------------------------------
/// Owning one range of the heap
/// ---------------------------------------------------------------------------

/// The bytes [lo, hi) of the heap hold `s`.  The range counterpart of
/// is_heap: it gives no access to any byte outside [lo, hi).
let is_heap_range (h: heap_t) (lo hi: nat) (s: Seq.seq U8.t) : slprop =
  pts_to_range h.data lo hi s

/// ---------------------------------------------------------------------------
/// What one segment returns
/// ---------------------------------------------------------------------------

/// The values of SP.seg_out other than its heap copy, in machine types for
/// extraction: `run.rw` (a nat) becomes U64.t, and `first_link`
/// (an option) becomes a flag and a value.
noeq type seg_result = {
  all_free   : bool;    (* no survivor: lead is the whole segment *)
  lead_fb    : U64.t;   (* leading free run, unflushed: first block *)
  lead_rw    : U64.t;   (*   and total words *)
  trail_fb   : U64.t;   (* trailing free run, unflushed: first block *)
  trail_rw   : U64.t;   (*   and total words *)
  has_link   : bool;    (* the segment linked at least one block *)
  first_link : U64.t;   (* the first block linked; 0UL when has_link is false *)
  local_head : U64.t;   (* head of the segment's local free list *)
}

/// `r` holds exactly the values of the model's segment output `o`.
let result_matches (r: seg_result) (o: SP.seg_out) : prop =
  r.all_free == o.SP.all_free /\
  r.lead_fb == o.SP.lead.SP.fb /\ U64.v r.lead_rw == o.SP.lead.SP.rw /\
  r.trail_fb == o.SP.trail.SP.fb /\ U64.v r.trail_rw == o.SP.trail.SP.rw /\
  (match o.SP.first_link with
   | None -> r.has_link == false /\ r.first_link == 0UL
   | Some a -> r.has_link == true /\ r.first_link == a) /\
  r.local_head == o.SP.local_head

/// ---------------------------------------------------------------------------
/// One segment
/// ---------------------------------------------------------------------------

/// Sweep the objects whose headers lie in [lo, hi).
///
/// `g` is the whole heap as it was before any segment ran; it is ghost and
/// shared by every worker.  `bs` is the boundary list the runtime chose;
/// it is also ghost.  Neither reaches the extracted code.
///
/// Precondition: the worker owns the bytes [lo, hi), and they are g's
///   bytes there; g is a heap the sequential pass may run on (SP.fused_pre);
///   and lo, hi are consecutive boundaries of a valid boundary list for g.
/// Postcondition: the worker still owns [lo, hi) and nothing else; those
///   bytes are the model's segment copy of the heap restricted to [lo, hi)
///   (exactly the bytes SP.splice keeps); and the returned record holds the
///   model's other outputs.
fn sweep_segment
  (heap: heap_t)
  (lo: hp_addr)
  (hi: U64.t{U64.v lo < U64.v hi /\ U64.v hi <= heap_size})
  (#g: erased heap_state)
  (#bs: erased (list nat))
  requires is_heap_range heap (U64.v lo) (U64.v hi)
             (Seq.slice g (U64.v lo) (U64.v hi)) **
           pure (SP.fused_pre g /\
                 SP.valid_bounds g bs /\
                 List.Tot.memP (U64.v lo, U64.v hi) (SP.segments bs))
  returns r: seg_result
  ensures exists* s.
    is_heap_range heap (U64.v lo) (U64.v hi) s **
    pure (s == Seq.slice (SP.sweep_segment g lo (U64.v hi)).SP.sheap
                         (U64.v lo) (U64.v hi) /\
          result_matches r (SP.sweep_segment g lo (U64.v hi)))
