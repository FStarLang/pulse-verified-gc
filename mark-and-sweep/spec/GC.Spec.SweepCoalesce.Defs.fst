/// ---------------------------------------------------------------------------
/// GC.Spec.SweepCoalesce.Defs — Fused sweep+coalesce function definitions
///
/// Defines fused_aux and fused_sweep_coalesce without importing Induction,
/// so Induction can depend on this module without creating a cycle.
/// ---------------------------------------------------------------------------
module GC.Spec.SweepCoalesce.Defs

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module SpecCoalesce = GC.Spec.Coalesce

/// Walks objects once, combining sweep's color transitions with
/// coalesce's blue-run accumulation.
///
/// g0: frozen source heap (used for color/wosize checks — never mutated)
/// g:  current heap (modified by flush_blue + makeWhite calls)
/// objs: remaining objects to process
/// fb:   first blue obj_addr of pending run (unused when rw=0)
/// rw:   total accumulated words in pending blue run (0 = no pending run)
/// fp:   free list pointer being threaded through

let rec fused_aux (g0: heap) (g: heap) (objs: seq obj_addr)
    (fb: U64.t) (rw: nat) (fp: U64.t)
  : GTot (heap & U64.t) (decreases Seq.length objs)
  = if Seq.length objs = 0 then
      SpecCoalesce.flush_blue g fb rw fp
    else
      let obj = Seq.head objs in
      let rest = Seq.tail objs in
      if is_black obj g0 then
        (* Survivor: flush any pending blue run, then reset to white *)
        let (g', fp') = SpecCoalesce.flush_blue g fb rw fp in
        let g'' = makeWhite obj g' in
        fused_aux g0 g'' rest 0UL 0 fp'
      else
        (* White or Blue in g0: accumulate into blue run *)
        let ws = U64.v (wosize_of_object obj g0) in
        let new_fb : U64.t = if rw = 0 then obj else fb in
        fused_aux g0 g rest new_fb (rw + ws + 1) fp

/// Top-level fused sweep+coalesce: walk all objects, build fresh free list
let fused_sweep_coalesce (g: heap) : GTot (heap & U64.t) =
  fused_aux g g (objects 0UL g) 0UL 0 0UL

/// ---------------------------------------------------------------------------
/// Unfolding lemmas
/// ---------------------------------------------------------------------------

let fused_aux_empty (g0 g: heap) (fb: U64.t) (rw: nat) (fp: U64.t)
  : Lemma (fused_aux g0 g Seq.empty fb rw fp ==
           SpecCoalesce.flush_blue g fb rw fp)
  = ()

let fused_aux_black_step (g0 g: heap) (objs: seq obj_addr)
    (fb: U64.t) (rw: nat) (fp: U64.t)
  : Lemma
    (requires Seq.length objs > 0 /\ is_black (Seq.head objs) g0)
    (ensures (let obj = Seq.head objs in
              let rest = Seq.tail objs in
              let (g', fp') = SpecCoalesce.flush_blue g fb rw fp in
              let g'' = makeWhite obj g' in
              fused_aux g0 g objs fb rw fp ==
              fused_aux g0 g'' rest 0UL 0 fp'))
  = ()

let fused_aux_nonblack_step (g0 g: heap) (objs: seq obj_addr)
    (fb: U64.t) (rw: nat) (fp: U64.t)
  : Lemma
    (requires Seq.length objs > 0 /\ ~(is_black (Seq.head objs) g0))
    (ensures (let obj = Seq.head objs in
              let rest = Seq.tail objs in
              let ws = U64.v (wosize_of_object obj g0) in
              let new_fb = if rw = 0 then obj else fb in
              fused_aux g0 g objs fb rw fp ==
              fused_aux g0 g rest new_fb (rw + ws + 1) fp))
  = ()
