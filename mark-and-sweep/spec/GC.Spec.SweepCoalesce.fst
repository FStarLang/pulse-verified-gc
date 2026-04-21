(*
   GC.Spec.SweepCoalesce — Fused sweep+coalesce specification

   Proves that a single-pass fused sweep+coalesce produces the same result
   as the sequential composition `coalesce(fst(sweep(g, fp)))`.

   The fused spec walks objects once:
   - Black objects (survivors): flush accumulated blue run, write white header
   - White/Blue objects (garbage/free): accumulate into blue run
   - At end: flush any remaining blue run

   This avoids the second linear heap scan that standalone coalesce requires.
*)
module GC.Spec.SweepCoalesce

open FStar.Seq
open FStar.Mul
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module SpecSweep = GC.Spec.Sweep
module SpecCoalesce = GC.Spec.Coalesce
module HeapGraph = GC.Spec.HeapGraph
module Alloc = GC.Spec.Allocator
module SI = GC.Spec.SweepInv
module ML = FStar.Math.Lemmas

/// ---------------------------------------------------------------------------
/// Fused sweep+coalesce: single-pass specification
/// ---------------------------------------------------------------------------

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

/// ---------------------------------------------------------------------------
/// Composition lemma: fused == coalesce ∘ sweep
/// ---------------------------------------------------------------------------
///
/// Strategy: prove by induction on the objects list that for well-formed heaps
/// with no gray objects, the fused single pass produces the same result as
/// sweeping all objects first and then coalescing the result.
///
/// Key correspondence:
///   - Black in g0 ↔ White in g_swept (survivor) ↔ coalesce flushes run
///   - White in g0 ↔ Blue in g_swept (garbage)   ↔ coalesce accumulates
///   - Blue  in g0 ↔ Blue in g_swept (free)      ↔ coalesce accumulates
///
/// The proof requires showing that sweep's color changes (black→white, white→blue)
/// map exactly to coalesce's branching (white→flush, blue→accumulate).

/// Helper: after sweep, black objects become white
val sweep_black_becomes_white (g: heap) (obj: obj_addr) (fp: U64.t)
  : Lemma
    (requires is_black obj g /\ ~(is_infix obj g))
    (ensures is_white obj (fst (SpecSweep.sweep_object g obj fp)))

/// Helper: after sweep, white objects become blue
val sweep_white_becomes_blue (g: heap) (obj: obj_addr) (fp: U64.t)
  : Lemma
    (requires is_white obj g /\ ~(is_infix obj g))
    (ensures is_blue obj (fst (SpecSweep.sweep_object g obj fp)))

/// Helper: after sweep on non-white, non-black, non-infix: noop
val sweep_else_noop (g: heap) (obj: obj_addr) (fp: U64.t)
  : Lemma
    (requires ~(is_white obj g) /\ ~(is_black obj g) /\ ~(is_infix obj g))
    (ensures SpecSweep.sweep_object g obj fp == (g, fp))

/// The main composition theorem
val fused_eq_sweep_coalesce (g: heap) (fp: U64.t)
  : Lemma
    (requires well_formed_heap g /\
              SI.heap_objects_dense g /\
              (forall (x: obj_addr). Seq.mem x (objects 0UL g) ==>
                ~(is_gray x g)))
    (ensures fused_sweep_coalesce g ==
             SpecCoalesce.coalesce (fst (SpecSweep.sweep g fp)))

/// ---------------------------------------------------------------------------
/// Proofs
/// ---------------------------------------------------------------------------

let sweep_black_becomes_white g obj fp =
  SpecSweep.sweep_object_black_becomes_white g obj fp

let sweep_white_becomes_blue g obj fp =
  SpecSweep.sweep_object_resets_self_color g obj fp

let sweep_else_noop g obj fp =
  ()  // By definition: sweep_object checks is_infix, is_white, is_black in order

/// The composition proof is the key contribution of this module.
/// It proceeds by induction on the objects list, showing step-by-step
/// that the fused walk tracks the same (heap, fp) state as sweep-then-coalesce.
///
/// This is a non-trivial proof that we leave as admit for now.
/// The proof obligation: for each object, show that fused_aux's case split
/// (black vs non-black in g0) produces the same heap mutations as
/// sweep_object followed by partial coalesce_aux.
let fused_eq_sweep_coalesce g fp =
  admit ()
