(*
   Pulse GC - Sweep Lemmas Implementation

   Pure F* lemmas extracted from GC.Impl.Sweep.
   These lemmas bridge Pulse-level operations to spec-level definitions.
*)

module GC.Impl.Sweep.Lemmas

#set-options "--z3rlimit 12"
open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
open GC.Impl.Fields
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module ML = FStar.Math.Lemmas
module SpecSweep = GC.Spec.Sweep
module SpecFields = GC.Spec.Fields
module SpecHeap = GC.Spec.Heap
module SpecObject = GC.Spec.Object
module SpecMark = GC.Spec.Mark
module SpecHeapGraph = GC.Spec.HeapGraph
module SI = GC.Spec.SweepInv
module SpecGCPost = GC.Spec.Correctness

/// ---------------------------------------------------------------------------
/// Overflow Helpers
/// ---------------------------------------------------------------------------

/// Helper: h_addr + (1+wz)*8 doesn't overflow
let lemma_next_addr_no_overflow (h_addr: nat) (wz: nat)
  : Lemma (requires h_addr < heap_size /\ wz <= pow2 54 - 1)
          (ensures h_addr + (1 + wz) * 8 < pow2 64)
=
  lemma_object_size_no_overflow wz;
  assert ((1 + wz) * 8 <= pow2 57);
  assert (h_addr < heap_size);
  assert (heap_size <= pow2 57);
  ML.pow2_lt_compat 64 58;
  Math.Lemmas.pow2_double_sum 57

/// Helper: any address <= heap_size has addr + 8 < pow2 64
let lemma_addr_plus_8_no_overflow (addr: nat)
  : Lemma (requires addr <= heap_size)
          (ensures addr + 8 < pow2 64)
=
  assert (heap_size <= pow2 57);
  Math.Lemmas.pow2_double_sum 57;
  ML.pow2_lt_compat 64 58

/// ---------------------------------------------------------------------------
/// Pure Helpers
/// ---------------------------------------------------------------------------
/// ---------------------------------------------------------------------------
/// Whiten/Bluen Bridge Lemmas
/// ---------------------------------------------------------------------------

/// Bridge: Pulse whiten (write_word with makeHeader White) == spec makeWhite
/// Bridge: Pulse bluen (write_word with makeHeader Blue) == spec makeBlue
/// ---------------------------------------------------------------------------
/// Sweep Post / Transfer Bridge Lemmas
/// ---------------------------------------------------------------------------
/// Bridge: obj_in_objects for initial head object (avoids heap subtyping in Pulse)
let obj_in_objects_head_bridge (g: GC.Spec.Base.heap)
  : Lemma (requires Seq.length (SpecFields.objects zero_addr g) > 0)
          (ensures SI.obj_in_objects (GC.Spec.Heap.f_address zero_addr) g)
  = SI.obj_in_objects_head g

/// ---------------------------------------------------------------------------
/// Density / Objects Nonempty Bridge Lemmas
/// ---------------------------------------------------------------------------
/// Bridge: from obj_in_objects (f_address h_addr) in one heap, derive objects nonempty
/// in a related heap. Combines transfer + elim + member_implies_objects_nonempty
/// into a single call to avoid --split_queries isolation.
/// ---------------------------------------------------------------------------
/// Sweep Loop Next Bridge
/// ---------------------------------------------------------------------------

/// Combined bridge: after sweep_object, establish all facts for the next iteration.
/// Avoids --split_queries isolation by doing everything in one pure F* call.
/// Takes RAW Pulse-accessible facts (spec_read_word, getWosize) to avoid long chains.
/// Density/membership conclusions are conditional on next_v + 8 < heap_size.
/// ---------------------------------------------------------------------------
/// Headers Preserved Bridge Lemmas
/// ---------------------------------------------------------------------------

/// Bridge: makeBlue preserves headers before h_addr
/// ---------------------------------------------------------------------------
/// Sweep Black Preservation Lemmas
/// ---------------------------------------------------------------------------
/// Bridge: whiten via spec_write_word preserves wfh + objects
/// Takes EXACTLY the terms from the Pulse context to avoid SMT unification
/// ---------------------------------------------------------------------------
/// Sweep White Preservation Lemmas
/// ---------------------------------------------------------------------------

/// Combined white-case preservation: writing to field 1 preserves wfh + objects.
/// Uses h_addr (outer scope) not field1_addr in ensures.
/// White-case: writing to field 1 preserves header at h_addr and headers before h_addr
/// After a field write at h_addr+8, the is_white/is_blue status at f_address(h_addr) is preserved
/// ---------------------------------------------------------------------------
/// Field / Sweep Object Spec Equivalence Lemmas
/// ---------------------------------------------------------------------------

/// Bridge: spec_write_word at field 1 == HeapGraph.set_field for field 1
/// set_field g obj 1 fp = write_word g (hd_address obj + mword * 1) fp = write_word g obj fp
/// spec_write_word g (h_addr + 8) fp = spec_write_word g (U64.v obj) fp = write_word g obj fp
/// Bridge: sweep_object spec equivalence for white case (wz > 0 branch)
/// After field write + makeBlue, the result matches sweep_object
/// Bridge: sweep_object spec equivalence for white case (wz == 0 branch)
/// Just makeBlue (no field write), result matches sweep_object
/// ---------------------------------------------------------------------------
/// Sweep Black Whiteness / Black Eq Lemmas
/// ---------------------------------------------------------------------------

/// Bridge: after sweep_black writes makeHeader wz White tag at h_addr,
/// the object is white and wosize is preserved.
/// Bridge: sweep_object spec equivalence for black case
/// ---------------------------------------------------------------------------
/// Color Contradiction and Color Bridge Lemmas
/// ---------------------------------------------------------------------------

/// Bridge: when getColor is neither white, black, gray, nor blue, contradiction.
/// Bridge: else case of sweep_object — object is neither white nor black.
/// Must be blue (from ~gray + exhaustiveness). sweep_object returns identity.
/// ---------------------------------------------------------------------------
/// Alignment Helper
/// ---------------------------------------------------------------------------

/// Helper: next object address preserves alignment
let lemma_next_addr_aligned (h_addr: nat) (wz: nat)
  : Lemma (requires h_addr % 8 == 0)
          (ensures (h_addr + (1 + wz) * 8) % 8 == 0)
=
  ML.lemma_mod_plus_distr_l h_addr ((1 + wz) * 8) 8;
  ML.lemma_mod_mul_distr_r (1 + wz) 8 8

/// ---------------------------------------------------------------------------
/// Spec-level sweep black lemmas
/// ---------------------------------------------------------------------------

/// These use only spec-level functions (no spec_read_word/spec_write_word)
/// so they don't trigger bitvector cascades in combined VCs.
