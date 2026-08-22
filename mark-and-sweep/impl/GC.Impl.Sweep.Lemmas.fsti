(*
   Pulse GC - Sweep Lemmas Interface

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
val lemma_next_addr_no_overflow (h_addr: nat) (wz: nat)
  : Lemma (requires h_addr < heap_size /\ wz <= pow2 54 - 1)
          (ensures h_addr + (1 + wz) * 8 < pow2 64)

/// Helper: any address <= heap_size has addr + 8 < pow2 64
val lemma_addr_plus_8_no_overflow (addr: nat)
  : Lemma (requires addr <= heap_size)
          (ensures addr + 8 < pow2 64)

/// ---------------------------------------------------------------------------
/// Pure Helpers
/// ---------------------------------------------------------------------------
/// ---------------------------------------------------------------------------
/// Whiten/Bluen Bridge Lemmas
/// ---------------------------------------------------------------------------
/// ---------------------------------------------------------------------------
/// Sweep Post / Transfer Bridge Lemmas
/// ---------------------------------------------------------------------------
/// Bridge: obj_in_objects for initial head object (avoids heap subtyping in Pulse)
val obj_in_objects_head_bridge (g: GC.Spec.Base.heap)
  : Lemma (requires Seq.length (SpecFields.objects zero_addr g) > 0)
          (ensures SI.obj_in_objects (GC.Spec.Heap.f_address zero_addr) g)
/// ---------------------------------------------------------------------------
/// Headers Preserved Bridge Lemmas
/// ---------------------------------------------------------------------------

/// ---------------------------------------------------------------------------
/// Sweep Black Preservation Lemmas
/// ---------------------------------------------------------------------------
/// ---------------------------------------------------------------------------
/// Sweep White Preservation Lemmas
/// ---------------------------------------------------------------------------
/// ---------------------------------------------------------------------------
/// Field / Sweep Object Spec Equivalence Lemmas
/// ---------------------------------------------------------------------------
/// ---------------------------------------------------------------------------
/// Alignment Helper
/// ---------------------------------------------------------------------------

/// Helper: next object address preserves alignment
val lemma_next_addr_aligned (h_addr: nat) (wz: nat)
  : Lemma (requires h_addr % 8 == 0)
          (ensures (h_addr + (1 + wz) * 8) % 8 == 0)

/// ---------------------------------------------------------------------------
/// Spec-level sweep black lemmas (no spec_read_word/spec_write_word in API)
/// ---------------------------------------------------------------------------
