(*
   Pulse GC - Fused Sweep+Coalesce Module Interface

   Exports the fused_sweep_coalesce entry point that combines sweep and
   coalesce into a single pass over the heap. Replaces the two-pass
   sweep-then-coalesce approach.
*)

module GC.Impl.FusedSweepCoalesce

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
module U64 = FStar.UInt64
module Seq = FStar.Seq
module Defs = GC.Spec.SweepCoalesce.Defs
module SCL = GC.Spec.SweepCoalesce.Lists
module SC = GC.Spec.SizeClass
module SpecFields = GC.Spec.Fields
module SpecObject = GC.Spec.Object
module SI = GC.Spec.SweepInv
module OT = GC.Spec.ObjectTable

/// Fused sweep+coalesce pass: walk all objects, whiten survivors,
/// merge adjacent free blocks, and push each merged block on the free list
/// of its size class.  Every list is rebuilt from empty, so the heads handed
/// in do not matter.
///
/// The same pass rebuilds the object-start table `tbl` (GC.Spec.ObjectTable)
/// of the heap it leaves: every entry is rewritten, from the output's walk
/// positions -- the survivors and the first header of each run -- so the
/// entries handed in do not matter either.
///
/// Precondition: well_formed heap, no gray objects (mark phase complete),
///               objects list is non-empty + dense
/// Postcondition: result matches the fused_sweep_coalesce_lists spec, and
///                the table is the result's
fn fused_sweep_coalesce (heap: heap_t) (heads: array U64.t) (tbl: array U64.t)
  requires is_heap heap 's ** pts_to heads 'fls ** pts_to tbl 't **
           pure (SpecFields.well_formed_heap 's /\
                 Seq.length (SpecFields.objects zero_addr 's) > 0 /\
                 GC.Spec.Fields.heap_objects_dense 's /\
                 (forall (x: obj_addr).
                   Seq.mem x (SpecFields.objects zero_addr 's) ==>
                   ~(SpecObject.is_gray x 's)) /\
                 Seq.length 'fls == SC.n_lists /\
                 Seq.length 't == OT.n_windows)
  ensures exists* s2 fls2 t2. is_heap heap s2 ** pts_to heads fls2 ** pts_to tbl t2 **
    pure ((s2, fls2) == SCL.fused_sweep_coalesce_lists 's /\
          OT.table_matches s2 t2)
