(*
   Pulse GC (Generational) - the write barrier

   OCaml 4.14's `caml_modify` and `caml_initialize` (runtime/memory.c) for a
   slot in the major heap, verified:

   - modify_field: read the old value, darken it while marking (4.14's
     `caml_darken`: resolve an infix pointer, grey a white block and push it
     on the persistent mark stack, or raise the overflow flag when the stack
     is full), write the new value, and say whether the slot must be added to
     the remembered set (the new value is a nursery pointer and the old one
     was not);
   - initialize_field: write the first value of a field of a block just allocated,
     and say whether the slot must be remembered (the value is a nursery
     pointer).  No darkening: the old value is garbage.

   The remembered set itself stays the stock C table (`add_to_ref_table`,
   which grows it): the bridge appends the slot exactly when the function
   returns true, and `GC.Gen.Barrier.modify_ref_table` /
   `initialize_ref_table` say that keeps the table covering and sound.  A
   write into a nursery object needs no barrier and never comes here: the C
   caller writes it directly (`Is_young (fp)`), as 4.14 does.
*)

module GC.Gen.Impl.Barrier

#lang-pulse

open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Gen.MinorHeap
open GC.Impl.Heap
open GC.Gen.Impl
module Ph = GC.Spec.Phase
module SpecHeap = GC.Spec.Heap
module SpecObj = GC.Spec.Object
module SpecFields = GC.Spec.Fields
module SPM = GC.Spec.SweepPhase.Mutator
module GB = GC.Gen.Barrier
module MPA = GC.Spec.MarkPhase.Alloc

/// **`caml_modify` of a major slot**, at the collector's phase.
///
/// The slot is a body word of the non-free, scannable, non-closure block
/// `x`, and the value is storable there; while marking it is a value the
/// program holds (`GB.modify_ok`: the trusted program obligation).  The
/// collector's state is kept at the same phase, the heap is the barrier's
/// (`GB.modify_heap`: while marking the old value darkened, then the
/// write), and the result says whether the slot must be remembered
/// (`GB.modify_records`).
///
/// The collector's record is passed by reference (`ghr`, the bridge's
/// `&gc_gen_heap`): the call copies one word, not the record.
fn modify_field (ghr: R.ref gen_heap_t) (slot: hp_addr) (v: U64.t)
                (#gh: erased gen_heap_t) (#p: perm) (#x: erased obj_addr)
  requires R.pts_to ghr #p gh ** gc_state gh 'd 'b 's 'fp 'ph **
           pure (GB.modify_ok 'ph ({ data = 'd; bump = 'b } <: minor_state) 's x slot v)
  returns r: bool
  ensures R.pts_to ghr #p gh ** gc_state gh 'd 'b (GB.modify_heap 'ph 's slot v) 'fp 'ph **
          pure (r == GB.modify_records 's slot v)

/// **`caml_initialize` of a major slot**: the slot is a body word of the
/// block `x` of the heap, not free (a block just allocated: while sweeping
/// or marking it is *fresh*, `SPM.fresh_ok` /
/// `GC.Spec.MarkPhase.Alloc.marking_fresh`, and a write into it keeps it so:
/// `SPM.fresh_write`, `GC.Spec.MarkPhase.Alloc.marking_fresh_write`; while
/// marking, what this asks is the part of `marking_fresh` the mark cache
/// needs: black, and nothing that is not free points into it).  The
/// heap is the write, the phase record and the mark state are kept, and the
/// result says whether the slot must be remembered
/// (`GB.initialize_records`).
fn initialize_field (ghr: R.ref gen_heap_t) (slot: hp_addr) (v: U64.t)
                    (#gh: erased gen_heap_t) (#p: perm) (#x: erased obj_addr)
  requires R.pts_to ghr #p gh **
           is_gen_heap gh 'd 'b 's 'fp ** gen_phase gh 's 'ph ** mark_state gh 's 'ph **
           pure (Seq.mem (reveal x) (SpecFields.objects zero_addr 's) /\ ~(SpecObj.is_blue x 's) /\
                 SPM.in_body 's x slot /\
                 (Ph.Marking? 'ph ==> SpecObj.is_black x 's /\
                                     SpecFields.well_formed_heap_with (MPA.free_or_new x) 's))
  returns r: bool
  ensures R.pts_to ghr #p gh **
          is_gen_heap gh 'd 'b (SpecHeap.write_word 's slot v) 'fp **
          gen_phase gh (SpecHeap.write_word 's slot v) 'ph **
          mark_state gh (SpecHeap.write_word 's slot v) 'ph **
          pure (r == GB.initialize_records v)
