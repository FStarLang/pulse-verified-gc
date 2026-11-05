(*
   Pulse GC (Generational) - the write barrier (see the interface)
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
open GC.Impl.Stack
open GC.Gen.Impl
module Ph = GC.Spec.Phase
module SpecHeap = GC.Spec.Heap
module SpecObj = GC.Spec.Object
module SpecFields = GC.Spec.Fields
module SPM = GC.Spec.SweepPhase.Mutator
module SPI = GC.Spec.SweepPhase.Intrinsic
module MM = GC.Spec.MarkPhase.Mutator
module GB = GC.Gen.Barrier
module MS = GC.Gen.MarkState
module GI = GC.Gen.Incremental
module Alloc = GC.Impl.Allocator
module MBI = GC.Impl.MarkBounded
module GBase = GC.Gen.Base
module PromoteImpl = GC.Gen.Impl.Promote
module MSl = GC.Gen.MarkSlice
module MSI = GC.Gen.Impl.MarkSlice
module MPA = GC.Spec.MarkPhase.Alloc

/// ---------------------------------------------------------------------------
/// Helpers
/// ---------------------------------------------------------------------------

/// A nursery pointer, at run time: 4.14's `Is_block (v) && Is_young (v)`.
inline_for_extraction
let young (v: U64.t) : (r: bool{r == GB.is_young v}) =
  let off = GBase.to_minor_offset_u64 v in
  U64.gte off 8UL && U64.lt off GBase.minor_heap_size_u64 && U64.eq (U64.rem off 8UL) 0UL

/// The barrier's darkening: raise the overflow flag if the stack is full,
/// then the bounded darkening (grey a white target, push it if there is
/// room).
inline_for_extraction
fn barrier_darken (heap: heap_t) (st: gray_stack) (ovr: R.ref bool) (old: U64.t)
  requires is_heap heap 's ** is_gray_stack st 'st ** R.pts_to ovr 'ov
  ensures exists* s2 st2 ov2.
    is_heap heap s2 ** is_gray_stack st st2 ** R.pts_to ovr ov2 **
    pure ((s2, st2) == MBI.check_and_darken_bounded_spec 's 'st old (stack_capacity st) /\
          ov2 == ('ov || Seq.length 'st = stack_capacity st))
{
  stack_facts st;
  let full = is_full st;
  let o = R.op_Bang ovr;
  R.op_Colon_Equals ovr (o || full);
  MBI.check_and_darken_bounded heap st old (stack_capacity st)
}

/// While marking the phase record holds `Marking` whatever the heap.
ghost
fn phase_marking (phase: R.ref Alloc.phase_state) (g': heap)
  requires Alloc.is_phase phase 'g 'ph ** pure (Ph.Marking? 'ph)
  ensures Alloc.is_phase phase g' 'ph
{
  unfold Alloc.is_phase;
  fold (Alloc.is_phase phase g' 'ph)
}

/// The darkening, out of line and reading the record through its pointer: so
/// the common path (not marking) of `modify_field` touches only the heap and
/// the phase record.
fn darken_via (ghr: R.ref gen_heap_t) (old: U64.t) (#gh: erased gen_heap_t) (#p: perm)
  requires R.pts_to ghr #p gh **
           is_heap gh.major 's ** is_gray_stack gh.mark_stack 'st ** R.pts_to gh.mark_overflow 'ov
  ensures exists* s2 st2 ov2.
    R.pts_to ghr #p gh **
    is_heap gh.major s2 ** is_gray_stack gh.mark_stack st2 ** R.pts_to gh.mark_overflow ov2 **
    pure ((s2, st2) == MBI.check_and_darken_bounded_spec 's 'st old (stack_capacity gh.mark_stack) /\
          ov2 == ('ov || Seq.length 'st = stack_capacity gh.mark_stack))
{
  let g = R.op_Bang ghr;
  rewrite (is_heap gh.major 's) as (is_heap g.major 's);
  rewrite (is_gray_stack gh.mark_stack 'st) as (is_gray_stack g.mark_stack 'st);
  rewrite (R.pts_to gh.mark_overflow 'ov) as (R.pts_to g.mark_overflow 'ov);
  barrier_darken g.major g.mark_stack g.mark_overflow old;
  with s2 st2 ov2. assert (is_heap g.major s2 ** is_gray_stack g.mark_stack st2 **
                           R.pts_to g.mark_overflow ov2);
  rewrite (is_heap g.major s2) as (is_heap gh.major s2);
  rewrite (is_gray_stack g.mark_stack st2) as (is_gray_stack gh.mark_stack st2);
  rewrite (R.pts_to g.mark_overflow ov2) as (R.pts_to gh.mark_overflow ov2);
}

/// ---------------------------------------------------------------------------
/// caml_modify
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
inline_for_extraction
fn modify_at (ghr: R.ref gen_heap_t) (gh: gen_heap_t) (slot: hp_addr) (v: U64.t)
             (#p: perm) (#x: erased obj_addr)
  requires R.pts_to ghr #p gh ** gc_state gh 'd 'b 's 'fp 'ph **
           pure (GB.modify_ok 'ph ({ data = 'd; bump = 'b } <: minor_state) 's x slot v)
  returns r: bool
  ensures R.pts_to ghr #p gh ** gc_state gh 'd 'b (GB.modify_heap 'ph 's slot v) 'fp 'ph **
          pure (r == GB.modify_records 's slot v)
{
  let minor : erased minor_state = hide ({ data = 'd; bump = 'b } <: minor_state);
  unfold gc_state;
  GB.modify_heap_facts 'ph minor 's 'fp x slot v;
  unfold is_gen_heap;
  unfold mark_state;
  with st ov c f r. _;
  stack_facts gh.mark_stack;
  GB.modify_mark_cache 'ph minor 's 'fp x slot v st ov (MSI.pos c f r) (stack_capacity gh.mark_stack);
  let old = read_word gh.major slot;
  unfold gen_phase;
  unfold Alloc.is_phase;
  let pv = R.op_Bang gh.phase_ref;
  fold (Alloc.is_phase gh.phase_ref 's 'ph);
  if (U64.gte pv.Alloc.ps_kind 2UL) {
    // Marking: the deletion barrier darkens the old value first.
    GI.phase_free_marking ();
    SpecFields.free_def_ok_elim SpecFields.free_stw;
    MSl.darken_spec_eq 's st old (stack_capacity gh.mark_stack);
    darken_via ghr old;
    with s1 st1 ov1. assert (is_heap gh.major s1 ** is_gray_stack gh.mark_stack st1 **
                             R.pts_to gh.mark_overflow ov1);
    write_word gh.major slot v;
    rewrite (is_heap gh.major (SpecHeap.write_word s1 slot v))
         as (is_heap gh.major (GB.modify_heap 'ph 's slot v));
    phase_marking gh.phase_ref (GB.modify_heap 'ph 's slot v);
    // A write into a field the mark slice has scanned restarts the scan of
    // the partly scanned object (`MS.reset_cur`).
    let cv = R.op_Bang gh.mark_cur;
    let fv = R.op_Bang gh.mark_field;
    if (cv <> 0UL && U64.gte slot cv && U64.lt (U64.add (U64.div (U64.sub slot cv) 8UL) 1UL) fv) {
      R.op_Colon_Equals gh.mark_field 1UL;
    };
    fold (mark_state gh (GB.modify_heap 'ph 's slot v) 'ph);
  } else {
    // Idle or sweeping: just the write, which keeps the walk and every
    // header, so the sweep's caches.
    write_word gh.major slot v;
    rewrite (is_heap gh.major (SpecHeap.write_word 's slot v))
         as (is_heap gh.major (GB.modify_heap 'ph 's slot v));
    PromoteImpl.phase_heads gh.phase_ref (GB.modify_heap 'ph 's slot v);
    fold (mark_state gh (GB.modify_heap 'ph 's slot v) 'ph);
  };
  GB.modify_phase_shape 'ph minor 's 'fp x slot v;
  fold (gen_phase gh (GB.modify_heap 'ph 's slot v) 'ph);
  fold (is_gen_heap gh 'd 'b (GB.modify_heap 'ph 's slot v) 'fp);
  fold (gc_state gh 'd 'b (GB.modify_heap 'ph 's slot v) 'fp 'ph);
  (young v && not (young old))
}
#pop-options

/// ---------------------------------------------------------------------------
/// caml_initialize
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
inline_for_extraction
fn initialize_at (gh: gen_heap_t) (slot: hp_addr) (v: U64.t) (#x: erased obj_addr)
  requires is_gen_heap gh 'd 'b 's 'fp ** gen_phase gh 's 'ph ** mark_state gh 's 'ph **
           pure (Seq.mem (reveal x) (SpecFields.objects zero_addr 's) /\ ~(SpecObj.is_blue x 's) /\
                 SPM.in_body 's x slot /\
                 (Ph.Marking? 'ph ==> SpecObj.is_black x 's /\
                                     SpecFields.well_formed_heap_with (MPA.free_or_new x) 's))
  returns r: bool
  ensures is_gen_heap gh 'd 'b (SpecHeap.write_word 's slot v) 'fp **
          gen_phase gh (SpecHeap.write_word 's slot v) 'ph **
          mark_state gh (SpecHeap.write_word 's slot v) 'ph **
          pure (r == GB.initialize_records v)
{
  MM.write_heads 's x slot v;
  unfold is_gen_heap;
  write_word gh.major slot v;
  fold (is_gen_heap gh 'd 'b (SpecHeap.write_word 's slot v) 'fp);
  unfold gen_phase;
  PromoteImpl.phase_heads gh.phase_ref (SpecHeap.write_word 's slot v);
  fold (gen_phase gh (SpecHeap.write_word 's slot v) 'ph);
  unfold mark_state;
  with st ov c f r. _;
  MS.mark_cache_write 's 'ph st ov (MSI.pos c f r) x slot v;
  fold (mark_state gh (SpecHeap.write_word 's slot v) 'ph);
  young v
}
#pop-options

/// ---------------------------------------------------------------------------
/// The entry points: the record by reference
/// ---------------------------------------------------------------------------

/// The record is read through the pointer, so the C call passes one word
/// rather than copying the whole `gen_heap_t`, and only the fields the
/// barrier reads are loaded.

fn modify_field (ghr: R.ref gen_heap_t) (slot: hp_addr) (v: U64.t)
                (#gh: erased gen_heap_t) (#p: perm) (#x: erased obj_addr)
  requires R.pts_to ghr #p gh ** gc_state gh 'd 'b 's 'fp 'ph **
           pure (GB.modify_ok 'ph ({ data = 'd; bump = 'b } <: minor_state) 's x slot v)
  returns r: bool
  ensures R.pts_to ghr #p gh ** gc_state gh 'd 'b (GB.modify_heap 'ph 's slot v) 'fp 'ph **
          pure (r == GB.modify_records 's slot v)
{
  let g = R.op_Bang ghr;
  rewrite (gc_state gh 'd 'b 's 'fp 'ph) as (gc_state g 'd 'b 's 'fp 'ph);
  let r = modify_at ghr g slot v #p #x;
  rewrite (gc_state g 'd 'b (GB.modify_heap 'ph 's slot v) 'fp 'ph)
       as (gc_state gh 'd 'b (GB.modify_heap 'ph 's slot v) 'fp 'ph);
  r
}

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
{
  let g = R.op_Bang ghr;
  rewrite (is_gen_heap gh 'd 'b 's 'fp) as (is_gen_heap g 'd 'b 's 'fp);
  rewrite (gen_phase gh 's 'ph) as (gen_phase g 's 'ph);
  rewrite (mark_state gh 's 'ph) as (mark_state g 's 'ph);
  let r = initialize_at g slot v #x;
  rewrite (is_gen_heap g 'd 'b (SpecHeap.write_word 's slot v) 'fp)
       as (is_gen_heap gh 'd 'b (SpecHeap.write_word 's slot v) 'fp);
  rewrite (gen_phase g (SpecHeap.write_word 's slot v) 'ph)
       as (gen_phase gh (SpecHeap.write_word 's slot v) 'ph);
  rewrite (mark_state g (SpecHeap.write_word 's slot v) 'ph)
       as (mark_state gh (SpecHeap.write_word 's slot v) 'ph);
  r
}
