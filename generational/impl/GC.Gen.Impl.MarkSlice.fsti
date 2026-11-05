(*
   Pulse GC (Generational) - the mark slice

   One slice of incremental marking (OCaml 4.14's `mark_slice`), over the
   major heap and the persistent mark cache (`GC.Gen.MarkState`): the mark
   stack, the overflow flag, the partly scanned object and its next field,
   and the rescan cursor.  It repeats, until `budget` words are scanned or
   marking is over:

   - resume the partly scanned object: scan its next fields (greying white
     targets, pushing them, or raising the flag when the stack is full) and,
     once the last one is scanned, blacken it; an object larger than what is
     left of the budget is scanned in parts across slices;
   - pop an entry: a grey object with fields becomes the partly scanned
     object, one without is blackened, a black one is skipped;
   - with the stack empty and a rescan in progress, walk the blocks from the
     rescan cursor pushing the grey ones, until the stack is a quarter full
     (4.14's `redarken_chunk`), or the budget is spent, or the heap ends;
   - with the stack empty and the flag up, start a rescan from the first
     block, the flag down;
   - with nothing left (stack empty, nothing partly scanned, no rescan, flag
     down), marking is over: nothing is grey.

   The budget counts words: a header for each entry popped and each block
   the rescan walks, a word for each field scanned.  `UINT64_MAX` is
   unbounded: the slice runs until marking is over (it always terminates:
   `GC.Gen.MarkSlice.slice_measure`).
*)

module GC.Gen.Impl.MarkSlice

#lang-pulse

open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Impl.Heap
open GC.Impl.Stack
module SpecFields = GC.Spec.Fields
module MS = GC.Gen.MarkState
module S = GC.Spec.MarkPhase.Slice
module Mark = GC.Spec.Mark
module GI = GC.Gen.Incremental

/// The positions held in the three references.
noextract
let pos (c f r: U64.t) : MS.mark_pos = { MS.cur = c; MS.fld = f; MS.rc = r }

/// What the slice needs of the heap: well formed, its walk covering it.
let heap_ok (g: heap) : prop =
  SpecFields.well_formed_heap g /\ SpecFields.heap_objects_dense g /\
  Seq.length (SpecFields.objects zero_addr g) > 0

/// **A mark slice.**  The heap after is some mark moves away (`S.mark_steps`),
/// the cache holds of it; when it returns true, marking is over: the cache is
/// empty and nothing is grey.  With an unbounded budget it returns true.
fn mark_slice (heap: heap_t) (stk: gray_stack) (ovr: R.ref bool)
              (curr fldr rcr: R.ref U64.t) (budget: U64.t)
  requires is_heap heap 's ** is_gray_stack stk 'st ** R.pts_to ovr 'ov **
           R.pts_to curr 'c ** R.pts_to fldr 'f ** R.pts_to rcr 'r **
           pure (MS.marking_cache 's 'st 'ov (pos 'c 'f 'r) /\ heap_ok 's)
  returns fin: bool
  ensures exists* s2 st2 ov2 c2 f2 r2.
    is_heap heap s2 ** is_gray_stack stk st2 ** R.pts_to ovr ov2 **
    R.pts_to curr c2 ** R.pts_to fldr f2 ** R.pts_to rcr r2 **
    pure (MS.marking_cache s2 st2 ov2 (pos c2 f2 r2) /\ heap_ok s2 /\ S.mark_steps 's s2 /\
          (fin ==> MS.cache_off st2 ov2 (pos c2 f2 r2) /\ Mark.noGreyObjects s2) /\
          (GI.unbounded (U64.v budget) ==> fin))
