(*
   Pulse GC - Bounded Mark Module Interface

   Exports the bounded mark loop entry point. Uses a configurable-size mark
   stack with overflow handling: when the stack is full during push_children,
   children are grayed but not pushed; a linear heap rescan rediscovers them.
*)

module GC.Impl.MarkBounded

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open GC.Impl.Heap
open GC.Impl.Object
open GC.Impl.Stack
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SpecMark = GC.Spec.Mark
module SpecMarkBounded = GC.Spec.MarkBounded
module SpecMarkBoundedInv = GC.Spec.MarkBoundedInv
module SpecMarkBoundedCorr = GC.Spec.MarkBoundedCorrectness
module SpecFields = GC.Spec.Fields
module SweepInv = GC.Spec.SweepInv
module SpecHeap = GC.Spec.Heap
module SpecObject = GC.Spec.Object
open GC.Spec.Base

/// Spec function: what darken_if_white_bounded computes
let darken_if_white_bounded_spec (g: heap_state) (st: Seq.seq obj_addr)
    (h_addr: hp_addr) (cap: nat)
  : GTot (heap_state & Seq.seq obj_addr)
  = if U64.v h_addr + U64.v mword < heap_size then
      let obj = SpecHeap.f_address h_addr in
      if SpecObject.is_white obj g then
        let g' = SpecObject.makeGray obj g in
        if Seq.length st < cap then (g', Seq.cons obj st)
        else (g', st)
      else (g, st)
    else (g, st)

/// Spec function: what check_and_darken_bounded computes.
///
/// The value is *resolved* before darkening: OCaml represents mutually
/// recursive closures with interior (infix) pointers, and it is the enclosing
/// closure --- not the infix header --- that must be greyed and scanned.
/// `SpecObject.resolve_object` is the identity on ordinary pointers.
let check_and_darken_bounded_spec (g: heap_state) (st: Seq.seq obj_addr) (v: U64.t) (cap: nat)
  : GTot (heap_state & Seq.seq obj_addr)
  = if U64.v v >= U64.v zero_addr + U64.v mword && U64.v v < heap_size && U64.v v % U64.v mword = 0 then
      let target : obj_addr = SpecObject.resolve_object v g in
      darken_if_white_bounded_spec g st (U64.sub target mword) cap
    else (g, st)

/// Spec worker for root preparation: darken roots[0..idx) using the same
/// bounded push discipline as field traversal.
let rec darken_roots_bounded_prefix_spec
    (g: heap_state) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
    (idx: nat{idx <= Seq.length roots}) (cap: nat)
  : GTot (heap_state & Seq.seq obj_addr) (decreases idx)
  = if idx = 0 then (g, st)
    else
      let (g0, st0) = darken_roots_bounded_prefix_spec g st roots (idx - 1) cap in
      check_and_darken_bounded_spec g0 st0 (Seq.index roots (idx - 1)) cap

let darken_roots_bounded_spec
    (g: heap_state) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t) (cap: nat)
  : GTot (heap_state & Seq.seq obj_addr)
  = darken_roots_bounded_prefix_spec g st roots (Seq.length roots) cap

val check_and_darken_bounded_spec_length_le_cap
  (g: heap_state) (st: Seq.seq obj_addr) (v: U64.t) (cap: nat)
  : Lemma (requires Seq.length st <= cap)
          (ensures Seq.length (snd (check_and_darken_bounded_spec g st v cap)) <= cap)

val darken_roots_bounded_prefix_step
  (g: heap_state) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (idx: nat{idx < Seq.length roots}) (cap: nat)
  : Lemma (ensures
      darken_roots_bounded_prefix_spec g st roots (idx + 1) cap ==
        (let (g0, st0) = darken_roots_bounded_prefix_spec g st roots idx cap in
         check_and_darken_bounded_spec g0 st0 (Seq.index roots idx) cap))

val darken_roots_bounded_prefix_length_le_cap
  (g: heap_state) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (idx: nat{idx <= Seq.length roots}) (cap: nat)
  : Lemma (requires Seq.length st <= cap)
          (ensures Seq.length (snd (darken_roots_bounded_prefix_spec g st roots idx cap)) <= cap)

/// A root value names an object of `g`.
///
/// Stated on the root's *resolution*, matching `check_and_darken_bounded_spec`,
/// which resolves before darkening.  An interior (infix) pointer is therefore a
/// legitimate root: it names the closure it points into.  On an ordinary
/// pointer `resolve_object` is the identity, so this is the earlier
/// "`v` is itself an enumerated, non-infix object" exactly.
let root_points_to_object (g: heap_state) (v: U64.t) : prop =
  if U64.v v >= U64.v zero_addr + U64.v mword &&
     U64.v v < heap_size &&
     U64.v v % U64.v mword = 0
  then Seq.mem (SpecObject.resolve_object (v <: obj_addr) g)
               (SpecFields.objects zero_addr g)
  else True

val check_and_darken_bounded_spec_preserves_is_infix
  (g: heap_state) (st: Seq.seq obj_addr) (v: U64.t) (cap: nat)
  (obj: obj_addr)
  : Lemma
      (ensures
        SpecObject.is_infix obj
          (fst (check_and_darken_bounded_spec g st v cap)) ==
        SpecObject.is_infix obj g)

val darken_roots_bounded_prefix_preserves_is_infix
  (g: heap_state) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (idx: nat{idx <= Seq.length roots}) (cap: nat) (obj: obj_addr)
  : Lemma
      (ensures
        SpecObject.is_infix obj
          (fst (darken_roots_bounded_prefix_spec g st roots idx cap)) ==
        SpecObject.is_infix obj g)

/// Darkening recolours headers, and `resolve_object` reads only the tag and
/// size, so the object a value names is the same before and after.
val check_and_darken_bounded_spec_preserves_resolve
  (g: heap_state) (st: Seq.seq obj_addr) (v: U64.t) (cap: nat)
  (obj: obj_addr)
  : Lemma
      (ensures
        SpecObject.resolve_object obj
          (fst (check_and_darken_bounded_spec g st v cap)) ==
        SpecObject.resolve_object obj g)

val darken_roots_bounded_prefix_preserves_resolve
  (g: heap_state) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (idx: nat{idx <= Seq.length roots}) (cap: nat) (obj: obj_addr)
  : Lemma
      (ensures
        SpecObject.resolve_object obj
          (fst (darken_roots_bounded_prefix_spec g st roots idx cap)) ==
        SpecObject.resolve_object obj g)

val darken_roots_bounded_spec_preserves_resolve
  (g: heap_state) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (cap: nat) (obj: obj_addr)
  : Lemma
      (ensures
        SpecObject.resolve_object obj
          (fst (darken_roots_bounded_spec g st roots cap)) ==
        SpecObject.resolve_object obj g)

val check_and_darken_bounded_spec_preserves_wosize
  (g: heap_state) (st: Seq.seq obj_addr) (v: U64.t) (cap: nat)
  (obj: obj_addr)
  : Lemma
      (ensures
        SpecObject.wosize_of_object obj
          (fst (check_and_darken_bounded_spec g st v cap)) ==
        SpecObject.wosize_of_object obj g)

val darken_roots_bounded_prefix_preserves_wosize
  (g: heap_state) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (idx: nat{idx <= Seq.length roots}) (cap: nat) (obj: obj_addr)
  : Lemma
      (ensures
        SpecObject.wosize_of_object obj
          (fst (darken_roots_bounded_prefix_spec g st roots idx cap)) ==
        SpecObject.wosize_of_object obj g)

val darken_roots_bounded_spec_preserves_wosize
  (g: heap_state) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (cap: nat) (obj: obj_addr)
  : Lemma
      (ensures
        SpecObject.wosize_of_object obj
          (fst (darken_roots_bounded_spec g st roots cap)) ==
        SpecObject.wosize_of_object obj g)

val check_and_darken_bounded_spec_preserves_objects
  (g: heap_state) (st: Seq.seq obj_addr) (v: U64.t) (cap: nat)
  : Lemma
      (ensures
        SpecFields.objects zero_addr
          (fst (check_and_darken_bounded_spec g st v cap)) ==
        SpecFields.objects zero_addr g)

val darken_roots_bounded_prefix_preserves_objects
  (g: heap_state) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (idx: nat{idx <= Seq.length roots}) (cap: nat)
  : Lemma
      (ensures
        SpecFields.objects zero_addr
          (fst (darken_roots_bounded_prefix_spec g st roots idx cap)) ==
        SpecFields.objects zero_addr g)

val darken_roots_bounded_spec_preserves_objects
  (g: heap_state) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (cap: nat)
  : Lemma
      (ensures
        SpecFields.objects zero_addr
          (fst (darken_roots_bounded_spec g st roots cap)) ==
        SpecFields.objects zero_addr g)

/// Transport `root_points_to_object` across a heap change that preserves both
/// the object enumeration and address resolution.
val root_points_to_object_transfer
  (g0 g1: heap_state) (v: U64.t)
  : Lemma
      (requires
        root_points_to_object g0 v /\
        SpecFields.objects zero_addr g1 == SpecFields.objects zero_addr g0 /\
        (forall (x: obj_addr). SpecObject.resolve_object x g1 == SpecObject.resolve_object x g0))
      (ensures root_points_to_object g1 v)

val check_and_darken_bounded_spec_preserves_read_word
  (g: heap_state) (st: Seq.seq obj_addr) (v: U64.t) (cap: nat)
  (slot: hp_addr)
  : Lemma
      (requires
        root_points_to_object g v /\
        (U64.v v >= U64.v zero_addr + U64.v mword /\
         U64.v v < heap_size /\
         U64.v v % U64.v mword == 0 ==>
         U64.sub (SpecObject.resolve_object (v <: obj_addr) g) mword <> slot))
      (ensures
        SpecHeap.read_word
          (fst (check_and_darken_bounded_spec g st v cap)) slot ==
        SpecHeap.read_word g slot)

val darken_roots_bounded_prefix_preserves_read_word
  (g: heap_state) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (idx: nat{idx <= Seq.length roots}) (cap: nat) (slot: hp_addr)
  : Lemma
      (requires
        forall (i:nat). i < idx ==>
          root_points_to_object g (Seq.index roots i) /\
          (U64.v (Seq.index roots i) >= U64.v zero_addr + U64.v mword /\
           U64.v (Seq.index roots i) < heap_size /\
           U64.v (Seq.index roots i) % U64.v mword == 0 ==>
           U64.sub (SpecObject.resolve_object (Seq.index roots i <: obj_addr) g) mword <> slot))
      (ensures
        SpecHeap.read_word
          (fst (darken_roots_bounded_prefix_spec g st roots idx cap)) slot ==
        SpecHeap.read_word g slot)

val darken_roots_bounded_spec_preserves_read_word
  (g: heap_state) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (cap: nat) (slot: hp_addr)
  : Lemma
      (requires
        forall (i:nat). i < Seq.length roots ==>
          root_points_to_object g (Seq.index roots i) /\
          (U64.v (Seq.index roots i) >= U64.v zero_addr + U64.v mword /\
           U64.v (Seq.index roots i) < heap_size /\
           U64.v (Seq.index roots i) % U64.v mword == 0 ==>
           U64.sub (SpecObject.resolve_object (Seq.index roots i <: obj_addr) g) mword <> slot))
      (ensures
        SpecHeap.read_word
          (fst (darken_roots_bounded_spec g st roots cap)) slot ==
        SpecHeap.read_word g slot)

val darken_roots_bounded_spec_preserves_bounded_mark_inv
  (g: heap_state) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (cap: nat)
  : Lemma
      (requires
        SpecMarkBoundedInv.bounded_mark_inv g st cap /\
        (forall (i:nat). i < Seq.length roots ==>
          root_points_to_object g (Seq.index roots i)))
      (ensures
        SpecMarkBoundedInv.bounded_mark_inv
          (fst (darken_roots_bounded_spec g st roots cap))
          (snd (darken_roots_bounded_spec g st roots cap))
          cap)

val darken_roots_bounded_spec_preserves_no_black
  (g: heap_state) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (cap: nat)
  : Lemma
      (requires SpecMark.no_black_objects g)
      (ensures
        SpecMark.no_black_objects
          (fst (darken_roots_bounded_spec g st roots cap)))

val darken_roots_bounded_spec_preserves_no_pointer_to_blue
  (g: heap_state) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (cap: nat)
  : Lemma
      (requires
        SpecFields.well_formed_heap g /\
        SpecMark.no_pointer_to_blue g /\
        (forall (i:nat). i < Seq.length roots ==>
          root_points_to_object g (Seq.index roots i)))
      (ensures
        SpecMark.no_pointer_to_blue
          (fst (darken_roots_bounded_spec g st roots cap)))

/// Darkening only recolours white objects, so it changes neither the set of
/// allocated objects nor the free-list head.  Both free-list facts therefore
/// come for free from `darken_roots_bounded_spec_preserves_objects`.
val darken_roots_bounded_spec_preserves_fp_valid
  (g: heap_state) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (cap: nat) (fp: U64.t)
  : Lemma
      (requires SweepInv.fp_valid fp g)
      (ensures SweepInv.fp_valid fp (fst (darken_roots_bounded_spec g st roots cap)))

val darken_roots_bounded_spec_preserves_fp_in_heap
  (g: heap_state) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (cap: nat) (fp: U64.t)
  : Lemma
      (requires GC.Spec.Sweep.fp_in_heap fp g)
      (ensures GC.Spec.Sweep.fp_in_heap fp (fst (darken_roots_bounded_spec g st roots cap)))

/// Bounded mark loop: process gray objects with overflow handling.
/// The outer loop alternates between draining the stack and rescanning
/// the heap for remaining gray objects until none remain.
///
/// Postcondition: well_formed_heap preserved, no gray objects, objects preserved,
/// mark_color_inv, gray_black_reachable, and gray_stays.
/// Check if object at h_addr is white. If so, gray it and push to stack
/// (if stack has capacity). Used by the bridge for root darkening.
fn darken_if_white_bounded (heap: heap_t) (st: gray_stack) (h_addr: hp_addr) (cap: Ghost.erased nat)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (U64.v h_addr + U64.v mword < heap_size /\
                 Seq.length 'st <= cap /\
                 stack_capacity st == cap)
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
    pure ((s2, st2) == darken_if_white_bounded_spec 's 'st h_addr cap)

/// Check if value is a pointer; if so, darken its target with bounded push.
fn check_and_darken_bounded (heap: heap_t) (st: gray_stack) (v: U64.t) (cap: Ghost.erased nat)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (Seq.length 'st <= cap /\ stack_capacity st == cap)
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
    pure ((s2, st2) == check_and_darken_bounded_spec 's 'st v cap)

/// Darken every root in the supplied root array.  This is the operational
/// preparation step used before invoking bounded mark with an explicit ghost
/// root set.
fn darken_roots_bounded
    (heap: heap_t) (st: gray_stack) (roots: array U64.t) (nroots: SZ.t)
    (cap: Ghost.erased nat)
  requires is_heap heap 's ** is_gray_stack st 'st ** pts_to roots 'rs **
           pure (SZ.v nroots == Seq.length 'rs /\
                 Seq.length 'st <= cap /\
                 stack_capacity st == cap)
  ensures exists* s2 st2 rs2.
    is_heap heap s2 ** is_gray_stack st st2 ** pts_to roots rs2 **
    pure (rs2 == 'rs /\
          (s2, st2) == darken_roots_bounded_spec 's 'st 'rs cap)

/// Bounded mark loop: process gray objects with overflow handling.
/// The outer loop alternates between draining the stack and rescanning
/// the heap for remaining gray objects until none remain.
///
/// Postcondition: well_formed_heap preserved, no gray objects, objects preserved,
/// mark_color_inv, gray_black_reachable, and gray_stays.
fn mark_loop_bounded (heap: heap_t) (st: gray_stack)
                     (roots: Ghost.erased (Seq.seq GC.Spec.Base.obj_addr))
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (SpecMarkBoundedInv.bounded_mark_inv 's 'st (stack_capacity st) /\
                 SpecMark.no_black_objects 's /\
                 SpecMark.no_pointer_to_blue 's /\
                 SpecMark.root_props 's roots /\
                 (forall (x:GC.Spec.Base.obj_addr). Seq.mem x (SpecFields.objects GC.Spec.Base.zero_addr 's) /\
                   (GC.Spec.Object.is_gray x 's \/ GC.Spec.Object.is_black x 's) ==> Seq.mem x roots) /\
                 (let graph = GC.Spec.HeapModel.create_graph 's in
                  let roots' = GC.Spec.HeapGraph.coerce_to_vertex_list roots in
                  GC.Spec.Graph.graph_wf graph /\ GC.Spec.Graph.is_vertex_set roots' /\
                  GC.Spec.Graph.subset_vertices roots' graph.vertices))
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
          pure (SpecFields.well_formed_heap s2 /\
                SweepInv.no_gray_objects s2 /\
                SpecFields.objects GC.Spec.Base.zero_addr s2 == SpecFields.objects GC.Spec.Base.zero_addr 's /\
                SpecMarkBoundedCorr.mark_color_inv 's s2 /\
                SpecMarkBoundedCorr.gray_black_reachable 's s2 roots /\
                SpecMarkBoundedCorr.gray_stays 's s2)
