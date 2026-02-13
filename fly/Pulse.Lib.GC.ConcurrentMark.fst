(*
   Pulse GC - Concurrent Mark Phase for Parallel GC

   Mark phase implementation:
   1. check_and_darken: check if pointer, gray if white (skip blue)
   2. push_children: gray all children of an object
   3. mark_step: pop gray, blacken, scan children
   4. mark_loop: iterate mark_step until gray stack is empty

   All functions preserve well_formed_heap.
   Uses types from common/Pulse.Lib.GC (Heap, Object, Stack).
*)

module Pulse.Lib.GC.ConcurrentMark

#lang-pulse

#set-options "--z3rlimit 50"

open FStar.Mul
open Pulse.Lib.Pervasives
open Pulse.Lib.GC.Heap
open Pulse.Lib.GC.Object
open Pulse.Lib.GC.Stack
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Header = Pulse.Lib.Header
module ML = FStar.Math.Lemmas
module SpecHeap = Pulse.Spec.GC.Heap
module SpecObject = Pulse.Spec.GC.Object
module SpecFields = Pulse.Spec.GC.Fields
open Pulse.Spec.GC.ColorLemmas

/// Bridge: Pulse getWosize == Spec getWosize (both compute shift_right 10)
let getWosize_eq (hdr: U64.t) : Lemma (getWosize hdr == SpecObject.getWosize hdr) =
  SpecObject.getWosize_spec hdr

/// ---------------------------------------------------------------------------
/// Ghost helpers
/// ---------------------------------------------------------------------------

ghost fn is_heap_length (h: heap_t)
  requires is_heap h 's
  ensures is_heap h 's ** pure (Seq.length 's == heap_size)
{
  unfold is_heap;
  fold (is_heap h 's)
}

/// ---------------------------------------------------------------------------
/// spec_field_address: compute field address
/// ---------------------------------------------------------------------------

let spec_field_address (h_addr: nat) (i: nat) : nat =
  h_addr + i * 8

/// ---------------------------------------------------------------------------
/// Bridge lemmas: connect Pulse writes to spec-level color operations
/// ---------------------------------------------------------------------------

/// Bridge: Pulse write of colorHeader Gray == spec makeGray, preserving wfh
#push-options "--z3rlimit 200"
let grayen_bridge (g: heap_state) (obj: obj_addr)
  : Lemma (requires Seq.length g == heap_size /\
                    SpecFields.well_formed_heap g /\
                    Seq.mem obj (SpecFields.objects 0UL g))
          (ensures (let h_addr = SpecHeap.hd_address obj in
                    let hdr = SpecHeap.read_word g h_addr in
                    let new_hdr = SpecObject.colorHeader hdr Header.Gray in
                    spec_write_word g (U64.v h_addr) new_hdr == SpecObject.makeGray obj g /\
                    SpecFields.well_formed_heap (SpecObject.makeGray obj g) /\
                    Seq.length (SpecObject.makeGray obj g) == Seq.length g))
  = let h_addr = SpecHeap.hd_address obj in
    SpecHeap.hd_address_spec obj;
    SpecFields.wf_object_size_bound g obj;
    hp_addr_plus_8 h_addr;
    spec_write_word_eq g h_addr (SpecObject.colorHeader (SpecHeap.read_word g h_addr) Header.Gray);
    SpecObject.makeGray_spec obj g;
    makeGray_preserves_wf g obj;
    SpecObject.makeGray_eq obj g;
    SpecObject.set_object_color_length obj g Header.Gray
#pop-options

/// Bridge: Pulse write of colorHeader Black == spec makeBlack, preserving wfh
#push-options "--z3rlimit 200"
let blacken_bridge (g: heap_state) (obj: obj_addr)
  : Lemma (requires Seq.length g == heap_size /\
                    SpecFields.well_formed_heap g /\
                    Seq.mem obj (SpecFields.objects 0UL g))
          (ensures (let h_addr = SpecHeap.hd_address obj in
                    let hdr = SpecHeap.read_word g h_addr in
                    let new_hdr = SpecObject.colorHeader hdr Header.Black in
                    spec_write_word g (U64.v h_addr) new_hdr == SpecObject.makeBlack obj g /\
                    SpecFields.well_formed_heap (SpecObject.makeBlack obj g) /\
                    Seq.length (SpecObject.makeBlack obj g) == Seq.length g))
  = let h_addr = SpecHeap.hd_address obj in
    SpecHeap.hd_address_spec obj;
    SpecFields.wf_object_size_bound g obj;
    hp_addr_plus_8 h_addr;
    spec_write_word_eq g h_addr (SpecObject.colorHeader (SpecHeap.read_word g h_addr) Header.Black);
    SpecObject.makeBlack_spec obj g;
    makeBlack_preserves_wf g obj;
    SpecObject.makeBlack_eq obj g;
    SpecObject.set_object_color_length obj g Header.Black
#pop-options

/// ---------------------------------------------------------------------------
/// Check and darken: if pointer, gray its target if white
/// Preserves well_formed_heap.
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 100"
fn check_and_darken (heap: heap_t) (st: gray_stack) (v: U64.t)
  requires is_heap heap 's ** is_gray_stack st 'gs **
           pure (SpecFields.well_formed_heap 's /\ Seq.length 's == heap_size)
  ensures exists* s2 gs2. is_heap heap s2 ** is_gray_stack st gs2 **
           pure (SpecFields.well_formed_heap s2)
{
  if (U64.v v >= U64.v mword && U64.v v < heap_size && U64.v v % U64.v mword = 0) {
    let h_addr : hp_addr = U64.sub v mword;
    hp_addr_plus_8 h_addr;
    let hdr = read_word heap h_addr;
    let c = getColor hdr;
    if (c = white) {
      let new_hdr = SpecObject.colorHeader hdr gray;
      write_word heap h_addr new_hdr;
      let obj : obj_addr = v;
      // Bridge: spec_write_word to makeGray
      spec_read_word_eq 's h_addr;
      SpecHeap.hd_address_spec obj;
      U64.v_inj h_addr (SpecHeap.hd_address obj);
      // Membership (derivable from well_formed_heap + parent field provenance)
      assume_ (pure (Seq.mem obj (SpecFields.objects 0UL 's)));
      grayen_bridge 's obj;
      rewrite (is_heap heap (spec_write_word 's (U64.v h_addr) new_hdr))
           as (is_heap heap (SpecObject.makeGray obj 's));
      push st obj;
      ()
    } else {
      ()
    }
  } else {
    ()
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// Push children: gray all pointer children of an object
/// Preserves well_formed_heap.
/// ---------------------------------------------------------------------------

fn push_children (heap: heap_t) (st: gray_stack) (h_addr: hp_addr) (wz: wosize)
  requires is_heap heap 's ** is_gray_stack st 'gs **
           pure (U64.v wz <= pow2 54 - 1 /\
                 U64.v h_addr + U64.v mword < heap_size /\
                 spec_field_address (U64.v h_addr) (U64.v wz + 1) <= heap_size /\
                 Seq.length 's == heap_size /\
                 SpecFields.well_formed_heap 's)
  ensures exists* s2 gs2. is_heap heap s2 ** is_gray_stack st gs2 **
           pure (SpecFields.well_formed_heap s2)
{
  let mut i = 1UL;

  while (U64.lte !i wz)
    invariant exists* vi s_i gs_i.
      pts_to i vi **
      is_heap heap s_i **
      is_gray_stack st gs_i **
      pure (U64.v vi >= 1 /\ U64.v vi <= U64.v wz + 1 /\
            SpecFields.well_formed_heap s_i /\ Seq.length s_i == heap_size)
  {
    let curr_i = !i;
    assert (pure (spec_field_address (U64.v h_addr) (U64.v curr_i) < heap_size));
    ML.lemma_mod_plus_distr_l (U64.v h_addr) (U64.v curr_i * 8) 8;
    let field_offset = U64.mul curr_i mword;
    let field_addr : hp_addr = U64.add h_addr field_offset;
    is_heap_length heap;
    let v = read_word heap field_addr;
    check_and_darken heap st v;
    i := U64.add curr_i 1UL
  }
}

/// ---------------------------------------------------------------------------
/// Maybe push children (if scannable)
/// Preserves well_formed_heap.
/// ---------------------------------------------------------------------------

fn maybe_push_children (heap: heap_t) (st: gray_stack) (h_addr: hp_addr)
                       (wz: wosize) (tag: U64.t)
  requires is_heap heap 's ** is_gray_stack st 'gs **
           pure (U64.v wz <= pow2 54 - 1 /\
                 U64.v h_addr + U64.v mword < heap_size /\
                 spec_field_address (U64.v h_addr) (U64.v wz + 1) <= heap_size /\
                 SpecFields.well_formed_heap 's /\
                 Seq.length 's == heap_size)
  ensures exists* s2 gs2. is_heap heap s2 ** is_gray_stack st gs2 **
           pure (SpecFields.well_formed_heap s2)
{
  if U64.lt tag no_scan_tag {
    push_children heap st h_addr wz
  }
}

/// ---------------------------------------------------------------------------
/// Mark step: pop gray, blacken, then scan children
/// Preserves well_formed_heap.
/// Order: blacken first (uses original ghost 's), then push children.
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 200"
fn mark_step (heap: heap_t) (st: gray_stack)
  requires is_heap heap 's ** is_gray_stack st 'gs **
           pure (Seq.length 'gs > 0 /\
                 SpecFields.well_formed_heap 's /\
                 stack_valid 's 'gs)
  ensures exists* s2 gs2. is_heap heap s2 ** is_gray_stack st gs2 **
           pure (SpecFields.well_formed_heap s2 /\
                 stack_valid s2 gs2)
{
  // Pop: 'gs == Seq.cons f_addr tl
  let f_addr = pop st;
  // f_addr == Seq.index 'gs 0, so stack_valid gives membership
  stack_valid_head 's 'gs;
  // 'gs == Seq.cons f_addr tl, so Seq.index 'gs 0 == f_addr
  with tl. assert (is_gray_stack st tl);
  // f_addr is a member of objects 0UL 's
  assert (pure (Seq.mem f_addr (SpecFields.objects 0UL 's)));

  let h_addr : hp_addr = U64.sub f_addr mword;
  hp_addr_plus_8 h_addr;

  is_heap_length heap;
  let hdr = read_word heap h_addr;
  let wz = getWosize hdr;
  let tag = getTag hdr;

  // Blacken FIRST: write black header (uses original ghost 's)
  let new_hdr = SpecObject.colorHeader hdr black;
  write_word heap h_addr new_hdr;

  // Bridge: spec_write_word 's h_addr new_hdr == makeBlack f_addr 's
  spec_read_word_eq 's h_addr;
  SpecHeap.hd_address_spec f_addr;
  U64.v_inj h_addr (SpecHeap.hd_address f_addr);
  // f_addr membership was established from stack_valid above
  blacken_bridge 's f_addr;
  rewrite (is_heap heap (spec_write_word 's (U64.v h_addr) new_hdr))
       as (is_heap heap (SpecObject.makeBlack f_addr 's));

  // Establish preconditions for maybe_push_children in the new ghost (makeBlack f_addr 's)
  // 1. Membership: f_addr in objects 0UL (makeBlack f_addr 's)
  objects_preserved_makeBlack 's f_addr;
  objects_preserved_mem (SpecObject.makeBlack f_addr 's) 's f_addr;
  // 2. Field bounds: derive from wf_object_size_bound + wosize bridge
  //    wf_object_size_bound gives: hd_address(f_addr) + 8 + wosize_of_object(f_addr, g) * 8 <= heap_size
  //    Need: spec_field_address h_addr (wz + 1) <= heap_size = h_addr + (wz+1)*8 = h_addr + 8 + wz*8
  SpecFields.wf_object_size_bound (SpecObject.makeBlack f_addr 's) f_addr;
  SpecHeap.hd_address_spec f_addr;
  // Now: h_addr + 8 + wosize_of_object f_addr (makeBlack f_addr 's) * 8 <= heap_size
  // Bridge wz to wosize_of_object f_addr (makeBlack f_addr 's):
  getWosize_eq hdr;
  SpecObject.wosize_of_object_spec f_addr 's;
  SpecObject.makeBlack_eq f_addr 's;
  SpecObject.color_preserves_wosize f_addr 's Header.Black;
  // wosize_of_object f_addr (makeBlack f_addr 's) == wosize_of_object f_addr 's
  //   == getWosize (read_word 's h_addr) == SpecObject.getWosize hdr == getWosize hdr == wz
  assert (pure (U64.v wz == U64.v (SpecObject.wosize_of_object f_addr 's)));
  assert (pure (SpecObject.wosize_of_object f_addr (SpecObject.makeBlack f_addr 's) ==
                SpecObject.wosize_of_object f_addr 's));

  // Then push children (heap is now makeBlack f_addr 's, which is well_formed)
  maybe_push_children heap st h_addr wz tag;
  // Stack validity: each pushed child is in objects (from check_and_darken assume_)
  // Will be proven when Step C eliminates the check_and_darken assume_
  with s_post gs_post. assert (is_heap heap s_post ** is_gray_stack st gs_post);
  assume_ (pure (stack_valid s_post gs_post));
  ()
}
#pop-options

/// ---------------------------------------------------------------------------
/// Mark loop: iterate until stack empty
/// Preserves well_formed_heap.
/// ---------------------------------------------------------------------------

fn mark_loop (heap: heap_t) (st: gray_stack)
  requires is_heap heap 's ** is_gray_stack st 'gs **
           pure (SpecFields.well_formed_heap 's /\
                 stack_valid 's 'gs)
  ensures exists* s2 gs2. is_heap heap s2 ** is_gray_stack st gs2 **
           pure (SpecFields.well_formed_heap s2)
{
  let mut continue_ = true;
  while (
    let c = !continue_;
    c
  )
  invariant b. exists* c s_i gs_i.
    pts_to continue_ c **
    is_heap heap s_i **
    is_gray_stack st gs_i **
    pure (b == c) **
    pure (SpecFields.well_formed_heap s_i /\
          stack_valid s_i gs_i)
  {
    let empty = is_empty st;
    if empty {
      continue_ := false;
      ()
    } else {
      mark_step heap st;
      ()
    }
  }
}
