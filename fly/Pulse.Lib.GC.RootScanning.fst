(*
   Pulse GC - Root Scanning for Parallel GC

   Root scanning phase for per-thread parallel marking:
   1. gray_root: gray one root (white->gray, push to stack)
   2. scan_thread_roots: iterate shadow stack, gray each root
   3. mark_root_blue: mark one root blue (white->blue)
   4. mark_other_roots_blue: mark all other threads' roots blue
   5. reset_blue_to_white_one: reset one blue object to white
   6. reset_blue_to_white: reset all blue markings

   All functions preserve well_formed_heap.
   Uses types from common/Pulse.Lib.GC (Heap, Object, Stack).
*)

module Pulse.Lib.GC.RootScanning

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.GC.Heap
open Pulse.Lib.GC.Object
open Pulse.Lib.GC.Stack
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Header = Pulse.Lib.Header
module SpecHeap = Pulse.Spec.GC.Heap
module SpecObject = Pulse.Spec.GC.Object
module SpecFields = Pulse.Spec.GC.Fields
open Pulse.Spec.GC.ColorLemmas

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
/// Bridge lemmas
/// ---------------------------------------------------------------------------

/// Bridge: colorHeader Gray write == makeGray, preserving wfh
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

/// Bridge: set_color64 3UL write == set_object_color_raw 3UL, preserving wfh
#push-options "--z3rlimit 200"
let blue_bridge (g: heap_state) (obj: obj_addr)
  : Lemma (requires Seq.length g == heap_size /\
                    SpecFields.well_formed_heap g /\
                    Seq.mem obj (SpecFields.objects 0UL g))
          (ensures (let h_addr = SpecHeap.hd_address obj in
                    let hdr = SpecHeap.read_word g h_addr in
                    let new_hdr = Header.set_color64 hdr 3UL in
                    spec_write_word g (U64.v h_addr) new_hdr == set_object_color_raw obj g 3UL /\
                    SpecFields.well_formed_heap (set_object_color_raw obj g 3UL) /\
                    Seq.length (set_object_color_raw obj g 3UL) == Seq.length g))
  = let h_addr = SpecHeap.hd_address obj in
    SpecHeap.hd_address_spec obj;
    SpecFields.wf_object_size_bound g obj;
    hp_addr_plus_8 h_addr;
    spec_write_word_eq g h_addr (Header.set_color64 (SpecHeap.read_word g h_addr) 3UL);
    set_object_color_raw_preserves_wf g obj 3UL;
    set_object_color_raw_length obj g 3UL
#pop-options

/// Bridge: colorHeader White write == makeWhite, preserving wfh
#push-options "--z3rlimit 200"
let whiten_bridge (g: heap_state) (obj: obj_addr)
  : Lemma (requires Seq.length g == heap_size /\
                    SpecFields.well_formed_heap g /\
                    Seq.mem obj (SpecFields.objects 0UL g))
          (ensures (let h_addr = SpecHeap.hd_address obj in
                    let hdr = SpecHeap.read_word g h_addr in
                    let new_hdr = SpecObject.colorHeader hdr Header.White in
                    spec_write_word g (U64.v h_addr) new_hdr == SpecObject.makeWhite obj g /\
                    SpecFields.well_formed_heap (SpecObject.makeWhite obj g) /\
                    Seq.length (SpecObject.makeWhite obj g) == Seq.length g))
  = let h_addr = SpecHeap.hd_address obj in
    SpecHeap.hd_address_spec obj;
    SpecFields.wf_object_size_bound g obj;
    hp_addr_plus_8 h_addr;
    spec_write_word_eq g h_addr (SpecObject.colorHeader (SpecHeap.read_word g h_addr) Header.White);
    SpecObject.makeWhite_spec obj g;
    makeWhite_preserves_wf g obj;
    SpecObject.makeWhite_eq obj g;
    SpecObject.set_object_color_length obj g Header.White
#pop-options

/// ---------------------------------------------------------------------------
/// Gray a single root (white -> gray, push to stack)
/// Preserves well_formed_heap.
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 100"
fn gray_root
  (heap: heap_t) (st: gray_stack) (root: obj_addr)
  requires is_heap heap 's ** is_gray_stack st 'gs **
           pure (SpecFields.well_formed_heap 's /\ Seq.length 's == heap_size /\
                 Seq.mem root (SpecFields.objects 0UL 's) /\
                 stack_valid 's 'gs /\
                 contiguous_heap 's)
  ensures exists* s2 gs2. is_heap heap s2 ** is_gray_stack st gs2 **
           pure (SpecFields.well_formed_heap s2 /\
                 objects_preserved s2 's /\
                 stack_valid s2 gs2 /\
                 contiguous_heap s2)
{
  let h_addr = hd_address root;
  hp_addr_plus_8 h_addr;
  let hdr = read_word heap h_addr;
  let c = getColor hdr;
  if (c = white) {
    let new_hdr = SpecObject.colorHeader hdr gray;
    write_word heap h_addr new_hdr;
    // Bridge to makeGray
    spec_read_word_eq 's h_addr;
    SpecHeap.hd_address_spec root;
    U64.v_inj h_addr (SpecHeap.hd_address root);
    grayen_bridge 's root;
    rewrite (is_heap heap (spec_write_word 's (U64.v h_addr) new_hdr))
         as (is_heap heap (SpecObject.makeGray root 's));
    objects_preserved_makeGray 's root;
    contiguous_heap_preserved_makeGray 's root;
    // Stack validity: makeGray preserves stack_valid, then push adds a valid object
    stack_valid_makeGray 's root 'gs;
    push st root;
    with gs2. assert (is_gray_stack st gs2);
    objects_preserved_mem (SpecObject.makeGray root 's) 's root;
    stack_valid_cons (SpecObject.makeGray root 's) root 'gs;
    ()
  } else {
    ()
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// Scan one thread's roots (iterate shadow stack, gray each root)
/// Preserves well_formed_heap.
/// ---------------------------------------------------------------------------

fn scan_thread_roots
  (heap: heap_t) (st: gray_stack)
  (roots: Seq.seq obj_addr)
  (n: SZ.t{SZ.v n == Seq.length roots})
  requires is_heap heap 's ** is_gray_stack st 'gs **
           pure (SpecFields.well_formed_heap 's /\
                 roots_valid 's roots /\
                 stack_valid 's 'gs /\
                 contiguous_heap 's)
  ensures exists* s2 gs2. is_heap heap s2 ** is_gray_stack st gs2 **
           pure (SpecFields.well_formed_heap s2 /\
                 objects_preserved s2 's /\
                 stack_valid s2 gs2 /\
                 contiguous_heap s2)
{
  let mut i = 0sz;
  while (
    let iv = !i;
    (SZ.lt iv n)
  )
  invariant b. exists* iv s_i gs_i.
    pts_to i iv **
    is_heap heap s_i **
    is_gray_stack st gs_i **
    pure (SZ.v iv <= SZ.v n) **
    pure (b == SZ.lt iv n) **
    pure (SpecFields.well_formed_heap s_i /\
          objects_preserved s_i 's /\
          stack_valid s_i gs_i /\
          contiguous_heap s_i)
  {
    let iv = !i;
    is_heap_length heap;
    let root = Seq.index roots (SZ.v iv);
    // root ∈ objects 0UL s_i follows from roots_valid 's roots + objects equality
    gray_root heap st root;
    i := SZ.add iv 1sz;
    ()
  }
}

/// ---------------------------------------------------------------------------
/// Mark one root blue (white -> blue via raw header manipulation)
/// Preserves well_formed_heap.
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 100"
fn mark_root_blue
  (heap: heap_t) (root: obj_addr)
  requires is_heap heap 's **
           pure (SpecFields.well_formed_heap 's /\ Seq.length 's == heap_size /\
                 Seq.mem root (SpecFields.objects 0UL 's) /\
                 contiguous_heap 's)
  ensures exists* s2. is_heap heap s2 **
           pure (SpecFields.well_formed_heap s2 /\
                 objects_preserved s2 's /\
                 contiguous_heap s2)
{
  let h_addr = hd_address root;
  hp_addr_plus_8 h_addr;
  let hdr = read_word heap h_addr;
  let c = getColor hdr;
  if (c = white) {
    // Blue = raw color bits 3 (not a standard color_sem)
    let new_hdr = Header.set_color64 hdr 3UL;
    write_word heap h_addr new_hdr;
    // Bridge to set_object_color_raw
    spec_read_word_eq 's h_addr;
    SpecHeap.hd_address_spec root;
    U64.v_inj h_addr (SpecHeap.hd_address root);
    blue_bridge 's root;
    rewrite (is_heap heap (spec_write_word 's (U64.v h_addr) new_hdr))
         as (is_heap heap (set_object_color_raw root 's 3UL));
    objects_preserved_by_raw_color 's root 3UL;
    contiguous_heap_preserved_raw_color 's root 3UL;
    ()
  } else {
    ()
  }
}
#pop-options

/// Mark all roots from other threads as blue.
/// Preserves well_formed_heap and objects enumeration.
fn mark_other_roots_blue
  (heap: heap_t)
  (other_roots: Seq.seq obj_addr)
  (n: SZ.t{SZ.v n == Seq.length other_roots})
  requires is_heap heap 's **
           pure (SpecFields.well_formed_heap 's /\
                 roots_valid 's other_roots /\
                 contiguous_heap 's)
  ensures exists* s2. is_heap heap s2 **
           pure (SpecFields.well_formed_heap s2 /\
                 objects_preserved s2 's /\
                 contiguous_heap s2)
{
  let mut i = 0sz;
  while (
    let iv = !i;
    (SZ.lt iv n)
  )
  invariant b. exists* iv s_i.
    pts_to i iv **
    is_heap heap s_i **
    pure (SZ.v iv <= SZ.v n) **
    pure (b == SZ.lt iv n) **
    pure (SpecFields.well_formed_heap s_i /\
          objects_preserved s_i 's /\
          contiguous_heap s_i)
  {
    let iv = !i;
    is_heap_length heap;
    let root = Seq.index other_roots (SZ.v iv);
    mark_root_blue heap root;
    i := SZ.add iv 1sz;
    ()
  }
}

#push-options "--z3rlimit 100"
fn reset_blue_to_white_one
  (heap: heap_t) (addr: obj_addr)
  requires is_heap heap 's **
           pure (SpecFields.well_formed_heap 's /\ Seq.length 's == heap_size /\
                 Seq.mem addr (SpecFields.objects 0UL 's) /\
                 contiguous_heap 's)
  ensures exists* s2. is_heap heap s2 **
           pure (SpecFields.well_formed_heap s2 /\
                 objects_preserved s2 's /\
                 contiguous_heap s2)
{
  let h_addr = hd_address addr;
  hp_addr_plus_8 h_addr;
  let hdr = read_word heap h_addr;
  // Check raw color bits: blue = 3
  let raw_color = Header.get_color64 hdr;
  if (raw_color = 3UL) {
    let new_hdr = SpecObject.colorHeader hdr white;
    write_word heap h_addr new_hdr;
    // Bridge to makeWhite
    spec_read_word_eq 's h_addr;
    SpecHeap.hd_address_spec addr;
    U64.v_inj h_addr (SpecHeap.hd_address addr);
    whiten_bridge 's addr;
    rewrite (is_heap heap (spec_write_word 's (U64.v h_addr) new_hdr))
         as (is_heap heap (SpecObject.makeWhite addr 's));
    objects_preserved_makeWhite 's addr;
    contiguous_heap_preserved_makeWhite 's addr;
    ()
  } else {
    ()
  }
}
#pop-options

/// Reset all previously-blued objects back to white.
/// Preserves well_formed_heap and objects enumeration.
fn reset_blue_to_white
  (heap: heap_t)
  (addrs: Seq.seq obj_addr)
  (n: SZ.t{SZ.v n == Seq.length addrs})
  requires is_heap heap 's **
           pure (SpecFields.well_formed_heap 's /\
                 roots_valid 's addrs /\
                 contiguous_heap 's)
  ensures exists* s2. is_heap heap s2 **
           pure (SpecFields.well_formed_heap s2 /\
                 objects_preserved s2 's /\
                 contiguous_heap s2)
{
  let mut i = 0sz;
  while (
    let iv = !i;
    (SZ.lt iv n)
  )
  invariant b. exists* iv s_i.
    pts_to i iv **
    is_heap heap s_i **
    pure (SZ.v iv <= SZ.v n) **
    pure (b == SZ.lt iv n) **
    pure (SpecFields.well_formed_heap s_i /\
          objects_preserved s_i 's /\
          contiguous_heap s_i)
  {
    let iv = !i;
    is_heap_length heap;
    let addr = Seq.index addrs (SZ.v iv);
    reset_blue_to_white_one heap addr;
    i := SZ.add iv 1sz;
    ()
  }
}
