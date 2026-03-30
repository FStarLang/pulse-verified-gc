(*
   Pulse GC - Sweep Module
   
   This module implements the sweep phase of the garbage collector.
   After marking, sweep resets colors of surviving (black) objects
   back to white for the next GC cycle.
   
   Based on: Proofs/Impl.GC_closure_infix_ver3.fst
*)

module Pulse.Lib.GC.Sweep

#lang-pulse

#set-options "--z3rlimit 50 --split_queries always"
open FStar.Mul
open Pulse.Lib.Pervasives
open Pulse.Lib.GC.Heap
open Pulse.Lib.GC.Object
open Pulse.Lib.GC.Fields
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module ML = FStar.Math.Lemmas
module SpecSweep = Pulse.Spec.GC.Sweep
module SpecFields = Pulse.Spec.GC.Fields
module SpecHeap = Pulse.Spec.GC.Heap
module SpecObject = Pulse.Spec.GC.Object
module SpecMark = Pulse.Spec.GC.Mark
module SpecHeapGraph = Pulse.Spec.GC.HeapGraph
module SI = Pulse.Spec.GC.SweepInv
module SpecGCPost = Pulse.Spec.GC.Correctness
open Pulse.Lib.GC.Sweep.Lemmas

/// Extract the pure length fact from is_heap, then refold
ghost fn is_heap_length (h: heap_t)
  requires is_heap h 's
  ensures is_heap h 's ** pure (Seq.length 's == heap_size)
{
  unfold is_heap;
  fold (is_heap h 's)
}

/// Write a free-list link to field 1 if the object has fields (wosize > 0)
/// Precondition: object fits in heap (h_addr + (1+wz)*8 <= heap_size)
fn write_freelist_link (heap: heap_t) (h_addr: hp_addr) (wz: wosize) (fp: U64.t)
  requires is_heap heap 's **
           pure (U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size)
  ensures exists* s2. is_heap heap s2
{
  if U64.gt wz 0UL {
    is_heap_length heap;
    let field1_addr_raw = U64.add h_addr mword;
    // h_addr + 8 < h_addr + (1+wz)*8 <= heap_size (since wz > 0)
    // h_addr % 8 == 0 implies (h_addr + 8) % 8 == 0
    let field1_addr : hp_addr = field1_addr_raw;
    write_word heap field1_addr fp
  }
}

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1 --split_queries always --z3refresh"
fn sweep_white_field_write (heap: heap_t) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (wz: wosize) (fp: U64.t)
  requires is_heap heap 's **
           pure (Seq.length 's == heap_size /\
                 U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size /\
                 SpecFields.well_formed_heap 's /\
                 SI.obj_in_objects (SpecHeap.f_address h_addr) 's /\
                 wz == SpecObject.getWosize (SpecHeap.read_word 's h_addr) /\
                 SpecObject.is_white (SpecHeap.f_address h_addr) 's /\
                 U64.v wz > 0 /\
                 SI.fp_valid fp 's)
  ensures exists* s1. is_heap heap s1 **
           pure (SpecFields.well_formed_heap s1 /\
                 SpecFields.objects zero_addr s1 == SpecFields.objects zero_addr 's /\
                 SpecObject.is_white (SpecHeap.f_address h_addr) s1 /\
                 SI.headers_preserved_from
                   (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8))
                   s1 's /\
                 SI.headers_preserved_before (U64.v h_addr) s1 's /\
                 SpecObject.getWosize (SpecHeap.read_word s1 h_addr) ==
                 SpecObject.getWosize (SpecHeap.read_word 's h_addr) /\
                 s1 == spec_write_word 's (U64.v h_addr + 8) fp)
{
  is_heap_length heap;
  let obj : obj_addr = SpecHeap.f_address h_addr;
  SI.obj_in_objects_elim obj 's;
  let field1_addr = field1_of h_addr;
  write_word heap field1_addr fp;
  // write_word gives: is_heap heap (SpecHeap.write_word 's field1_addr fp)
  //                 ** pure (SpecHeap.write_word 's field1_addr fp == spec_write_word 's (U64.v field1_addr) fp)
  // Establish the additional bridge equalities
  spec_write_word_eq 's field1_addr fp;
  assert (pure (U64.v field1_addr == U64.v h_addr + 8));
  // Call lemmas (they work with spec_write_word in their pre/postconditions)
  sweep_white_write_preserves 's h_addr wz fp;
  sweep_white_header_preserved 's h_addr wz fp;
  headers_preserved_from_spec_write
    (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8))
    's field1_addr fp;
  sweep_white_color_preserved 's h_addr wz fp;
  ()
}
#pop-options

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1 --split_queries always --z3refresh"
fn sweep_write_blue_hdr (heap: heap_t) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (wz: wosize)
  requires is_heap heap 's1 **
           pure (Seq.length 's1 == heap_size /\
                 SpecFields.well_formed_heap 's1 /\
                 Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr 's1) /\
                 SpecObject.is_white (SpecHeap.f_address h_addr) 's1 /\
                 U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size /\
                 wz == SpecObject.getWosize (SpecHeap.read_word 's1 h_addr))
  ensures exists* s2. is_heap heap s2 **
           pure (s2 == SpecObject.makeBlue (SpecHeap.f_address h_addr) 's1)
{
  let obj : obj_addr = SpecHeap.f_address h_addr;
  let hdr = read_word heap h_addr;
  let blue_hdr = makeHeader (getWosize hdr) blue (getTag hdr);
  write_word heap h_addr blue_hdr;
  SpecHeap.hd_f_roundtrip h_addr;
  bluen_eq 's1 obj;
  ()
}
#pop-options

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1 --split_queries always --z3refresh"
fn sweep_white_blue_mark (heap: heap_t) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (wz: wosize)
  requires is_heap heap 's1 **
           pure (Seq.length 's1 == heap_size /\
                 SpecFields.well_formed_heap 's1 /\
                 Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr 's1) /\
                 SpecObject.is_white (SpecHeap.f_address h_addr) 's1 /\
                 U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size /\
                 wz == SpecObject.getWosize (SpecHeap.read_word 's1 h_addr))
  ensures exists* s2. is_heap heap s2 **
           pure (SpecFields.well_formed_heap s2 /\
                 SpecFields.objects zero_addr s2 == SpecFields.objects zero_addr 's1 /\
                 SpecObject.is_blue (SpecHeap.f_address h_addr) s2 /\
                 SI.headers_preserved_from
                   (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8))
                   s2 's1 /\
                 SI.headers_preserved_before (U64.v h_addr) s2 's1 /\
                 SpecObject.getWosize (SpecHeap.read_word s2 h_addr) ==
                 SpecObject.getWosize (SpecHeap.read_word 's1 h_addr) /\
                 s2 == SpecObject.makeBlue (SpecHeap.f_address h_addr) 's1)
{
  let obj : obj_addr = SpecHeap.f_address h_addr;
  sweep_write_blue_hdr heap h_addr wz;
  with s2. assert (is_heap heap s2);
  // Bridge makeBlue to set_object_color for downstream lemmas
  SpecObject.makeBlue_eq obj 's1;
  SpecObject.makeBlue_is_blue obj 's1;
  SpecMark.color_change_preserves_wf 's1 obj Pulse.Lib.Header.Blue;
  SpecFields.color_change_preserves_objects 's1 obj Pulse.Lib.Header.Blue;
  SpecHeap.hd_f_roundtrip h_addr;
  makeBlue_headers_preserved_from
    (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8))
    's1 h_addr;
  makeBlue_headers_preserved_before 's1 h_addr;
  makeBlue_preserves_getWosize 's1 h_addr;
  // Explicit equality: connect existential witness s2 to lemma conclusions
  assert (pure (s2 == SpecObject.makeBlue obj 's1));
  // Assert each postcondition conjunct explicitly so split queries can use equality
  assert (pure (SpecFields.well_formed_heap s2));
  assert (pure (SpecFields.objects zero_addr s2 == SpecFields.objects zero_addr 's1));
  assert (pure (SpecObject.is_blue (SpecHeap.f_address h_addr) s2));
  assert (pure (SI.headers_preserved_from
    (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8)) s2 's1));
  assert (pure (SI.headers_preserved_before (U64.v h_addr) s2 's1));
  assert (pure (SpecObject.getWosize (SpecHeap.read_word s2 h_addr) ==
    SpecObject.getWosize (SpecHeap.read_word 's1 h_addr)));
  ()
}
#pop-options

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1 --split_queries always --z3refresh"
fn sweep_white_spec (heap: heap_t) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (wz: wosize) (fp: U64.t)
  requires is_heap heap 's **
           pure (U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size /\
                 SpecFields.well_formed_heap 's /\
                 SI.obj_in_objects (SpecHeap.f_address h_addr) 's /\
                 wz == SpecObject.getWosize (SpecHeap.read_word 's h_addr) /\
                 SpecObject.is_white (SpecHeap.f_address h_addr) 's /\
                 SI.fp_valid fp 's)
  returns new_fp: U64.t
  ensures exists* s2. is_heap heap s2 **
           pure (SpecFields.well_formed_heap s2 /\
                 SpecFields.objects zero_addr s2 == SpecFields.objects zero_addr 's /\
                 new_fp == SpecHeap.f_address h_addr /\
                 SI.headers_preserved_from
                   (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8))
                   s2 's /\
                 SpecObject.is_blue (SpecHeap.f_address h_addr) s2 /\
                 SI.headers_preserved_before (U64.v h_addr) s2 's /\
                 SpecObject.getWosize (SpecHeap.read_word s2 h_addr) ==
                 SpecObject.getWosize (SpecHeap.read_word 's h_addr) /\
                 s2 == fst (SpecSweep.sweep_object 's (SpecHeap.f_address h_addr) fp))
{
  if U64.gt wz 0UL {
    is_heap_length heap;
    let obj : obj_addr = SpecHeap.f_address h_addr;
    SI.obj_in_objects_elim obj 's;
    // Step 1: Write free-list link
    sweep_white_field_write heap h_addr wz fp;
    with s1. assert (is_heap heap s1);
    // Step 2: Write blue header
    sweep_white_blue_mark heap h_addr wz;
    with s2. assert (is_heap heap s2);
    // Chain preservation facts: 's -> s1 -> s2
    headers_preserved_from_trans_bridge
      (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8))
      (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8))
      's s1 s2;
    SI.headers_preserved_before_trans (U64.v h_addr) 's s1 s2;
    // Bridge: makeBlue obj s1 == fst(sweep_object 's obj fp)
    sweep_object_white_write_eq 's h_addr wz fp;
      SpecHeap.f_address h_addr
    // }
  } else {
    is_heap_length heap;
    let obj : obj_addr = SpecHeap.f_address h_addr;
    SI.obj_in_objects_elim obj 's;
    // Just write blue header (no field write)
    sweep_white_blue_mark heap h_addr wz;
    with s2. assert (is_heap heap s2);
    sweep_object_white_noop_eq 's h_addr wz fp;
      SpecHeap.f_address h_addr
    // }
  }
}
#pop-options
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1 --split_queries always --z3refresh"
/// Helper: write a white header for the black->white sweep case
fn sweep_write_white_hdr (heap: heap_t) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (wz: wosize)
  requires is_heap heap 's **
           pure (Seq.length 's == heap_size /\
                 U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size /\
                 SpecFields.well_formed_heap 's /\
                 Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr 's) /\
                 SpecObject.is_black (SpecHeap.f_address h_addr) 's /\
                 wz == SpecObject.getWosize (SpecHeap.read_word 's h_addr))
  ensures exists* s2. is_heap heap s2 **
           pure (s2 == SpecObject.makeWhite (SpecHeap.f_address h_addr) 's)
{
  let obj : obj_addr = SpecHeap.f_address h_addr;
  let hdr = read_word heap h_addr;
  let new_hdr = makeHeader (getWosize hdr) white (getTag hdr);
  write_word heap h_addr new_hdr;
  SpecHeap.hd_f_roundtrip h_addr;
  whiten_eq 's obj;
  ()
}
#pop-options

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1 --split_queries always --z3refresh"
fn sweep_black_spec (heap: heap_t) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (wz: wosize) (fp: U64.t)
  requires is_heap heap 's **
           pure (U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size /\
                 Seq.length 's == heap_size /\
                 SpecFields.well_formed_heap 's /\
                 Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr 's) /\
                 SpecObject.is_black (SpecHeap.f_address h_addr) 's /\
                 wz == SpecObject.getWosize (SpecHeap.read_word 's h_addr) /\
                 ~(SpecObject.is_white (SpecHeap.f_address h_addr) 's))
  returns new_fp: U64.t
  ensures exists* s2. is_heap heap s2 **
           pure (SpecFields.well_formed_heap s2 /\
                 SpecFields.objects zero_addr s2 == SpecFields.objects zero_addr 's /\
                 SI.headers_preserved_from
                   (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8))
                   s2 's /\
                 SI.headers_preserved_before (U64.v h_addr) s2 's /\
                 SpecObject.is_white (SpecHeap.f_address h_addr) s2 /\
                 SpecObject.getWosize (SpecHeap.read_word s2 h_addr) ==
                 SpecObject.getWosize (SpecHeap.read_word 's h_addr) /\
                 s2 == fst (SpecSweep.sweep_object 's (SpecHeap.f_address h_addr) fp) /\
                 new_fp == snd (SpecSweep.sweep_object 's (SpecHeap.f_address h_addr) fp))
{
  // Write the white header (no spec_read_word in its signature)
  sweep_write_white_hdr heap h_addr wz;
  with s2. assert (is_heap heap s2);
  let obj = SpecHeap.f_address h_addr;
  // Bridge makeWhite to set_object_color for downstream lemmas
  SpecObject.makeWhite_eq obj 's;
  sweep_black_preserves_spec 's h_addr;
  sweep_black_whiteness_spec 's h_addr;
  sweep_object_black_eq_spec 's h_addr fp;
  makeWhite_preserves_getWosize 's h_addr;
  makeWhite_headers_preserved_from
    (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8))
    's h_addr;
  makeWhite_headers_preserved_before_spec 's h_addr;
  // Explicit equality: connect existential witness s2 to lemma conclusions
  assert (pure (s2 == SpecObject.makeWhite obj 's));
  // Assert postcondition conjuncts for E-matching
  assert (pure (SpecFields.well_formed_heap s2));
  assert (pure (SpecFields.objects zero_addr s2 == SpecFields.objects zero_addr 's));
  assert (pure (SI.headers_preserved_from
    (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8)) s2 's));
  assert (pure (SI.headers_preserved_before (U64.v h_addr) s2 's));
  assert (pure (SpecObject.is_white (SpecHeap.f_address h_addr) s2));
  assert (pure (SpecObject.getWosize (SpecHeap.read_word s2 h_addr) ==
    SpecObject.getWosize (SpecHeap.read_word 's h_addr)));
  assert (pure (s2 == fst (SpecSweep.sweep_object 's (SpecHeap.f_address h_addr) fp)));
  assert (pure (fp == snd (SpecSweep.sweep_object 's (SpecHeap.f_address h_addr) fp)));
  fp
}
#pop-options
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always"
fn sweep_white_case (heap: heap_t) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (wz: wosize) (fp: U64.t)
  requires is_heap heap 's **
           pure (U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size /\
                 SpecFields.well_formed_heap 's /\
                 SI.obj_in_objects (SpecHeap.f_address h_addr) 's /\
                 wz == SpecObject.getWosize (SpecHeap.read_word 's h_addr) /\
                 SpecObject.is_white (SpecHeap.f_address h_addr) 's /\
                 SI.fp_valid fp 's)
  returns new_fp: U64.t
  ensures exists* s2. is_heap heap s2 **
           pure (SI.sweep_post 's s2 new_fp /\
                 SI.headers_preserved_from
                   (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8))
                   s2 's /\
                 (SpecObject.is_white (SpecHeap.f_address h_addr) s2 \/ SpecObject.is_blue (SpecHeap.f_address h_addr) s2) /\
                 SI.headers_preserved_before (U64.v h_addr) s2 's /\
                 SpecObject.getWosize (SpecHeap.read_word s2 h_addr) ==
                 SpecObject.getWosize (SpecHeap.read_word 's h_addr) /\
                 s2 == fst (SpecSweep.sweep_object 's (SpecHeap.f_address h_addr) fp) /\
                 new_fp == snd (SpecSweep.sweep_object 's (SpecHeap.f_address h_addr) fp))
{
  let r = sweep_white_spec heap h_addr wz fp;
  with s2. assert (is_heap heap s2);
  obj_in_objects_transfer_bridge (SpecHeap.f_address h_addr) 's s2;
  SI.fp_valid_from_obj (SpecHeap.f_address h_addr) s2;
  sweep_post_intro_bridge 's s2 r;
  r
}
#pop-options

/// Helper: handle black case only 
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1 --split_queries always --z3refresh"
fn sweep_black_case (heap: heap_t) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (wz: wosize) (fp: U64.t)
  requires is_heap heap 's **
           pure (U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size /\
                 SpecFields.well_formed_heap 's /\
                 SI.obj_in_objects (SpecHeap.f_address h_addr) 's /\
                 wz == SpecObject.getWosize (SpecHeap.read_word 's h_addr) /\
                 SpecObject.is_black (SpecHeap.f_address h_addr) 's /\
                 ~(SpecObject.is_white (SpecHeap.f_address h_addr) 's) /\
                 SI.fp_valid fp 's)
  returns new_fp: U64.t
  ensures exists* s2. is_heap heap s2 **
           pure (SI.sweep_post 's s2 new_fp /\
                 SI.headers_preserved_from
                   (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8))
                   s2 's /\
                 SpecObject.is_white (SpecHeap.f_address h_addr) s2 /\
                 SI.headers_preserved_before (U64.v h_addr) s2 's /\
                 SpecObject.getWosize (SpecHeap.read_word s2 h_addr) ==
                 SpecObject.getWosize (SpecHeap.read_word 's h_addr) /\
                 s2 == fst (SpecSweep.sweep_object 's (SpecHeap.f_address h_addr) fp) /\
                 new_fp == snd (SpecSweep.sweep_object 's (SpecHeap.f_address h_addr) fp))
{
  is_heap_length heap;
  SI.obj_in_objects_elim (SpecHeap.f_address h_addr) 's;
  let _ = sweep_black_spec heap h_addr wz fp;
  with s2. assert (is_heap heap s2);
  fp_valid_transfer_bridge fp 's s2;
  sweep_post_intro_bridge 's s2 fp;
  assert (pure (s2 == fst (SpecSweep.sweep_object 's (SpecHeap.f_address h_addr) fp)));
  fp
}
#pop-options

/// Sweep one object: dispatch by color
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always"
fn sweep_object (heap: heap_t) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (wz: wosize) (fp: U64.t)
  requires is_heap heap 's **
           pure (U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size /\
                 SpecFields.well_formed_heap 's /\
                 SI.obj_in_objects (SpecHeap.f_address h_addr) 's /\
                 wz == SpecObject.getWosize (SpecHeap.read_word 's h_addr) /\
                 ~(SpecObject.is_gray (SpecHeap.f_address h_addr) 's) /\
                 SI.fp_valid fp 's)
  returns new_fp: U64.t
  ensures exists* s2. is_heap heap s2 **
           pure (SI.sweep_post 's s2 new_fp /\
                 SI.headers_preserved_from
                   (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8))
                   s2 's /\
                 (SpecObject.is_white (SpecHeap.f_address h_addr) s2 \/ SpecObject.is_blue (SpecHeap.f_address h_addr) s2) /\
                 SI.headers_preserved_before (U64.v h_addr) s2 's /\
                 SpecObject.getWosize (SpecHeap.read_word s2 h_addr) ==
                 SpecObject.getWosize (SpecHeap.read_word 's h_addr) /\
                 s2 == fst (SpecSweep.sweep_object 's (SpecHeap.f_address h_addr) fp) /\
                 new_fp == snd (SpecSweep.sweep_object 's (SpecHeap.f_address h_addr) fp))
{
  is_heap_length heap;
  
  let hdr = read_word heap h_addr;
  
  spec_read_word_eq 's h_addr;
  getWosize_eq hdr;
  let color = getColor hdr;
  getColor_eq hdr;
  
  if (color = white) {
    is_white_from_color h_addr 's;
    sweep_white_case heap h_addr wz fp
  } else if (color = black) {
    is_not_white_from_color h_addr 's;
    is_black_from_color h_addr 's;
    sweep_black_case heap h_addr wz fp
  } else {
    SI.obj_in_objects_elim (SpecHeap.f_address h_addr) 's;
    is_not_white_from_color h_addr 's;
    is_not_black_from_color h_addr 's;
    sweep_object_else_bridge h_addr 's fp;
    sweep_post_intro_bridge 's 's fp;
    SI.headers_preserved_from_refl
      (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8)) 's;
    SI.headers_preserved_before_refl (U64.v h_addr) 's;
    fp
  }
}
#pop-options
#push-options "--z3rlimit 50 --split_queries always"
fn next_object (h_addr: hp_addr) (wz: wosize)
  requires pure (U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size)
  returns addr: U64.t
  ensures pure (U64.v addr % 8 == 0 /\
                U64.v addr == U64.v h_addr + (1 + U64.v wz) * 8)
{
  lemma_object_size_no_overflow (U64.v wz);
  lemma_next_addr_no_overflow (U64.v h_addr) (U64.v wz);
  lemma_next_addr_aligned (U64.v h_addr) (U64.v wz);
  let skip = U64.add 1UL wz;
  let offset = U64.mul skip mword;
  U64.add h_addr offset
}
#pop-options

/// ---------------------------------------------------------------------------
/// Main Sweep Loop
/// ---------------------------------------------------------------------------

/// Read the object header and extract wosize, establishing spec-level connection.
/// Factored out to isolate spec_read_word_eq from sweep_loop_body's combined VC.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1 --split_queries always --z3refresh"
fn sweep_read_wz (heap: heap_t) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size})
  requires is_heap heap 's **
           pure (Seq.length 's == heap_size /\
                 U64.v h_addr + 8 < heap_size)
  returns wz: wosize
  ensures is_heap heap 's **
          pure (wz == SpecObject.getWosize (SpecHeap.read_word 's h_addr))
{
  let hdr = read_word heap h_addr;
  let wz = getWosize hdr;
  spec_read_word_eq 's h_addr;
  getWosize_eq hdr;
  wz
}
#pop-options

/// Loop body: dispatch sweep_object, advance, maintain invariants
/// No spec_read_word in this fn — wosize comes from sweep_read_wz
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1 --z3refresh --split_queries always"
fn sweep_loop_body (heap: heap_t) (current: ref U64.t) (free_ptr: ref U64.t) (g_init: Ghost.erased heap_state)
  requires pts_to current 'v0 ** pts_to free_ptr 'fv0 ** is_heap heap 's **
           with_pure (U64.v 'v0 % 8 == 0 /\
                 U64.v 'v0 + U64.v mword < heap_size /\
                 U64.v 'v0 + 8 < pow2 64 /\
                 SpecFields.well_formed_heap 's /\
                 SpecFields.well_formed_heap g_init /\
                 SI.heap_objects_dense g_init /\
                 SI.no_gray_objects g_init /\
                 SpecFields.objects zero_addr 's == SpecFields.objects zero_addr g_init /\
                 SI.fp_valid 'fv0 's /\
                 SI.headers_preserved_from (U64.v 'v0) 's g_init /\
                 SI.objects_white_before (U64.v 'v0) 's /\
                 SI.obj_in_objects (SpecHeap.f_address 'v0) 's /\
                 Seq.length (SpecFields.objects (U64.uint_to_t (U64.v 'v0)) 's) > 0)
  ensures  exists* v1 fv1 s1.
             pts_to current v1 ** pts_to free_ptr fv1 ** is_heap heap s1 **
             pure (U64.v v1 % 8 == 0 /\
                   U64.v v1 <= heap_size /\
                   U64.v v1 + 8 < pow2 64 /\
                   SpecFields.well_formed_heap s1 /\
                   SpecFields.well_formed_heap g_init /\
                   SI.heap_objects_dense g_init /\
                   SI.no_gray_objects g_init /\
                   SpecFields.objects zero_addr s1 == SpecFields.objects zero_addr g_init /\
                   SI.fp_valid fv1 s1 /\
                   SI.headers_preserved_from (U64.v v1) s1 g_init /\
                   SI.objects_white_before (U64.v v1) s1 /\
                   (U64.v v1 + 8 < heap_size ==>
                     SI.obj_in_objects (SpecHeap.f_address v1) s1 /\
                     Seq.length (SpecFields.objects (U64.uint_to_t (U64.v v1)) s1) > 0) /\
                   (U64.v v1 < heap_size ==>
                     SpecSweep.sweep_aux s1 (SpecFields.objects (U64.uint_to_t (U64.v v1)) s1) fv1 ==
                     SpecSweep.sweep_aux 's (SpecFields.objects (U64.uint_to_t (U64.v 'v0)) 's) 'fv0) /\ //you need assumptions on 'v0 here
                   (U64.v v1 >= heap_size ==>
                     (s1, fv1) == SpecSweep.sweep_aux 's (SpecFields.objects (U64.uint_to_t (U64.v 'v0)) 's) 'fv0) /\
                  True  )
{ 
  let h_addr_raw = !current;
  let h_addr : (a:hp_addr{U64.v a + U64.v mword < heap_size}) = h_addr_raw;
  
  with s_cur. assert (is_heap heap s_cur);
  is_heap_length heap;
  
  let wz = sweep_read_wz heap h_addr;
  
  ML.lemma_mod_plus_distr_l (U64.v h_addr) 8 8;
  SpecFields.objects_nonempty_head_fits h_addr s_cur;
  // Derive ~(is_gray) for current object from no_gray_objects on initial heap
  SI.headers_preserved_from_elim (U64.v h_addr) h_addr s_cur g_init;
  SpecHeap.hd_f_roundtrip h_addr;
  // Establish preconditions for no_gray_at_preserved explicitly
  assert (pure (SpecHeap.hd_address (SpecHeap.f_address h_addr) == h_addr));
  assert (pure (SpecHeap.read_word s_cur h_addr == SpecHeap.read_word g_init h_addr));
  assert (pure (SpecHeap.read_word s_cur (SpecHeap.hd_address (SpecHeap.f_address h_addr)) ==
                SpecHeap.read_word g_init (SpecHeap.hd_address (SpecHeap.f_address h_addr))));
  // Also need obj membership in g_init's objects
  // Bridge: f_address h_addr == uint_to_t (U64.v 'v0 + 8) from precondition
  assert (pure (SI.obj_in_objects (SpecHeap.f_address h_addr) s_cur));
  SI.obj_in_objects_elim (SpecHeap.f_address h_addr) s_cur;
  assert (pure (Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr g_init)));
  SI.no_gray_at_preserved (SpecHeap.f_address h_addr) g_init s_cur;
  assert (pure (~(SpecObject.is_gray (SpecHeap.f_address h_addr) s_cur)));
  
  let cur_fp = !free_ptr;
  let new_fp = sweep_object heap h_addr wz cur_fp;
  free_ptr := new_fp;
  let next_addr = next_object h_addr wz;
  current := next_addr;
  
  with s_post. assert (is_heap heap s_post);
  // Key equality: connect existential witness to sweep_object result
  assert (pure (s_post == fst (SpecSweep.sweep_object s_cur (SpecHeap.f_address h_addr) cur_fp)));
  assert (pure (new_fp == snd (SpecSweep.sweep_object s_cur (SpecHeap.f_address h_addr) cur_fp)));
  is_heap_length heap;
  SI.sweep_post_elim_wfh s_cur s_post new_fp;
  sweep_post_elim_objects_bridge s_cur s_post new_fp;
  assert (pure (SpecFields.objects zero_addr s_post == SpecFields.objects zero_addr g_init));
  SI.sweep_post_elim_fp s_cur s_post new_fp;
  fp_valid_transfer_bridge new_fp s_post s_post;
  lemma_addr_plus_8_no_overflow (U64.v next_addr);
  assert (pure (U64.v next_addr <= heap_size));
  assert (pure (U64.v next_addr == U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8)));
  // Maintain objects_white_before
  SI.objects_white_before_step h_addr s_cur s_post;
  // Combined bridge: headers chain + density → all next-iteration facts
  sweep_loop_next_spec h_addr wz s_cur s_post g_init new_fp;
  // Sweep_aux tracking
  SpecSweep.sweep_aux_objects_step h_addr s_cur cur_fp;
  // Assert ALL postcondition conjuncts explicitly for E-matching
  assert (pure (U64.v next_addr % 8 == 0));
  assert (pure (U64.v next_addr <= heap_size));
  assert (pure (U64.v next_addr + 8 < pow2 64));
  assert (pure (SpecFields.well_formed_heap s_post));
  assert (pure (SpecFields.well_formed_heap g_init));
  assert (pure (SI.heap_objects_dense g_init));
  assert (pure (SI.no_gray_objects g_init));
  assert (pure (SpecFields.objects zero_addr s_post == SpecFields.objects zero_addr g_init));
  assert (pure (SI.fp_valid new_fp s_post));
  assert (pure (SI.headers_preserved_from (U64.v next_addr) s_post g_init));
  assert (pure (SI.objects_white_before (U64.v next_addr) s_post));
  assert (pure (U64.v next_addr + 8 < heap_size ==>
    SI.obj_in_objects (SpecHeap.f_address next_addr) s_post /\
    Seq.length (SpecFields.objects (U64.uint_to_t (U64.v next_addr)) s_post) > 0));
  assert (pure (U64.v next_addr < heap_size ==>
    SpecSweep.sweep_aux s_post (SpecFields.objects (U64.uint_to_t (U64.v next_addr)) s_post) new_fp ==
    SpecSweep.sweep_aux 's (SpecFields.objects (U64.uint_to_t (U64.v 'v0)) 's) 'fv0));
  assert (pure (U64.v next_addr >= heap_size ==>
    (s_post, new_fp) == SpecSweep.sweep_aux 's (SpecFields.objects (U64.uint_to_t (U64.v 'v0)) 's) 'fv0));
  ()
}
#pop-options

/// Inner sweep loop
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1 --z3refresh --split_queries always"
fn sweep_loop (heap: heap_t) (current: ref U64.t) (free_ptr: ref U64.t)
  requires pts_to current 'v0 ** pts_to free_ptr 'fv0 ** is_heap heap 's **
           pure (U64.v 'v0 % 8 == 0 /\
                 U64.v 'v0 <= heap_size /\
                 U64.v 'v0 + 8 < pow2 64 /\
                 SpecFields.well_formed_heap 's /\
                 SI.heap_objects_dense 's /\
                 SI.fp_valid 'fv0 's /\
                 SI.headers_preserved_from (U64.v 'v0) 's 's /\
                 SI.no_gray_objects 's /\
                 SI.objects_white_before (U64.v 'v0) 's /\
                 (U64.v 'v0 + 8 < heap_size ==>
                   SI.obj_in_objects (SpecHeap.f_address 'v0) 's /\
                   Seq.length (SpecFields.objects (U64.uint_to_t (U64.v 'v0)) 's) > 0) /\
                 (U64.v 'v0 < heap_size ==>
                   SpecSweep.sweep_aux 's (SpecFields.objects (U64.uint_to_t (U64.v 'v0)) 's) 'fv0 ==
                   SpecSweep.sweep 's 'fv0) /\
                 (U64.v 'v0 >= heap_size ==>
                   (reveal 's, reveal 'fv0) == SpecSweep.sweep 's 'fv0))
  ensures  exists* vf fvf sf.
             pts_to current vf ** pts_to free_ptr fvf ** is_heap heap sf **
             pure (SpecFields.well_formed_heap sf /\
                   (forall (x: obj_addr). Seq.mem x (SpecFields.objects zero_addr sf) ==>
                     (SpecObject.is_white x sf \/ SpecObject.is_blue x sf)) /\
                   (sf, fvf) == SpecSweep.sweep 's 'fv0)
{
  while (U64.lt (U64.add !current mword) heap_size_u64)
    invariant exists* v fv s.
      pts_to current v **
      pts_to free_ptr fv **
      is_heap heap s **
      pure (U64.v v % 8 == 0 /\
            U64.v v <= heap_size /\
            U64.v v + 8 < pow2 64 /\
            SpecFields.well_formed_heap s /\
            SpecFields.well_formed_heap 's /\
            SI.heap_objects_dense 's /\
            SI.no_gray_objects 's /\
            SpecFields.objects zero_addr s == SpecFields.objects zero_addr 's /\
            SI.fp_valid fv s /\
            SI.headers_preserved_from (U64.v v) s 's /\
            SI.objects_white_before (U64.v v) s /\
            (U64.v v + 8 < heap_size ==>
              SI.obj_in_objects (SpecHeap.f_address v) s /\
              Seq.length (SpecFields.objects (U64.uint_to_t (U64.v v)) s) > 0) /\
            (U64.v v < heap_size ==>
              SpecSweep.sweep_aux s (SpecFields.objects (U64.uint_to_t (U64.v v)) s) fv == SpecSweep.sweep 's 'fv0) /\
            (U64.v v >= heap_size ==> (s, fv) == SpecSweep.sweep 's 'fv0))
  {
    sweep_loop_body heap current free_ptr 's;
  };
  // After loop: v + 8 >= heap_size and objects_white_before (U64.v v) s
  // Derive all objects are white
  with v_exit. assert (pts_to current v_exit);
  with fv_exit. assert (pts_to free_ptr fv_exit);
  with s_exit. assert (is_heap heap s_exit);
  SI.objects_white_before_exit (U64.v v_exit) s_exit;
  // Sweep_aux termination: objects returns empty when v + 8 >= heap_size
  SpecSweep.sweep_aux_empty s_exit fv_exit;
  ()
}
#pop-options

/// Sweep all objects in heap, building free list
/// fp: initial free pointer (0UL for null/empty free list)
/// Precondition: well_formed_heap ensures each object fits in heap
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always --z3refresh"
fn sweep (heap: heap_t) (fp: U64.t)
  requires is_heap heap 's ** pure (SpecFields.well_formed_heap 's /\
                                    Seq.length (SpecFields.objects zero_addr 's) > 0 /\
                                    SI.heap_objects_dense 's /\
                                    SI.fp_valid fp 's /\
                                    SI.no_gray_objects 's)
  returns final_fp: U64.t
  ensures  exists* s2. is_heap heap s2 **
    pure (SpecFields.well_formed_heap s2 /\
          (forall (x: obj_addr). Seq.mem x (SpecFields.objects zero_addr s2) ==>
            (SpecObject.is_white x s2 \/ SpecObject.is_blue x s2)) /\
          (s2, final_fp) == SpecSweep.sweep 's fp)
{
  is_heap_length heap;
  // Establish initial obj_in_objects for head object
  obj_in_objects_head_bridge 's;
  // 0 + 8 < pow2 64 for initial invariant
  lemma_addr_plus_8_no_overflow 0;
  // Initial headers_preserved_from: reflexivity
  SI.headers_preserved_from_refl (U64.v zero_addr) 's;
  // Initial objects_white_before: vacuously true at position 0
  SI.objects_white_before_zero 's;
  let cur_init : U64.t = zero_addr;
  let mut current = cur_init;
  let mut free_ptr = fp;
  // Bridge: f_address zero_addr == uint_to_t 8 == f_address cur_init
  SpecHeap.f_address_spec cur_init;
  assert (pure (SpecHeap.f_address cur_init == U64.uint_to_t 8));
  assert (pure (U64.v cur_init + 8 < heap_size ==>
    SI.obj_in_objects (SpecHeap.f_address cur_init) 's));
  // Establish sweep_aux initial condition: sweep g fp = sweep_aux g (objects 0UL g) fp
  // and cur_init = zero_addr = 0UL, so objects (uint_to_t (v cur_init)) 's = objects 0UL 's
  assert (pure (U64.v cur_init < heap_size ==>
    SpecSweep.sweep_aux 's (SpecFields.objects (U64.uint_to_t (U64.v cur_init)) 's) fp ==
    SpecSweep.sweep 's fp));
  assert (pure (U64.v cur_init >= heap_size ==>
    (reveal 's, fp) == SpecSweep.sweep 's fp));
  sweep_loop heap current free_ptr;
  
  let result = !free_ptr;
  result
}
#pop-options
