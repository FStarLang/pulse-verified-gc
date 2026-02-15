(*
   Pulse GC - Sweep Phase for Parallel GC

   Stop-the-world sweep phase:
   1. Iterate all objects in the heap
   2. White objects: garbage (skip or reclaim)
   3. Black objects: reset to white for next GC cycle
   4. Gray/blue objects: should not exist after marking

   All functions preserve well_formed_heap.
   Uses types from common/Pulse.Lib.GC (Heap, Object).
*)

module Pulse.Lib.GC.Sweep

#lang-pulse

#set-options "--z3rlimit 50"

open FStar.Mul
open Pulse.Lib.Pervasives
open Pulse.Lib.GC.Heap
open Pulse.Lib.GC.Object
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module ML = FStar.Math.Lemmas
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
/// Overflow helpers
/// ---------------------------------------------------------------------------

/// Bridge: Pulse.Lib.GC.Object.getWosize == Pulse.Spec.GC.Object.getWosize
let getWosize_eq (hdr: U64.t) : Lemma (getWosize hdr == SpecObject.getWosize hdr) =
  SpecObject.getWosize_spec hdr;
  // Both are U64.shift_right hdr 10ul
  assert (getWosize hdr == U64.shift_right hdr 10ul)

let lemma_skip_no_overflow (wz: nat)
  : Lemma (requires wz <= pow2 54 - 1)
          (ensures (1 + wz) * 8 <= pow2 57 /\ (1 + wz) * 8 < pow2 64)
=
  assert (1 + wz <= pow2 54);
  ML.lemma_mult_le_right 8 (1 + wz) (pow2 54);
  assert ((1 + wz) * 8 <= pow2 54 * 8);
  Math.Lemmas.pow2_plus 54 3;
  assert (pow2 54 * pow2 3 == pow2 57);
  assert (pow2 54 * 8 == pow2 57);
  ML.pow2_lt_compat 64 57

let lemma_next_addr_no_overflow (h_addr: nat) (wz: nat)
  : Lemma (requires h_addr < heap_size /\ wz <= pow2 54 - 1)
          (ensures h_addr + (1 + wz) * 8 < pow2 64)
=
  lemma_skip_no_overflow wz;
  assert ((1 + wz) * 8 <= pow2 57);
  assert (h_addr < heap_size);
  assert (heap_size <= pow2 57);
  ML.pow2_lt_compat 64 58;
  Math.Lemmas.pow2_double_sum 57

/// ---------------------------------------------------------------------------
/// Bridge: connect Pulse whiten write to spec makeWhite
/// ---------------------------------------------------------------------------

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
/// Sweep one object: preserves well_formed_heap
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 150"
fn sweep_object
  (heap: heap_t) (obj: obj_addr)
  requires is_heap heap 's **
           pure (U64.v obj < heap_size /\
                 SpecFields.well_formed_heap 's /\
                 Seq.length 's == heap_size /\
                 Seq.mem obj (SpecFields.objects 0UL 's) /\
                 contiguous_heap 's)
  ensures exists* s2. is_heap heap s2 **
           pure (SpecFields.well_formed_heap s2 /\
                 objects_preserved s2 's /\
                 contiguous_heap s2)
{
  is_heap_length heap;
  let h_addr : hp_addr = SpecHeap.hd_address obj;
  SpecHeap.hd_address_bounds obj;
  hp_addr_plus_8 h_addr;
  let hdr = read_word heap h_addr;
  let c = getColor hdr;
  if (c = black) {
    // Black -> live object: reset to white for next cycle
    let new_hdr = SpecObject.colorHeader hdr white;
    write_word heap h_addr new_hdr;
    // Bridge to makeWhite
    spec_read_word_eq 's h_addr;
    whiten_bridge 's obj;
    rewrite (is_heap heap (spec_write_word 's (U64.v h_addr) new_hdr))
         as (is_heap heap (SpecObject.makeWhite obj 's));
    objects_preserved_makeWhite 's obj;
    contiguous_heap_preserved_makeWhite 's obj;
    ()
  } else {
    // White -> garbage, Gray/Blue -> shouldn't exist after marking
    // No heap change: objects trivially preserved
    ()
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// Sweep all objects: preserves well_formed_heap
/// ---------------------------------------------------------------------------

/// Linear scan of all objects in the heap.
#push-options "--z3rlimit 500"
fn sweep_all
  (heap: heap_t) (heap_len: U64.t{U64.v heap_len == heap_size})
  requires is_heap heap 's **
           pure (SpecFields.well_formed_heap 's /\
                 Seq.length (SpecFields.objects 0UL 's) > 0 /\
                 contiguous_heap 's)
  ensures exists* s2. is_heap heap s2 **
           pure (SpecFields.well_formed_heap s2)
{
  // Establish initial membership: head of objects(0, g) is obj_address(0)
  cursor_mem_init 's;

  let mut cursor = 0UL;
  while (U64.lt (U64.add !cursor 8UL) heap_len)
    invariant exists* c s_i.
      pts_to cursor c **
      is_heap heap s_i **
      pure (U64.v c <= U64.v heap_len /\
            U64.v c % 8 == 0 /\
            U64.v c + 8 < pow2 64 /\
            SpecFields.well_formed_heap s_i /\
            Seq.length s_i == heap_size /\
            objects_preserved s_i 's /\
            contiguous_heap s_i /\
            cursor_mem c s_i)
  {
    let c = !cursor;
    let h_addr : hp_addr = c;
    hp_addr_plus_8 h_addr;
    is_heap_length heap;

    // Compute obj_addr from cursor: obj = cursor + 8
    // cursor_mem gives us Seq.mem (obj_address c) (objects 0UL s_i)
    // since loop condition ensures c + 8 < heap_size, and c < heap_size, c % 8 == 0
    let obj : obj_addr = U64.add c 8UL;
    // obj == obj_address c (U64.add vs U64.add_mod, both h_addr+8 < pow2 64)
    U64.v_inj obj (SpecFields.obj_address c);

    let hdr = read_word heap h_addr;
    let wz = getWosize hdr;

    // Compute cursor advancement BEFORE sweep (using current ghost s_i)
    // Bridge wz: Pulse getWosize == Spec getWosize, hdr == read_word s_i c
    with s_i. assert (is_heap heap s_i);
    spec_read_word_eq s_i c;
    getWosize_eq hdr;
    cursor_mem_advance s_i c;
    lemma_next_addr_no_overflow (U64.v c) (U64.v wz);

    // Sweep this object
    sweep_object heap obj;
    with s_after. assert (is_heap heap s_after);

    // Advance cursor
    let obj_words = U64.add wz 1UL;
    let byte_size = U64.mul obj_words 8UL;
    let new_cursor = U64.add c byte_size;

    // Transfer cursor_mem from s_i to s_after via objects_preserved
    cursor_mem_from_objects_preserved s_after s_i new_cursor;
    cursor := new_cursor;
    ()
  }
}
#pop-options
