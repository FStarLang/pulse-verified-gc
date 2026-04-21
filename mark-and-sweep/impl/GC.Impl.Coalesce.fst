(*
   Pulse GC - Coalesce Module

   Merges adjacent free (blue) objects into larger free blocks after sweep.
   Walks objects using header-address cursor, accumulating blue runs,
   and flushing merged blocks to the free list.
*)

module GC.Impl.Coalesce

#lang-pulse

#set-options "--z3rlimit 100 --split_queries always"
open FStar.Mul
open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
open GC.Impl.Fields
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module ML = FStar.Math.Lemmas
module SpecCoalesce = GC.Spec.Coalesce
module SpecFields = GC.Spec.Fields
module SpecHeap = GC.Spec.Heap
module SpecObject = GC.Spec.Object
module SpecHeapGraph = GC.Spec.HeapGraph
module Alloc = GC.Spec.Allocator
module Header = GC.Lib.Header
open GC.Impl.Coalesce.Lemmas

/// Extract the pure length fact from is_heap
ghost fn coalesce_heap_length (h: heap_t)
  requires is_heap h 's
  ensures is_heap h 's ** pure (Seq.length 's == heap_size)
{
  unfold is_heap;
  fold (is_heap h 's)
}

/// ---------------------------------------------------------------------------
/// flush_blue implementation
/// ---------------------------------------------------------------------------

/// Write the merged header for a blue run
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1 --z3refresh"
fn flush_blue_write_header (heap: heap_t) (fb: obj_addr) (rw: U64.t{U64.v rw >= 1 /\ U64.v rw < pow2 54})
  requires is_heap heap 's **
           pure (Seq.length 's == heap_size)
  ensures exists* s2. is_heap heap s2 **
           pure (Seq.length s2 == heap_size /\
                 (let hd = SpecHeap.hd_address fb in
                  let wz_u64 : SpecObject.wosize = U64.uint_to_t (U64.v rw - 1) in
                  let spec_hdr = SpecObject.makeHeader wz_u64 Header.Blue 0UL in
                  s2 == SpecHeap.write_word 's hd spec_hdr))
{
  let hd : hp_addr = U64.sub fb mword;
  SpecHeap.hd_address_spec fb;
  let wz = U64.sub rw 1UL;
  let hdr = makeHeader wz blue 0UL;
  makeHeader_bridge wz blue 0UL;
  write_word heap hd hdr
}
#pop-options

/// Write free list link to field 1 of merged block
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1 --z3refresh"
fn flush_blue_write_link (heap: heap_t) (fb: hp_addr) (fp: U64.t)
  requires is_heap heap 's **
           pure (Seq.length 's == heap_size /\
                 U64.v fb + U64.v mword <= heap_size)
  ensures exists* s2. is_heap heap s2 **
           pure (s2 == SpecHeap.write_word 's fb fp /\
                 Seq.length s2 == heap_size)
{
  write_word heap fb fp
}
#pop-options

/// Zero a range of fields starting at addr, n words
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1 --z3refresh"
fn zero_fields_loop (heap: heap_t) (start_addr: U64.t) (n: U64.t)
  requires is_heap heap 's **
           pure (Seq.length 's == heap_size /\
                 U64.v start_addr % U64.v mword == 0 /\
                 U64.v start_addr + U64.v n * U64.v mword <= heap_size)
  ensures exists* s2. is_heap heap s2 **
           pure (s2 == Alloc.zero_fields 's start_addr (U64.v n) /\
                 Seq.length s2 == heap_size)
{
  let mut idx = 0UL;
  let mut addr = start_addr;
  while (U64.lt !idx n)
    invariant exists* i a s.
      pts_to idx i **
      pts_to addr a **
      is_heap heap s **
      pure (U64.v i <= U64.v n /\
            U64.v a == U64.v start_addr + U64.v i * U64.v mword /\
            U64.v a % U64.v mword == 0 /\
            U64.v a + (U64.v n - U64.v i) * U64.v mword <= heap_size /\
            Seq.length s == heap_size /\
            Alloc.zero_fields s (U64.uint_to_t (U64.v a)) (U64.v n - U64.v i) ==
              Alloc.zero_fields 's start_addr (U64.v n))
  {
    let cur_a = !addr;
    let cur_i = !idx;
    with s_cur. assert (is_heap heap s_cur);
    // Unfold zero_fields one step
    zero_fields_step s_cur cur_a (U64.v n - U64.v cur_i);
    write_word heap cur_a 0UL;
    let next_a = U64.add cur_a mword;
    let next_i = U64.add cur_i 1UL;
    addr := next_a;
    idx := next_i;
    ()
  };
  ()
}
#pop-options

/// Full flush_blue implementation
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1 --z3refresh"
fn flush_blue_impl (heap: heap_t) (fb: U64.t) (rw: U64.t) (fp: U64.t)
  requires is_heap heap 's **
           pure (Seq.length 's == heap_size /\
                 (U64.v rw > 0 ==>
                   U64.v rw < pow2 54 /\
                   U64.v fb >= U64.v mword /\
                   U64.v fb < heap_size /\
                   U64.v fb % U64.v mword == 0 /\
                   U64.v fb - U64.v mword + U64.v rw * U64.v mword <= heap_size))
  returns res: (U64.t & U64.t)
  ensures exists* s2. is_heap heap s2 **
           pure ((s2, snd res) == SpecCoalesce.flush_blue 's fb (U64.v rw) fp /\
                 fst res == 0UL /\
                 Seq.length s2 == heap_size)
{
  if U64.eq rw 0UL {
    (0UL, fp)
  } else {
    // Write merged header
    SpecHeap.hd_address_spec fb;
    flush_blue_write_header heap fb rw;
    with s1. assert (is_heap heap s1);
    let wz = U64.sub rw 1UL;
    if U64.gt wz 0UL {
      // Write free list link to field 1
      flush_blue_write_link heap fb fp;
      with s2. assert (is_heap heap s2);
      if U64.gt wz 1UL {
        // Zero fields 2..wz
        let zero_start = U64.add fb mword;
        let n_zero = U64.sub wz 1UL;
        zero_fields_loop heap zero_start n_zero;
        with s3. assert (is_heap heap s3);
        flush_blue_impl_wz_ge2 's fb wz fp s1 s2 s3;
        (0UL, fb)
      } else {
        flush_blue_impl_wz1 's fb fp s1 s2;
        (0UL, fb)
      }
    } else {
      // wosize = 0: just header, no fields, don't link to free list
      flush_blue_impl_wz0 's fb fp s1;
      (0UL, fp)
    }
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// Main coalesce loop
/// ---------------------------------------------------------------------------

/// The main coalesce entry point
#push-options "--z3rlimit 400 --fuel 2 --ifuel 1 --z3refresh"
fn coalesce (heap: heap_t)
  requires is_heap heap 's **
           pure (SpecCoalesce.post_sweep_strong 's)
  returns new_fp: U64.t
  ensures exists* s2. is_heap heap s2 **
    pure (SpecFields.well_formed_heap s2 /\
          (forall (x: obj_addr). Seq.mem x (SpecFields.objects zero_addr s2) ==>
            (SpecObject.is_white x s2 \/ SpecObject.is_blue x s2)) /\
          (s2, new_fp) == SpecCoalesce.coalesce 's)
{
  coalesce_heap_length heap;
  coalesce_unfold 's;

  let mut current = (zero_addr <: U64.t);
  let mut fb_ref = 0UL;
  let mut rw_ref = 0UL;
  let mut fp_ref = 0UL;

  while (U64.lt (U64.add !current mword) heap_size_u64)
    invariant exists* v fb rw fv s.
      pts_to current v **
      pts_to fb_ref fb **
      pts_to rw_ref rw **
      pts_to fp_ref fv **
      is_heap heap s **
      pure (U64.v v % 8 == 0 /\
            U64.v v <= heap_size /\
            U64.v v + 8 < pow2 64 /\
            Seq.length s == heap_size /\
            // Suffix preservation
            (forall (addr: hp_addr). U64.v addr >= U64.v v ==>
              SpecHeap.read_word s addr == SpecHeap.read_word 's addr) /\
            // Run geometry
            (U64.v rw > 0 ==>
              U64.v rw < pow2 54 /\
              U64.v fb >= U64.v mword /\
              U64.v fb < heap_size /\
              U64.v fb % U64.v mword == 0 /\
              U64.v fb - U64.v mword + U64.v rw * U64.v mword == U64.v v) /\
            // Spec equivalence
            (U64.v v < heap_size ==>
              Seq.length (SpecFields.objects (U64.uint_to_t (U64.v v)) 's) > 0 /\
              SpecCoalesce.coalesce_aux 's s
                (SpecFields.objects (U64.uint_to_t (U64.v v)) 's)
                fb (U64.v rw) fv ==
              SpecCoalesce.coalesce 's) /\
            (U64.v v >= heap_size ==>
              SpecCoalesce.flush_blue s fb (U64.v rw) fv ==
              SpecCoalesce.coalesce 's))
  {
    let cur = !current;
    let cur_fb = !fb_ref;
    let cur_rw = !rw_ref;
    let cur_fv = !fp_ref;
    with s. assert (is_heap heap s);

    // Read header from current heap (= original by suffix preservation)
    let hdr = read_word heap cur;
    let wz = getWosize hdr;
    let obj : obj_addr = SpecHeap.f_address cur;

    // Establish that cur is a valid hp_addr for objects operations
    // Since cur + 8 < heap_size (loop guard), we can read header at cur
    objects_advance cur 's;
    let ws_plus_1 = U64.add wz 1UL;
    let offset = U64.mul ws_plus_1 mword;
    let next = U64.add cur offset;

    // Check if blue
    let clr = getColor hdr;
    if Header.Blue? clr {
      // Blue case: accumulate run
      let new_fb = (if U64.eq cur_rw 0UL then obj else cur_fb);
      let new_rw = U64.add cur_rw ws_plus_1;

      current := next;
      fb_ref := new_fb;
      rw_ref := new_rw;

      // Step lemma
      coalesce_step_blue 's s cur
        (SpecFields.objects (U64.uint_to_t (U64.v cur)) 's)
        cur_fb (U64.v cur_rw) cur_fv;
      // Need is_blue bridge
      is_blue_from_original 's s obj cur;
      admit()
    } else {
      // White case: flush pending run, then advance
      let (new_rw, new_fv) = flush_blue_impl heap cur_fb cur_rw cur_fv;
      with s_post. assert (is_heap heap s_post);

      current := next;
      fb_ref := 0UL;
      rw_ref := new_rw;
      fp_ref := new_fv;

      // Step lemma
      coalesce_step_white 's s cur
        (SpecFields.objects (U64.uint_to_t (U64.v cur)) 's)
        cur_fb (U64.v cur_rw) cur_fv;
      // Suffix preservation after flush
      flush_blue_suffix_preserved s cur_fb (U64.v cur_rw) cur_fv (U64.v cur);
      admit()
    }
  };

  // After loop: flush any trailing blue run
  let final_fb = !fb_ref;
  let final_rw = !rw_ref;
  let final_fv = !fp_ref;
  with s_exit. assert (is_heap heap s_exit);
  let (_, result_fp) = flush_blue_impl heap final_fb final_rw final_fv;
  coalesce_step_empty 's s_exit final_fb (U64.v final_rw) final_fv;
  with s2. assert (is_heap heap s2);
  // s2 == fst(flush_blue s_exit ...) and (s_exit, flush_blue ...) == coalesce 's
  // so (s2, result_fp) == coalesce 's

  // Establish well_formed_heap and all-white-or-blue from spec lemmas
  SpecCoalesce.coalesce_preserves_wf 's;
  SpecCoalesce.coalesce_all_white_or_blue 's;
  result_fp
}
#pop-options
