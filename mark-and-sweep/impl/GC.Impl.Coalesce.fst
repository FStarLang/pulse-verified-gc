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
module SI = GC.Spec.SweepInv
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

/// Spec-related invariant predicate.
/// Uses if/then/else guards (not ==>) so F*'s typechecker propagates guards
/// into branches, ensuring `objects` (which requires hp_addr) is well-typed.
noextract unfold
let coalesce_spec_inv (g0: heap_state) (g: heap_state)
  (v_nat: nat) (fb: U64.t) (rw_nat: nat) (fv: U64.t) : prop =
  if v_nat < heap_size && v_nat % 8 = 0 then
    let start : hp_addr = U64.uint_to_t v_nat in
    let objs = SpecFields.objects start g0 in
    (if v_nat + U64.v mword < heap_size then
      Seq.length objs > 0 /\
      SI.obj_in_objects (U64.uint_to_t (v_nat + U64.v mword)) g0
    else True) /\
    SpecCoalesce.coalesce_aux g0 g objs fb rw_nat fv == SpecCoalesce.coalesce g0
  else
    SpecCoalesce.coalesce_aux g0 g Seq.empty fb rw_nat fv == SpecCoalesce.coalesce g0

/// The main coalesce entry point
#push-options "--z3rlimit 800 --fuel 2 --ifuel 1 --z3refresh"
fn coalesce (heap: heap_t)
  requires is_heap heap 's **
           pure (SpecCoalesce.post_sweep_strong 's /\
                 Seq.length (SpecFields.objects zero_addr 's) > 0 /\
                 SI.heap_objects_dense 's)
  returns new_fp: U64.t
  ensures exists* s2. is_heap heap s2 **
    pure (SpecFields.well_formed_heap s2 /\
          (forall (x: obj_addr). Seq.mem x (SpecFields.objects zero_addr s2) ==>
            (SpecObject.is_white x s2 \/ SpecObject.is_blue x s2)) /\
          (s2, new_fp) == SpecCoalesce.coalesce 's)
{
  coalesce_heap_length heap;
  coalesce_unfold 's;
  // Pre-loop: establish initial objects walk facts
  objects_mem_at_zero 's;
  SI.obj_in_objects_intro (SpecHeap.f_address zero_addr) 's;
  SpecHeap.f_address_spec zero_addr;

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
            // Spec equivalence and walk validity (guarded for well-typedness)
            coalesce_spec_inv 's s (U64.v v) fb (U64.v rw) fv)
  {
    let cur = !current;
    let cur_fb = !fb_ref;
    let cur_rw = !rw_ref;
    let cur_fv = !fp_ref;
    with s. assert (is_heap heap s);

    // Read header from current heap
    let hdr = read_word heap cur;
    let wz = getWosize hdr;
    let obj : obj_addr = SpecHeap.f_address cur;

    // Bridge: suffix preservation → reading from s == reading from 's
    is_blue_from_original 's s obj cur;

    // Bridge impl getWosize to spec getWosize
    GC.Impl.Object.getWosize_eq hdr;

    // Advance computation (using original heap)
    objects_advance cur 's;
    let ws_plus_1 = U64.add wz 1UL;
    lemma_object_size_no_overflow (U64.v wz);
    let offset = U64.mul ws_plus_1 mword;
    lemma_address_add_no_overflow (U64.v cur) (U64.v offset);
    let next = U64.add cur offset;

    // Convert obj_in_objects → Seq.mem (f_address cur) for density lemmas
    SI.obj_in_objects_elim (U64.uint_to_t (U64.v cur + U64.v mword)) 's;
    SpecHeap.f_address_spec cur;

    // Propagate objects density for next iteration
    SI.objects_dense_step cur 's;
    SI.objects_dense_obj_in cur 's;

    // Bridge impl getColor to spec getColor
    GC.Impl.Object.getColor_eq hdr;

    // Check if blue
    let clr = getColor hdr;
    if Header.Blue? clr {
      // Blue case: accumulate run (no writes to heap)
      let new_fb = (if U64.eq cur_rw 0UL then obj else cur_fb);
      let new_rw = U64.add cur_rw ws_plus_1;

      current := next;
      fb_ref := new_fb;
      rw_ref := new_rw;

      // Step lemma: unfold coalesce_aux one step for blue
      SpecHeap.hd_f_roundtrip cur;
      SpecObject.color_of_object_spec obj s;
      SpecObject.is_blue_iff obj s;

      // Bridge lemma: produces all facts needed for the new invariant
      blue_step_coalesce_aux_eq 's s cur
        cur_fb (U64.v cur_rw) cur_fv;

      // Arithmetic facts from bridge lemma
      assert (pure (U64.v next % 8 == 0));
      assert (pure (U64.v next <= heap_size));
      assert (pure (U64.v next + 8 < pow2 64));
      assert (pure (U64.v new_rw == U64.v cur_rw + U64.v wz + 1));
      assert (pure (U64.v new_rw > 0));
      assert (pure (U64.v new_rw < pow2 54));
      assert (pure (U64.v new_fb >= U64.v mword));
      assert (pure (U64.v new_fb < heap_size));
      assert (pure (U64.v new_fb % U64.v mword == 0));
      assert (pure (U64.v new_fb - U64.v mword + U64.v new_rw * U64.v mword == U64.v next));

      // Suffix preservation: next >= cur, so forall addr >= next follows from forall addr >= cur
      assert (pure (U64.v next >= U64.v cur));
      assert (pure (forall (addr: hp_addr). U64.v addr >= U64.v next ==>
        SpecHeap.read_word s addr == SpecHeap.read_word 's addr));

      // coalesce_spec_inv at next: assert the two cases from bridge lemma
      assert (pure (
        U64.v next < heap_size ==>
          SpecCoalesce.coalesce_aux 's s
            (SpecFields.objects (U64.uint_to_t (U64.v next)) 's)
            new_fb (U64.v new_rw) cur_fv == SpecCoalesce.coalesce 's));
      assert (pure (
        U64.v next >= heap_size ==>
          SpecCoalesce.coalesce_aux 's s Seq.empty
            new_fb (U64.v new_rw) cur_fv == SpecCoalesce.coalesce 's));
      ()
    } else {
      // White case: flush pending run, then advance
      let (new_rw, new_fv) = flush_blue_impl heap cur_fb cur_rw cur_fv;
      with s_post. assert (is_heap heap s_post);

      current := next;
      fb_ref := 0UL;
      rw_ref := new_rw;
      fp_ref := new_fv;

      // Bridge: connect impl getColor to spec is_blue for the not-blue precondition
      SpecHeap.hd_f_roundtrip cur;
      SpecObject.color_of_object_spec obj s;
      SpecObject.is_blue_iff obj s;

      // Bridge lemma: produces all facts needed for the new invariant
      white_step_coalesce_aux_eq 's s cur
        cur_fb (U64.v cur_rw) cur_fv;

      // Arithmetic facts from bridge lemma
      assert (pure (U64.v next % 8 == 0));
      assert (pure (U64.v next <= heap_size));
      assert (pure (U64.v next + 8 < pow2 64));

      // new_rw = 0UL from flush_blue_impl, so run geometry is trivially satisfied
      assert (pure (U64.v new_rw == 0));

      // Suffix preservation: chained through flush
      assert (pure (forall (addr: hp_addr). U64.v addr >= U64.v next ==>
        SpecHeap.read_word s_post addr == SpecHeap.read_word 's addr));

      // coalesce_spec_inv at next: assert the two cases from bridge lemma
      assert (pure (
        U64.v next < heap_size ==>
          SpecCoalesce.coalesce_aux 's s_post
            (SpecFields.objects (U64.uint_to_t (U64.v next)) 's)
            0UL (U64.v new_rw) new_fv == SpecCoalesce.coalesce 's));
      assert (pure (
        U64.v next >= heap_size ==>
          SpecCoalesce.coalesce_aux 's s_post Seq.empty
            0UL (U64.v new_rw) new_fv == SpecCoalesce.coalesce 's));
      ()
    }
  };

  // After loop: v + 8 >= heap_size, so objects v 's is empty (or else branch)
  // Either way: coalesce_aux 's s_exit Seq.empty fb rw fv == coalesce 's
  let final_fb = !fb_ref;
  let final_rw = !rw_ref;
  let final_fv = !fp_ref;
  with s_exit. assert (is_heap heap s_exit);

  // Bridge: coalesce_aux with Seq.empty = flush_blue
  coalesce_step_empty 's s_exit final_fb (U64.v final_rw) final_fv;

  let (_, result_fp) = flush_blue_impl heap final_fb final_rw final_fv;
  with s2. assert (is_heap heap s2);

  // Establish well_formed_heap and all-white-or-blue from spec lemmas
  SpecCoalesce.coalesce_preserves_wf 's;
  SpecCoalesce.coalesce_all_white_or_blue 's;
  result_fp
}
#pop-options
