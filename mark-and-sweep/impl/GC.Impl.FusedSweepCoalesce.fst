(*
   Pulse GC - Fused Sweep+Coalesce Implementation

   A single-pass loop that combines sweep (blacken→white) and coalesce
   (merge adjacent free blocks) into one traversal. Replaces the two-pass
   sweep-then-coalesce approach.

   Follows the same loop structure as GC.Impl.Coalesce, but:
   - Checks colors against the *original* (frozen) heap g0, not the mutable heap
   - Black objects get flushed (pending blue run) then whitened
   - Non-black objects (white, blue) get accumulated into the blue run
   - The spec is Defs.fused_aux (from GC.Spec.SweepCoalesce.Defs)
*)

module GC.Impl.FusedSweepCoalesce

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
module U64 = FStar.UInt64
module Seq = FStar.Seq
module Defs = GC.Spec.SweepCoalesce.Defs
module SCL = GC.Spec.SweepCoalesce.Lists
module FLs = GC.Spec.FreeLists
module SC = GC.Spec.SizeClass
module SZ = FStar.SizeT
module SpecCoalesce = GC.Spec.Coalesce
module SpecFields = GC.Spec.Fields
module SpecObject = GC.Spec.Object
module SpecHeap = GC.Spec.Heap
module Header = GC.Lib.Header
module SI = GC.Spec.SweepInv
module FusedLemmas = GC.Impl.FusedSweepCoalesce.Lemmas
module CoalLemmas = GC.Impl.Coalesce.Lemmas
module Coalesce = GC.Impl.Coalesce
module R = Pulse.Lib.Reference
module OT = GC.Spec.ObjectTable
module TS = GC.Spec.ObjectTable.Sweep
module ImplOT = GC.Impl.ObjectTable

open GC.Impl.Fields

/// ---------------------------------------------------------------------------
/// Helper: expose heap length from is_heap
/// ---------------------------------------------------------------------------

ghost fn fused_heap_length (h: heap_t)
  requires is_heap h 's
  ensures is_heap h 's ** pure (Seq.length 's == heap_size)
{
  unfold is_heap;
  fold (is_heap h 's)
}

/// ---------------------------------------------------------------------------
/// Spec invariant for the fused loop
/// ---------------------------------------------------------------------------

/// Mirrors coalesce_spec_inv but for fused_aux / fused_sweep_coalesce
let fused_spec_inv (g0: heap_state) (g: heap_state)
  (v_nat: nat) (fb: U64.t) (rw_nat: nat) (fv: FLs.fl_state) : prop =
  if v_nat < heap_size && v_nat % 8 = 0 then
    let start : hp_addr = U64.uint_to_t v_nat in
    let objs = SpecFields.objects start g0 in
    (if v_nat + U64.v mword < heap_size then
      Seq.length objs > 0 /\
      SI.obj_in_objects (U64.uint_to_t (v_nat + U64.v mword)) g0
    else True) /\
    SCL.fused_aux_lists g0 g objs fb rw_nat fv == SCL.fused_sweep_coalesce_lists g0
  else
    SCL.fused_aux_lists g0 g Seq.empty fb rw_nat fv == SCL.fused_sweep_coalesce_lists g0

/// ---------------------------------------------------------------------------
/// Main entry point
/// ---------------------------------------------------------------------------

/// The list a run of `rw` words goes on (`GC.Spec.SweepCoalesce.Lists.run_class`).
inline_for_extraction
let run_class (rw: U64.t) : (c: SZ.t{SZ.v c == SCL.run_class (U64.v rw) /\ SZ.v c < SC.n_lists}) =
  SC.n_small_u64_v ();
  if U64.gte rw 2UL && U64.lte (U64.sub rw 1UL) SC.n_small_u64
  then begin
    SC.size_class_lt (U64.v rw - 1);
    FStar.SizeT.fits_at_least_16 (U64.v rw - 1);
    SZ.uint64_to_sizet (U64.sub rw 1UL)
  end
  else 0sz

/// Flush a pending run on the list of its class.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
fn flush_blue_lists_impl (heap: heap_t) (heads: array U64.t) (fb: U64.t) (rw: U64.t)
  requires is_heap heap 's ** pts_to heads 'fls **
           pure (Seq.length 's == heap_size /\
                 Seq.length 'fls == SC.n_lists /\
                 (U64.v rw > 0 ==>
                   U64.v rw < pow2 54 /\
                   U64.v fb >= U64.v mword /\
                   U64.v fb < heap_size /\
                   U64.v fb % U64.v mword == 0 /\
                   U64.v fb - U64.v mword + U64.v rw * U64.v mword <= heap_size))
  ensures exists* s2 fls2. is_heap heap s2 ** pts_to heads fls2 **
           pure ((s2, fls2) == SCL.flush_blue_lists 's fb (U64.v rw) 'fls /\
                 Seq.length s2 == heap_size /\
                 Seq.length fls2 == SC.n_lists)
{
  let c = run_class rw;
  let old = heads.(c);
  let res = Coalesce.flush_blue_impl heap fb rw old;
  heads.(c) <- snd res
}
#pop-options

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1 --z3refresh"
fn fused_sweep_coalesce (heap: heap_t) (heads: array U64.t) (tbl: array U64.t)
  requires is_heap heap 's ** pts_to heads 'fls ** pts_to tbl 't **
           pure (SpecFields.well_formed_heap 's /\
                 Seq.length (SpecFields.objects zero_addr 's) > 0 /\
                 GC.Spec.Fields.heap_objects_dense 's /\
                 (forall (x: obj_addr).
                   Seq.mem x (SpecFields.objects zero_addr 's) ==>
                   ~(SpecObject.is_gray x 's)) /\
                 Seq.length 'fls == SC.n_lists /\
                 Seq.length 't == OT.n_windows)
  ensures exists* s2 fls2 t2. is_heap heap s2 ** pts_to heads fls2 ** pts_to tbl t2 **
    pure ((s2, fls2) == SCL.fused_sweep_coalesce_lists 's /\
          OT.table_matches s2 t2)
{
  // Establish initial facts
  fused_heap_length heap;
  FusedLemmas.fused_unfold 's;
  CoalLemmas.objects_mem_at_zero 's;
  SI.obj_in_objects_intro (SpecHeap.f_address zero_addr) 's;
  SpecHeap.f_address_spec zero_addr;

  // Every list starts empty.
  GC.Impl.FreeLists.clear_heads heads;

  let mut current = (zero_addr <: U64.t);
  let mut fb_ref = 0UL;
  let mut rw_ref = 0UL;

  // The table cursor: the last output header, and the first window not yet
  // written with its boundary.
  let mut prev = (zero_addr <: U64.t);
  let mut k = 0UL;
  let mut nb = (zero_addr <: U64.t);
  OT.objs_from_zero 's;

  while (U64.lt (U64.add !current mword) heap_size_u64)
    invariant exists* v fb rw fv s tv vp vk vnb.
      pts_to current v **
      pts_to fb_ref fb **
      pts_to rw_ref rw **
      pts_to heads fv **
      is_heap heap s **
      pts_to tbl tv ** R.pts_to prev vp ** R.pts_to k vk ** R.pts_to nb vnb **
      pure (Seq.length tv == OT.n_windows /\ U64.v vk <= OT.n_windows /\
            U64.v vnb == OT.boundary (U64.v vk) /\
            OT.cursor (TS.out_emit 's (OT.objs_from 's (U64.v v)) (U64.v rw)) vp (U64.v vk) tv ==
              OT.cursor (TS.out_emit 's (SpecFields.objects zero_addr 's) 0) zero_addr 0 't) **
      pure (Seq.length fv == SC.n_lists /\
            U64.v v % 8 == 0 /\
            U64.v v <= heap_size /\
            U64.v v + 8 < pow2 64 /\
            Seq.length s == heap_size /\
            // Suffix preservation: unprocessed region matches original
            (forall (addr: hp_addr). U64.v addr >= U64.v v ==>
              SpecHeap.read_word s addr == SpecHeap.read_word 's addr) /\
            // Run geometry (same as coalesce)
            (U64.v rw > 0 ==>
              U64.v rw < pow2 54 /\
              U64.v fb >= U64.v mword /\
              U64.v fb < heap_size /\
              U64.v fb % U64.v mword == 0 /\
              U64.v fb - U64.v mword + op_Star (U64.v rw) (U64.v mword) == U64.v v) /\
            // Spec equivalence
            fused_spec_inv 's s (U64.v v) fb (U64.v rw) fv)
    decreases (heap_size - U64.v !current)
  {
    let cur = !current;
    let cur_fb = !fb_ref;
    let cur_rw = !rw_ref;
    with cur_fv. assert (pts_to heads cur_fv);
    with s. assert (is_heap heap s);
    let vprev = !prev;
    with tv. assert (pts_to tbl tv);
    with vk. assert (R.pts_to k vk);

    // Read header from current heap (same bytes as original via suffix preservation)
    let hdr = read_word heap cur;
    let wz = getWosize hdr;
    let obj : obj_addr = SpecHeap.f_address cur;

    // Bridge: suffix preservation → colors readable from current heap match original
    FusedLemmas.is_black_from_original 's s obj cur;

    // Bridge impl getWosize to spec getWosize
    GC.Impl.Object.getWosize_eq hdr;

    // Advance computation (using original heap for objects walk)
    CoalLemmas.objects_advance cur 's;
    let ws_plus_1 = U64.add wz 1UL;
    lemma_object_size_no_overflow (U64.v wz);
    let offset = U64.mul ws_plus_1 mword;
    lemma_address_add_no_overflow (U64.v cur) (U64.v offset);
    let next = U64.add cur offset;

    // Convert obj_in_objects → Seq.mem
    SI.obj_in_objects_elim (U64.uint_to_t (U64.v cur + U64.v mword)) 's;
    SpecHeap.f_address_spec cur;

    // Propagate objects density for next iteration
    SI.objects_dense_step cur 's;
    SI.objects_dense_obj_in cur 's;

    // Bridge impl getColor to spec getColor
    GC.Impl.Object.getColor_eq hdr;

    // Check if black in g0 (which equals black in g since suffix preserved)
    let clr = getColor hdr;
    if Header.Black? clr {
      // =====================================================
      // BLACK CASE: flush pending blue run, then whiten
      // =====================================================

      // 1. Bridge lemma: establish what the spec expects BEFORE any mutations
      SpecHeap.hd_f_roundtrip cur;
      SpecObject.color_of_object_spec obj s;
      SpecObject.is_black_iff obj s;

      FusedLemmas.black_step_fused_aux_eq 's s cur
        cur_fb (U64.v cur_rw) cur_fv;

      // 2. Flush any pending blue run onto the list of its class
      flush_blue_lists_impl heap heads cur_fb cur_rw;
      let new_rw = 0UL;
      with s_flush new_fv. assert (is_heap heap s_flush ** pts_to heads new_fv);

      // 2a. flush_blue suffix preservation: reads at cur and beyond are unchanged
      CoalLemmas.flush_blue_suffix_preserved s cur_fb (U64.v cur_rw)
        (FLs.fls_head cur_fv (SCL.run_class (U64.v cur_rw))) (U64.v cur);
      // Connect s_flush to fst of flush_blue
      assert (pure (s_flush == fst (SCL.flush_blue_lists s cur_fb (U64.v cur_rw) cur_fv)));
      // Chain: s_flush preserves reads at cur from s, and s preserves from 's
      assert (pure (SpecHeap.read_word s_flush (SpecHeap.hd_address obj) ==
                    SpecHeap.read_word 's (SpecHeap.hd_address obj)));

      // 2b. s_flush length from flush_blue_impl postcondition (already have Seq.length s_flush == heap_size)

      // 2c. Establish Seq.mem obj (objects zero_addr 's) via density
      // obj == f_address cur, obj_in_objects is in the invariant from density lemmas
      // SI.obj_in_objects_elim was called above, giving Seq.mem obj (objects zero_addr 's)

      // 3. Write white header for the black object
      let white_hdr = makeHeader wz Header.White (getTag hdr);
      write_word heap cur white_hdr;
      with s_white. assert (is_heap heap s_white);

      // 4. Bridge: write_word matches makeWhite
      GC.Impl.Object.getTag_eq hdr;
      // Key fact: hdr is the same value that whiten_from_original will see
      // hdr == read_word s cur == read_word s_flush cur == read_word s_flush (hd_address obj)
      assert (pure (hdr == SpecHeap.read_word s_flush (SpecHeap.hd_address obj)));
      FusedLemmas.whiten_from_original 's s_flush obj;

      // 5. makeWhite suffix preservation (for next iteration)
      SpecHeap.hd_address_spec obj;
      FusedLemmas.makeWhite_suffix_preserved s_flush obj (U64.v next);
      FusedLemmas.makeWhite_length s_flush obj;

      // 6. The survivor is an output walk position: the windows below it
      //    belong to the previous one.
      TS.cursor_out_emit_step 's cur (U64.v cur_rw) vprev (U64.v vk) tv;
      ImplOT.emit_impl tbl k nb vprev cur;
      prev := cur;

      // 7. Update loop state
      current := next;
      fb_ref := 0UL;
      rw_ref := new_rw;

      // Arithmetic facts
      assert (pure (U64.v next % 8 == 0));
      assert (pure (U64.v next <= heap_size));
      assert (pure (U64.v next + 8 < pow2 64));
      assert (pure (U64.v new_rw == 0));

      // Suffix preservation for s_white past next:
      // s_white == makeWhite obj s_flush
      // makeWhite only writes at hd_address obj (< next)
      // s_flush agrees with 's past cur (from flush_blue suffix + original suffix)
      // Therefore s_white agrees with 's past next
      assert (pure (forall (addr: hp_addr). U64.v addr >= U64.v next ==>
        SpecHeap.read_word s_white addr == SpecHeap.read_word 's addr));

      // Spec equivalence from black_step bridge lemma
      assert (pure (
        U64.v next < heap_size ==>
          SCL.fused_aux_lists 's s_white
            (SpecFields.objects (U64.uint_to_t (U64.v next)) 's)
            0UL 0 new_fv == SCL.fused_sweep_coalesce_lists 's));
      assert (pure (
        U64.v next >= heap_size ==>
          SCL.fused_aux_lists 's s_white Seq.empty
            0UL 0 new_fv == SCL.fused_sweep_coalesce_lists 's));
      ()
    } else {
      // =====================================================
      // NON-BLACK CASE: accumulate into blue run (no heap writes)
      // =====================================================
      let new_fb = (if U64.eq cur_rw 0UL then obj else cur_fb);
      let new_rw = U64.add cur_rw ws_plus_1;

      // A run's first object is an output walk position (its header becomes
      // the run's); the rest of a run is not.  With no run starting, the
      // emit is given 0, below every boundary, and writes nothing.
      TS.cursor_out_emit_step 's cur (U64.v cur_rw) vprev (U64.v vk) tv;
      let starts = U64.eq cur_rw 0UL;
      OT.emit_stop tv (U64.v vk) vprev 0;
      ImplOT.emit_impl tbl k nb vprev (if starts then cur else 0UL);
      prev := (if starts then cur else vprev);

      current := next;
      fb_ref := new_fb;
      rw_ref := new_rw;

      // Step lemma
      SpecHeap.hd_f_roundtrip cur;
      SpecObject.color_of_object_spec obj s;
      SpecObject.is_black_iff obj s;

      FusedLemmas.nonblack_step_fused_aux_eq 's s cur
        cur_fb (U64.v cur_rw) cur_fv;

      // Arithmetic facts
      assert (pure (U64.v next % 8 == 0));
      assert (pure (U64.v next <= heap_size));
      assert (pure (U64.v next + 8 < pow2 64));
      assert (pure (U64.v new_rw == U64.v cur_rw + U64.v wz + 1));
      assert (pure (U64.v new_rw > 0));
      assert (pure (U64.v new_rw < pow2 54));
      assert (pure (U64.v new_fb >= U64.v mword));
      assert (pure (U64.v new_fb < heap_size));
      assert (pure (U64.v new_fb % U64.v mword == 0));
      assert (pure (U64.v new_fb - U64.v mword + op_Star (U64.v new_rw) (U64.v mword) == U64.v next));

      // Suffix preservation: no writes happened, next >= cur
      assert (pure (U64.v next >= U64.v cur));
      assert (pure (forall (addr: hp_addr). U64.v addr >= U64.v next ==>
        SpecHeap.read_word s addr == SpecHeap.read_word 's addr));

      // Spec equivalence from nonblack_step bridge lemma
      assert (pure (
        U64.v next < heap_size ==>
          SCL.fused_aux_lists 's s
            (SpecFields.objects (U64.uint_to_t (U64.v next)) 's)
            new_fb (U64.v new_rw) cur_fv == SCL.fused_sweep_coalesce_lists 's));
      assert (pure (
        U64.v next >= heap_size ==>
          SCL.fused_aux_lists 's s Seq.empty
            new_fb (U64.v new_rw) cur_fv == SCL.fused_sweep_coalesce_lists 's));
      ()
    }
  };

  // =====================================================
  // POST-LOOP: flush final pending blue run
  // =====================================================
  let final_fb = !fb_ref;
  let final_rw = !rw_ref;
  with final_fv. assert (pts_to heads final_fv);
  with s_exit. assert (is_heap heap s_exit);

  // Bridge: fused_aux_lists with Seq.empty == flush_blue_lists
  FusedLemmas.fused_step_empty 's s_exit final_fb (U64.v final_rw) final_fv;

  flush_blue_lists_impl heap heads final_fb final_rw;

  // Every window not yet written belongs to the last output position.
  let vprev = !prev;
  with v_exit. assert (pts_to current v_exit);
  with tv. assert (pts_to tbl tv);
  with vk. assert (R.pts_to k vk);
  with vrw. assert (pts_to rw_ref vrw);
  assert (pure (U64.v v_exit + 8 >= heap_size /\ U64.v v_exit <= heap_size /\
                U64.v v_exit % 8 == 0));
  assert (pure (OT.cursor (TS.out_emit 's (OT.objs_from 's (U64.v v_exit)) (U64.v vrw))
                          vprev (U64.v vk) tv ==
                OT.cursor (TS.out_emit 's (SpecFields.objects zero_addr 's) 0) zero_addr 0 't));
  TS.cursor_out_emit_end 's (U64.v v_exit) (U64.v vrw) vprev (U64.v vk) tv;
  ImplOT.emit_impl tbl k nb vprev heap_size_u64;
  with t2. assert (pts_to tbl t2);
  assert (pure (t2 == OT.cursor (TS.out_emit 's (SpecFields.objects zero_addr 's) 0) zero_addr 0 't));
  TS.fused_table 's 't;
  assert (pure (OT.table_matches (fst (SCL.fused_sweep_coalesce_lists 's)) t2))
}
#pop-options
