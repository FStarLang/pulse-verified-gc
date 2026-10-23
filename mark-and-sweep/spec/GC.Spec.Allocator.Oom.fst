/// ---------------------------------------------------------------------------
/// GC.Spec.Allocator.Oom - when the major allocator may say no
/// ---------------------------------------------------------------------------
///
/// The runtime raises `Out_of_memory` from exactly one place: `verified_allocate`
/// (verified_gc/alloc_gen.c) calls `allocate`, and if that fails it runs a full
/// collection and calls `allocate` once more.  A second failure is the OOM.
///
/// This module says what such a failure means: on the heap a full collection
/// produces, `alloc_spec` returns no object only if **every free block in the
/// heap is smaller than the request** (`fused_oom_no_fit`).  It does not say
/// the heap is full.  Fragmentation can still make an allocation fail with
/// enough free words in total; it just cannot fail while a big enough block
/// exists.
///
/// The argument has three layers:
///
///   1. `alloc_search_oom_cells_small` -- if the search returns no object, every
///      cell reachable from where it started is too small.  The search and the
///      free list walk the same chain (`FL.fl_next` reads the link exactly as
///      `alloc_search` does), and `fl_chain_terminates` rules out running out of
///      fuel before the end of it.
///   2. `alloc_spec_oom_no_fit` -- with `fl_complete`, every blue object that
///      could be a cell *is* reachable, so layer 1 covers all of them; a
///      wosize-0 fragment is smaller than any request of at least one word.
///      Two layers because the heap-wide claim is not inductive: blocks the walk
///      has already passed are not reachable from the next node.
///   3. `coalesce_oom_no_fit` / `fused_oom_no_fit` -- the coalescer's output
///      satisfies every hypothesis of layer 2, so the statement holds at the
///      pass the collector actually runs.

module GC.Spec.Allocator.Oom

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
open GC.Lib.Header

module U64 = FStar.UInt64
module FL = GC.Spec.FreeList
module AllocLemmas = GC.Spec.Allocator.Lemmas
module Coalesce = GC.Spec.Coalesce
module CD = GC.Spec.Coalesce.Descending
module CC = GC.Spec.Coalesce.Complete
module SI = GC.Spec.SweepInv
module Corr = GC.Spec.Correctness
module SC = GC.Spec.SweepCoalesce
module SCD = GC.Spec.SweepCoalesce.Defs
module SpecSweep = GC.Spec.Sweep

/// ---------------------------------------------------------------------------
/// Layer 1: a failed search saw only small cells
/// ---------------------------------------------------------------------------

/// Nothing is on a chain whose head is not a cell.
private let not_node_unreachable (g: heap) (cur y: U64.t)
  : Lemma (requires ~(FL.fl_node cur))
          (ensures ~(FL.reachable_on_fl g cur y))
  = introduce forall (n: nat). ~(FL.on_fl g cur y n)
    with (if n = 0 then () else ())

/// A heap object is at least one word above `zero_addr`: objects lie strictly
/// above it and both are word-aligned.  This closes the gap between
/// `alloc_search`'s lower guard (`zero_addr + mword`) and `FL.fl_node`'s
/// (`mword`).
private let object_above_zero_addr (g: heap) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g))
          (ensures U64.v x >= U64.v zero_addr + U64.v mword)
  = objects_addresses_gt_start zero_addr g x;
    GC.Spec.ZeroAddr.zero_addr_ok ()

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
private let rec alloc_search_oom_cells_small
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat) (y: U64.t)
  : Lemma
    (requires well_formed_heap_part1 g /\ wz >= 1 /\
              AllocLemmas.fl_valid g cur_fp fuel /\
              AllocLemmas.fl_chain_terminates g cur_fp fuel /\
              (alloc_search g head_fp prev_fp cur_fp wz fuel).obj_out == 0UL /\
              FL.reachable_on_fl g cur_fp y)
    (ensures U64.v y >= U64.v mword /\ U64.v y < heap_size /\ U64.v y % U64.v mword == 0 /\
             U64.v (wosize_of_object (y <: obj_addr) g) < wz)
    (decreases fuel)
  =
  if not (FL.fl_node cur_fp) then not_node_unreachable g cur_fp y
  else if fuel = 0 then begin
    // A cell is not a terminal node, and zero steps never reach one.
    AllocLemmas.fl_chain_terminates_valid_zero g cur_fp
  end
  else if U64.v cur_fp >= heap_size then ()
  else begin
    let obj : obj_addr = cur_fp in
    AllocLemmas.fl_valid_elim g cur_fp fuel;
    object_above_zero_addr g obj;
    let hd = hd_address obj in
    hd_address_spec obj;
    wosize_of_object_spec obj g;
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    assert (U64.v hd + 16 <= heap_size);
    let next_fp = read_word g obj in
    assert (FL.fl_next g cur_fp == next_fp);
    if block_wz >= wz then begin
      // The search allocates here: the right-justified object lies inside the
      // block, which well_formed_heap_part1 puts inside the heap, so the bounds
      // guard cannot fire and obj_out is a real address -- contradicting the
      // hypothesis that it is 0.
      let leftover = block_wz - wz in
      let ahn = U64.v hd + leftover * 8 in
      assert (U64.v hd + 8 + block_wz * 8 <= heap_size);
      assert (ahn + 8 < heap_size);
      aligned_plus_mul8 (U64.v hd) leftover;
      assert (ahn % 8 == 0);
      assert (U64.v cur_fp + leftover * 8 < heap_size);
      assert (U64.v (U64.add cur_fp (U64.uint_to_t (leftover * 8))) >= U64.v cur_fp)
    end
    else if y = cur_fp then ()
    else begin
      FL.reachable_uncons g cur_fp y;
      AllocLemmas.fl_chain_terminates_elim g cur_fp fuel;
      alloc_search_oom_cells_small g head_fp cur_fp next_fp wz (fuel - 1) y
    end
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Layer 2: with a complete free list, no blue block fits
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let alloc_spec_oom_no_fit (g: heap) (fp: U64.t) (wz: nat)
  : Lemma
    (requires well_formed_heap_part1 g /\ wz >= 1 /\
              AllocLemmas.fl_valid g fp heap_words /\
              AllocLemmas.fl_chain_terminates g fp heap_words /\
              FL.fl_complete g fp /\
              (alloc_spec g fp wz).obj_out == 0UL)
    (ensures forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ is_blue x g ==>
               U64.v (wosize_of_object x g) < wz)
  = let aux (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr g) /\ is_blue x g)
              (ensures U64.v (wosize_of_object x g) < wz)
      = if U64.v (wosize_of_object x g) = 0 then ()
        else begin
          FL.fl_complete_elim g fp x;
          alloc_search_oom_cells_small g fp 0UL fp wz heap_words x
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// Layer 3: after a full collection
/// ---------------------------------------------------------------------------

/// The coalescer's output satisfies every hypothesis of layer 2.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let coalesce_oom_no_fit (g: heap) (wz: nat)
  : Lemma
    (requires Coalesce.post_sweep_strong g /\ wz >= 1 /\
              (let r = Coalesce.coalesce g in
               (alloc_spec (fst r) (snd r) wz).obj_out == 0UL))
    (ensures (let g' = fst (Coalesce.coalesce g) in
              forall (x: obj_addr). Seq.mem x (objects zero_addr g') /\ is_blue x g' ==>
                U64.v (wosize_of_object x g') < wz))
  = let r = Coalesce.coalesce g in
    Coalesce.coalesce_preserves_wf g;
    wf_parts ();
    CD.coalesce_fl_entry g;
    CC.coalesce_complete g;
    alloc_spec_oom_no_fit (fst r) (snd r) wz
#pop-options

/// **After a full collection, a failed allocation means no free block anywhere
/// is big enough.**
///
/// Stated over `fused_sweep_coalesce`, the pass the collector runs
/// (`GC.Impl.collect_with_roots` returns exactly its result), under the
/// hypotheses `GC.Impl.fst` already discharges at that call site -- the same
/// ones as `GC.Spec.Coalesce.Complete.fused_exact`.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let fused_oom_no_fit (h_init h_mark: heap) (roots: seq obj_addr) (fp: U64.t) (wz: nat)
  : Lemma
    (requires
      Corr.mark_post h_init h_mark roots fp /\
      well_formed_heap h_mark /\
      heap_objects_dense h_mark /\
      SpecSweep.fp_in_heap fp h_mark /\
      (forall (x: obj_addr). Seq.mem x (objects zero_addr h_mark) ==> ~(is_gray x h_mark)) /\
      wz >= 1 /\
      (let r = SCD.fused_sweep_coalesce h_mark in
       (alloc_spec (fst r) (snd r) wz).obj_out == 0UL))
    (ensures (let g' = fst (SCD.fused_sweep_coalesce h_mark) in
              forall (x: obj_addr). Seq.mem x (objects zero_addr g') /\ is_blue x g' ==>
                U64.v (wosize_of_object x g') < wz))
  = SC.fused_eq_sweep_coalesce h_mark fp;
    Corr.sweep_post_sweep_strong_gen h_init h_mark roots fp;
    coalesce_oom_no_fit (fst (SpecSweep.sweep h_mark fp)) wz
#pop-options
