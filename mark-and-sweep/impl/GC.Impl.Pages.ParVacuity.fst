/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.ParVacuity - the parallel sweep's theorems are not vacuous
/// ---------------------------------------------------------------------------
///
/// The hypotheses of the parallel sweep's theorems can all hold:
///   - `SweepChunks.sweep_chunks_eq`, `SweepSplit.split` and
///     `CDrive.sweep_par_seq` hold of the allocator's first state, with one
///     chunk or more, and an empty bitmap (`par_ready`);
///   - a pool page whose first slot holds a white block whose header's bit is
///     set has its marks where the bitmap sweep reads them
///     (`BitmapUnits.pool_marks`), and the specification's sweep keeps that
///     block (`pool_marked_live`);
///   - a run holding one white block whose header's bit is set has its marks
///     on the run's walk (`BitmapUnits.run_marks`).

module GC.Impl.Pages.ParVacuity

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Inv
open GC.Spec.Pages.Init
open GC.Spec.Pages.PoolInit

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Seq = FStar.Seq
module UI = FStar.UInt
module BM = GC.Spec.Pages.Bitmap
module BU = GC.Spec.Pages.BitmapUnits
module SP = GC.Spec.Pages.SweepPage
module SRg = GC.Spec.Pages.SweepRange
module SSp = GC.Spec.Pages.SweepSplit
module SCh = GC.Spec.Pages.SweepChunks
module SSt = GC.Spec.Pages.StartSweep
module SV = GC.Spec.Pages.SweepVacuity
module CSw = GC.Impl.Pages.CSweep
module CP = GC.Impl.Pages.CPar

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// A bitmap with one bit set
/// ---------------------------------------------------------------------------

let zeros : Seq.seq U32.t = Seq.create BM.bm_len 0ul

/// The bitmap with only the bit of the word at `a` set.
let one_bit (a: nat{BM.in_pages a}) : Seq.seq U32.t =
  BM.widx_bound a;
  Seq.upd zeros (BM.widx a / 32) (U32.shift_left 1ul (U32.uint_to_t (BM.widx a % 32)))

let pow2_bit (k j: nat)
  : Lemma (requires k < 32 /\ j < 32) (ensures BM.bit_of (U32.shift_left 1ul (U32.uint_to_t k)) j == (j = k))
  = UI.shift_left_value_lemma #32 1 k;
    FStar.Math.Lemmas.pow2_lt_compat 32 k;
    FStar.Math.Lemmas.small_mod (pow2 k) (pow2 32);
    UI.pow2_nth_lemma #32 k (31 - j);
    BM.nth_div 32 (pow2 k) j

/// **Only `a` is marked.**
let one_bit_marked (a: nat{BM.in_pages a}) (x: nat)
  : Lemma (BM.marked (one_bit a) x == (x = a))
  = BM.widx_bound a;
    if BM.in_pages x then begin
      BM.widx_bound x;
      let w = BM.widx a / 32 in
      if BM.widx x / 32 = w then begin
        pow2_bit (BM.widx a % 32) (BM.widx x % 32);
        if BM.widx x % 32 = BM.widx a % 32 then BM.widx_inj a x
      end
    end

/// ---------------------------------------------------------------------------
/// The whole parallel sweep
/// ---------------------------------------------------------------------------

/// One chunk: from page 0 to the end.
let one_chunk : Seq.seq U64.t =
  GC.Spec.Pages.Pool.n_pages_small ();
  Seq.cons 0UL (Seq.create 1 (U64.uint_to_t n_pages))

let zeros_unmarked (x: nat) : Lemma (not (BM.marked zeros x))
  = if BM.in_pages x then begin
      BM.widx_bound x;
      BM.zero_bits (BM.widx x % 32)
    end

let zero_marks (g: heap) (pm: page_map)
  : Lemma (requires forall (j: nat{j < n_pages}). (entry pm j).kind == Free)
          (ensures CSw.marks_from g zeros pm 0 n_pages)
  = FStar.Classical.forall_intro zeros_unmarked;
    let aux (j: nat{j < n_pages}) : Lemma (CSw.unit_marks g zeros pm j) = () in
    FStar.Classical.forall_intro aux

let start_free (j: nat{j < n_pages})
  : Lemma ((entry (SSt.start_sweep init_state).pm j).kind == Free)
  = SSt.clear_entry init_state.pm j

/// **The parallel sweep's hypotheses hold** of the allocator's first state,
/// with one chunk and an empty bitmap.
let par_ready (g: heap)
  : Lemma (let st0 = SSt.start_sweep init_state in
           SCh.empty_st st0 /\ map_ok init_state.pm /\ map_ok st0.pm /\
           CP.bounds_good st0.pm one_chunk 1 /\
           CSw.marks_from g zeros st0.pm 0 n_pages /\ Seq.length zeros == BM.bm_len /\
           SSp.l_ok st0 0 st0.pm /\ SRg.wreach st0.pm 0 n_pages)
  = let st0 = SSt.start_sweep init_state in
    all_free_ok ();
    SSt.clear_map_ok init_state.pm;
    FStar.Classical.forall_intro start_free;
    zero_marks g st0.pm;
    GC.Spec.Pages.Pool.n_pages_small ();
    if n_pages > 0 then assert (walk_page st0.pm 0);
    SRg.walk_reach st0.pm 0 n_pages;
    assert (SCh.bnd one_chunk 0 == 0);
    assert (SCh.bnd one_chunk 1 == n_pages)

/// ---------------------------------------------------------------------------
/// A pool page and a run with a mark
/// ---------------------------------------------------------------------------

/// A fresh pool page whose first slot holds a white block filling it.
let pool_white (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) : GTot heap =
  cls_bounds c;
  write_word (pool_init g i c) (slot_hd i c 0) (SV.hdr_of (cls c) White)

let slot_in (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (BM.in_pages (slot_base i c k))
  = slot_fits i c k;
    page_base_mono i (i + 1);
    page_base_mono (i + 1) n_pages;
    page_base_aligned i

/// **A marked white block on a pool page**: the marks are where the bitmap
/// sweep reads them, and the specification's sweep keeps the block.
let pool_marked_live (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (let a = slot_base i c 0 in
           BM.in_pages a /\
           BU.pool_marks (pool_white g i c) (one_bit a) i c /\
           SP.live (BM.with_marks (pool_white g i c) (one_bit a)) i c 0)
  = cls_bounds c;
    slot_in i c 0;
    let a = slot_base i c 0 in
    let g0 = pool_init g i c in
    let g1 = pool_white g i c in
    let bs = one_bit a in
    FStar.Classical.forall_intro (one_bit_marked a);
    slot_fits i c 0;
    read_write_same g0 (slot_hd i c 0) (SV.hdr_of (cls c) White);
    SV.hdr_of_spec (cls c) White;
    assert (mk_hp_addr a == slot_hd i c 0);
    let others (k: nat) : Lemma (k < n_slots c /\ k > 0 ==> ~(color_at g1 (slot_base i c k) == Black))
      = if k < n_slots c && k > 0 then begin
          pool_init_free g i c k;
          slot_fits i c k;
          slot_below i c 0 k;
          read_write_different g0 (slot_hd i c 0) (slot_hd i c k) (SV.hdr_of (cls c) White);
          assert (mk_hp_addr (slot_base i c k) == slot_hd i c k)
        end
    in
    FStar.Classical.forall_intro others;
    let only (k: nat) : Lemma (k < n_slots c /\ k > 0 ==> slot_base i c k <> a)
      = if k < n_slots c && k > 0 then slot_below i c 0 k
    in
    FStar.Classical.forall_intro only;
    BU.live_iff g1 bs i c 0

/// **A marked white block on a run**: the marks are on the run's walk.
let run_marked (g: heap) (i: nat{i < n_pages})
  : Lemma (BM.in_pages (page_base i) /\
           BU.run_marks (SV.run_heap g i White) (one_bit (page_base i)) i 1)
  = cls_bounds 0;
    page_base_mono i (i + 1);
    page_base_mono (i + 1) n_pages;
    page_base_aligned i;
    let g1 = SV.run_heap g i White in
    FStar.Classical.forall_intro (one_bit_marked (page_base i));
    read_write_same g (page_addr i) (SV.hdr_of page_wsize White);
    SV.hdr_of_spec page_wsize White;
    FStar.Math.Lemmas.distributivity_add_left i 1 page_bytes;
    BU.on_walk_step g1 (page_base i) (page_base (i + 1)) (page_base i)
