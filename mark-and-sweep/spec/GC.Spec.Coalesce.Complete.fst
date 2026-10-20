/// ---------------------------------------------------------------------------
/// GC.Spec.Coalesce.Complete - the coalescer drops nothing on the floor
/// ---------------------------------------------------------------------------
///
/// `GC.Spec.Coalesce.Descending` proves the *soundness* half of the free-list
/// story: every cell the coalescer's chain reaches is a real blue block, and
/// the chain terminates.  Both are satisfied by the empty chain, so between
/// them they do not rule out a collector that reclaims nothing.
///
/// This module is the other half -- `GC.Spec.FreeList.fl_complete` of the
/// coalescer's output, from `post_sweep` alone.  That matters beyond the
/// statement itself: `fl_complete` previously appeared only as a hypothesis,
/// never as a conclusion about a heap anything constructs, so every theorem
/// resting on it described a set of heaps that nothing was known to inhabit.
/// `coalesce_partition` at the end of this module is the first consumer to be
/// handed one.
///
/// It could not have been proved before the wosize-0 fragment forced
/// `fl_complete` to be weakened.  The old form -- every *blue* object is on
/// the chain -- is flatly false of a heap containing a fragment, which is blue
/// and has no field to hold a link.  The weakened form is exactly the
/// condition `flush_blue` itself branches on, which is why the two now agree.
///
/// The argument has three layers:
///
///   1. `flush_blue_links_cell` -- the flush declines to link in three cases,
///      and two of them (`wz >= pow2 54`, and no room for a link word) are
///      unreachable given the run geometry.  The fragment is the only block
///      the coalescer ever leaves off its chain.
///   2. `on_fl_mono` / `reachable_trans` / `fl_desc_chain_reach_frame` and
///      `coalesce_aux_chain_grows` -- a block earns its place on the list at
///      the moment it is flushed, which is far from the final heap and the
///      final head.  These carry it the rest of the way: the walk only ever
///      prepends, and it only ever writes above the chain's ceiling.
///   3. `coalesce_aux_complete` -- the induction, case for case the same walk
///      as `GC.Spec.Coalesce.coalesce_aux_walk_all_wb_tag`.
///
/// Two small helpers here (`run_words_small`, `merged_block_decompose`) are
/// copies of private definitions in `GC.Spec.Coalesce.Descending` and
/// `GC.Spec.Coalesce`; exporting them instead would re-verify those modules'
/// reverse-dependency closures for no change in content.

module GC.Spec.Coalesce.Complete

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Coalesce
open GC.Spec.FreeList

module U64 = FStar.UInt64
module CD = GC.Spec.Coalesce.Descending
module FL = GC.Spec.FreeList
module FLD = GC.Spec.FreeList.Descending
module Part = GC.Spec.Partition
module WE = GC.Spec.WalkEnd
module SI = GC.Spec.SweepInv
module Corr = GC.Spec.Correctness
module SC = GC.Spec.SweepCoalesce
module SCD = GC.Spec.SweepCoalesce.Defs
module SpecSweep = GC.Spec.Sweep

#set-options "--fuel 0 --ifuel 0 --z3rlimit 40"

/// A run that fits in the heap is far shorter than a wosize can express.
/// (`GC.Spec.Coalesce.Descending.run_words_small`, which is private there.)
private let run_words_small (run_words: nat) (run_end: nat) (hdv: nat)
  : Lemma (requires hdv + run_words * U64.v mword == run_end /\ run_end <= heap_size)
          (ensures run_words - 1 < pow2 54)
  = FStar.Math.Lemmas.pow2_plus 54 3;
    assert_norm (pow2 3 == 8);
    assert (pow2 54 * 8 == pow2 57);
    assert (run_words * 8 <= heap_size);
    if run_words >= pow2 54 then begin
      FStar.Math.Lemmas.lemma_mult_le_right 8 (pow2 54) run_words;
      assert (pow2 57 <= run_words * 8)
    end

/// **A run with room for a link word is always linked.**
///
/// The two defensive branches of `flush_blue` -- the `pow2 54` size guard and
/// the `hd + 2 * mword <= heap_size` room check -- are both discharged by the
/// run geometry alone.  The run ends at `run_end <= heap_size < pow2 57`, so it
/// is under `pow2 54` words; and a run of at least two words that ends inside
/// the heap has its first two words inside the heap.  So whenever the merged
/// block is a cell at all, the flush pushes it onto the chain.
let flush_blue_links_cell
  (g: heap) (run_end: nat) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      run_end <= heap_size /\
      CD.run_geometry run_end first_blue run_words /\
      run_words >= 2)
    (ensures (
      let r = flush_blue g first_blue run_words fp in
      snd r == first_blue /\
      Seq.length (fst r) == heap_size /\
      is_blue (first_blue <: obj_addr) (fst r) /\
      U64.v (wosize_of_object (first_blue <: obj_addr) (fst r)) == run_words - 1 /\
      read_word (fst r) (first_blue <: hp_addr) == fp))
  = let fb : obj_addr = first_blue in
    let hd = hd_address fb in
    hd_address_spec fb;
    // Hatch 2: the run fits in the heap, so its wosize fits in a header.
    run_words_small run_words run_end (U64.v hd);
    // Hatch 3: two words of a >= 2-word run that ends inside the heap.
    assert (U64.v hd + run_words * U64.v mword == run_end);
    FStar.Math.Lemmas.lemma_mult_le_right (U64.v mword) 2 run_words;
    assert (U64.v hd + U64.v mword * 2 <= run_end);
    FStar.Math.Lemmas.pow2_lt_compat 64 54;
    flush_blue_preserves_length g fb run_words fp;
    flush_blue_header_spec g fb run_words fp;
    flush_blue_field1_spec g fb run_words fp;
    let g' = fst (flush_blue g fb run_words fp) in
    let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
    makeHeader_getWosize wz_u64 Blue 0UL;
    makeHeader_getColor wz_u64 Blue 0UL;
    wosize_of_object_spec fb g';
    color_of_object_spec fb g';
    is_blue_iff fb g'

/// ---------------------------------------------------------------------------
/// Transporting free-list membership
/// ---------------------------------------------------------------------------
///
/// Completeness is a claim about the *final* heap and the *final* head, but the
/// fact that a block is on the list is earned at the moment it is flushed, far
/// from either.  These three lemmas carry it the rest of the way: reachability
/// tolerates a bigger fuel bound, composes, and -- given a descending chain --
/// survives any write above the chain's ceiling.

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let rec on_fl_mono (g: heap) (fp obj: U64.t) (n m: nat)
  : Lemma (requires on_fl g fp obj n /\ n <= m)
          (ensures on_fl g fp obj m)
          (decreases n)
  = if n = 0 then ()
    else if not (fl_node fp) then ()
    else if fp = obj then ()
    else on_fl_mono g (fl_next g fp) obj (n - 1) (m - 1)

let rec on_fl_trans (g: heap) (a b c: U64.t) (n m: nat)
  : Lemma (requires on_fl g a b n /\ on_fl g b c m)
          (ensures on_fl g a c (n + m))
          (decreases n)
  = if n = 0 then ()
    else if a = b then on_fl_mono g b c m (n + m)
    else begin
      on_fl_uncons g a b n;
      on_fl_trans g (fl_next g a) b c (n - 1) m;
      on_fl_cons g a c (n - 1 + m)
    end

/// Reachability composes along the chain.
let reachable_trans (g: heap) (a b c: U64.t)
  : Lemma (requires reachable_on_fl g a b /\ reachable_on_fl g b c)
          (ensures reachable_on_fl g a c)
  = eliminate exists (n: nat). on_fl g a b n
    with eliminate exists (m: nat). on_fl g b c m
         with (on_fl_trans g a b c n m; assert (on_fl g a c (n + m)))

/// **The frame rule for membership.**  `fl_desc_chain_frame` says a descending
/// chain survives a write above its ceiling; this says the *contents* do too.
/// Every read the walk down from `fp` performs is at an address below `bound`,
/// so no such write can disconnect a cell that was on the list.
let rec fl_desc_chain_reach_frame (g g': heap) (fp: U64.t) (bound: nat) (y: U64.t)
  : Lemma
    (requires
      FLD.fl_desc_chain g fp bound /\
      Seq.length g' == Seq.length g /\
      (forall (a: hp_addr). U64.v a + U64.v mword <= bound ==> read_word g' a == read_word g a) /\
      reachable_on_fl g fp y)
    (ensures reachable_on_fl g' fp y)
    (decreases bound)
  = if fp = 0UL then ()          // `fl_node 0UL` is false, so nothing is reachable
    else begin
      let o : obj_addr = fp in
      let hdv = U64.v fp - U64.v mword in
      // The chain bounds the head's own link word inside `bound`, so the two
      // heaps agree on `fl_next` here.
      assert (hdv + 2 * U64.v mword <= bound);
      assert (read_word g' (o <: hp_addr) == read_word g (o <: hp_addr));
      assert (fl_next g' fp == fl_next g fp);
      if fp = y then reachable_head g' fp
      else begin
        reachable_uncons g fp y;
        fl_desc_chain_reach_frame g g' (fl_next g fp) hdv y;
        reachable_cons g' fp y
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The chain only ever grows at the front
/// ---------------------------------------------------------------------------

/// **A flush never loses a cell.**
///
/// Whatever was on the list before the flush is still on it after, and if the
/// flushed run was big enough to be a cell, the merged block joins it.  The
/// first half is the interesting one: it is what lets a block earn its place on
/// the list at the moment it is flushed and keep it for the rest of the walk.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let flush_blue_chain_grows
  (g: heap) (run_end: nat) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      run_end <= heap_size /\
      CD.run_geometry run_end first_blue run_words /\
      FLD.fl_desc_chain g fp (CD.run_floor run_end first_blue run_words))
    (ensures (
      let r = flush_blue g first_blue run_words fp in
      Seq.length (fst r) == heap_size /\
      (forall (y: U64.t). reachable_on_fl g fp y ==> reachable_on_fl (fst r) (snd r) y) /\
      (run_words >= 2 ==> reachable_on_fl (fst r) (snd r) first_blue)))
  = let r = flush_blue g first_blue run_words fp in
    let floor = CD.run_floor run_end first_blue run_words in
    flush_blue_preserves_length g first_blue run_words fp;
    // Nothing below the run floor moves, so the existing chain is untouched.
    let frame (a: hp_addr)
      : Lemma (requires U64.v a + U64.v mword <= floor)
              (ensures read_word (fst r) a == read_word g a)
      = flush_blue_preserves_outside g first_blue run_words fp a
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires frame);
    let carry (y: U64.t)
      : Lemma (requires reachable_on_fl g fp y)
              (ensures reachable_on_fl (fst r) (snd r) y)
      = fl_desc_chain_reach_frame g (fst r) fp floor y;
        if snd r = fp then ()
        else begin
          // The only other possibility is that the merged block was pushed on
          // top, in which case its link word is the old head.
          let fb : obj_addr = first_blue in
          flush_blue_links_cell g run_end first_blue run_words fp;
          assert (snd r == first_blue);
          assert (read_word (fst r) (fb <: hp_addr) == fp);
          assert (fl_node first_blue);
          assert (fl_next (fst r) first_blue == fp);
          // `reachable g fp y` forces `fl_node fp`, so `fp` is on its own list.
          reachable_is_node g fp fp;
          reachable_head (fst r) fp;
          reachable_cons (fst r) first_blue fp;
          reachable_trans (fst r) first_blue fp y
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires carry);
    if run_words >= 2 then begin
      flush_blue_links_cell g run_end first_blue run_words fp;
      reachable_head (fst r) first_blue
    end
#pop-options

/// **The whole walk never loses a cell.**
///
/// Same statement lifted over `coalesce_aux`, by the same induction as
/// `GC.Spec.Coalesce.Descending.coalesce_aux_desc` -- whose descending-chain
/// invariant this carries along, because the frame rule for membership needs
/// it at every step.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let rec coalesce_aux_chain_grows
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires
      objs == objects start g0 /\
      Seq.length g0 == heap_size /\
      Seq.length g == heap_size /\
      CD.run_geometry (U64.v start) first_blue run_words /\
      FLD.fl_desc_chain g fp (CD.run_floor (U64.v start) first_blue run_words))
    (ensures (
      let r = coalesce_aux g0 g objs first_blue run_words fp in
      Seq.length (fst r) == heap_size /\
      (forall (y: U64.t). reachable_on_fl g fp y ==> reachable_on_fl (fst r) (snd r) y)))
    (decreases Seq.length objs)
  = coalesce_aux_preserves_length g0 g objs first_blue run_words fp;
    if Seq.length objs = 0 then
      flush_blue_chain_grows g (U64.v start) first_blue run_words fp
    else begin
      objects_nonempty_next start g0;
      let header = read_word g0 start in
      let wz = getWosize header in
      let obj = f_address start in
      f_address_spec start;
      hd_address_spec obj;
      wosize_of_object_spec obj g0;
      let ws = U64.v (wosize_of_object obj g0) in
      let rest_start_nat = U64.v start + (U64.v wz + 1) * U64.v mword in
      assert (rest_start_nat <= heap_size);
      if is_blue obj g0 then begin
        let new_first : U64.t = if run_words = 0 then obj else first_blue in
        let new_rw = run_words + ws + 1 in
        assert (CD.run_floor rest_start_nat new_first new_rw ==
                CD.run_floor (U64.v start) first_blue run_words);
        if rest_start_nat < heap_size then begin
          let next : hp_addr = U64.uint_to_t rest_start_nat in
          Seq.lemma_tl obj (objects next g0);
          coalesce_aux_chain_grows g0 g next (Seq.tail objs) new_first new_rw fp
        end
        else begin
          objects_tail_empty_when_done start g0;
          flush_blue_chain_grows g rest_start_nat new_first new_rw fp
        end
      end
      else begin
        // A survivor ends the run.  Membership earned before the flush is
        // carried across it, then across the rest of the walk.
        flush_blue_chain_grows g (U64.v start) first_blue run_words fp;
        CD.flush_blue_desc g (U64.v start) first_blue run_words fp;
        let g' = fst (flush_blue g first_blue run_words fp) in
        let fp' = snd (flush_blue g first_blue run_words fp) in
        if rest_start_nat < heap_size then begin
          let next : hp_addr = U64.uint_to_t rest_start_nat in
          Seq.lemma_tl obj (objects next g0);
          FLD.fl_desc_chain_weaken g' fp' (U64.v start) rest_start_nat;
          coalesce_aux_chain_grows g0 g' next (Seq.tail objs) 0UL 0 fp'
        end
        else
          objects_tail_empty_when_done start g0
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Completeness
/// ---------------------------------------------------------------------------

/// Stepping over a merged block, as `GC.Spec.Coalesce.merged_block_decompose`
/// (private there).  An object of the walk that starts at a merged block is
/// either that block or lies in the walk that resumes after it.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
private let merged_block_decompose
  (g': heap) (fb: obj_addr) (run_words: pos) (start: U64.t) (y: obj_addr)
  : Lemma
    (requires
      Seq.length g' == heap_size /\
      U64.v fb >= U64.v mword /\
      U64.v fb < heap_size /\
      U64.v fb % U64.v mword == 0 /\
      U64.v fb - U64.v mword + run_words * U64.v mword == U64.v start /\
      run_words - 1 < pow2 54 /\
      U64.v start <= heap_size /\
      U64.v start % U64.v mword == 0 /\
      read_word g' (hd_address fb) == makeHeader (U64.uint_to_t (run_words - 1)) Blue 0UL /\
      Seq.mem y (objects (hd_address fb) g'))
    (ensures
      y = fb \/ (U64.v start < heap_size /\ Seq.mem y (objects (start <: hp_addr) g')))
  = hd_address_spec fb;
    let sync = hd_address fb in
    let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
    makeHeader_getWosize wz_u64 Blue 0UL;
    f_address_spec sync;
    objects_nonempty_next sync g';
    Seq.cons_head_tail (objects sync g');
    mem_cons_lemma y fb (Seq.tail (objects sync g'));
    if y = fb then ()
    else begin
      if U64.v start >= heap_size then assert (Seq.mem y (Seq.tail (objects sync g')))
      else begin
        Seq.lemma_tl fb (objects (start <: hp_addr) g');
        assert (Seq.mem y (objects (start <: hp_addr) g'))
      end
    end
#pop-options

/// **Every cell the coalescer leaves behind is on its free list.**
///
/// The dual of `GC.Spec.Coalesce.Descending.coalesce_aux_desc`: that one says
/// the chain contains nothing but cells, this one says it misses none.  The
/// induction is the same walk, and the cases line up with
/// `GC.Spec.Coalesce.coalesce_aux_walk_all_wb_tag` -- the object `y` is either
/// the block the current run flushes to, an untouched white survivor (excluded
/// here by hypothesis, since survivors are not blue), or an object of the walk
/// that resumes after this step.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 300"
let rec coalesce_aux_complete
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (all_objs: seq obj_addr) (y: obj_addr)
  : Lemma
    (requires
      walk_pre g0 g start objs all_objs first_blue run_words /\
      (forall (addr: hp_addr). U64.v addr >= U64.v start ==>
        read_word g addr == read_word g0 addr) /\
      FLD.fl_desc_chain g fp (CD.run_floor (U64.v start) first_blue run_words) /\
      (let sync : hp_addr =
         if run_words > 0 then hd_address (first_blue <: obj_addr) else start in
       let g' = coalesce_heap g0 g objs first_blue run_words fp in
       Seq.mem y (objects sync g') /\
       is_blue y g' /\ U64.v (wosize_of_object y g') >= 1))
    (ensures (
      let r = coalesce_aux g0 g objs first_blue run_words fp in
      reachable_on_fl (fst r) (snd r) y))
    (decreases Seq.length objs)
  = let g' = coalesce_heap g0 g objs first_blue run_words fp in
    coalesce_aux_preserves_length g0 g objs first_blue run_words fp;
    if Seq.length objs = 0 then begin
      assert (Seq.equal objs Seq.empty);
      coalesce_heap_empty g0 g first_blue run_words fp;
      if run_words > 0 then begin
        flush_blue_preserves_length g first_blue run_words fp;
        hd_address_spec (first_blue <: obj_addr);
        run_words_bound first_blue run_words start;
        flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
        merged_block_decompose g' (first_blue <: obj_addr) run_words start y;
        // The walk is over, so nothing follows the merged block: y is it.
        if y <> (first_blue <: obj_addr) then begin
          flush_blue_preserves_outside g first_blue run_words fp start;
          assert (read_word g' start == read_word g0 start)
        end
        else begin
          // `wosize y g' >= 1` is exactly `run_words >= 2`, which is the
          // condition under which the flush links.
          let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
          makeHeader_getWosize wz_u64 Blue 0UL;
          wosize_of_object_spec (first_blue <: obj_addr) g';
          assert (run_words >= 2);
          flush_blue_chain_grows g (U64.v start) first_blue run_words fp
        end
      end
    end
    else begin
      objects_nonempty_next start g0;
      let header = read_word g0 start in
      let wz = getWosize header in
      let obj = f_address start in
      f_address_spec start;
      hd_address_spec obj;
      let rest_start_nat = U64.v start + (U64.v wz + 1) * U64.v mword in
      assert (obj == Seq.head objs);
      Seq.cons_head_tail objs;
      wosize_of_object_spec obj g0;
      let ws = U64.v (wosize_of_object obj g0) in

      let tail_sub (o: obj_addr)
        : Lemma (Seq.mem o (Seq.tail objs) ==> Seq.mem o all_objs)
        = mem_cons_lemma o obj (Seq.tail objs)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires tail_sub);

      if is_blue obj g0 then begin
        let new_first : U64.t = if run_words = 0 then obj else first_blue in
        let new_rw = run_words + ws + 1 in

        let tail_white_inv (o: obj_addr)
          : Lemma (Seq.mem o (Seq.tail objs) /\ is_white o g0 ==>
                   read_word g (hd_address o) == read_word g0 (hd_address o))
          = mem_cons_lemma o obj (Seq.tail objs)
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires tail_white_inv);

        coalesce_heap_blue_step g0 g objs first_blue run_words fp;
        // The run's floor does not move, so the chain invariant carries over.
        assert (CD.run_floor rest_start_nat new_first new_rw ==
                CD.run_floor (U64.v start) first_blue run_words);

        if rest_start_nat < heap_size then begin
          let next : hp_addr = U64.uint_to_t rest_start_nat in
          Seq.lemma_tl obj (objects next g0);
          assert (Seq.tail objs == objects next g0);
          coalesce_aux_complete g0 g next (Seq.tail objs) new_first new_rw fp all_objs y
        end
        else begin
          objects_tail_empty_when_done start g0;
          assert (Seq.equal (Seq.tail objs) Seq.empty);
          coalesce_heap_empty g0 g new_first new_rw fp;
          flush_blue_preserves_length g new_first new_rw fp;
          hd_address_spec (new_first <: obj_addr);
          let rest_u64 : U64.t = U64.uint_to_t rest_start_nat in
          run_words_bound_le new_first new_rw rest_u64;
          flush_blue_header_spec g (new_first <: obj_addr) new_rw fp;
          merged_block_decompose g' (new_first <: obj_addr) new_rw rest_u64 y;
          // Nothing follows: y is the merged block.
          let wz_merged : wosize = U64.uint_to_t (new_rw - 1) in
          makeHeader_getWosize wz_merged Blue 0UL;
          wosize_of_object_spec (new_first <: obj_addr) g';
          assert (new_rw >= 2);
          flush_blue_chain_grows g rest_start_nat new_first new_rw fp
        end
      end
      else begin
        // A survivor ends the run.
        mem_cons_lemma obj obj (Seq.tail objs);
        is_blue_iff obj g0; is_white_iff obj g0;
        assert (is_white obj g0);

        let (g_flush, fp_flush) = flush_blue g first_blue run_words fp in
        flush_blue_preserves_length g first_blue run_words fp;
        flush_blue_chain_grows g (U64.v start) first_blue run_words fp;
        CD.flush_blue_desc g (U64.v start) first_blue run_words fp;

        coalesce_heap_white_step g0 g objs first_blue run_words fp g_flush fp_flush;
        coalesce_heap_preserves_length g0 g_flush (Seq.tail objs) 0UL 0 fp_flush;
        assert (Seq.length g' == heap_size);

        if rest_start_nat < heap_size then begin
          let next : hp_addr = U64.uint_to_t rest_start_nat in
          Seq.lemma_tl obj (objects next g0);
          assert (Seq.tail objs == objects next g0);
          FLD.fl_desc_chain_weaken g_flush fp_flush (U64.v start) rest_start_nat;

          coalesce_heap_preserves_before_run_start g0 g_flush next (Seq.tail objs)
            0UL 0 fp_flush start;
          flush_blue_preserves_outside g first_blue run_words fp start;
          assert (read_word g' start == read_word g0 start);

          objects_nonempty_at start g' g0;
          objects_nonempty_next start g';
          Seq.cons_head_tail (objects start g');
          f_address_spec start;
          mem_cons_lemma y (f_address start) (Seq.tail (objects start g'));
          Seq.lemma_tl obj (objects next g');

          // Invariants for the recursive call.
          let flush_addr_inv (addr: hp_addr)
            : Lemma (requires U64.v addr >= U64.v next)
                    (ensures read_word g_flush addr == read_word g0 addr)
            = flush_blue_preserves_outside g first_blue run_words fp addr
          in
          FStar.Classical.forall_intro (FStar.Classical.move_requires flush_addr_inv);
          let flush_white_hdr_inv (o: obj_addr)
            : Lemma
              (requires Seq.mem o (Seq.tail objs) /\ is_white o g0)
              (ensures read_word g_flush (hd_address o) == read_word g0 (hd_address o))
            = mem_cons_lemma o obj (Seq.tail objs);
              objects_addresses_gt_start next g0 o;
              hd_address_spec o;
              flush_blue_preserves_outside g first_blue run_words fp (hd_address o)
          in
          FStar.Classical.forall_intro (FStar.Classical.move_requires flush_white_hdr_inv);

          if run_words > 0 then begin
            hd_address_spec (first_blue <: obj_addr);
            run_words_bound first_blue run_words start;
            flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
            coalesce_heap_preserves_before_run_start g0 g_flush next (Seq.tail objs)
              0UL 0 fp_flush (hd_address (first_blue <: obj_addr));
            merged_block_decompose g' (first_blue <: obj_addr) run_words start y;
            if y = (first_blue <: obj_addr) then begin
              let wz_fb : wosize = U64.uint_to_t (run_words - 1) in
              makeHeader_getWosize wz_fb Blue 0UL;
              wosize_of_object_spec (first_blue <: obj_addr) g';
              assert (run_words >= 2);
              // The block joined the list at the flush; the rest of the walk
              // only prepends, so it is still there at the end.
              coalesce_aux_chain_grows g0 g_flush next (Seq.tail objs) 0UL 0 fp_flush
            end
            else if y = obj then begin
              // A white survivor is not blue in the output: excluded.
              color_of_header_eq obj g0 g';
              is_blue_iff obj g'; is_blue_iff obj g0
            end
            else
              coalesce_aux_complete g0 g_flush next (Seq.tail objs) 0UL 0 fp_flush all_objs y
          end
          else begin
            if y = obj then begin
              color_of_header_eq obj g0 g';
              is_blue_iff obj g'; is_blue_iff obj g0
            end
            else
              coalesce_aux_complete g0 g_flush next (Seq.tail objs) 0UL 0 fp_flush all_objs y
          end
        end
        else begin
          objects_tail_empty_when_done start g0;
          assert (Seq.equal (Seq.tail objs) Seq.empty);
          coalesce_heap_empty g0 g_flush 0UL 0 fp_flush;
          flush_blue_preserves_outside g first_blue run_words fp start;
          assert (read_word g' start == read_word g0 start);
          objects_nonempty_at start g' g0;
          objects_nonempty_next start g';
          mem_cons_lemma y (f_address start) (Seq.tail (objects start g'));

          if run_words > 0 then begin
            hd_address_spec (first_blue <: obj_addr);
            run_words_bound first_blue run_words start;
            flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
            merged_block_decompose g' (first_blue <: obj_addr) run_words start y;
            if y = (first_blue <: obj_addr) then begin
              let wz_fb : wosize = U64.uint_to_t (run_words - 1) in
              makeHeader_getWosize wz_fb Blue 0UL;
              wosize_of_object_spec (first_blue <: obj_addr) g';
              assert (run_words >= 2)
            end
            else begin
              assert (y == obj);
              color_of_header_eq y g0 g';
              is_blue_iff y g'; is_blue_iff y g0
            end
          end
          else begin
            assert (y == obj);
            color_of_header_eq y g0 g';
            is_blue_iff y g'; is_blue_iff y g0
          end
        end
      end
    end
#pop-options

/// **The coalescer's output free list is complete.**
///
/// The missing half of `GC.Spec.Coalesce.Descending.coalesce_fl_entry`.  That
/// lemma says the chain contains only cells and terminates -- both of which the
/// empty chain satisfies, so together they do not rule out a collector that
/// reclaims nothing.  This says the chain contains *every* cell, which is the
/// statement that the collector actually recovered the garbage it swept.
///
/// The wosize-0 fragment is deliberately not a cell: it has no field to hold a
/// link, so it cannot be on any list.  It is still free space, and
/// `GC.Spec.Partition` counts it as such.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let coalesce_complete (g: heap)
  : Lemma
    (requires post_sweep g)
    (ensures (let r = coalesce g in FL.fl_complete (fst r) (snd r)))
  = coalesce_heap_unfold g g (objects zero_addr g) 0UL 0 0UL;
    let r = coalesce g in
    let g' = fst r in
    let fp' = snd r in
    assert (g' == coalesce_heap g g (objects zero_addr g) 0UL 0 0UL);
    assert (FLD.fl_desc_chain g 0UL (CD.run_floor (U64.v zero_addr) 0UL 0));
    let aux (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g') /\ is_blue y g' /\
                        U64.v (wosize_of_object y g') >= 1)
              (ensures reachable_on_fl g' fp' y)
      = coalesce_aux_complete g g zero_addr (objects zero_addr g) 0UL 0 0UL
          (objects zero_addr g) y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// The payoff: the partition, at a heap the collector actually produces
/// ---------------------------------------------------------------------------

/// **Every word of the post-collection heap is accounted for.**
///
/// `GC.Spec.Partition.heap_partition_strong` is stated of an arbitrary heap
/// satisfying three hypotheses, and until now the third -- `fl_complete` --
/// had no base case anywhere in the development, so the theorem described a
/// set of heaps that nothing was known to inhabit.  All three now come from
/// `post_sweep`, which `GC.Spec.Correctness.sweep_post_sweep_strong` proves of
/// the sweeper's output and `GC.Gen.PostCollectionShape` already consumes.
///
/// So: after a collection, the heap is exactly the live words, plus the words
/// on the free list, plus the fragments -- with no fourth class of free space
/// that has been lost track of.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let coalesce_partition (g: heap)
  : Lemma
    (requires post_sweep g)
    (ensures (
      let r = coalesce g in
      let g' = fst r in
      let objs = objects zero_addr g' in
      U64.v zero_addr
      + (Part.white_whsize g' objs
         + Part.onchain_whsize g' (snd r) objs
         + Part.frag_whsize g' objs) * U64.v mword
      == WE.walk_end g' zero_addr))
  = coalesce_preserves_length g;
    coalesce_all_white_or_blue g;
    coalesce_complete g;
    Part.heap_partition_strong (fst (coalesce g)) (snd (coalesce g))
#pop-options

/// **The partition, at the heap the collector actually produces.**
///
/// `coalesce_partition` is about `coalesce g`, but the shipped pipeline is the
/// fused single pass: `GC.Impl.fst` calls `fused_sweep_coalesce heap`, never
/// `sweep` and `coalesce` separately.  `fused_eq_sweep_coalesce` bridges the
/// two, and `sweep_post_sweep_strong_gen` supplies `post_sweep` of the sweeper's
/// output from the mark postcondition, so the identity transfers to the pass
/// the collector runs.
///
/// The hypotheses are exactly the ones `GC.Impl.fst` already discharges at the
/// call site (`fp_valid_transfer`, `noGreyObjects_from_no_gray`, and the mark
/// postcondition it carries in).
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let fused_partition (h_init h_mark: heap) (roots: seq obj_addr) (fp: U64.t)
  : Lemma
    (requires
      Corr.mark_post h_init h_mark roots fp /\
      well_formed_heap h_mark /\
      SI.heap_objects_dense h_mark /\
      SpecSweep.fp_in_heap fp h_mark /\
      (forall (x: obj_addr). Seq.mem x (objects zero_addr h_mark) ==> ~(is_gray x h_mark)))
    (ensures (
      let r = SCD.fused_sweep_coalesce h_mark in
      let g' = fst r in
      let objs = objects zero_addr g' in
      U64.v zero_addr
      + (Part.white_whsize g' objs
         + Part.onchain_whsize g' (snd r) objs
         + Part.frag_whsize g' objs) * U64.v mword
      == WE.walk_end g' zero_addr))
  = SC.fused_eq_sweep_coalesce h_mark fp;
    Corr.sweep_post_sweep_strong_gen h_init h_mark roots fp;
    coalesce_partition (fst (SpecSweep.sweep h_mark fp))
#pop-options

/// ---------------------------------------------------------------------------
/// Coalesce establishes fl_exact
/// ---------------------------------------------------------------------------
///
/// `coalesce_complete` gives the completeness half. The soundness half is
/// already known in other forms: `coalesce_fl_entry` gives the allocator's
/// `fl_valid` + `fl_chain_terminates`, and `coalesce_desc` gives
/// `fl_desc_chain`, which records for every node on the chain that it is in
/// range, aligned, blue, has room for a link, and lies below the previous one.
/// `fl_sound` asks for one more thing per node: that it is an object of the
/// heap walk. The same `mem_step` that `coalesce_fl_entry` uses supplies that
/// one link at a time, so `fl_sound` follows by induction along the chain.

/// One step of that induction: anything reachable in `n` links from a head
/// that starts a descending chain is a sound cell.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let rec on_fl_desc_sound
  (g: heap) (fp: U64.t) (bound: nat)
  (mem_step: (a: U64.t -> Lemma
     (requires U64.v a >= U64.v mword /\ U64.v a < heap_size /\
               U64.v a % U64.v mword == 0 /\
               Seq.mem (a <: obj_addr) (objects zero_addr g) /\
               is_blue (a <: obj_addr) g /\
               U64.v (wosize_of_object (a <: obj_addr) g) >= 1)
     (ensures (let n = read_word g (a <: obj_addr) in
               n == 0UL \/
               (U64.v n >= U64.v mword /\ U64.v n < heap_size /\
                U64.v n % U64.v mword == 0 /\
                Seq.mem (n <: obj_addr) (objects zero_addr g))))))
  (obj: U64.t) (n: nat)
  : Lemma
    (requires
      FLD.fl_desc_chain g fp bound /\ bound <= heap_size /\
      (fp == 0UL \/
       (U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
        U64.v fp % U64.v mword == 0 /\
        Seq.mem (fp <: obj_addr) (objects zero_addr g))) /\
      on_fl g fp obj n)
    (ensures
      fl_node obj /\
      (U64.v obj >= U64.v mword /\ U64.v obj < heap_size /\ U64.v obj % U64.v mword == 0) /\
      Seq.mem (obj <: obj_addr) (objects zero_addr g) /\
      is_blue (obj <: obj_addr) g /\
      U64.v (wosize_of_object (obj <: obj_addr) g) >= 1)
    (decreases n)
  = // `on_fl` with any fuel forces `fl_node fp`, so `fp` is not null and is a
    // real object; the descending chain then gives its colour and size.
    if fp = obj then ()
    else begin
      on_fl_uncons g fp obj n;
      let o : obj_addr = fp in
      mem_step fp;
      on_fl_desc_sound g (read_word g o) (U64.v fp - U64.v mword) mem_step obj (n - 1)
    end
#pop-options

/// A descending chain whose links all land on heap objects is sound.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let fl_desc_chain_gives_sound
  (g: heap) (fp: U64.t)
  (mem_step: (a: U64.t -> Lemma
     (requires U64.v a >= U64.v mword /\ U64.v a < heap_size /\
               U64.v a % U64.v mword == 0 /\
               Seq.mem (a <: obj_addr) (objects zero_addr g) /\
               is_blue (a <: obj_addr) g /\
               U64.v (wosize_of_object (a <: obj_addr) g) >= 1)
     (ensures (let n = read_word g (a <: obj_addr) in
               n == 0UL \/
               (U64.v n >= U64.v mword /\ U64.v n < heap_size /\
                U64.v n % U64.v mword == 0 /\
                Seq.mem (n <: obj_addr) (objects zero_addr g))))))
  : Lemma
    (requires FLD.fl_desc_chain g fp heap_size /\
              (fp == 0UL \/
               (U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                U64.v fp % U64.v mword == 0 /\
                Seq.mem (fp <: obj_addr) (objects zero_addr g))))
    (ensures FL.fl_sound g fp)
  = let aux (obj: U64.t)
      : Lemma (requires reachable_on_fl g fp obj)
              (ensures
                fl_node obj /\
                (U64.v obj >= U64.v mword /\ U64.v obj < heap_size /\
                 U64.v obj % U64.v mword == 0) /\
                Seq.mem (obj <: obj_addr) (objects zero_addr g) /\
                is_blue (obj <: obj_addr) g /\
                U64.v (wosize_of_object (obj <: obj_addr) g) >= 1)
      = eliminate exists (n: nat). on_fl g fp obj n
        with on_fl_desc_sound g fp heap_size mem_step obj n
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// **The coalescer's output free list is sound**, in the form `fl_exact`
/// uses: every cell reachable from the head is a blue heap object with room
/// for a link. Assembled exactly as `coalesce_fl_entry` is.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let coalesce_sound (g: heap)
  : Lemma (requires post_sweep g)
          (ensures (let r = coalesce g in FL.fl_sound (fst r) (snd r)))
  = let r = coalesce g in
    let g' = fst r in
    let fp' = snd r in
    CD.coalesce_desc g;
    coalesce_head_in_walk g;
    let mem_step (a: U64.t)
      : Lemma
        (requires U64.v a >= U64.v mword /\ U64.v a < heap_size /\
                  U64.v a % U64.v mword == 0 /\
                  Seq.mem (a <: obj_addr) (objects zero_addr g') /\
                  is_blue (a <: obj_addr) g' /\
                  U64.v (wosize_of_object (a <: obj_addr) g') >= 1)
        (ensures (let n = read_word g' (a <: obj_addr) in
                  n == 0UL \/
                  (U64.v n >= U64.v mword /\ U64.v n < heap_size /\
                   U64.v n % U64.v mword == 0 /\
                   Seq.mem (n <: obj_addr) (objects zero_addr g'))))
      = coalesce_heap_unfold g g (objects zero_addr g) 0UL 0 0UL;
        coalesce_aux_blue_field0_valid g g zero_addr (objects zero_addr g)
          (objects zero_addr g) 0UL 0 0UL (a <: obj_addr)
    in
    fl_desc_chain_gives_sound g' fp' mem_step
#pop-options

/// **Coalescing establishes `fl_exact`.** The free list the coalescer builds
/// is exactly the cells of the heap it returns: nothing on the chain is
/// anything but a free cell, and no free cell is missing from it.
///
/// "Establishes", not "preserves": the coalescer discards any incoming free
/// list and builds its own from a null head, so it needs nothing about the
/// old list -- only `post_sweep`, the colours sweep leaves. Whatever state
/// allocation left the list in, a collection restores `fl_exact`.
let coalesce_exact (g: heap)
  : Lemma (requires post_sweep g)
          (ensures (let r = coalesce g in FL.fl_exact (fst r) (snd r)))
  = coalesce_sound g;
    coalesce_complete g

/// The same, at the pass the collector actually runs. Same hypotheses as
/// `fused_partition`.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let fused_exact (h_init h_mark: heap) (roots: seq obj_addr) (fp: U64.t)
  : Lemma
    (requires
      Corr.mark_post h_init h_mark roots fp /\
      well_formed_heap h_mark /\
      SI.heap_objects_dense h_mark /\
      SpecSweep.fp_in_heap fp h_mark /\
      (forall (x: obj_addr). Seq.mem x (objects zero_addr h_mark) ==> ~(is_gray x h_mark)))
    (ensures (let r = SCD.fused_sweep_coalesce h_mark in FL.fl_exact (fst r) (snd r)))
  = SC.fused_eq_sweep_coalesce h_mark fp;
    Corr.sweep_post_sweep_strong_gen h_init h_mark roots fp;
    coalesce_exact (fst (SpecSweep.sweep h_mark fp))
#pop-options
