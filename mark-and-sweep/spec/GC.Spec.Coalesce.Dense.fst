module GC.Spec.Coalesce.Dense

/// Coalescing preserves the "the walk tiles the heap" invariant.
///
/// `GC.Spec.SweepInv.heap_objects_dense` is one of the fifteen clauses of
/// `GC.Gen.HeapInvariant.major_heap_shape`, and it is the one clause the
/// coalescer cannot inherit by transfer: merging a run of free blocks changes
/// the wosize of the block at the run's head, so `heap_objects_dense_transfer`
/// (which needs equal wosizes everywhere) does not apply.
///
/// `GC.Spec.WalkEnd` turns density into a single scalar -- the address at which
/// the walk stops -- and this module proves, by induction over the coalescing
/// walk, that the coalescer leaves that address alone.  The intuition is that
/// coalescing re-tiles the heap: a merged block covers exactly the addresses
/// its constituent free blocks covered, and a survivor keeps its header, so the
/// last block still ends where it did before.

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Coalesce

module U64 = FStar.UInt64
module SI = GC.Spec.SweepInv
module WE = GC.Spec.WalkEnd

#set-options "--fuel 0 --ifuel 0 --z3rlimit 40"

/// The walk position a merged block is reported against, once its header has
/// been written: the block spans `[hd_address fb, run_end)`, so the walk steps
/// straight from the block to `run_end`.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 80"
private let merged_block_walk_end
  (g': heap) (fb: obj_addr) (run_words: pos) (run_end: U64.t)
  : Lemma
    (requires
      Seq.length g' == heap_size /\
      U64.v fb >= U64.v mword /\
      U64.v fb < heap_size /\
      U64.v fb % U64.v mword == 0 /\
      U64.v run_end <= heap_size /\
      U64.v fb - U64.v mword + run_words * U64.v mword == U64.v run_end /\
      run_words - 1 < pow2 54 /\
      read_word g' (hd_address fb) == makeHeader (U64.uint_to_t (run_words - 1)) Blue 0UL)
    (ensures (
      let sync = hd_address fb in
      (U64.v run_end >= heap_size ==> WE.walk_end g' sync == heap_size) /\
      (U64.v run_end < heap_size ==>
       WE.walk_end g' sync == WE.walk_end g' (run_end <: hp_addr))))
  = hd_address_spec fb;
    run_words_bound_le fb run_words run_end;
    merged_block_head g' fb run_words;
    let sync = hd_address fb in
    let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
    makeHeader_getWosize wz_u64 Blue 0UL;
    WE.walk_end_step g' sync
#pop-options

/// The walk position of a survivor, whose header the coalesce left alone.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 80"
private let survivor_walk_end
  (g0 g': heap) (start: hp_addr)
  : Lemma
    (requires
      Seq.length (objects start g0) > 0 /\
      read_word g' start == read_word g0 start)
    (ensures (
      let wz = getWosize (read_word g0 start) in
      let next = U64.v start + (U64.v wz + 1) * 8 in
      (next >= heap_size ==> WE.walk_end g' start == heap_size) /\
      (next < heap_size ==>
       WE.walk_end g' start == WE.walk_end g' (mk_hp_addr next) /\
       WE.walk_end g0 start == WE.walk_end g0 (mk_hp_addr next))))
  = objects_nonempty_at start g' g0;
    WE.walk_end_step g0 start;
    WE.walk_end_step g' start
#pop-options

/// ---------------------------------------------------------------------------
/// The induction
/// ---------------------------------------------------------------------------

val coalesce_aux_walk_end
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      walk_pre g0 g start objs all_objs first_blue run_words /\
      WE.walk_end g0 start + 8 >= heap_size)
    (ensures (
      let sync : hp_addr =
        if run_words > 0 then hd_address (first_blue <: obj_addr) else start in
      WE.walk_end (coalesce_heap g0 g objs first_blue run_words fp) sync
        == WE.walk_end g0 start))
    (decreases Seq.length objs)

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let rec coalesce_aux_walk_end g0 g start objs first_blue run_words fp all_objs =
  let sync : hp_addr =
    if run_words > 0 then hd_address (first_blue <: obj_addr) else start in
  if Seq.length objs = 0 then begin
    coalesce_heap_empty g0 g first_blue run_words fp;
    WE.walk_end_empty g0 start;
    let g' = fst (flush_blue g first_blue run_words fp) in
    flush_blue_preserves_length g first_blue run_words fp;
    WE.walk_end_at_tail g' start;
    if run_words > 0 then begin
      let fb : obj_addr = first_blue in
      hd_address_spec fb;
      run_words_bound fb run_words start;
      flush_blue_header_spec g fb run_words fp;
      merged_block_walk_end g' fb run_words start
    end;
    assert (WE.walk_end (coalesce_heap g0 g objs first_blue run_words fp) sync
            == WE.walk_end g0 start)
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
    WE.walk_end_step g0 start;

    if is_blue obj g0 then begin
      let new_first : U64.t = if run_words = 0 then obj else first_blue in
      let new_rw = run_words + ws + 1 in
      assert (hd_address (new_first <: obj_addr) == sync);

      let tail_white_inv (o: obj_addr)
        : Lemma (Seq.mem o (Seq.tail objs) /\ is_white o g0 ==>
                 read_word g (hd_address o) == read_word g0 (hd_address o))
        = mem_cons_lemma o obj (Seq.tail objs)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires tail_white_inv);

      coalesce_heap_blue_step g0 g objs first_blue run_words fp;

      if rest_start_nat < heap_size then begin
        let next : hp_addr = U64.uint_to_t rest_start_nat in
        Seq.lemma_tl obj (objects next g0);
        coalesce_aux_walk_end g0 g next (Seq.tail objs) new_first new_rw fp all_objs
      end
      else begin
        // The run reaches the end of the heap: the merged block is the last
        // block, and it ends exactly at `heap_size`.
        objects_tail_empty_when_done start g0;
        coalesce_heap_empty g0 g new_first new_rw fp;
        let g' = fst (flush_blue g new_first new_rw fp) in
        flush_blue_preserves_length g new_first new_rw fp;
        let nfb : obj_addr = new_first in
        hd_address_spec nfb;
        let run_end : U64.t = U64.uint_to_t rest_start_nat in
        run_words_bound_le nfb new_rw run_end;
        flush_blue_header_spec g nfb new_rw fp;
        merged_block_walk_end g' nfb new_rw run_end
      end;
      assert (WE.walk_end (coalesce_heap g0 g objs first_blue run_words fp) sync
              == WE.walk_end g0 start)
    end
    else begin
      mem_cons_lemma obj obj (Seq.tail objs);
      is_blue_iff obj g0; is_white_iff obj g0;
      assert (is_white obj g0);

      let (g_flush, fp_flush) = flush_blue g first_blue run_words fp in
      flush_blue_preserves_length g first_blue run_words fp;
      coalesce_heap_white_step g0 g objs first_blue run_words fp g_flush fp_flush;
      let g_result = coalesce_heap g0 g_flush (Seq.tail objs) 0UL 0 fp_flush in
      coalesce_heap_preserves_length g0 g_flush (Seq.tail objs) 0UL 0 fp_flush;

      // The survivor's header survives both the flush of the pending run (it
      // lies strictly below `start`) and the rest of the walk (which only
      // writes at or above `start`).
      white_addr_outside_all_blue g0 obj start;
      flush_blue_preserves_outside g first_blue run_words fp start;

      if rest_start_nat < heap_size then begin
        let next : hp_addr = U64.uint_to_t rest_start_nat in
        Seq.lemma_tl obj (objects next g0);

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

        coalesce_heap_preserves_outside g0 g_flush next (Seq.tail objs)
          0UL 0 fp_flush all_objs start;
        survivor_walk_end g0 g_result start;
        coalesce_aux_walk_end g0 g_flush next (Seq.tail objs) 0UL 0 fp_flush all_objs;
        if run_words > 0 then begin
          let fb : obj_addr = first_blue in
          hd_address_spec fb;
          run_words_bound fb run_words start;
          flush_blue_header_spec g fb run_words fp;
          assert (U64.v first_blue <= U64.v next);
          coalesce_heap_preserves_before_run_start g0 g_flush next (Seq.tail objs)
            0UL 0 fp_flush (hd_address fb);
          merged_block_walk_end g_result fb run_words start
        end
      end
      else begin
        // The survivor is the last block and it ends exactly at `heap_size`.
        objects_tail_empty_when_done start g0;
        coalesce_heap_empty g0 g_flush 0UL 0 fp_flush;
        survivor_walk_end g0 g_result start;
        if run_words > 0 then begin
          let fb : obj_addr = first_blue in
          hd_address_spec fb;
          run_words_bound fb run_words start;
          flush_blue_header_spec g fb run_words fp;
          merged_block_walk_end g_result fb run_words start
        end
      end;
      assert (WE.walk_end (coalesce_heap g0 g objs first_blue run_words fp) sync
              == WE.walk_end g0 start)
    end
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Top level
/// ---------------------------------------------------------------------------

/// **Coalescing preserves density**, and the coalesced heap still enumerates at
/// least one object.  These are the two structural clauses of
/// `GC.Gen.HeapInvariant.major_heap_shape` that the coalescer has to re-earn
/// rather than inherit.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let coalesce_dense (g: heap)
  : Lemma
    (requires post_sweep g /\ SI.heap_objects_dense g /\
              Seq.length (objects zero_addr g) > 0)
    (ensures (
      let g' = fst (coalesce g) in
      SI.heap_objects_dense g' /\ Seq.length (objects zero_addr g') > 0))
  = let g' = fst (coalesce g) in
    coalesce_preserves_length g;
    WE.walk_end_of_dense_top g;
    coalesce_heap_unfold g g (objects zero_addr g) 0UL 0 0UL;
    coalesce_aux_walk_end g g zero_addr (objects zero_addr g) 0UL 0 0UL
      (objects zero_addr g);
    WE.walk_nonempty_of_walk_end g' zero_addr;
    WE.dense_from_walk_end g'
#pop-options
