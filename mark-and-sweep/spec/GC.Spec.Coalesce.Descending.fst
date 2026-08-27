module GC.Spec.Coalesce.Descending

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Coalesce

module U64 = FStar.UInt64
module FLD = GC.Spec.FreeList.Descending
module AllocLemmas = GC.Spec.Allocator.Lemmas

#set-options "--fuel 0 --ifuel 0 --z3rlimit 40"

/// A run that fits in the heap is far shorter than a wosize can express, so
/// `flush_blue`'s defensive `wz >= pow2 54` branch is unreachable.  Lifted out
/// so the `pow2` arithmetic never enters the walk's context.
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

/// The merged block written by a flush is blue with room for a link word, and
/// its link word is the incoming free-list head.
private let flushed_block_shape
  (g: heap) (fb: obj_addr) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires
      run_words >= 2 /\
      run_words - 1 < pow2 54 /\
      U64.v (hd_address fb) + run_words * U64.v mword <= heap_size /\
      Seq.length g == heap_size)
    (ensures (let g' = fst (flush_blue g fb run_words fp) in
              Seq.length g' == heap_size /\
              is_blue fb g' /\
              U64.v (wosize_of_object fb g') >= 1 /\
              read_word g' fb == fp))
  = FStar.Math.Lemmas.pow2_lt_compat 64 54;
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

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let flush_blue_desc g run_end first_blue run_words fp =
  let r = flush_blue g first_blue run_words fp in
  let floor = run_floor run_end first_blue run_words in
  flush_blue_preserves_length g first_blue run_words fp;
  // Everything strictly below the run floor is untouched, so the chain built so
  // far survives the flush verbatim.
  let frame (a: hp_addr)
    : Lemma (requires U64.v a + U64.v mword <= floor)
            (ensures read_word (fst r) a == read_word g a)
    = flush_blue_preserves_outside g first_blue run_words fp a
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires frame);
  FLD.fl_desc_chain_frame g (fst r) fp floor;
  if run_words = 0 then ()
  else begin
    let fb : obj_addr = first_blue in
    let hd = hd_address fb in
    hd_address_spec fb;
    assert (floor == U64.v hd);
    run_words_small run_words run_end (U64.v hd);
    if run_words >= 2 && U64.v hd + U64.v mword * 2 <= heap_size then begin
      flushed_block_shape g fb run_words fp;
      assert (snd r == first_blue);
      assert (U64.v hd + 2 * U64.v mword <= run_end);
      FLD.fl_desc_chain_cons (fst r) fb run_end
    end
    else begin
      assert (snd r == fp);
      FLD.fl_desc_chain_weaken (fst r) fp floor run_end
    end
  end
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
let rec coalesce_aux_desc g0 g start objs first_blue run_words fp =
  if Seq.length objs = 0 then begin
    flush_blue_desc g (U64.v start) first_blue run_words fp;
    let r = flush_blue g first_blue run_words fp in
    FLD.fl_desc_chain_weaken (fst r) (snd r) (U64.v start) heap_size
  end
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
      // The run grows.  Its floor does not move -- it is either the run's
      // existing first block or this object, which starts exactly here -- so
      // the chain invariant carries over unchanged.
      let new_first : U64.t = if run_words = 0 then obj else first_blue in
      let new_rw = run_words + ws + 1 in
      assert (run_floor rest_start_nat new_first new_rw ==
              run_floor (U64.v start) first_blue run_words);
      if rest_start_nat < heap_size then begin
        let next : hp_addr = U64.uint_to_t rest_start_nat in
        Seq.lemma_tl obj (objects next g0);
        coalesce_aux_desc g0 g next (Seq.tail objs) new_first new_rw fp
      end
      else begin
        objects_tail_empty_when_done start g0;
        flush_blue_desc g rest_start_nat new_first new_rw fp;
        let r = flush_blue g new_first new_rw fp in
        FLD.fl_desc_chain_weaken (fst r) (snd r) rest_start_nat heap_size
      end
    end
    else begin
      // A survivor ends the run: flush it, then continue with an empty run
      // whose floor is the next walk position.
      flush_blue_desc g (U64.v start) first_blue run_words fp;
      let g' = fst (flush_blue g first_blue run_words fp) in
      let fp' = snd (flush_blue g first_blue run_words fp) in
      if rest_start_nat < heap_size then begin
        let next : hp_addr = U64.uint_to_t rest_start_nat in
        Seq.lemma_tl obj (objects next g0);
        FLD.fl_desc_chain_weaken g' fp' (U64.v start) rest_start_nat;
        coalesce_aux_desc g0 g' next (Seq.tail objs) 0UL 0 fp'
      end
      else begin
        objects_tail_empty_when_done start g0;
        FLD.fl_desc_chain_weaken g' fp' (U64.v start) heap_size
      end
    end
  end
#pop-options

#push-options "--fuel 1 --ifuel 1"
let coalesce_desc g =
  assert (FLD.fl_desc_chain g 0UL (run_floor (U64.v zero_addr) 0UL 0));
  coalesce_aux_desc g g zero_addr (objects zero_addr g) 0UL 0 0UL
#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 60"
let coalesce_fl_entry g =
  let r = coalesce g in
  let g' = fst r in
  let fp' = snd r in
  coalesce_desc g;
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
  FLD.fl_desc_chain_gives_valid g' fp' mem_step
#pop-options
