(*
   Pulse GC - Heap operations on one range [lo, hi) of the heap

   Range counterparts of GC.Impl.Heap.read_word and write_word, of the
   whitening step of GC.Impl.FusedSweepCoalesce, and of
   GC.Impl.Coalesce.flush_blue_impl.  Each owns only the bytes [lo, hi), as
   a pts_to_range on the heap array (docs/parallel-sweep-phase1.md, §7).

   Each is specified against a ghost whole heap `g`: the range holds
   g's bytes [lo, hi), and an operation whose writes all land in [lo, hi)
   leaves the range holding the bytes of the spec operation's result.  So
   the whole-heap spec lemmas apply unchanged, and only the addresses need
   to be shown inside the range.

   A word is read and written as 8 bytes.  ArrayWord's word primitives take
   a whole array, so using them here would need a new assumed primitive;
   these use only Pulse's verified pts_to_range_index and _upd.
*)

module GC.Impl.HeapRange

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsToRange
open GC.Impl.Heap
open GC.Impl.Object
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SpecHeap = GC.Spec.Heap
module SpecObject = GC.Spec.Object
module SpecCoalesce = GC.Spec.Coalesce
module Alloc = GC.Spec.Allocator
module Header = GC.Lib.Header
module CL = GC.Impl.Coalesce.Lemmas

/// ---------------------------------------------------------------------------
/// The range predicate
/// ---------------------------------------------------------------------------

/// The bytes [lo, hi) of the heap hold those of the whole heap `g`.  This is
/// GC.Impl.SweepSegment.is_heap_range heap lo hi (Seq.slice g lo hi).
let heap_range (h: heap_t) (lo: nat) (hi: nat{lo <= hi /\ hi <= heap_size}) (g: heap_state)
  : slprop =
  pts_to_range h.data lo hi (Seq.slice g lo hi)

/// The word at `a` lies in [lo, hi).
let word_in (lo hi: nat) (a: nat) : prop = lo <= a /\ a + 8 <= hi

/// ---------------------------------------------------------------------------
/// Reading and writing one word
/// ---------------------------------------------------------------------------

/// Updating one byte of the heap inside [lo, hi) updates the range.
let slice_upd (g: Seq.seq U8.t) (lo hi: nat) (a: nat) (b: U8.t)
  : Lemma (requires lo <= a /\ a < hi /\ hi <= Seq.length g)
          (ensures Seq.slice (Seq.upd g a b) lo hi == Seq.upd (Seq.slice g lo hi) (a - lo) b)
  = Seq.lemma_eq_intro (Seq.slice (Seq.upd g a b) lo hi) (Seq.upd (Seq.slice g lo hi) (a - lo) b)

/// The word at `a`, read from the range.
fn read_word_r (h: heap_t) (#lo: erased nat) (#hi: erased nat{lo <= hi /\ hi <= heap_size})
  (addr: hp_addr) (#g: erased heap_state)
  requires heap_range h lo hi g ** pure (word_in lo hi (U64.v addr))
  returns v: U64.t
  ensures heap_range h lo hi g ** pure (v == SpecHeap.read_word g addr)
{
  unfold heap_range;
  let i = SZ.uint64_to_sizet addr;
  let b0 = pts_to_range_index h.data i;
  let b1 = pts_to_range_index h.data (SZ.add i 1sz);
  let b2 = pts_to_range_index h.data (SZ.add i 2sz);
  let b3 = pts_to_range_index h.data (SZ.add i 3sz);
  let b4 = pts_to_range_index h.data (SZ.add i 4sz);
  let b5 = pts_to_range_index h.data (SZ.add i 5sz);
  let b6 = pts_to_range_index h.data (SZ.add i 6sz);
  let b7 = pts_to_range_index h.data (SZ.add i 7sz);
  SpecHeap.read_word_spec g addr;
  fold (heap_range h lo hi g);
  combine_bytes b0 b1 b2 b3 b4 b5 b6 b7
}

/// The 8 byte updates of write_word, on the range.
#push-options "--fuel 0 --ifuel 0"
let write_slice (g: heap_state) (lo hi: nat) (addr: hp_addr) (v: U64.t)
  : Lemma (requires word_in lo hi (U64.v addr) /\ hi <= heap_size)
          (ensures (let a = U64.v addr - lo in
                    let s = Seq.slice g lo hi in
                    let s = Seq.upd s a (uint64_to_uint8 v) in
                    let s = Seq.upd s (a+1) (uint64_to_uint8 (U64.shift_right v 8ul)) in
                    let s = Seq.upd s (a+2) (uint64_to_uint8 (U64.shift_right v 16ul)) in
                    let s = Seq.upd s (a+3) (uint64_to_uint8 (U64.shift_right v 24ul)) in
                    let s = Seq.upd s (a+4) (uint64_to_uint8 (U64.shift_right v 32ul)) in
                    let s = Seq.upd s (a+5) (uint64_to_uint8 (U64.shift_right v 40ul)) in
                    let s = Seq.upd s (a+6) (uint64_to_uint8 (U64.shift_right v 48ul)) in
                    let s = Seq.upd s (a+7) (uint64_to_uint8 (U64.shift_right v 56ul)) in
                    s == Seq.slice (SpecHeap.write_word g addr v) lo hi))
  = let a = U64.v addr in
    SpecHeap.write_word_spec g addr v;
    let s0 : Seq.seq U8.t = g in
    let s1 = Seq.upd s0 a (uint64_to_uint8 v) in
    let s2 = Seq.upd s1 (a+1) (uint64_to_uint8 (U64.shift_right v 8ul)) in
    let s3 = Seq.upd s2 (a+2) (uint64_to_uint8 (U64.shift_right v 16ul)) in
    let s4 = Seq.upd s3 (a+3) (uint64_to_uint8 (U64.shift_right v 24ul)) in
    let s5 = Seq.upd s4 (a+4) (uint64_to_uint8 (U64.shift_right v 32ul)) in
    let s6 = Seq.upd s5 (a+5) (uint64_to_uint8 (U64.shift_right v 40ul)) in
    let s7 = Seq.upd s6 (a+6) (uint64_to_uint8 (U64.shift_right v 48ul)) in
    slice_upd s0 lo hi a (uint64_to_uint8 v);
    slice_upd s1 lo hi (a+1) (uint64_to_uint8 (U64.shift_right v 8ul));
    slice_upd s2 lo hi (a+2) (uint64_to_uint8 (U64.shift_right v 16ul));
    slice_upd s3 lo hi (a+3) (uint64_to_uint8 (U64.shift_right v 24ul));
    slice_upd s4 lo hi (a+4) (uint64_to_uint8 (U64.shift_right v 32ul));
    slice_upd s5 lo hi (a+5) (uint64_to_uint8 (U64.shift_right v 40ul));
    slice_upd s6 lo hi (a+6) (uint64_to_uint8 (U64.shift_right v 48ul));
    slice_upd s7 lo hi (a+7) (uint64_to_uint8 (U64.shift_right v 56ul))
#pop-options

/// Write the word at `a`, inside the range.
fn write_word_r (h: heap_t) (#lo: erased nat) (#hi: erased nat{lo <= hi /\ hi <= heap_size})
  (addr: hp_addr) (v: U64.t) (#g: erased heap_state)
  requires heap_range h lo hi g ** pure (word_in lo hi (U64.v addr))
  ensures heap_range h lo hi (SpecHeap.write_word g addr v)
{
  unfold heap_range;
  write_slice g lo hi addr v;
  let i = SZ.uint64_to_sizet addr;
  pts_to_range_upd h.data i (uint64_to_uint8 v);
  pts_to_range_upd h.data (SZ.add i 1sz) (uint64_to_uint8 (U64.shift_right v 8ul));
  pts_to_range_upd h.data (SZ.add i 2sz) (uint64_to_uint8 (U64.shift_right v 16ul));
  pts_to_range_upd h.data (SZ.add i 3sz) (uint64_to_uint8 (U64.shift_right v 24ul));
  pts_to_range_upd h.data (SZ.add i 4sz) (uint64_to_uint8 (U64.shift_right v 32ul));
  pts_to_range_upd h.data (SZ.add i 5sz) (uint64_to_uint8 (U64.shift_right v 40ul));
  pts_to_range_upd h.data (SZ.add i 6sz) (uint64_to_uint8 (U64.shift_right v 48ul));
  pts_to_range_upd h.data (SZ.add i 7sz) (uint64_to_uint8 (U64.shift_right v 56ul));
  fold (heap_range h lo hi (SpecHeap.write_word g addr v))
}

/// ---------------------------------------------------------------------------
/// Whitening one object
/// ---------------------------------------------------------------------------

/// The header the sweep writes for a survivor is makeWhite's.  (As
/// GC.Impl.FusedSweepCoalesce.Lemmas.whiten_from_original, without the
/// facts about the whole heap it does not use.)
let whiten_header (g: heap_state) (obj: obj_addr)
  : Lemma (requires SpecObject.is_black obj g)
          (ensures (let hdr = SpecHeap.read_word g (SpecHeap.hd_address obj) in
                    SpecHeap.write_word g (SpecHeap.hd_address obj)
                      (makeHeader (getWosize hdr) Header.White (getTag hdr)) ==
                    SpecObject.makeWhite obj g))
  = let hdr = SpecHeap.read_word g (SpecHeap.hd_address obj) in
    SpecObject.is_black_iff obj g;
    SpecObject.color_of_object_spec obj g;
    SpecObject.gray_or_black_valid hdr;
    getWosize_eq hdr;
    getTag_eq hdr;
    lib_makeHeader_eq_colorHeader hdr Header.White;
    SpecObject.makeWhite_spec obj g

/// Whiten a black object whose header lies in the range.
fn makeWhite_r (h: heap_t) (#lo: erased nat) (#hi: erased nat{lo <= hi /\ hi <= heap_size})
  (obj: obj_addr) (#g: erased heap_state)
  requires heap_range h lo hi g **
           pure (word_in lo hi (U64.v obj - 8) /\ SpecObject.is_black obj g)
  ensures heap_range h lo hi (SpecObject.makeWhite obj g)
{
  let hd : hp_addr = U64.sub obj mword;
  SpecHeap.hd_address_spec obj;
  let hdr = read_word_r h hd;
  whiten_header g obj;
  write_word_r h hd (makeHeader (getWosize hdr) Header.White (getTag hdr));
  rewrite (heap_range h lo hi
             (SpecHeap.write_word g hd (makeHeader (getWosize hdr) Header.White (getTag hdr))))
       as (heap_range h lo hi (SpecObject.makeWhite obj g))
}

/// ---------------------------------------------------------------------------
/// Flushing a free run
/// ---------------------------------------------------------------------------

/// Zero n words from start_addr, all inside the range.
fn zero_fields_r (h: heap_t) (#lo: erased nat) (#hi: erased nat{lo <= hi /\ hi <= heap_size})
  (start_addr: U64.t) (n: U64.t) (#g: erased heap_state)
  requires heap_range h lo hi g **
           pure (U64.v start_addr % U64.v mword == 0 /\
                 lo <= U64.v start_addr /\
                 U64.v start_addr + U64.v n * U64.v mword <= hi)
  ensures heap_range h lo hi (Alloc.zero_fields g start_addr (U64.v n))
{
  let mut idx = 0UL;
  let mut addr = start_addr;
  while (U64.lt !idx n)
    invariant exists* i a s.
      pts_to idx i **
      pts_to addr a **
      heap_range h lo hi s **
      pure (U64.v i <= U64.v n /\
            U64.v a == U64.v start_addr + U64.v i * U64.v mword /\
            U64.v a % U64.v mword == 0 /\
            U64.v a + (U64.v n - U64.v i) * U64.v mword <= hi /\
            Alloc.zero_fields s (U64.uint_to_t (U64.v a)) (U64.v n - U64.v i) ==
              Alloc.zero_fields g start_addr (U64.v n))
    decreases (U64.v n - U64.v !idx)
  {
    let cur_a = !addr;
    let cur_i = !idx;
    with s_cur. assert (heap_range h lo hi s_cur);
    CL.zero_fields_step s_cur cur_a (U64.v n - U64.v cur_i);
    write_word_r h cur_a 0UL;
    addr := U64.add cur_a mword;
    idx := U64.add cur_i 1UL
  };
  with s. assert (heap_range h lo hi s);
  rewrite (heap_range h lo hi s) as (heap_range h lo hi (Alloc.zero_fields g start_addr (U64.v n)))
}

/// A run's header wosize: one less than its words.
inline_for_extraction
let run_wz (rw: U64.t{0 < U64.v rw /\ U64.v rw < pow2 54}) : r:wosize{U64.v r == U64.v rw - 1} =
  U64.sub rw 1UL

/// Where a flush writes: the header, the link word when there are two words
/// or more, and the words after it when there are three or more.
let run_words_in (lo hi fb rw: nat)
  : Lemma (requires rw >= 1 /\ fb >= 8 /\ fb % 8 == 0 /\ lo <= fb - 8 /\ fb - 8 + rw * 8 <= hi)
          (ensures word_in lo hi (fb - 8) /\
                   (rw >= 2 ==> word_in lo hi fb) /\
                   (rw >= 3 ==> (fb + 8) % 8 == 0 /\ lo <= fb + 8 /\
                                fb + 8 + (rw - 2) * 8 <= hi))
  = ()

/// The wosize of a run that is neither empty nor over one word.
let wz_one (wz: U64.t)
  : Lemma (requires U64.v wz > 0 /\ ~(U64.v wz > 1)) (ensures wz == 1UL)
  = U64.v_inj wz 1UL

let wz_zero (wz: U64.t)
  : Lemma (requires ~(U64.v wz > 0)) (ensures wz == 0UL)
  = U64.v_inj wz 0UL

/// flush_blue on a run inside the range: the run's words [fb - 8,
/// fb - 8 + rw * 8) lie in [lo, hi).  Returns the new head.
fn flush_blue_r (h: heap_t) (#lo: erased nat) (#hi: erased nat{lo <= hi /\ hi <= heap_size})
  (fb: U64.t) (rw: U64.t) (fp: U64.t) (#g: erased heap_state)
  requires heap_range h lo hi g **
           pure (U64.v rw > 0 ==>
                   U64.v rw < pow2 54 /\
                   U64.v fb >= U64.v mword /\
                   U64.v fb < heap_size /\
                   U64.v fb % U64.v mword == 0 /\
                   lo <= U64.v fb - U64.v mword /\
                   U64.v fb - U64.v mword + U64.v rw * U64.v mword <= hi)
  returns fp': U64.t
  ensures heap_range h lo hi (fst (SpecCoalesce.flush_blue g fb (U64.v rw) fp)) **
          pure (fp' == snd (SpecCoalesce.flush_blue g fb (U64.v rw) fp))
{
  if (U64.eq rw 0UL) {
    rewrite (heap_range h lo hi g)
         as (heap_range h lo hi (fst (SpecCoalesce.flush_blue g fb (U64.v rw) fp)));
    fp
  } else {
    let fb' : obj_addr = fb;
    run_words_in lo hi (U64.v fb) (U64.v rw);
    let hd : hp_addr = U64.sub fb mword;
    SpecHeap.hd_address_spec fb';
    U64.v_inj hd (SpecHeap.hd_address fb');
    let wz : (r:wosize{U64.v r == U64.v rw - 1}) = run_wz rw;
    let hdr = makeHeader wz blue 0UL;
    CL.makeHeader_bridge wz blue 0UL;
    write_word_r h hd hdr;
    with g1. assert (heap_range h lo hi g1);
    if (U64.gt wz 0UL) {
      let fba : hp_addr = fb;
      write_word_r h fba fp;
      with g2. assert (heap_range h lo hi g2);
      if (U64.gt wz 1UL) {
        let zero_start = U64.add fb mword;
        zero_fields_r h zero_start (U64.sub wz 1UL);
        with g3. assert (heap_range h lo hi g3);
        CL.flush_blue_impl_wz_ge2 g fb' wz fp g1 g2 g3;
        rewrite (heap_range h lo hi g3)
             as (heap_range h lo hi (fst (SpecCoalesce.flush_blue g fb (U64.v rw) fp)));
        fb
      } else {
        wz_one wz;
        CL.flush_blue_impl_wz1 g fb' fp g1 g2;
        rewrite (heap_range h lo hi g2)
             as (heap_range h lo hi (fst (SpecCoalesce.flush_blue g fb (U64.v rw) fp)));
        fb
      }
    } else {
      wz_zero wz;
      CL.flush_blue_impl_wz0 g fb' fp g1;
      rewrite (heap_range h lo hi g1)
           as (heap_range h lo hi (fst (SpecCoalesce.flush_blue g fb (U64.v rw) fp)));
      fp
    }
  }
}

/// ---------------------------------------------------------------------------
/// Non-vacuity
/// ---------------------------------------------------------------------------

/// The pure lemmas above, on arguments meeting their preconditions: the
/// whole heap as the range, the first word after zero_addr, and a run of one
/// word.  The whitening bridge is guarded by the object being black.
let range_witness (g: heap_state) (v: U64.t) (obj: obj_addr) : unit =
  let z = zero_addr in
  write_slice g 0 heap_size z v;
  slice_upd g 0 heap_size (U64.v z) 0uy;
  GC.Spec.Base.aligned_plus_mul8 (U64.v z) 1;
  run_words_in 0 heap_size (U64.v z + 8) 1;
  wz_one 1UL;
  wz_zero 0UL;
  if SpecObject.is_black obj g then whiten_header g obj
