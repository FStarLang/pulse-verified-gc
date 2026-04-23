(*
   Pure F* bridge lemmas for the fused sweep+coalesce implementation.
*)

module GC.Impl.FusedSweepCoalesce.Lemmas

open FStar.Seq
open FStar.Mul
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
module Defs = GC.Spec.SweepCoalesce.Defs
module SpecCoalesce = GC.Spec.Coalesce
module Alloc = GC.Spec.Allocator
module HeapGraph = GC.Spec.HeapGraph
module Header = GC.Lib.Header
module SI = GC.Spec.SweepInv
module CoalLemmas = GC.Impl.Coalesce.Lemmas

#set-options "--z3rlimit 100 --fuel 2 --ifuel 1"

/// ---------------------------------------------------------------------------
/// fused_unfold
/// ---------------------------------------------------------------------------

let fused_unfold g = ()

/// ---------------------------------------------------------------------------
/// is_black_from_original
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let is_black_from_original g0 g obj start =
  f_address_spec start;
  hd_f_roundtrip start;
  assert (hd_address obj == start);
  assert (read_word g start == read_word g0 start);
  color_of_header_eq obj g0 g
#pop-options

/// ---------------------------------------------------------------------------
/// makeWhite_suffix_preserved
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let makeWhite_suffix_preserved g obj bound =
  makeWhite_spec obj g;
  let hd = hd_address obj in
  let white_hdr = colorHeader (read_word g hd) Header.White in
  assert (makeWhite obj g == write_word g hd white_hdr);
  write_preserves_after g hd white_hdr
#pop-options

/// ---------------------------------------------------------------------------
/// makeWhite_length
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let makeWhite_length g obj =
  makeWhite_spec obj g
#pop-options

/// ---------------------------------------------------------------------------
/// whiten_from_original
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let whiten_from_original g0 g' obj =
  let h_addr = hd_address obj in
  let hdr_g0 = read_word g0 h_addr in
  let hdr_g' = read_word g' h_addr in
  assert (hdr_g' == hdr_g0);
  is_black_iff obj g0;
  color_of_object_spec obj g0;
  assert (getColor hdr_g0 == Header.Black);
  gray_or_black_valid hdr_g0;
  assert (Header.valid_header64 hdr_g');
  // Bridge impl getWosize/getTag to spec
  GC.Impl.Object.getWosize_eq hdr_g';
  GC.Impl.Object.getTag_eq hdr_g';
  // impl makeHeader == spec colorHeader (when header is valid)
  GC.Impl.Object.lib_makeHeader_eq_colorHeader hdr_g' Header.White;
  // makeWhite obj g' == write_word g' h_addr (colorHeader hdr White)
  makeWhite_spec obj g'
#pop-options

/// ---------------------------------------------------------------------------
/// Private helpers: objects_advance, run_words_fits, step lemmas
/// ---------------------------------------------------------------------------

private let objects_advance (start: hp_addr) (g: heap)
  : Lemma
    (requires Seq.length g == heap_size /\ Seq.length (objects start g) > 0)
    (ensures (
      let hdr = read_word g start in
      let wz = getWosize hdr in
      let next_nat = U64.v start + (U64.v wz + 1) * U64.v mword in
      next_nat <= heap_size /\
      next_nat < pow2 64 /\
      (next_nat < heap_size ==>
        Seq.equal (Seq.tail (objects start g)) (objects (U64.uint_to_t next_nat) g)) /\
      (next_nat >= heap_size ==>
        Seq.equal (Seq.tail (objects start g)) Seq.empty)))
  = CoalLemmas.objects_advance start g

private let run_words_fits (g0: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat)
  : Lemma
    (requires
      objs == objects start g0 /\
      Seq.length g0 == heap_size /\
      (run_words > 0 ==>
        U64.v first_blue >= U64.v mword /\
        U64.v first_blue < heap_size /\
        U64.v first_blue % U64.v mword == 0 /\
        U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v start))
    (ensures run_words < heap_size / U64.v mword /\ run_words < pow2 57)
  = CoalLemmas.run_words_fits g0 start objs first_blue run_words

private let fused_step_nonblack_helper (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires
      Seq.length objs > 0 /\
      ~(is_black (Seq.head objs) g0) /\
      objs == objects start g0 /\
      Seq.length g0 == heap_size)
    (ensures (
      let obj = Seq.head objs in
      let wz = getWosize (read_word g0 start) in
      let ws = U64.v wz in
      let new_first : U64.t = if run_words = 0 then obj else first_blue in
      let next_nat = U64.v start + (ws + 1) * U64.v mword in
      next_nat <= heap_size /\
      (next_nat < heap_size ==>
        Seq.equal (Seq.tail objs) (objects (U64.uint_to_t next_nat) g0)) /\
      (next_nat >= heap_size ==>
        Seq.equal (Seq.tail objs) Seq.empty) /\
      Defs.fused_aux g0 g objs first_blue run_words fp ==
        Defs.fused_aux g0 g (Seq.tail objs) new_first (run_words + ws + 1) fp))
  = objects_advance start g0;
    let obj = Seq.head objs in
    f_address_spec start;
    hd_f_roundtrip start;
    wosize_of_object_spec obj g0;
    assert (hd_address obj == start);
    assert (wosize_of_object obj g0 == getWosize (read_word g0 start))

private let fused_step_black_helper (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires
      Seq.length objs > 0 /\
      is_black (Seq.head objs) g0 /\
      objs == objects start g0 /\
      Seq.length g0 == heap_size)
    (ensures (
      let obj = Seq.head objs in
      let wz = getWosize (read_word g0 start) in
      let ws = U64.v wz in
      let (g', fp') = SpecCoalesce.flush_blue g first_blue run_words fp in
      let g'' = makeWhite obj g' in
      let next_nat = U64.v start + (ws + 1) * U64.v mword in
      next_nat <= heap_size /\
      (next_nat < heap_size ==>
        Seq.equal (Seq.tail objs) (objects (U64.uint_to_t next_nat) g0)) /\
      (next_nat >= heap_size ==>
        Seq.equal (Seq.tail objs) Seq.empty) /\
      Defs.fused_aux g0 g objs first_blue run_words fp ==
        Defs.fused_aux g0 g'' (Seq.tail objs) 0UL 0 fp'))
  = objects_advance start g0;
    let obj = Seq.head objs in
    f_address_spec start;
    hd_f_roundtrip start;
    wosize_of_object_spec obj g0;
    assert (hd_address obj == start);
    assert (wosize_of_object obj g0 == getWosize (read_word g0 start))

/// ---------------------------------------------------------------------------
/// nonblack_step_fused_aux_eq
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let nonblack_step_fused_aux_eq g0 g start first_blue run_words fp =
  fused_step_nonblack_helper g0 g start (objects start g0) first_blue run_words fp;
  let wz = getWosize (read_word g0 start) in
  let ws = U64.v wz in
  let obj = f_address start in
  let new_first : U64.t = if run_words = 0 then obj else first_blue in
  let new_rw = run_words + ws + 1 in
  let next_nat = U64.v start + (ws + 1) * U64.v mword in
  let tail_objs = Seq.tail (objects start g0) in
  assert (Defs.fused_aux g0 g tail_objs new_first new_rw fp ==
          Defs.fused_sweep_coalesce g0);
  FStar.Math.Lemmas.lemma_mod_plus (U64.v start) (ws + 1) (U64.v mword);
  f_address_spec start;
  assert (U64.v obj == U64.v start + U64.v mword);
  assert (new_rw > 0);
  (if run_words = 0 then begin
    assert (new_first == obj);
    assert (U64.v new_first == U64.v start + U64.v mword);
    assert (U64.v new_first >= U64.v mword);
    assert (U64.v new_first - U64.v mword + new_rw * U64.v mword ==
            U64.v start + (ws + 1) * U64.v mword)
  end else begin
    assert (new_first == first_blue);
    assert (U64.v new_first - U64.v mword + new_rw * U64.v mword ==
            U64.v first_blue - U64.v mword + (run_words + ws + 1) * U64.v mword);
    FStar.Math.Lemmas.distributivity_add_left run_words (ws + 1) (U64.v mword);
    assert (U64.v first_blue - U64.v mword + run_words * U64.v mword + (ws + 1) * U64.v mword ==
            U64.v start + (ws + 1) * U64.v mword)
  end);
  assert (U64.v new_first - U64.v mword + new_rw * U64.v mword == next_nat);
  assert (next_nat <= heap_size);
  assert (U64.v new_first >= U64.v mword);
  assert (new_rw * U64.v mword <= next_nat);
  FStar.Math.Lemmas.lemma_div_le (new_rw * U64.v mword) heap_size (U64.v mword);
  FStar.Math.Lemmas.cancel_mul_div new_rw (U64.v mword);
  assert (new_rw <= heap_size / U64.v mword);
  FStar.Math.Lemmas.pow2_plus 3 54;
  assert (pow2 57 == U64.v mword * pow2 54);
  FStar.Math.Lemmas.lemma_div_exact heap_size (U64.v mword);
  assert (heap_size == U64.v mword * (heap_size / U64.v mword));
  assert (U64.v mword * (heap_size / U64.v mword) < U64.v mword * pow2 54);
  FStar.Math.Lemmas.pow2_le_compat 57 3;
  FStar.Math.Lemmas.pow2_double_sum 57;
  FStar.Math.Lemmas.pow2_lt_compat 64 58;
  if next_nat < heap_size then begin
    Seq.lemma_eq_elim tail_objs (objects (U64.uint_to_t next_nat) g0);
    assert (tail_objs == objects (U64.uint_to_t next_nat) g0)
  end;
  if next_nat >= heap_size then begin
    Seq.lemma_eq_elim tail_objs (Seq.empty #obj_addr);
    assert (tail_objs == Seq.empty #obj_addr)
  end
#pop-options

/// ---------------------------------------------------------------------------
/// flush_blue_suffix_chain (private helper for black_step)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
private let flush_blue_suffix_chain
  (g0 g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (start_val: nat) (addr: hp_addr)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      Seq.length g0 == heap_size /\
      U64.v addr >= start_val /\
      (forall (a: hp_addr). U64.v a >= start_val ==> read_word g a == read_word g0 a) /\
      (run_words > 0 ==>
        U64.v first_blue >= U64.v mword /\
        U64.v first_blue < heap_size /\
        U64.v first_blue % U64.v mword == 0 /\
        U64.v first_blue - U64.v mword + run_words * U64.v mword == start_val))
    (ensures (
      let (g', _) = SpecCoalesce.flush_blue g first_blue run_words fp in
      read_word g' addr == read_word g0 addr))
  = SpecCoalesce.flush_blue_preserves_outside g first_blue run_words fp addr;
    assert (read_word (fst (SpecCoalesce.flush_blue g first_blue run_words fp)) addr ==
            read_word g addr)
#pop-options

/// ---------------------------------------------------------------------------
/// black_step_fused_aux_eq
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 400 --fuel 2 --ifuel 1"
let black_step_fused_aux_eq g0 g start first_blue run_words fp =
  fused_step_black_helper g0 g start (objects start g0) first_blue run_words fp;
  let wz = getWosize (read_word g0 start) in
  let ws = U64.v wz in
  let obj = f_address start in
  let (g', fp') = SpecCoalesce.flush_blue g first_blue run_words fp in
  let g'' = makeWhite obj g' in
  let next_nat = U64.v start + (ws + 1) * U64.v mword in
  let tail_objs = Seq.tail (objects start g0) in
  assert (Defs.fused_aux g0 g'' tail_objs 0UL 0 fp' ==
          Defs.fused_sweep_coalesce g0);
  FStar.Math.Lemmas.lemma_mod_plus (U64.v start) (ws + 1) (U64.v mword);
  SpecCoalesce.flush_blue_preserves_length g first_blue run_words fp;
  assert (Seq.length g' == heap_size);
  makeWhite_length g' obj;
  assert (Seq.length g'' == heap_size);
  let chain_flush (addr: hp_addr) : Lemma
    (requires U64.v addr >= U64.v start)
    (ensures read_word g' addr == read_word g0 addr)
  = flush_blue_suffix_chain g0 g first_blue run_words fp (U64.v start) addr
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires chain_flush);
  hd_address_spec obj;
  f_address_spec start;
  assert (hd_address obj == start);
  assert (U64.v (hd_address obj) + U64.v mword <= next_nat);
  makeWhite_suffix_preserved g' obj next_nat;
  let chain_all (addr: hp_addr) : Lemma
    (requires U64.v addr >= next_nat)
    (ensures read_word g'' addr == read_word g0 addr)
  = assert (read_word g'' addr == read_word g' addr);
    assert (U64.v addr >= U64.v start);
    assert (read_word g' addr == read_word g0 addr)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires chain_all);
  assert (next_nat <= heap_size);
  FStar.Math.Lemmas.pow2_le_compat 57 3;
  FStar.Math.Lemmas.pow2_double_sum 57;
  FStar.Math.Lemmas.pow2_lt_compat 64 58;
  if next_nat < heap_size then begin
    Seq.lemma_eq_elim tail_objs (objects (U64.uint_to_t next_nat) g0);
    assert (tail_objs == objects (U64.uint_to_t next_nat) g0)
  end;
  if next_nat >= heap_size then begin
    Seq.lemma_eq_elim tail_objs (Seq.empty #obj_addr);
    assert (tail_objs == Seq.empty #obj_addr)
  end
#pop-options

/// ---------------------------------------------------------------------------
/// flush_blue_length (delegate to coalesce lemma)
/// ---------------------------------------------------------------------------

let flush_blue_length g fb rw fp =
  CoalLemmas.flush_blue_length g fb rw fp

/// ---------------------------------------------------------------------------
/// fused_step_empty
/// ---------------------------------------------------------------------------

let fused_step_empty g0 g first_blue run_words fp = ()
