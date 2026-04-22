(*
   Pure F* bridge lemmas for the coalesce implementation.
*)

module GC.Impl.Coalesce.Lemmas

open FStar.Seq
open FStar.Mul
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Coalesce
module Alloc = GC.Spec.Allocator
module HeapGraph = GC.Spec.HeapGraph

#set-options "--z3rlimit 100 --fuel 2 --ifuel 1"

/// Objects walk produces nonempty + advance
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let objects_advance start g =
  let hdr = read_word g start in
  let wz = getWosize hdr in
  let next_nat = U64.v start + (U64.v wz + 1) * U64.v mword in
  assert (next_nat <= heap_size);
  assert (heap_size < pow2 64)
#pop-options

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let coalesce_step_blue g0 g start objs first_blue run_words fp =
  objects_advance start g0;
  let obj = Seq.head objs in
  f_address_spec start;
  hd_f_roundtrip start;
  wosize_of_object_spec obj g0;
  assert (hd_address obj == start);
  assert (wosize_of_object obj g0 == getWosize (read_word g0 start))
#pop-options

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let coalesce_step_white g0 g start objs first_blue run_words fp =
  objects_advance start g0;
  let obj = Seq.head objs in
  f_address_spec start;
  hd_f_roundtrip start;
  wosize_of_object_spec obj g0;
  assert (hd_address obj == start);
  assert (wosize_of_object obj g0 == getWosize (read_word g0 start))
#pop-options

let coalesce_step_empty g0 g first_blue run_words fp = ()

#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
let flush_blue_length g fb rw fp =
  flush_blue_preserves_length g fb rw fp
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
let objects_mem_at_zero g =
  objects_nonempty_head 0UL g;
  let objs = objects 0UL g in
  Seq.Properties.cons_head_tail objs;
  Seq.Properties.mem_cons (f_address 0UL) (Seq.tail objs)
#pop-options

let coalesce_unfold g = ()

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let run_words_fits g0 start objs first_blue run_words =
  if run_words > 0 then begin
    assert (run_words * U64.v mword <= U64.v start);
    assert (U64.v start <= heap_size);
    FStar.Math.Lemmas.lemma_div_le (run_words * U64.v mword) heap_size (U64.v mword);
    FStar.Math.Lemmas.cancel_mul_div run_words (U64.v mword)
  end
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let is_blue_from_original g0 g obj start =
  f_address_spec start;
  hd_f_roundtrip start;
  assert (hd_address obj == start);
  assert (read_word g start == read_word g0 start);
  color_of_header_eq obj g0 g
#pop-options

#push-options "--z3rlimit 100 --fuel 2 --ifuel 0"
let zero_fields_step g addr n = ()
#pop-options

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let flush_blue_suffix_preserved g first_blue run_words fp cursor =
  if run_words = 0 then ()
  else begin
    let aux (addr: hp_addr) : Lemma
      (requires U64.v addr >= cursor)
      (ensures read_word (fst (flush_blue g first_blue run_words fp)) addr == read_word g addr)
    = assert (U64.v addr >= U64.v first_blue - U64.v mword + run_words * U64.v mword);
      flush_blue_preserves_outside g first_blue run_words fp addr
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let makeHeader_bridge wz c tag =
  makeHeader_is_pack_header64 wz c tag;
  GC.Impl.Object.makeHeader_eq_pack_header wz c tag;
  U64.v_inj (GC.Impl.Object.makeHeader wz c tag) (makeHeader wz c tag)
#pop-options

#push-options "--z3rlimit 50 --fuel 2 --ifuel 0"
let set_field_1_eq_write_word g fb fp =
  hd_address_spec fb;
  // set_field g fb 1UL fp unfolds to:
  //   write_word g (U64.add (hd_address fb) (U64.mul mword 1UL)) fp
  // We need: U64.add (hd_address fb) (U64.mul mword 1UL) == fb
  // hd_address fb = fb - 8, so fb - 8 + 8 = fb
  assert (U64.v (U64.mul mword 1UL) = U64.v mword);
  assert (U64.v (U64.add (hd_address fb) (U64.mul mword 1UL)) = U64.v fb);
  U64.v_inj (U64.add (hd_address fb) (U64.mul mword 1UL)) fb
#pop-options

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let blue_step_coalesce_aux_eq g0 g start first_blue run_words fp =
  coalesce_step_blue g0 g start (objects start g0) first_blue run_words fp;
  let wz = getWosize (read_word g0 start) in
  let ws = U64.v wz in
  let obj = f_address start in
  let new_first : U64.t = if run_words = 0 then obj else first_blue in
  let new_rw = run_words + ws + 1 in
  let next_nat = U64.v start + (ws + 1) * U64.v mword in
  let tail_objs = Seq.tail (objects start g0) in
  // From step lemma + old invariant: transitivity
  assert (coalesce_aux g0 g tail_objs new_first new_rw fp == coalesce g0);
  // Alignment: start % 8 = 0 and (ws + 1) * 8 % 8 = 0
  FStar.Math.Lemmas.lemma_mod_plus (U64.v start) (ws + 1) (U64.v mword);
  // Run geometry
  f_address_spec start;
  assert (U64.v obj == U64.v start + U64.v mword);
  assert (new_rw > 0);
  // new_first properties
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
  // new_rw < pow2 54: from new_rw * 8 <= heap_size < pow2 57 = 8 * pow2 54
  assert (U64.v new_first - U64.v mword + new_rw * U64.v mword == next_nat);
  assert (next_nat <= heap_size);
  assert (U64.v new_first >= U64.v mword);
  assert (new_rw * U64.v mword <= next_nat);
  FStar.Math.Lemmas.lemma_div_le (new_rw * U64.v mword) heap_size (U64.v mword);
  FStar.Math.Lemmas.cancel_mul_div new_rw (U64.v mword);
  assert (new_rw <= heap_size / U64.v mword);
  // heap_size < pow2 57 = 8 * pow2 54, and heap_size is a multiple of 8
  // => heap_size / 8 < pow2 54
  FStar.Math.Lemmas.pow2_plus 3 54;
  assert (pow2 57 == U64.v mword * pow2 54);
  FStar.Math.Lemmas.lemma_div_exact heap_size (U64.v mword);
  // heap_size = 8 * (heap_size / 8) and heap_size < 8 * pow2 54
  // => heap_size / 8 < pow2 54
  assert (heap_size == U64.v mword * (heap_size / U64.v mword));
  assert (U64.v mword * (heap_size / U64.v mword) < U64.v mword * pow2 54);
  // next_nat + 8 < pow2 64: next_nat <= heap_size < pow2 57, 8 <= pow2 57, pow2 58 < pow2 64
  FStar.Math.Lemmas.pow2_le_compat 57 3;
  FStar.Math.Lemmas.pow2_double_sum 57;
  FStar.Math.Lemmas.pow2_lt_compat 64 58;
  // Seq.equal → == for both cases
  if next_nat < heap_size then begin
    Seq.lemma_eq_elim tail_objs (objects (U64.uint_to_t next_nat) g0);
    assert (tail_objs == objects (U64.uint_to_t next_nat) g0)
  end;
  if next_nat >= heap_size then begin
    Seq.lemma_eq_elim tail_objs (Seq.empty #obj_addr);
    assert (tail_objs == Seq.empty #obj_addr)
  end
#pop-options

/// Top-level suffix chain: composes flush_blue_preserves_outside (for specific addr)
/// with g→g0 suffix to get g'→g0 suffix.
/// Avoids universals that fail to instantiate with --split_queries always.
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
      let (g', _) = flush_blue g first_blue run_words fp in
      read_word g' addr == read_word g0 addr))
  = // Call the pointwise lemma (no universal in postcondition)
    flush_blue_preserves_outside g first_blue run_words fp addr;
    assert (read_word (fst (flush_blue g first_blue run_words fp)) addr == read_word g addr)
#pop-options

#push-options "--z3rlimit 400 --fuel 2 --ifuel 1"
let white_step_coalesce_aux_eq g0 g start first_blue run_words fp =
  coalesce_step_white g0 g start (objects start g0) first_blue run_words fp;
  let wz = getWosize (read_word g0 start) in
  let ws = U64.v wz in
  let (g', fp') = flush_blue g first_blue run_words fp in
  let next_nat = U64.v start + (ws + 1) * U64.v mword in
  let tail_objs = Seq.tail (objects start g0) in
  // From step lemma + old invariant: transitivity
  assert (coalesce_aux g0 g' tail_objs 0UL 0 fp' == coalesce g0);
  // Alignment: start % 8 = 0 and (ws + 1) * 8 % 8 = 0
  FStar.Math.Lemmas.lemma_mod_plus (U64.v start) (ws + 1) (U64.v mword);
  // Heap length preservation
  flush_blue_length g first_blue run_words fp;
  assert (Seq.length g' == heap_size);
  // Build chained suffix: forall addr >= next_nat. read_word g' addr == read_word g0 addr
  // Uses top-level helper to avoid local-function scoping issues with --split_queries
  let chain (addr: hp_addr) : Lemma
    (requires U64.v addr >= next_nat)
    (ensures read_word g' addr == read_word g0 addr)
  = flush_blue_suffix_chain g0 g first_blue run_words fp (U64.v start) addr
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires chain);
  // next_nat + 8 < pow2 64: from next_nat <= heap_size < pow2 57
  assert (next_nat <= heap_size);
  FStar.Math.Lemmas.pow2_le_compat 57 3;
  assert (U64.v mword <= pow2 57);
  FStar.Math.Lemmas.pow2_double_sum 57;
  assert (pow2 57 + pow2 57 = pow2 58);
  FStar.Math.Lemmas.pow2_lt_compat 64 58;
  assert (pow2 58 < pow2 64);
  // Seq.equal → == for both cases
  if next_nat < heap_size then begin
    Seq.lemma_eq_elim tail_objs (objects (U64.uint_to_t next_nat) g0);
    assert (tail_objs == objects (U64.uint_to_t next_nat) g0)
  end;
  if next_nat >= heap_size then begin
    Seq.lemma_eq_elim tail_objs (Seq.empty #obj_addr);
    assert (tail_objs == Seq.empty #obj_addr)
  end
#pop-options

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let flush_blue_impl_wz0 g fb fp g1 =
  hd_address_spec fb
#pop-options

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let flush_blue_impl_wz1 g fb fp g1 g2 =
  hd_address_spec fb;
  set_field_1_eq_write_word g1 fb fp
#pop-options

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let flush_blue_impl_wz_ge2 g fb wz fp g1 g2 g3 =
  hd_address_spec fb;
  set_field_1_eq_write_word g1 fb fp;
  // Show U64.add fb mword == U64.uint_to_t (U64.v fb + U64.v mword)
  assert (U64.v (U64.add fb mword) = U64.v fb + U64.v mword);
  U64.v_inj (U64.add fb mword) (U64.uint_to_t (U64.v fb + U64.v mword))
#pop-options
