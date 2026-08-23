(*
   Pure F* bridge lemmas for the coalesce implementation.
*)

module GC.Impl.Coalesce.Lemmas

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Coalesce
module Alloc = GC.Spec.Allocator
module HeapGraph = GC.Spec.HeapGraph

#set-options "--z3rlimit 25 --fuel 2 --ifuel 1"
module Header = GC.Lib.Header

/// Objects walk produces nonempty + advance
#push-options "--z3rlimit 25 --fuel 2 --ifuel 1"
let objects_advance start g =
  let hdr = read_word g start in
  let wz = getWosize hdr in
  let next_nat = U64.v start + (U64.v wz + 1) * U64.v mword in
  assert (next_nat <= heap_size);
  assert (heap_size < pow2 64)
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
let objects_mem_at_zero g =
  objects_nonempty_head zero_addr g;
  let objs = objects zero_addr g in
  Seq.Properties.cons_head_tail objs;
  Seq.Properties.mem_cons (f_address zero_addr) (Seq.tail objs)
#pop-options

#push-options "--z3rlimit 25 --fuel 2 --ifuel 0"
let zero_fields_step g addr n = ()
#pop-options

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
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

#push-options "--z3rlimit 12 --fuel 2 --ifuel 0"
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

/// Top-level suffix chain: composes flush_blue_preserves_outside (for specific addr)
/// with g→g0 suffix to get g'→g0 suffix.
/// Avoids universals that fail to instantiate with --split_queries always.
#push-options "--z3rlimit 25 --fuel 2 --ifuel 1"
let flush_blue_impl_wz0 g fb fp g1 =
  hd_address_spec fb
#pop-options

#push-options "--z3rlimit 25 --fuel 2 --ifuel 1"
let flush_blue_impl_wz1 g fb fp g1 g2 =
  hd_address_spec fb;
  set_field_1_eq_write_word g1 fb fp
#pop-options

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let flush_blue_impl_wz_ge2 g fb wz fp g1 g2 g3 =
  hd_address_spec fb;
  set_field_1_eq_write_word g1 fb fp;
  // Show U64.add fb mword == U64.uint_to_t (U64.v fb + U64.v mword)
  assert (U64.v (U64.add fb mword) = U64.v fb + U64.v mword);
  U64.v_inj (U64.add fb mword) (U64.uint_to_t (U64.v fb + U64.v mword))
#pop-options
