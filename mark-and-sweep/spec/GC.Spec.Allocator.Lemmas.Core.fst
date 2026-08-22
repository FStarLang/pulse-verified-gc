(*
   GC.Spec.Allocator.Lemmas — Bridge proofs connecting the allocator to the GC.

   Main theorem: alloc_spec preserves well_formed_heap, so the GC can be
   called after any sequence of allocations.
*)
module GC.Spec.Allocator.Lemmas.Core

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Allocator.Lemmas.Header
open GC.Spec.Allocator.Lemmas.Split
open GC.Spec.Allocator.Lemmas.Part1
module AllocCommon = GC.Spec.Allocator.Lemmas.Common
open GC.Spec.Allocator.Lemmas.Common
module AllocChain = GC.Spec.Allocator.Lemmas.Chain
open GC.Spec.Allocator.Lemmas.Chain

/// Module-level default: all functions get z3rlimit 10 unless overridden
#push-options "--z3rlimit 10 --z3refresh"

/// Sections 1-4 moved to GC.Spec.Allocator.Lemmas.Header
/// Sections 5-7 moved to GC.Spec.Allocator.Lemmas.Split
/// Section P1 moved to GC.Spec.Allocator.Lemmas.Part1
/// Re-export vals required by our .fsti (from Header and Split sub-modules)
let make_header_getWosize = make_header_getWosize
/// ===========================================================================
/// Section 8: alloc_search preserves well_formed_heap
/// ===========================================================================

/// ===========================================================================
/// Section 9: Top-level theorem
/// ===========================================================================

let fl_chain_terminates_terminal = AllocChain.fl_chain_terminates_terminal
let fl_chain_terminates_step = AllocChain.fl_chain_terminates_step
let fl_chain_terminates_elim = AllocChain.fl_chain_terminates_elim
let fl_chain_terminates_valid_zero = AllocChain.fl_chain_terminates_valid_zero
/// ===========================================================================
/// Section 9b: alloc_spec preserves objects membership
/// ===========================================================================

/// (Moved to GC.Spec.Allocator.Lemmas.Chain)

/// ===========================================================================
/// Section P1-search: alloc_search preserves objects under part1
/// (Moved from Part1.fst since it needs fl_valid defined in this module)
/// ===========================================================================

#restart-solver

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let rec alloc_search_preserves_objects_part1
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    fl_valid g cur_fp fuel /\
                    fl_chain_terminates g cur_fp fuel /\
                    (prev_fp <> 0UL ==>
                      (prev_fp <> cur_fp /\
                       U64.v prev_fp >= U64.v mword /\
                       U64.v prev_fp < heap_size /\
                       U64.v prev_fp % U64.v mword = 0 /\
                       Seq.mem prev_fp (objects zero_addr g) /\
                       U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1)))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                      Seq.mem x (objects zero_addr r.heap_out))))
          (decreases fuel)
  = if fuel = 0 then ()
    else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
    else if U64.v cur_fp >= heap_size then ()
    else if U64.v cur_fp % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = cur_fp in
      let hd = hd_address obj in
      let hdr = read_word g hd in
      let block_wz = U64.v (getWosize hdr) in
      hd_address_spec obj;
      hd_address_bounds obj;
      fl_valid_gives_mem g cur_fp fuel;
      fl_valid_gives_wosize g cur_fp fuel;
      assert (Seq.mem obj (objects zero_addr g));
      let next_fp =
        if U64.v hd + 16 <= heap_size then read_word g obj
        else 0UL
      in
      if block_wz >= wz then begin
        // Found a suitable block
        alloc_from_block_objects_facts_part1 g obj wz next_fp;
        let (g', new_fp) = alloc_from_block g obj wz next_fp in
        if prev_fp = 0UL then ()
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          let prev : obj_addr = prev_fp in
          assert (Seq.mem prev (objects zero_addr g'));
          wosize_of_object_spec prev g;
          wosize_of_object_bound prev g;
          hd_address_spec prev;
          if block_wz - wz >= 2 then begin
            let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
            if U64.v prev < U64.v obj then begin
              objects_separated zero_addr g prev obj;
              assert (U64.v (hd_address prev) < U64.v hd);
              alloc_split_g3_agrees_part1 g obj wz next_fp (hd_address prev)
            end else begin
              wosize_of_object_spec obj g;
              objects_separated zero_addr g obj prev;
              assert (U64.v (hd_address prev) > U64.v hd + block_wz * 8);
              assert (U64.v (hd_address prev) <> U64.v hd);
              assert (U64.v (hd_address prev) <> rem_hd_nat);
              assert (U64.v (hd_address prev) <> rem_hd_nat + 8);
              alloc_split_g3_agrees_part1 g obj wz next_fp (hd_address prev)
            end
          end else begin
            assert (prev <> obj);
            if U64.v prev < U64.v obj then
              objects_separated zero_addr g prev obj
            else
              objects_separated zero_addr g obj prev;
            let alloc_hdr = make_header (U64.uint_to_t block_wz) white_bits 0UL in
            alloc_from_block_exact g obj wz next_fp;
            read_write_different g hd (hd_address prev) alloc_hdr
          end;
          wosize_of_object_spec prev g';
          assert (wosize_of_object prev g' == wosize_of_object prev g);
          assert (U64.v (wosize_of_object prev g') >= 1);
          write_body_preserves_objects_local zero_addr g' prev (prev <: hp_addr) new_fp
        end
        else ()
      end
      else begin
        fl_valid_elim g cur_fp fuel;
        assert (cur_fp <> next_fp);
        if U64.v hd + 16 <= heap_size then
          fl_chain_terminates_elim g cur_fp fuel
        else ();
        alloc_search_preserves_objects_part1 g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

/// (Moved to GC.Spec.Allocator.Lemmas.Chain)

/// ===========================================================================
/// Section F: alloc_search preserves fl_valid
/// ===========================================================================

/// ===========================================================================
/// Section G: Top-level theorem — alloc_spec preserves fl_valid
/// ===========================================================================

let chain_avoids_head_ne = AllocChain.chain_avoids_head_ne
let chain_avoids_tail = AllocChain.chain_avoids_tail
let chain_avoids_transfer = AllocChain.chain_avoids_transfer
let chain_avoids_transfer_on_chain = AllocChain.chain_avoids_transfer_on_chain
/// ===========================================================================
/// Section G1b: alloc_spec preserves fl_chain_terminates
/// ===========================================================================
/// Section G2: Top-level theorem — alloc_spec preserves objects membership
/// ===========================================================================

/// ===========================================================================
/// Section H: alloc_spec preserves no_black_objects
/// ===========================================================================

module Header = GC.Lib.Header
open GC.Spec.Mark

/// ---------------------------------------------------------------------------
/// Helper: make_header get_color roundtrip
/// ---------------------------------------------------------------------------

/// The color bits of make_header faithfully store the given color value
#restart-solver

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let make_header_getColor (wz: U64.t{U64.v wz < pow2 54})
                                  (c: U64.t{U64.v c < 4})
                                  (t: U64.t{U64.v t < 256})
  : Lemma (Header.get_color (U64.v (make_header wz c t)) == U64.v c)
  = let hdr = make_header wz c t in
    make_header_value wz c t;
    Header.get_color_val (U64.v hdr);
    FStar.UInt.shift_right_value_lemma #64 (U64.v hdr) 8;
    assert_norm (pow2 8 = 256);
    FStar.Math.Lemmas.lemma_div_plus (U64.v c * 256 + U64.v t) (U64.v wz * 4) 256;
    FStar.Math.Lemmas.lemma_div_plus (U64.v t) (U64.v c) 256;
    FStar.Math.Lemmas.small_div (U64.v t) 256;
    FStar.UInt.logand_mask #64 (U64.v wz * 4 + U64.v c) 2;
    assert_norm (pow2 2 - 1 = 3);
    FStar.Math.Lemmas.lemma_mod_plus (U64.v c) (U64.v wz) 4;
    FStar.Math.Lemmas.small_mod (U64.v c) 4
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: field write preserves no_black_objects
/// ---------------------------------------------------------------------------

/// ---------------------------------------------------------------------------
/// Top-level: alloc_spec preserves no_black_objects
/// ---------------------------------------------------------------------------

/// ===========================================================================
/// Section I: alloc_spec removes obj_out from the chain
/// ===========================================================================

/// ---------------------------------------------------------------------------
/// Keep Core as a compatibility re-export.
/// ---------------------------------------------------------------------------

let chain_avoids_transfer_excl2 = AllocChain.chain_avoids_transfer_excl2
/// alloc_spec preserves objects membership under part1
let alloc_spec_preserves_objects_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    fl_valid g fp heap_words /\
                    fl_chain_terminates g fp heap_words)
          (ensures (let r = alloc_spec g fp requested_wz in
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                      Seq.mem x (objects zero_addr r.heap_out))))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_preserves_objects_part1 g fp 0UL fp wz heap_words
