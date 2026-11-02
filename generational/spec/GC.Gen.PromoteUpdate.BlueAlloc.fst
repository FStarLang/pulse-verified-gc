/// ---------------------------------------------------------------------------
/// GC.Gen.PromoteUpdate.BlueAlloc — alloc preserves the free-list shape
/// ---------------------------------------------------------------------------

module GC.Gen.PromoteUpdate.BlueAlloc

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Reachability
open GC.Gen.Remembered
open GC.Gen.Promote
open GC.Gen.WriteBodyLemmas
open GC.Gen.PromoteUpdate.Aux
open GC.Gen.PromoteUpdate.Header

module AllocLemmas = GC.Spec.Allocator.Lemmas
module FreeListShape = GC.Gen.FreeListShape
module WriteBody = GC.Gen.WriteBodyLemmas

/// The allocator's output free-list head is null or a syntactically valid heap
/// pointer when all blue free-list link fields have that same value shape.
/// The predecessor cell lies entirely outside the block being carved up.
/// Trivial from `objects_separated`, but the call sites are deep inside
/// closures nested in a recursive proof, where the query is large enough that
/// Z3 will not find it; discharged here where the context is empty.
#push-options "--z3rlimit 30 --fuel 1 --ifuel 0"
private let block_prev_separated (g: heap) (obj prev: obj_addr) (bwz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem (obj <: U64.t) (objects zero_addr g) /\
                    Seq.mem (prev <: U64.t) (objects zero_addr g) /\
                    (prev <: U64.t) <> (obj <: U64.t) /\
                    U64.v (getWosize (read_word g (hd_address obj))) == bwz)
          (ensures U64.v prev + 8 <= U64.v obj \/
                   U64.v prev > U64.v obj + bwz * 8)
  = hd_address_spec obj;
    hd_address_bounds obj;
    hd_address_spec prev;
    hd_address_bounds prev;
    wosize_of_object_spec obj g;
    wosize_of_object_spec prev g;
    wosize_of_object_bound prev g;
    if U64.v prev < U64.v obj then objects_separated zero_addr g prev obj
    else objects_separated zero_addr g obj prev
#pop-options


/// The same, sharpened by `prev` having at least one field: then its header
/// and link both sit a full word below the block's header.
#push-options "--z3rlimit 30 --fuel 1 --ifuel 0"
private let block_prev_separated_body (g: heap) (obj prev: obj_addr) (bwz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem (obj <: U64.t) (objects zero_addr g) /\
                    Seq.mem (prev <: U64.t) (objects zero_addr g) /\
                    (prev <: U64.t) <> (obj <: U64.t) /\
                    U64.v (wosize_of_object prev g) >= 1 /\
                    U64.v (getWosize (read_word g (hd_address obj))) == bwz)
          (ensures U64.v prev + 8 <= U64.v (hd_address obj) \/
                   U64.v prev > U64.v obj + bwz * 8)
  = hd_address_spec obj;
    hd_address_bounds obj;
    hd_address_spec prev;
    hd_address_bounds prev;
    wosize_of_object_spec obj g;
    wosize_of_object_spec prev g;
    wosize_of_object_bound prev g;
    if U64.v prev < U64.v obj then objects_separated zero_addr g prev obj
    else objects_separated zero_addr g obj prev
#pop-options

#push-options "--z3rlimit 12 --fuel 1 --ifuel 0"
private let alloc_from_block_fp_pointer_or_zero
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires
      well_formed_heap_part1 g /\
      Seq.mem obj (objects zero_addr g) /\
      is_blue obj g /\
      FreeListShape.blue_link_fields_valid g /\
      FreeListShape.fp_pointer_or_zero next_fp /\
      wz >= 1 /\
      U64.v (getWosize (read_word g (hd_address obj))) >= wz /\
      U64.v (wosize_of_object obj g) >= 1 /\
      U64.v (hd_address obj) + 16 <= heap_size)
    (ensures
      FreeListShape.fp_pointer_or_zero
        (snd (GC.Spec.Allocator.alloc_from_block g obj wz next_fp)))
  = let hd = hd_address obj in
    hd_address_spec obj;
    hd_address_bounds obj;
    wosize_of_object_spec obj g;
    // Right-justification makes this immediate: the block's replacement in
    // the free list is either the block ITSELF -- still a perfectly good
    // object address, since the remainder keeps it -- or the old link, which
    // the hypothesis already covers.
    GC.Spec.Allocator.alloc_replacement_fp_eq g obj wz next_fp;
    objects_addresses_gt_start zero_addr g obj;
    assert (FreeListShape.fp_pointer_or_zero (obj <: U64.t))
#pop-options

#push-options "--z3rlimit 12 --fuel 1 --ifuel 0"
private let rec alloc_search_fp_pointer_or_zero
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires
      well_formed_heap_part1 g /\
      AllocLemmas.fl_valid g cur_fp fuel /\
      AllocLemmas.fl_chain_terminates g cur_fp fuel /\
      FreeListShape.blue_link_fields_valid g /\
      FreeListShape.fp_pointer_or_zero head_fp /\
      wz >= 1 /\
      (GC.Spec.Allocator.alloc_search g head_fp prev_fp cur_fp wz fuel).obj_out <> 0UL /\
      (forall (obj: obj_addr). Seq.mem obj (objects zero_addr g) /\ is_blue obj g = false ==>
        AllocLemmas.chain_avoids g cur_fp obj fuel = true) /\
      (prev_fp <> 0UL ==>
        (prev_fp <> cur_fp /\
         U64.v prev_fp >= U64.v mword /\ U64.v prev_fp < heap_size /\
         U64.v prev_fp % U64.v mword = 0 /\
         Seq.mem prev_fp (objects zero_addr g) /\
         U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1 /\
         is_blue (prev_fp <: obj_addr) g)))
    (ensures
      FreeListShape.fp_pointer_or_zero
        (GC.Spec.Allocator.alloc_search g head_fp prev_fp cur_fp wz fuel).fp_out)
    (decreases fuel)
  =
    if fuel = 0 then ()
    else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
    else if U64.v cur_fp >= heap_size then ()
    else if U64.v cur_fp % U64.v mword <> 0 then ()
    else begin
      assert (U64.v cur_fp >= U64.v mword /\
              U64.v cur_fp < heap_size /\
              U64.v cur_fp % U64.v mword == 0);
      let obj : obj_addr = cur_fp in
      let hd = hd_address obj in
      hd_address_spec obj;
      hd_address_bounds obj;
      let hdr = read_word g hd in
      let bwz = U64.v (getWosize hdr) in
      let next_fp = if U64.v hd + 16 <= heap_size then read_word g obj else 0UL in
      AllocLemmas.fl_valid_elim g cur_fp fuel;
      AllocLemmas.fl_valid_gives_mem g cur_fp fuel;
      AllocLemmas.fl_valid_gives_wosize g cur_fp fuel;
      wosize_of_object_spec obj g;
      wfh_part1_obj_bound g obj;
      assert (U64.v (hd_address obj) + 16 <= heap_size);

      if not (is_blue obj g) then
        AllocLemmas.chain_avoids_head_ne g cur_fp (obj <: U64.t) fuel
      else if bwz >= wz then begin
        // `fp_out` is either `head_fp`, which the precondition covers, or the
        // block's replacement -- and that case no longer lines up with
        // `prev_fp = 0` alone: an unusable predecessor takes the same arm.
        FreeListShape.blue_link_fields_valid_elim g obj;
        assert (FreeListShape.fp_pointer_or_zero next_fp);
        GC.Spec.Allocator.alloc_replacement_fp_eq g obj wz next_fp;
        alloc_from_block_fp_pointer_or_zero g obj wz next_fp
      end else begin
        AllocLemmas.fl_chain_terminates_elim g cur_fp fuel;
        let chain_blue_next (nobj: obj_addr)
          : Lemma (requires Seq.mem nobj (objects zero_addr g) /\ is_blue nobj g = false)
                  (ensures AllocLemmas.chain_avoids g next_fp nobj (fuel - 1) = true)
          = AllocLemmas.chain_avoids_tail g cur_fp nobj fuel
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires chain_blue_next);
        alloc_search_fp_pointer_or_zero g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let alloc_spec_preserves_fp_pointer_or_zero
  (g: heap) (fp: U64.t) (wz: nat)
  =
    let fuel = heap_words in
    let chain_avoids_non_blue (obj: obj_addr)
      : Lemma (requires Seq.mem obj (objects zero_addr g) /\ is_blue obj g = false)
              (ensures AllocLemmas.chain_avoids g fp obj fuel = true)
      = reveal_opaque (`%chain_objects_blue) chain_objects_blue
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires chain_avoids_non_blue);
    alloc_search_fp_pointer_or_zero g fp 0UL fp wz fuel
#pop-options

#push-options "--z3rlimit 150 --fuel 1 --ifuel 0"
private let rec alloc_search_preserves_blfv
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma
    (requires
      well_formed_heap_part1 g /\
      AllocLemmas.fl_valid g cur_fp fuel /\
      AllocLemmas.fl_chain_terminates g cur_fp fuel /\
      FreeListShape.blue_link_fields_valid g /\
      wz >= 1 /\
      (GC.Spec.Allocator.alloc_search g head_fp prev_fp cur_fp wz fuel).obj_out <> 0UL /\
      (forall (obj: obj_addr). Seq.mem obj (objects zero_addr g) /\ is_blue obj g = false ==>
        AllocLemmas.chain_avoids g cur_fp obj fuel = true) /\
      (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
        Seq.mem x (objects zero_addr (GC.Spec.Allocator.alloc_search g head_fp prev_fp cur_fp wz fuel).heap_out)) /\
      (prev_fp <> 0UL ==>
        (prev_fp <> cur_fp /\
         U64.v prev_fp >= U64.v mword /\ U64.v prev_fp < heap_size /\
         U64.v prev_fp % U64.v mword = 0 /\
         Seq.mem prev_fp (objects zero_addr g) /\
         U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1 /\
         is_blue (prev_fp <: obj_addr) g)))
    (ensures
      FreeListShape.blue_link_fields_valid
        (GC.Spec.Allocator.alloc_search g head_fp prev_fp cur_fp wz fuel).heap_out)
    (decreases fuel)
  =
    let open GC.Spec.Allocator in
    if fuel = 0 then ()
    else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
    else if U64.v cur_fp >= heap_size then ()
    else if U64.v cur_fp % U64.v mword <> 0 then ()
    else begin
      assert (U64.v cur_fp >= U64.v mword /\ U64.v cur_fp < heap_size /\ U64.v cur_fp % U64.v mword == 0);
      let obj : obj_addr = cur_fp in
      let hd = hd_address obj in
      hd_address_spec obj;
      hd_address_bounds obj;
      let hdr = read_word g hd in
      let bwz = U64.v (getWosize hdr) in
      let next_fp = if U64.v hd + 16 <= heap_size then read_word g obj else 0UL in
      AllocLemmas.fl_valid_elim g cur_fp fuel;
      AllocLemmas.fl_valid_gives_mem g cur_fp fuel;
      AllocLemmas.fl_valid_gives_wosize g cur_fp fuel;
      wosize_of_object_spec obj g;
      wfh_part1_obj_bound g obj;
      assert (U64.v (hd_address obj) + 16 <= heap_size);

      if not (is_blue obj g) then
        AllocLemmas.chain_avoids_head_ne g cur_fp (obj <: U64.t) fuel
      else if bwz >= wz then begin
        let leftover = bwz - wz in
        let ahn = U64.v hd + leftover * 8 in
        if ahn + 8 >= heap_size || ahn >= pow2 64 || ahn % 8 <> 0 then
          GC.Spec.Allocator.alloc_search_found_oob g head_fp prev_fp cur_fp wz fuel
        else begin
        wosize_of_object_spec obj g;
        wfh_part1_obj_bound g obj;
        let new_rem_fp = GC.Spec.Allocator.alloc_replacement_fp g obj wz next_fp in
        GC.Spec.Allocator.alloc_replacement_fp_eq g obj wz next_fp;
        let prev_usable =
          prev_fp <> 0UL && U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
          U64.v prev_fp % U64.v mword = 0 && U64.v prev_fp <> U64.v hd in
        let base = if prev_usable then write_word g (prev_fp <: hp_addr) new_rem_fp else g in
        (if prev_usable then begin
           let prev_obj : obj_addr = prev_fp in
           hd_address_spec prev_obj;
           hd_address_bounds prev_obj;
           wosize_of_object_spec prev_obj g;
           wosize_of_object_bound prev_obj g;
           AllocLemmas.write_body_preserves_wfh_part1
             g prev_obj (prev_obj <: hp_addr) new_rem_fp;
           AllocLemmas.write_body_preserves_objects_local
             zero_addr g prev_obj (prev_obj <: hp_addr) new_rem_fp;
           read_write_different g (prev_obj <: hp_addr) hd new_rem_fp
         end else ());
        assert (well_formed_heap_part1 base);
        assert (objects zero_addr base == objects zero_addr g);
        assert (read_word base hd == hdr);
        let heap_out = fst (alloc_from_block base obj wz next_fp) in
        assert (heap_out == (alloc_search g head_fp prev_fp cur_fp wz fuel).heap_out);
        FreeListShape.blue_link_fields_valid_elim g obj;
        assert (FreeListShape.fp_pointer_or_zero next_fp);
        alloc_from_block_fp_pointer_or_zero g obj wz next_fp;
        AllocLemmas.alloc_from_block_objects_facts_part1 base obj wz next_fp;

        let blfv_proof (src: obj_addr)
          : Lemma (requires Seq.mem src (objects zero_addr heap_out) /\
                            is_blue src heap_out /\
                            U64.v (wosize_of_object src heap_out) >= 1 /\
                            U64.v (hd_address src) + 16 <= heap_size)
                  (ensures (let v = read_word heap_out src in
                            FreeListShape.fp_pointer_or_zero v))
          = // the only object allocation creates is the allocated block, and
            // that one is white, so a BLUE `src` was already there
            (if not (Seq.mem (src <: U64.t) (objects zero_addr base)) then begin
               GC.Gen.AllocProps.alloc_from_block_obj_not_blue base obj wz next_fp;
               AllocLemmas.alloc_from_block_objects_backward_part1 base obj wz next_fp src;
               f_address_spec (mk_hp_addr ahn);
               is_blue_iff src heap_out;
               assert False
             end else ());
            assert (Seq.mem (src <: U64.t) (objects zero_addr g));
            hd_address_spec src;
            hd_address_bounds src;
            wosize_of_object_spec src g;
            wosize_of_object_spec obj g;
            if (src <: U64.t) = (obj <: U64.t) then begin
              // `src` IS the block.  At leftover = 0 its header turns white,
              // at leftover = 1 the remainder has wosize 0 -- both excluded by
              // the hypotheses -- so it is the blue remainder, and its link
              // word is the one the allocation deliberately leaves alone.
              (if leftover = 0 then begin
                 GC.Spec.Allocator.alloc_from_block_exact base obj wz next_fp;
                 let ahdr0 = make_header (U64.uint_to_t wz) white_bits 0UL in
                 AllocLemmas.make_header_getColor (U64.uint_to_t wz) white_bits 0UL;
                 getColor_raw ahdr0;
                 read_write_same base hd ahdr0;
                 color_of_object_spec src heap_out;
                 is_blue_iff src heap_out;
                 assert False
               end else ());
              assert (leftover >= 1);
              GC.Spec.Allocator.alloc_from_block_split_normal base obj wz next_fp;
              let rhdr = make_header (U64.uint_to_t (leftover - 1)) blue_bits 0UL in
              let ahdr = make_header (U64.uint_to_t wz) white_bits 0UL in
              let b1 = write_word base hd rhdr in
              let ah : hp_addr = U64.uint_to_t ahn in
              assert (heap_out == write_word b1 ah ahdr);
              read_write_different b1 ah hd ahdr;
              read_write_same base hd rhdr;
              AllocLemmas.make_header_getWosize
                (U64.uint_to_t (leftover - 1)) blue_bits 0UL;
              wosize_of_object_spec src heap_out;
              assert (U64.v (wosize_of_object src heap_out) == leftover - 1);
              assert (leftover >= 2);
              // the link word sits strictly below the allocated header
              assert (U64.v (src <: U64.t) + 8 <= ahn);
              read_write_different b1 ah (src <: hp_addr) ahdr;
              read_write_different base hd (src <: hp_addr) rhdr;
              (if prev_usable then begin
                 let prev_obj : obj_addr = prev_fp in
                 block_prev_separated_body g obj prev_obj bwz;
                 assert (bwz >= 1);
                 read_write_different g (prev_obj <: hp_addr) (src <: hp_addr) new_rem_fp
               end else ());
              assert (read_word heap_out src == read_word g src);
              FreeListShape.blue_link_fields_valid_elim g obj
            end
            else begin
              // A different object: both header writes miss it; only the prev
              // link can touch its field 0, and that value is fine by the
              // block-level lemma above.
              wosize_of_object_bound src g;
              block_prev_separated g obj src bwz;
              GC.Gen.AllocProps.alloc_from_block_read_frame
                base obj wz next_fp (hd_address src);
              (if prev_usable then begin
                 let prev_obj : obj_addr = prev_fp in
                 hd_address_spec prev_obj;
                 hd_address_bounds prev_obj;
                 wosize_of_object_spec prev_obj g;
                 wosize_of_object_bound prev_obj g;
                 (if (src <: U64.t) = prev_fp then ()
                  else if U64.v src < U64.v prev_fp then
                    objects_separated zero_addr g src prev_obj
                  else
                    objects_separated zero_addr g prev_obj src);
                 read_write_different g (prev_obj <: hp_addr) (hd_address src) new_rem_fp
               end else ());
              wosize_of_object_spec src heap_out;
              color_of_header_eq src heap_out g;
              is_blue_iff src g;
              is_blue_iff src heap_out;
              assert (U64.v (wosize_of_object src g) >= 1);
              // with a field of its own, `src`'s link word is a full word
              // clear of the block, so the header writes miss it too
              block_prev_separated_body g obj src bwz;
              GC.Gen.AllocProps.alloc_from_block_read_frame base obj wz next_fp (src <: hp_addr);
              if prev_usable && (src <: U64.t) = prev_fp then begin
                read_write_same g (prev_fp <: hp_addr) new_rem_fp;
                assert (read_word heap_out src == new_rem_fp)
              end else begin
                (if prev_usable then begin
                   let prev_obj : obj_addr = prev_fp in
                   (if U64.v src < U64.v prev_fp then
                      objects_separated zero_addr g src prev_obj
                    else
                      objects_separated zero_addr g prev_obj src);
                   read_write_different g (prev_obj <: hp_addr) (src <: hp_addr) new_rem_fp
                 end else ());
                assert (read_word heap_out src == read_word g src);
                FreeListShape.blue_link_fields_valid_elim g src
              end
            end
        in
        FreeListShape.blue_link_fields_valid_intro heap_out blfv_proof
        end
      end else begin
        AllocLemmas.fl_chain_terminates_elim g cur_fp fuel;
        let chain_blue_next (nobj: obj_addr)
          : Lemma (requires Seq.mem nobj (objects zero_addr g) /\ is_blue nobj g = false)
                  (ensures AllocLemmas.chain_avoids g next_fp nobj (fuel - 1) = true)
          = AllocLemmas.chain_avoids_tail g cur_fp nobj fuel
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires chain_blue_next);
        alloc_search_preserves_blfv g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let alloc_spec_preserves_blue_link_fields_valid
  (g: heap) (fp: U64.t) (wz: nat)
  =
    let fuel = heap_words in
    AllocLemmas.alloc_spec_preserves_objects_part1 g fp wz;
    let chain_avoids_non_blue (obj: obj_addr)
      : Lemma (requires Seq.mem obj (objects zero_addr g) /\ is_blue obj g = false)
              (ensures AllocLemmas.chain_avoids g fp obj fuel = true)
      = reveal_opaque (`%chain_objects_blue) chain_objects_blue
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires chain_avoids_non_blue);
    alloc_search_preserves_blfv g fp 0UL fp wz fuel
#pop-options
