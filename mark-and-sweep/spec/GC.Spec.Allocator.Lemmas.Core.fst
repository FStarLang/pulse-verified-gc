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
module AllocSearchBase = GC.Spec.Allocator.Lemmas.SearchBase
open GC.Spec.Allocator.Lemmas.SearchBase
module AllocSearchChain = GC.Spec.Allocator.Lemmas.SearchChain

/// Module-level default: all functions get z3rlimit 20 unless overridden
#push-options "--z3rlimit 20 --z3refresh"

/// Sections 1-4 moved to GC.Spec.Allocator.Lemmas.Header
/// Sections 5-7 moved to GC.Spec.Allocator.Lemmas.Split
/// Section P1 moved to GC.Spec.Allocator.Lemmas.Part1
/// Re-export vals required by our .fsti (from Header and Split sub-modules)
let make_header_getWosize = make_header_getWosize
let make_header_getTag = make_header_getTag
let alloc_from_block_preserves_wf = alloc_from_block_preserves_wf

/// ===========================================================================
/// Section 8: alloc_search preserves well_formed_heap
/// ===========================================================================
/// Shared search helpers moved to SearchBase.
let next_fp_in_objects = AllocSearchBase.next_fp_in_objects
let alloc_from_block_objects_facts = AllocSearchBase.alloc_from_block_objects_facts

#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
let rec alloc_search_preserves_wf
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires well_formed_heap g /\
                    fl_valid g cur_fp fuel /\
                    (prev_fp <> 0UL ==>
                      (prev_fp <> cur_fp /\
                       U64.v prev_fp >= U64.v mword /\
                       U64.v prev_fp < heap_size /\
                       U64.v prev_fp % U64.v mword = 0 /\
                       Seq.mem prev_fp (objects zero_addr g) /\
                       U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1)))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    well_formed_heap r.heap_out))
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
      assert (U64.v (wosize_of_object obj g) >= 1);
      let next_fp =
        if U64.v hd + 16 <= heap_size then read_word g obj
        else 0UL
      in
      if block_wz >= wz then begin
        // Found: alloc_from_block preserves wf
        if U64.v hd + 16 <= heap_size then
          next_fp_in_objects g obj;
        alloc_from_block_preserves_wf g obj wz next_fp;
        let (g', new_fp) = alloc_from_block g obj wz next_fp in
        // Handle prev_fp update
        if prev_fp = 0UL then ()
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          let prev : obj_addr = prev_fp in
          // prev ∈ objects(0, g') (old objects preserved)
          alloc_from_block_objects_facts g obj wz next_fp;
          assert (Seq.mem prev (objects zero_addr g'));
          // wosize(prev, g) >= 1 from precondition
          assert (U64.v (wosize_of_object prev g) >= 1);
          wosize_of_object_spec prev g;
          wosize_of_object_bound prev g;
          wf_object_size_bound g prev;
          // wosize(prev, g') = wosize(prev, g) since prev's header is unchanged
          hd_address_spec prev;
          wosize_of_object_spec obj g;
          // Show prev's header is unchanged from g to g'
          hd_address_spec prev;
          wosize_of_object_spec obj g;
          if block_wz - wz >= 2 then begin
            // Split case: 3 writes at hd, rem_hd, rem_obj
            let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
            let rem_obj_nat = rem_hd_nat + 8 in
            if U64.v prev < U64.v obj then begin
              objects_separated zero_addr g prev obj;
              assert (U64.v (hd_address prev) < U64.v hd);
              assert (rem_hd_nat > U64.v hd);
              assert (U64.v (hd_address prev) <> rem_hd_nat);
              assert (U64.v (hd_address prev) <> rem_obj_nat)
            end else begin
              objects_separated zero_addr g obj prev;
              assert (U64.v prev > U64.v obj + U64.v (wosize_of_object_as_wosize obj g) * 8);
              assert (U64.v (hd_address prev) > U64.v hd + block_wz * 8 - 8);
              assert (U64.v (hd_address prev) <> U64.v hd);
              assert (U64.v (hd_address prev) <> rem_hd_nat);
              assert (U64.v (hd_address prev) <> rem_obj_nat)
            end;
            alloc_split_g3_agrees g obj wz next_fp (hd_address prev)
          end else begin
            // Exact fit: only write at hd
            // prev ≠ obj from precondition (prev_fp <> cur_fp)
            assert (prev <> obj);
            if U64.v prev < U64.v obj then
              objects_separated zero_addr g prev obj
            else begin
              assert (U64.v prev > U64.v obj); // from prev ≠ obj
              objects_separated zero_addr g obj prev
            end;
            assert (U64.v (hd_address prev) <> U64.v hd);
            let alloc_hdr = make_header (U64.uint_to_t block_wz) white_bits 0UL in
            alloc_from_block_exact g obj wz next_fp;
            assert (fst (alloc_from_block g obj wz next_fp) == write_word g hd alloc_hdr);
            read_write_different g hd (hd_address prev) alloc_hdr
          end;
          wosize_of_object_spec prev g';
          assert (wosize_of_object prev g' == wosize_of_object prev g);
          // new_fp: either rem_fp (pointer) or 0UL
          // is_pointer_field new_fp ==> Seq.mem new_fp (objects zero_addr g')
          alloc_from_block_objects_facts g obj wz next_fp;
          // field_write_preserves_wf: prev ∈ objects(0,g'), addr=prev within body, new_fp ok
          field_write_preserves_wf g' prev (prev <: hp_addr) new_fp
        end
        else ()
      end
      else begin
        // Advance: same heap, recurse
        fl_valid_next g cur_fp fuel;
        // cur_fp ≠ next_fp: if hd+16>heap_size, next_fp=0UL≠cur_fp;
        // otherwise fl_valid_next gives read_word g obj ≠ cur_fp
        assert (cur_fp <> next_fp);
        // cur_fp becomes prev_fp; wosize(cur_fp, g) >= 1 from fl_valid_gives_wosize
        alloc_search_preserves_wf g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

/// ===========================================================================
/// Section 9: Top-level theorem
/// ===========================================================================

let alloc_spec_preserves_wf (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires well_formed_heap g /\
                    fl_valid g fp (heap_size / U64.v mword))
          (ensures (let r = alloc_spec g fp requested_wz in
                    well_formed_heap r.heap_out))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_preserves_wf g fp 0UL fp wz (heap_size / U64.v mword)

/// Re-export chain machinery required by Core.fsti (implemented in Chain)
let fl_valid_transfer = AllocChain.fl_valid_transfer
let fl_chain_terminates_terminal = AllocChain.fl_chain_terminates_terminal
let fl_valid_any_fuel = AllocChain.fl_valid_any_fuel
let fl_chain_terminates_transfer = AllocChain.fl_chain_terminates_transfer
let fl_chain_terminates_weaken = AllocChain.fl_chain_terminates_weaken
let fl_chain_terminates_step = AllocChain.fl_chain_terminates_step
let fl_chain_terminates_elim = AllocChain.fl_chain_terminates_elim
let fl_chain_terminates_valid_zero = AllocChain.fl_chain_terminates_valid_zero
let walk_chain_zero = AllocChain.walk_chain_zero
let walk_chain_valid_zero = AllocChain.walk_chain_valid_zero
let walk_chain_valid_prefix = AllocChain.walk_chain_valid_prefix
let walk_chain_valid_at = AllocChain.walk_chain_valid_at
let walk_chain_valid_snoc = AllocChain.walk_chain_valid_snoc
let walk_chain_append = AllocChain.walk_chain_append
let fl_chain_terminates_unfold_steps = AllocChain.fl_chain_terminates_unfold_steps
let fl_chain_kcycle_not_terminates = AllocChain.fl_chain_kcycle_not_terminates
let fl_chain_2cycle_not_terminates = AllocChain.fl_chain_2cycle_not_terminates
let fl_chain_terminates_splice = AllocChain.fl_chain_terminates_splice
let fl_valid_field_write = AllocChain.fl_valid_field_write
let fl_valid_field_write_tail = AllocChain.fl_valid_field_write_tail
/// ===========================================================================
/// Section 9b: alloc_spec preserves objects membership
/// ===========================================================================

#restart-solver
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
let rec alloc_search_preserves_objects
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires well_formed_heap g /\
                    fl_valid g cur_fp fuel /\
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
        if U64.v hd + 16 <= heap_size then
          next_fp_in_objects g obj;
        alloc_from_block_objects_facts g obj wz next_fp;
        let (g', new_fp) = alloc_from_block g obj wz next_fp in
        // alloc_from_block_objects_facts gives:
        //   forall h. mem h (objects 0 g) ==> mem h (objects 0 g')
        if prev_fp = 0UL then ()
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          // Need: objects 0 g2 == objects 0 g' where g2 = write_word g' prev_fp new_fp
          let prev : obj_addr = prev_fp in
          assert (Seq.mem prev (objects zero_addr g'));
          alloc_from_block_preserves_wf g obj wz next_fp;
          // prev ∈ objects(0, g') and wosize(prev, g') >= 1
          // write at prev_fp which is within [prev, prev + wosize*8)
          // since prev_fp == prev, addr = prev >= obj = prev ✓
          // and prev < prev + wosize*8 since wosize >= 1 ✓
          wosize_of_object_spec prev g;
          wosize_of_object_bound prev g;
          wf_object_size_bound g prev;
          hd_address_spec prev;
          // Need wosize(prev, g') == wosize(prev, g) — header unchanged
          if block_wz - wz >= 2 then begin
            let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
            if U64.v prev < U64.v obj then begin
              objects_separated zero_addr g prev obj;
              assert (U64.v (hd_address prev) < U64.v hd);
              alloc_split_g3_agrees g obj wz next_fp (hd_address prev)
            end else begin
              wosize_of_object_spec obj g;
              objects_separated zero_addr g obj prev;
              assert (U64.v (hd_address prev) > U64.v hd + block_wz * 8);
              assert (U64.v (hd_address prev) <> U64.v hd);
              assert (U64.v (hd_address prev) <> rem_hd_nat);
              assert (U64.v (hd_address prev) <> rem_hd_nat + 8);
              alloc_split_g3_agrees g obj wz next_fp (hd_address prev)
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
          // write_word_preserves_objects: writing within a field of prev preserves objects
          write_word_preserves_objects g' prev (prev <: hp_addr) new_fp
        end
        else ()
      end
      else begin
        fl_valid_next g cur_fp fuel;
        assert (cur_fp <> next_fp);
        alloc_search_preserves_objects g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

/// (Moved to GC.Spec.Allocator.Lemmas.Chain)

/// ===========================================================================
/// Section P1-search: alloc_search preserves objects under part1
/// (Moved from Part1.fst since it needs fl_valid defined in this module)
/// ===========================================================================

#restart-solver
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"
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

/// Shared transfer precondition helpers moved to SearchBase.
let alloc_split_fl_transfer_pre = AllocSearchBase.alloc_split_fl_transfer_pre
let alloc_exact_fl_transfer_pre = AllocSearchBase.alloc_exact_fl_transfer_pre


/// The main recursive proof: alloc_search preserves fl_valid.
#restart-solver
#push-options "--z3rlimit 400 --fuel 1 --ifuel 0"
let rec alloc_search_preserves_fl_valid
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires well_formed_heap g /\
                    fl_valid g cur_fp fuel /\
                    fl_chain_terminates g cur_fp fuel /\
                    fl_valid g head_fp (heap_size / U64.v mword) /\
                    wz >= 1 /\
                    (prev_fp <> 0UL ==>
                      (prev_fp <> cur_fp /\
                       U64.v prev_fp >= U64.v mword /\
                       U64.v prev_fp < heap_size /\
                       U64.v prev_fp % U64.v mword = 0 /\
                       Seq.mem prev_fp (objects zero_addr g) /\
                       U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1 /\
                       U64.v (hd_address (prev_fp <: obj_addr)) + 16 <= heap_size /\
                       read_word g (prev_fp <: obj_addr) = cur_fp)))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    fl_valid r.heap_out r.fp_out (heap_size / U64.v mword)))
          (decreases fuel)
  = let big_fuel = heap_size / U64.v mword in
    if fuel = 0 then ()
    // Base cases: result = {g, head_fp, 0UL}. fl_valid g head_fp big_fuel from precondition.
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
      fl_valid_next g cur_fp fuel;
      assert (Seq.mem obj (objects zero_addr g));
      assert (U64.v (wosize_of_object obj g) >= 1);
      wosize_of_object_spec obj g;
      wosize_of_object_bound obj g;
      wf_object_size_bound g obj;
      getWosize_bound hdr;
      let next_fp =
        if U64.v hd + 16 <= heap_size then read_word g obj
        else 0UL
      in
      // hd + 16 always <= heap_size for valid objects: obj >= 8, obj < 1024, aligned to 8
      // So hd = obj - 8, hd + 16 = obj + 8 <= heap_size
      assert (U64.v hd + 16 <= heap_size);
      // fl_valid g next_fp (fuel-1) from fl_valid_next
      assert (fl_valid g next_fp (fuel - 1));
      // fl_chain_terminates g next_fp (fuel-1) from fl_chain_terminates g cur_fp fuel
      fl_chain_terminates_elim g cur_fp fuel;
      assert (fl_chain_terminates g next_fp (fuel - 1));
      if block_wz >= wz then begin
        // ===== Found a suitable block =====
        next_fp_in_objects g obj;
        alloc_from_block_preserves_wf g obj wz next_fp;
        let (g', new_fp) = alloc_from_block g obj wz next_fp in
        // Upgrade fl_valid g next_fp (fuel-1) to fl_valid g next_fp big_fuel
        fl_valid_any_fuel g next_fp (fuel - 1) big_fuel;
        assert (fl_valid g next_fp big_fuel);
        if prev_fp = 0UL then begin
          // ===== prev_fp = 0UL: fp_out = new_fp =====
          if block_wz - wz >= 2 then begin
            // ===== Split case: new_fp = rem_obj =====
            alloc_split_facts g obj wz next_fp;
            alloc_from_block_objects_facts g obj wz next_fp;
            let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
            let rem_obj_nat = rem_hd_nat + 8 in
            let rem_wz = block_wz - wz - 1 in
            // new_fp = rem_obj from alloc_split_facts
            // rem_obj ∈ objects(0, g') from alloc_from_block_objects_facts
            assert (is_pointer_field new_fp ==> Seq.mem new_fp (objects zero_addr g'));
            // Transfer fl_valid g next_fp big_fuel to g'
            let transfer_aux (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr g))
              (ensures Seq.mem a (objects zero_addr g') /\
                       (U64.v (wosize_of_object a g) >= 1 ==>
                         U64.v (wosize_of_object a g') >= 1) /\
                       (U64.v (wosize_of_object a g) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g' a == read_word g a))
            = alloc_split_fl_transfer_pre g obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux);
            fl_valid_transfer g g' next_fp big_fuel;
            assert (fl_valid g' next_fp big_fuel);
            fl_valid_weaken g' next_fp big_fuel (big_fuel - 1);
            // Build fl_valid g' new_fp big_fuel via fl_valid_step
            // new_fp = rem_obj:
            //   rem_obj ∈ objects(0, g') ✓
            //   wosize(rem_obj, g') = rem_wz >= 1 ✓ (block_wz - wz >= 2 => rem_wz >= 1)
            //   hd(rem_obj) + 16 <= heap_size: rem_hd + 16 = rem_obj + 8 <= heap_size ✓
            //   link(rem_obj, g') = next_fp (written by alloc_from_block)
            //   next_fp ≠ rem_obj: from objects_separated (rem_obj is interior to obj's old block)
            //   fl_valid g' next_fp (big_fuel - 1) ✓
            // Need to show rem_obj is valid and call fl_valid_step
            alloc_split_rem_in_objects g obj wz next_fp;
            assert (Seq.mem new_fp (objects zero_addr g'));
            // Reconstruct intermediate heaps to read back new_fp's fields
            alloc_from_block_split_normal g obj wz next_fp;
            let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
            let g1 = write_word g hd alloc_hdr in
            let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
            let rem_hdr = make_header (U64.uint_to_t rem_wz) blue_bits 0UL in
            let g2 = write_word g1 rem_hd rem_hdr in
            let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
            let g3 = write_word g2 rem_obj next_fp in
            assert (g' == g3);
            assert (new_fp == rem_obj);
            // 1. read_word g' new_fp = next_fp (link to tail)
            read_write_same g2 rem_obj next_fp;
            assert (read_word g' new_fp == next_fp);
            // 2. wosize_of_object new_fp g' = rem_wz >= 1
            //    hd_address(rem_obj) = rem_hd (since rem_obj = rem_hd + 8)
            hd_address_spec (rem_obj <: obj_addr);
            assert (hd_address (rem_obj <: obj_addr) == rem_hd);
            // read_word g' rem_hd = rem_hdr (via trace through writes)
            read_write_different g2 rem_obj rem_hd next_fp;
            read_write_same g1 rem_hd rem_hdr;
            assert (read_word g' rem_hd == rem_hdr);
            wosize_of_object_spec (new_fp <: obj_addr) g';
            make_header_getWosize (U64.uint_to_t rem_wz) blue_bits 0UL;
            assert (U64.v (wosize_of_object (new_fp <: obj_addr) g') == rem_wz);
            assert (rem_wz >= 1);
            // 3. new_fp is a valid object address
            assert (U64.v new_fp == rem_obj_nat);
            assert (rem_obj_nat >= 16);
            assert (U64.v new_fp >= U64.v mword);
            assert (U64.v new_fp < heap_size);
            assert (U64.v new_fp % U64.v mword == 0);
            // 4. hd_address(new_fp) + 16 <= heap_size
            //    hd_address(new_fp) = rem_hd, rem_hd + 16 = rem_obj + 8
            //    next_hd = hd + (block_wz+1)*8 <= heap_size (from wf_object_size_bound)
            //    rem_obj + 8 = hd + (wz+3)*8 <= hd + (block_wz+1)*8 since block_wz >= wz+2
            let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
            assert (next_hd_nat <= heap_size);
            assert (rem_obj_nat + 8 <= next_hd_nat);
            assert (U64.v (hd_address (new_fp <: obj_addr)) + 16 <= heap_size);
            // 5. next_fp <> new_fp: next_fp is either terminal or in objects(0,g)
            //    If terminal (0, < mword, >= heap_size, unaligned): can't equal rem_obj
            //    If in objects: objects_separated gives it's outside obj's block,
            //    but rem_obj is inside obj's block, so they differ
            assert (next_fp <> cur_fp);  // from fl_valid_next
            (if next_fp = 0UL then ()
             else if U64.v next_fp < U64.v mword then ()
             else if U64.v next_fp >= heap_size then ()
             else if U64.v next_fp % U64.v mword <> 0 then ()
             else begin
               // next_fp is valid and in objects(0,g)
               assert (big_fuel > 0);
               fl_valid_gives_mem g next_fp big_fuel;
               assert (Seq.mem next_fp (objects zero_addr g));
               // rem_obj is in [obj+8, obj+block_wz*8) (interior of obj's block)
               // next_fp is either before obj or after obj's block
               if U64.v next_fp < U64.v obj then begin
                 // next_fp < obj < rem_obj
                 assert (U64.v next_fp < U64.v new_fp)
               end else begin
                 // next_fp > obj: objects_separated gives next_fp > obj + wosize*8
                 objects_separated zero_addr g obj (next_fp <: obj_addr);
                 assert (U64.v next_fp > U64.v obj + block_wz * 8);
                 // rem_obj = hd + (1+wz)*8 + 8 = obj + wz*8 + 8 < obj + block_wz*8
                 assert (U64.v new_fp < U64.v obj + block_wz * 8);
                 assert (U64.v next_fp > U64.v new_fp)
               end
             end);
            assert (next_fp <> new_fp);
            // 6. Build fl_valid g' new_fp big_fuel via fl_valid_step
            fl_valid_step g' new_fp big_fuel
          end else begin
            // ===== Exact-fit case: new_fp = next_fp =====
            alloc_exact_preserves_wf g obj wz next_fp;
            alloc_from_block_exact g obj wz next_fp;
            // Transfer fl_valid g next_fp big_fuel to g'
            // Use obj_addr parameter to avoid subtyping issues in ensures
            let transfer_aux (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr g))
              (ensures Seq.mem a (objects zero_addr g') /\
                       (U64.v (wosize_of_object a g) >= 1 ==>
                         U64.v (wosize_of_object a g') >= 1) /\
                       (U64.v (wosize_of_object a g) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g' a == read_word g a))
            = alloc_exact_fl_transfer_pre g obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux);
            fl_valid_transfer g g' next_fp big_fuel;
            // fp_out = new_fp = next_fp (in exact fit, alloc_from_block returns (g1, next_fp))
            // fl_valid g' next_fp big_fuel ✓
            ()
          end
        end
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          // ===== prev_fp ≠ 0UL: fp_out = head_fp, heap_out = write_word g' prev_fp new_fp =====
          // g2 = write_word g' prev_fp new_fp, result = {g2, head_fp}
          let prev_obj : obj_addr = prev_fp in
          let g2 = write_word g' (prev_obj <: hp_addr) new_fp in
          //
          // Step 1: Establish fl_valid g' head_fp big_fuel via transfer from g
          // Step 2: Establish fl_valid g' new_fp big_fuel
          // Step 3: prev_fp ∈ objects(0, g') with wosize >= 1
          // Step 4: new_fp ≠ prev_fp
          // Step 5: fl_valid g2 new_fp big_fuel via fl_valid_field_write_tail
          // Step 6: fl_valid g2 head_fp big_fuel via fl_valid_field_write
          //
          if block_wz - wz >= 2 then begin
            // ----- Split sub-case -----
            alloc_split_facts g obj wz next_fp;
            alloc_from_block_objects_facts g obj wz next_fp;
            let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
            let rem_obj_nat = rem_hd_nat + 8 in
            let rem_wz = block_wz - wz - 1 in
            // Step 1: Transfer fl_valid from g to g' for head_fp
            let transfer_aux_s (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr g))
              (ensures Seq.mem a (objects zero_addr g') /\
                       (U64.v (wosize_of_object a g) >= 1 ==>
                         U64.v (wosize_of_object a g') >= 1) /\
                       (U64.v (wosize_of_object a g) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g' a == read_word g a))
            = alloc_split_fl_transfer_pre g obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux_s);
            fl_valid_transfer g g' head_fp big_fuel;
            assert (fl_valid g' head_fp big_fuel);
            // Step 2: Build fl_valid g' new_fp big_fuel (same as prev_fp=0 split case)
            fl_valid_transfer g g' next_fp big_fuel;
            fl_valid_weaken g' next_fp big_fuel (big_fuel - 1);
            alloc_split_rem_in_objects g obj wz next_fp;
            assert (Seq.mem new_fp (objects zero_addr g'));
            // Reconstruct intermediate heaps
            alloc_from_block_split_normal g obj wz next_fp;
            let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
            let g1 = write_word g hd alloc_hdr in
            let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
            let rem_hdr = make_header (U64.uint_to_t rem_wz) blue_bits 0UL in
            let g2_tmp = write_word g1 rem_hd rem_hdr in
            let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
            let g3 = write_word g2_tmp rem_obj next_fp in
            assert (g' == g3);
            assert (new_fp == rem_obj);
            // wosize of new_fp in g': need wosize_of_object new_fp g' >= 1
            make_header_getWosize (U64.uint_to_t rem_wz) blue_bits 0UL;
            // The header at rem_hd in g' is rem_hdr
            // rem_hd = hd_address(rem_obj), so wosize_of_object rem_obj g' = getWosize(read_word g' rem_hd)
            // read_word g' rem_hd: written as g2_tmp = write_word g1 rem_hd rem_hdr, then
            //   g3 = write_word g2_tmp rem_obj next_fp. Since rem_obj ≠ rem_hd (rem_obj = rem_hd + 8),
            //   read_word g3 rem_hd = read_word g2_tmp rem_hd = rem_hdr
            read_write_different g2_tmp rem_obj rem_hd next_fp;
            assert (read_word g' rem_hd == rem_hdr);
            hd_address_spec (new_fp <: obj_addr);
            assert (hd_address (new_fp <: obj_addr) == rem_hd);
            wosize_of_object_spec (new_fp <: obj_addr) g';
            assert (rem_wz >= 1);
            assert (U64.v (wosize_of_object (new_fp <: obj_addr) g') >= 1);
            // read_word g' new_fp = next_fp (written as last step of alloc_from_block)
            read_write_same g2_tmp rem_obj next_fp;
            assert (read_word g' (new_fp <: obj_addr) == next_fp);
            // next_fp ≠ new_fp
            assert (next_fp <> cur_fp);
            assert (next_fp <> obj);
            assert (big_fuel > 0);
            (if next_fp = 0UL then ()
             else if U64.v next_fp < U64.v mword then ()
             else if U64.v next_fp >= heap_size then ()
             else if U64.v next_fp % U64.v mword <> 0 then ()
             else begin
               fl_valid_gives_mem g next_fp big_fuel;
               assert (Seq.mem next_fp (objects zero_addr g));
               assert (U64.v new_fp == rem_obj_nat);
               assert (rem_obj_nat >= U64.v obj);
               if U64.v next_fp < U64.v obj then begin
                 assert (U64.v new_fp < U64.v obj + block_wz * 8);
                 assert (U64.v next_fp < U64.v obj);
                 assert (U64.v new_fp >= U64.v obj)
               end else begin
                 assert (U64.v next_fp > U64.v obj);
                 objects_separated zero_addr g obj (next_fp <: obj_addr);
                 assert (U64.v next_fp > U64.v obj + block_wz * 8);
                 assert (U64.v new_fp < U64.v obj + block_wz * 8)
               end
             end);
            assert (next_fp <> new_fp);
            fl_valid_step g' new_fp big_fuel;
            assert (fl_valid g' new_fp big_fuel);
            // Step 3: prev_fp ∈ objects(0, g') with wosize >= 1
            // prev_fp ∈ objects(0, g) from precondition, transfer preserves
            assert (Seq.mem prev_fp (objects zero_addr g'));
            // wosize preserved: alloc_split_fl_transfer_pre gives it
            alloc_split_fl_transfer_pre g obj wz next_fp prev_obj;
            assert (U64.v (wosize_of_object prev_obj g') >= 1);
            // Step 4: new_fp ≠ prev_fp
            // new_fp = rem_obj, which is interior to obj's old block
            // prev_fp ≠ cur_fp (= obj) from precondition, and prev_fp is a different object
            // prev_fp < obj or prev_fp > obj + block_wz * 8
            // new_fp ∈ [obj + wz*8 + 8, obj + block_wz * 8) ⊂ obj's block
            // So new_fp ≠ prev_fp
            (if U64.v prev_fp <= U64.v obj then begin
               objects_separated zero_addr g prev_obj obj;
               // prev_fp + wosize(prev_fp)*8 < obj, and new_fp >= obj
               assert (U64.v new_fp > U64.v prev_fp)
             end else begin
               objects_separated zero_addr g obj prev_obj;
               // obj + block_wz * 8 < prev_fp, and new_fp < obj + block_wz*8
               assert (U64.v prev_fp > U64.v obj + block_wz * 8);
               assert (U64.v new_fp < U64.v obj + block_wz * 8);
               assert (U64.v new_fp < U64.v prev_fp)
             end);
            assert (new_fp <> prev_fp);
            // Step 5: fl_valid g2 new_fp big_fuel via fl_valid_field_write_tail
            fl_valid_field_write_tail g' prev_obj new_fp big_fuel;
            assert (fl_valid g2 new_fp big_fuel);
            // Step 6: fl_valid g2 head_fp big_fuel via fl_valid_field_write
            fl_valid_field_write g' prev_obj new_fp head_fp big_fuel big_fuel
          end else begin
            // ----- Exact-fit sub-case -----
            alloc_exact_preserves_wf g obj wz next_fp;
            alloc_from_block_exact g obj wz next_fp;
            // Step 1: Transfer fl_valid from g to g' for head_fp
            let transfer_aux_e (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr g))
              (ensures Seq.mem a (objects zero_addr g') /\
                       (U64.v (wosize_of_object a g) >= 1 ==>
                         U64.v (wosize_of_object a g') >= 1) /\
                       (U64.v (wosize_of_object a g) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g' a == read_word g a))
            = alloc_exact_fl_transfer_pre g obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux_e);
            fl_valid_transfer g g' head_fp big_fuel;
            assert (fl_valid g' head_fp big_fuel);
            // Step 2: fl_valid g' new_fp big_fuel
            // In exact-fit: new_fp = next_fp (alloc_from_block returns (g1, next_fp))
            fl_valid_transfer g g' next_fp big_fuel;
            assert (fl_valid g' new_fp big_fuel);
            // Step 3: prev_fp ∈ objects(0, g') with wosize >= 1
            assert (Seq.mem prev_fp (objects zero_addr g'));
            alloc_exact_fl_transfer_pre g obj wz next_fp prev_obj;
            assert (U64.v (wosize_of_object prev_obj g') >= 1);
            // Step 4: new_fp ≠ prev_fp
            // In exact-fit, new_fp = next_fp = read_word g cur_fp.
            // We have: read_word g prev_fp = cur_fp (precondition).
            // If next_fp = prev_fp, then chain is prev_fp → cur_fp → prev_fp (2-cycle).
            // fl_chain_terminates g next_fp (fuel-1) contradicts this cycle.
            (if new_fp = prev_fp then begin
              // next_fp = prev_fp creates a 2-cycle: prev_fp → cur_fp → prev_fp
              assert (read_word g (prev_fp <: obj_addr) == cur_fp);
              assert (read_word g obj == next_fp);
              assert (next_fp == prev_fp);
              fl_chain_2cycle_not_terminates g prev_fp cur_fp (fuel - 1);
              assert (fl_chain_terminates g next_fp (fuel - 1) = false);
              // But we proved fl_chain_terminates g next_fp (fuel-1) = true
              assert false
            end else ());
            assert (new_fp <> prev_fp);
            // Step 5: fl_valid g2 new_fp big_fuel via fl_valid_field_write_tail
            fl_valid_field_write_tail g' prev_obj new_fp big_fuel;
            // Step 6: fl_valid g2 head_fp big_fuel via fl_valid_field_write
            fl_valid_field_write g' prev_obj new_fp head_fp big_fuel big_fuel
          end
        end
        else ()
      end
      else begin
        // ===== Advance: block too small, continue search =====
        // cur_fp becomes prev_fp; wosize(cur_fp, g) >= 1 from fl_valid_gives_wosize
        // cur_fp ≠ next_fp: from fl_valid_next (no self-loop)
        assert (cur_fp <> next_fp);
        // New precondition: read_word g cur_fp = next_fp
        assert (read_word g obj == next_fp);
        assert (U64.v hd + 16 <= heap_size);
        alloc_search_preserves_fl_valid g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

/// ===========================================================================
/// Section G: Top-level theorem — alloc_spec preserves fl_valid
/// ===========================================================================

let alloc_spec_preserves_fl_valid (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires well_formed_heap g /\
                    fl_valid g fp (heap_size / U64.v mword) /\
                    fl_chain_terminates g fp (heap_size / U64.v mword))
          (ensures (let r = alloc_spec g fp requested_wz in
                    fl_valid r.heap_out r.fp_out (heap_size / U64.v mword)))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_preserves_fl_valid g fp 0UL fp wz (heap_size / U64.v mword)

let chain_avoids_unfold_step = AllocChain.chain_avoids_unfold_step
let chain_avoids_head_ne = AllocChain.chain_avoids_head_ne
let chain_avoids_tail = AllocChain.chain_avoids_tail
let chain_avoids_transfer = AllocChain.chain_avoids_transfer
let chain_avoids_transfer_on_chain = AllocChain.chain_avoids_transfer_on_chain
let chain_avoids_weaken = AllocChain.chain_avoids_weaken
let chain_avoids_strengthen = AllocChain.chain_avoids_strengthen
let first_hit_spec = AllocChain.first_hit_spec
let walk_chain_one_step = AllocChain.walk_chain_one_step
let chain_avoids_prev = AllocChain.chain_avoids_prev
let not_in_fl_chain_b_is_chain_avoids = AllocChain.not_in_fl_chain_b_is_chain_avoids
let fl_chain_predecessor_not_in_suffix_b = AllocChain.fl_chain_predecessor_not_in_suffix_b
let fl_chain_terminates_transfer_excl = AllocChain.fl_chain_terminates_transfer_excl
let fl_chain_no_early_repeat = AllocChain.fl_chain_no_early_repeat
let walk_chain_valid_preserved = AllocChain.walk_chain_valid_preserved


/// ===========================================================================
/// Section G1b: alloc_spec preserves fl_chain_terminates
/// ===========================================================================

/// (Moved to GC.Spec.Allocator.Lemmas.Chain)

/// ---------------------------------------------------------------------------
/// alloc_search_preserves_fl_chain_terminates moved to SearchChain.
let alloc_spec_preserves_fl_chain_terminates = AllocSearchChain.alloc_spec_preserves_fl_chain_terminates

/// Section G2: Top-level theorem — alloc_spec preserves objects membership
/// ===========================================================================

let alloc_spec_preserves_objects (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires well_formed_heap g /\
                    fl_valid g fp (heap_size / U64.v mword))
          (ensures (let r = alloc_spec g fp requested_wz in
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                      Seq.mem x (objects zero_addr r.heap_out))))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_preserves_objects g fp 0UL fp wz (heap_size / U64.v mword)


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
#push-options "--z3rlimit 400 --fuel 0 --ifuel 0"
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

/// make_header with white_bits produces White color
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
private let make_header_color_white (wz: U64.t{U64.v wz < pow2 54})
  : Lemma (getColor (make_header wz white_bits 0UL) == Header.White)
  = let hdr = make_header wz white_bits 0UL in
    getColor_raw hdr;
    make_header_getColor wz white_bits 0UL
#pop-options

/// make_header with blue_bits produces Blue color
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let make_header_color_blue (wz: U64.t{U64.v wz < pow2 54})
  : Lemma (getColor (make_header wz blue_bits 0UL) == Header.Blue)
  = let hdr = make_header wz blue_bits 0UL in
    getColor_raw hdr;
    make_header_getColor wz blue_bits 0UL
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: field write preserves no_black_objects
/// ---------------------------------------------------------------------------

/// Writing to a field (body address) of an object preserves no_black_objects.
#restart-solver
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
private let field_write_preserves_no_black
  (g: heap) (obj: obj_addr) (addr: hp_addr) (v: U64.t)
  : Lemma (requires no_black_objects g /\
                    well_formed_heap g /\
                    Seq.mem obj (objects zero_addr g) /\
                    U64.v addr >= U64.v obj /\
                    U64.v addr < U64.v obj + U64.v (wosize_of_object obj g) * 8 /\
                    U64.v addr % 8 = 0)
          (ensures no_black_objects (write_word g addr v))
  = let g' = write_word g addr v in
    write_word_preserves_objects g obj addr v;
    let aux (h: obj_addr) : Lemma
      (requires Seq.mem h (objects zero_addr g'))
      (ensures ~(is_black h g'))
    = assert (Seq.mem h (objects zero_addr g));
      hd_address_spec h;
      hd_address_spec obj;
      if U64.v h <= U64.v obj then begin
        read_write_different g addr (hd_address h) v;
        color_of_header_eq h g g'
      end else begin
        objects_separated zero_addr g obj h;
        read_write_different g addr (hd_address h) v;
        color_of_header_eq h g g'
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// alloc_from_block preserves no_black_objects
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--split_queries always --z3rlimit 100 --fuel 0 --ifuel 0"
private let alloc_from_block_preserves_no_black
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires no_black_objects g /\
                    well_formed_heap g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     U64.v (getWosize hdr) >= wz) /\
                    (is_pointer_field next_fp ==> Seq.mem next_fp (objects zero_addr g)))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    no_black_objects g'))
  = let hdr = read_word g (hd_address obj) in
    let block_wz = U64.v (getWosize hdr) in
    let hd = hd_address obj in
    let (g', rem_fp) = alloc_from_block g obj wz next_fp in
    hd_address_spec obj;
    wosize_of_object_spec obj g;
    getWosize_bound hdr;
    if block_wz - wz >= 2 then begin
      // Split case
      alloc_split_facts g obj wz next_fp;
      let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
      let rem_obj_nat = rem_hd_nat + 8 in
      let rem_wz = block_wz - wz - 1 in
      let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
      let rem_obj_addr : obj_addr = U64.uint_to_t rem_obj_nat in
      let aux_before (p: hp_addr) : Lemma
        (requires U64.v p < U64.v hd)
        (ensures read_word g' p == read_word g p)
      = alloc_split_g3_agrees g obj wz next_fp p
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux_before);
      make_header_color_white (U64.uint_to_t wz);
      make_header_color_blue (U64.uint_to_t rem_wz);
      let aux (h: obj_addr) : Lemma
        (requires Seq.mem h (objects zero_addr g'))
        (ensures ~(is_black h g'))
      = objects_addresses_gt_start zero_addr g obj;
        hd_address_spec obj;
        assert (U64.v zero_addr <= U64.v hd);
        split_new_mem_in_old_or_rem zero_addr g g' obj wz block_wz h;
        if U64.v h = rem_obj_nat then begin
          hd_address_spec rem_obj_addr;
          color_of_object_spec rem_obj_addr g';
          is_black_iff rem_obj_addr g'
        end else begin
          assert (Seq.mem h (objects zero_addr g));
          if h = obj then begin
            color_of_object_spec obj g';
            is_black_iff obj g'
          end else begin
            hd_address_spec h;
            if U64.v h < U64.v obj then begin
              objects_separated zero_addr g h obj;
              assert (U64.v (hd_address h) < U64.v hd);
              alloc_split_g3_agrees g obj wz next_fp (hd_address h)
            end else begin
              objects_separated zero_addr g obj h;
              assert (U64.v (hd_address h) > U64.v hd + block_wz * 8);
              assert (U64.v (hd_address h) <> U64.v hd);
              assert (U64.v (hd_address h) <> rem_hd_nat);
              assert (U64.v (hd_address h) <> rem_obj_nat);
              alloc_split_g3_agrees g obj wz next_fp (hd_address h)
            end;
            color_of_header_eq h g g'
          end
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    end else begin
      // Exact fit case
      alloc_from_block_exact g obj wz next_fp;
      let alloc_hdr = make_header (U64.uint_to_t block_wz) white_bits 0UL in
      make_header_getWosize (U64.uint_to_t block_wz) white_bits 0UL;
      header_write_same_wosize_preserves_objects g obj alloc_hdr;
      read_write_same g hd alloc_hdr;
      make_header_color_white (U64.uint_to_t block_wz);
      let aux (h: obj_addr) : Lemma
        (requires Seq.mem h (objects zero_addr g'))
        (ensures ~(is_black h g'))
      = assert (Seq.mem h (objects zero_addr g));
        if h = obj then begin
          color_of_object_spec obj g';
          is_black_iff obj g'
        end else begin
          hd_address_spec h;
          if U64.v h < U64.v obj then
            objects_separated zero_addr g h obj
          else
            objects_separated zero_addr g obj h;
          read_write_different g hd (hd_address h) alloc_hdr;
          color_of_header_eq h g g'
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// alloc_search preserves no_black_objects
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
let rec alloc_search_preserves_no_black
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires no_black_objects g /\
                    well_formed_heap g /\
                    fl_valid g cur_fp fuel /\
                    (prev_fp <> 0UL ==>
                      (prev_fp <> cur_fp /\
                       U64.v prev_fp >= U64.v mword /\
                       U64.v prev_fp < heap_size /\
                       U64.v prev_fp % U64.v mword = 0 /\
                       Seq.mem prev_fp (objects zero_addr g) /\
                       U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1)))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    no_black_objects r.heap_out))
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
        if U64.v hd + 16 <= heap_size then
          next_fp_in_objects g obj;
        alloc_from_block_preserves_no_black g obj wz next_fp;
        let (g', new_fp) = alloc_from_block g obj wz next_fp in
        if prev_fp = 0UL then ()
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          let prev : obj_addr = prev_fp in
          alloc_from_block_objects_facts g obj wz next_fp;
          assert (Seq.mem prev (objects zero_addr g'));
          alloc_from_block_preserves_wf g obj wz next_fp;
          hd_address_spec prev;
          wosize_of_object_spec prev g;
          wosize_of_object_spec obj g;
          wosize_of_object_bound prev g;
          wf_object_size_bound g prev;
          if block_wz - wz >= 2 then begin
            let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
            let rem_obj_nat = rem_hd_nat + 8 in
            if U64.v prev < U64.v obj then begin
              objects_separated zero_addr g prev obj;
              assert (U64.v (hd_address prev) < U64.v hd);
              assert (rem_hd_nat > U64.v hd);
              assert (U64.v (hd_address prev) <> rem_hd_nat);
              assert (U64.v (hd_address prev) <> rem_obj_nat);
              alloc_split_g3_agrees g obj wz next_fp (hd_address prev)
            end else begin
              objects_separated zero_addr g obj prev;
              assert (U64.v (hd_address prev) > U64.v hd + block_wz * 8 - 8);
              assert (U64.v (hd_address prev) <> U64.v hd);
              assert (U64.v (hd_address prev) <> rem_hd_nat);
              assert (U64.v (hd_address prev) <> rem_obj_nat);
              alloc_split_g3_agrees g obj wz next_fp (hd_address prev)
            end
          end else begin
            assert (prev <> obj);
            if U64.v prev < U64.v obj then
              objects_separated zero_addr g prev obj
            else
              objects_separated zero_addr g obj prev;
            assert (U64.v (hd_address prev) <> U64.v hd);
            let alloc_hdr = make_header (U64.uint_to_t block_wz) white_bits 0UL in
            alloc_from_block_exact g obj wz next_fp;
            assert (fst (alloc_from_block g obj wz next_fp) == write_word g hd alloc_hdr);
            read_write_different g hd (hd_address prev) alloc_hdr
          end;
          wosize_of_object_spec prev g';
          assert (wosize_of_object prev g' == wosize_of_object prev g);
          field_write_preserves_no_black g' prev (prev <: hp_addr) new_fp
        end
        else ()
      end
      else begin
        fl_valid_next g cur_fp fuel;
        assert (cur_fp <> next_fp);
        alloc_search_preserves_no_black g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Top-level: alloc_spec preserves no_black_objects
/// ---------------------------------------------------------------------------

let alloc_spec_preserves_no_black (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires no_black_objects g /\
                    well_formed_heap g /\
                    fl_valid g fp (heap_size / U64.v mword))
          (ensures (let r = alloc_spec g fp requested_wz in
                    no_black_objects r.heap_out))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_preserves_no_black g fp 0UL fp wz (heap_size / U64.v mword)


/// ===========================================================================
/// Section I: alloc_spec removes obj_out from the chain
/// ===========================================================================

/// ---------------------------------------------------------------------------
/// Object-not-in-chain proof moved to GC.Spec.Allocator.Lemmas.ObjNotInChain.
/// Keep Core as a compatibility re-export.
/// ---------------------------------------------------------------------------

module AllocObjNotInChain = GC.Spec.Allocator.Lemmas.ObjNotInChain
let chain_avoids_transfer_excl = AllocChain.chain_avoids_transfer_excl
let chain_avoids_transfer_excl2 = AllocChain.chain_avoids_transfer_excl2
let chain_avoids_unfold_steps = AllocChain.chain_avoids_unfold_steps
let alloc_spec_obj_not_in_chain = AllocObjNotInChain.alloc_spec_obj_not_in_chain

/// alloc_spec preserves objects membership under part1
let alloc_spec_preserves_objects_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    fl_valid g fp (heap_size / U64.v mword) /\
                    fl_chain_terminates g fp (heap_size / U64.v mword))
          (ensures (let r = alloc_spec g fp requested_wz in
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                      Seq.mem x (objects zero_addr r.heap_out))))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_preserves_objects_part1 g fp 0UL fp wz (heap_size / U64.v mword)
