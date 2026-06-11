(*
   GC.Spec.Allocator.Lemmas.SearchChain — allocator search proofs for
   free-list termination and removing the allocated object from the chain.
*)
module GC.Spec.Allocator.Lemmas.SearchChain

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
open GC.Spec.Allocator.Lemmas.Common
module AllocChain = GC.Spec.Allocator.Lemmas.Chain
open GC.Spec.Allocator.Lemmas.Chain
open GC.Spec.Allocator.Lemmas.SearchBase

/// Module-level default: all functions get z3rlimit 20 unless overridden
#push-options "--z3rlimit 20 --z3refresh"

/// The main recursive proof: alloc_search preserves fl_chain_terminates
/// ---------------------------------------------------------------------------
///
/// Key addition: we carry walk_chain invariants that track where we are in the
/// chain from head_fp. This allows us to use fl_chain_terminates_unfold_steps
/// in the prev≠0 case, avoiding the step-count inflation of splice.

#restart-solver
#push-options "--split_queries always --z3rlimit 100 --fuel 1 --ifuel 0"
private let rec alloc_search_preserves_fl_chain_terminates
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires well_formed_heap g /\
                    fl_valid g cur_fp fuel /\
                    fl_chain_terminates g cur_fp fuel /\
                    fl_valid g head_fp (heap_size / U64.v mword) /\
                    fl_chain_terminates g head_fp (heap_size / U64.v mword) /\
                    wz >= 1 /\
                    fuel <= heap_size / U64.v mword /\
                    (prev_fp <> 0UL ==>
                      (prev_fp <> cur_fp /\
                       U64.v prev_fp >= U64.v mword /\
                       U64.v prev_fp < heap_size /\
                       U64.v prev_fp % U64.v mword = 0 /\
                       Seq.mem prev_fp (objects zero_addr g) /\
                       U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1 /\
                       U64.v (hd_address (prev_fp <: obj_addr)) + 16 <= heap_size /\
                       read_word g (prev_fp <: obj_addr) = cur_fp)) /\
                    // Walk-chain invariants
                    fuel <= heap_size / U64.v mword /\
                    walk_chain g head_fp (heap_size / U64.v mword - fuel) = cur_fp /\
                    walk_chain_valid g head_fp (heap_size / U64.v mword - fuel) /\
                    (prev_fp <> 0UL ==> fuel < heap_size / U64.v mword /\
                                        walk_chain g head_fp (heap_size / U64.v mword - fuel - 1) = prev_fp))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    fl_chain_terminates r.heap_out r.fp_out (heap_size / U64.v mword)))
          (decreases fuel)
  = let big_fuel = heap_size / U64.v mword in
    if fuel = 0 then ()
    else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
    else if U64.v cur_fp >= heap_size then ()
    else if U64.v cur_fp % U64.v mword <> 0 then ()
    else begin
      assert (fuel > 0);
      assert (U64.v cur_fp >= U64.v mword);
      assert (U64.v cur_fp < heap_size);
      assert (U64.v cur_fp % U64.v mword = 0);
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
      assert (U64.v hd + 16 <= heap_size);
      assert (fl_valid g next_fp (fuel - 1));
      fl_chain_terminates_elim g cur_fp fuel;
      assert (fl_chain_terminates g next_fp (fuel - 1));
      if block_wz >= wz then begin
        // ===== Found a suitable block =====
        next_fp_in_objects g obj;
        alloc_from_block_preserves_wf g obj wz next_fp;
        let (g', new_fp) = alloc_from_block g obj wz next_fp in
        // Upgrade fl_valid/terminates g next_fp (fuel-1) to big_fuel
        fl_valid_any_fuel g next_fp (fuel - 1) big_fuel;
        assert (fl_valid g next_fp big_fuel);
        fl_chain_terminates_weaken g next_fp (fuel - 1) big_fuel;
        assert (fl_chain_terminates g next_fp big_fuel);
        if prev_fp = 0UL then begin
          // ===== prev_fp = 0UL: fp_out = new_fp =====
          if block_wz - wz >= 2 then begin
            // ===== Split case: new_fp = rem_obj =====
            alloc_split_facts g obj wz next_fp;
            alloc_from_block_objects_facts g obj wz next_fp;
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
            fl_chain_terminates_weaken g next_fp (fuel - 1) (big_fuel - 1);
            fl_valid_any_fuel g next_fp (fuel - 1) (big_fuel - 1);
            fl_chain_terminates_transfer g g' next_fp (big_fuel - 1);
            let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
            let rem_obj_nat = rem_hd_nat + 8 in
            alloc_from_block_split_normal g obj wz next_fp;
            let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
            let g1 = write_word g hd alloc_hdr in
            let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
            let rem_wz = block_wz - wz - 1 in
            let rem_hdr = make_header (U64.uint_to_t rem_wz) blue_bits 0UL in
            let g2 = write_word g1 rem_hd rem_hdr in
            let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
            let g3 = write_word g2 rem_obj next_fp in
            assert (g' == g3);
            assert (new_fp == rem_obj);
            read_write_same g2 rem_obj next_fp;
            assert (read_word g' new_fp == next_fp);
            assert (U64.v new_fp >= U64.v mword);
            assert (U64.v new_fp < heap_size);
            assert (U64.v new_fp % U64.v mword == 0);
            hd_address_spec (new_fp <: obj_addr);
            assert (hd_address (new_fp <: obj_addr) == rem_hd);
            let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
            assert (next_hd_nat <= heap_size);
            assert (rem_obj_nat + 8 <= next_hd_nat);
            assert (U64.v (hd_address (new_fp <: obj_addr)) + 16 <= heap_size);
            fl_chain_terminates_step g' new_fp big_fuel
          end else begin
            // ===== Exact-fit case: new_fp = next_fp =====
            alloc_exact_preserves_wf g obj wz next_fp;
            alloc_from_block_exact g obj wz next_fp;
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
            fl_chain_terminates_transfer g g' next_fp big_fuel;
            fl_chain_terminates_weaken g' next_fp big_fuel big_fuel;
            ()
          end
        end
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          // ===== prev_fp != 0UL: fp_out = head_fp, heap_out = write_word g' prev_fp new_fp =====
          let prev_obj : obj_addr = prev_fp in
          let g2 = write_word g' (prev_obj <: hp_addr) new_fp in
          //
          // Strategy: Use fl_chain_terminates_unfold_steps to decompose the chain.
          // Let d = big_fuel - fuel - 1 (depth of prev_fp from head_fp).
          // 1. Show walk_chain_valid g2 head_fp d and walk_chain g2 head_fp d = prev_fp
          // 2. Apply fl_chain_terminates_unfold_steps g2 head_fp d big_fuel:
          //    fl_chain_terminates g2 head_fp big_fuel = fl_chain_terminates g2 prev_fp (fuel+1)
          // 3. prev_fp valid, read_word g2 prev_fp = new_fp:
          //    fl_chain_terminates g2 prev_fp (fuel+1) = fl_chain_terminates g2 new_fp fuel
          // 4. Establish fl_chain_terminates g2 new_fp fuel
          //
          let d = big_fuel - fuel - 1 in
          if block_wz - wz >= 2 then begin
            // ----- Split sub-case -----
            alloc_split_facts g obj wz next_fp;
            alloc_from_block_objects_facts g obj wz next_fp;
            let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
            let rem_obj_nat = rem_hd_nat + 8 in
            let rem_wz = block_wz - wz - 1 in
            // Establish quantifier: for a in objects(g), read g' a = read g a
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
            // Establish locality of write_word at prev_fp (read_word g2 a = read_word g' a for a far from prev_fp)
            write_word_locality g' (prev_obj <: hp_addr) new_fp;
            // Establish new_fp != prev_fp
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
            read_write_same g2_tmp rem_obj next_fp;
            assert (read_word g' new_fp == next_fp);
            (if U64.v prev_fp <= U64.v obj then begin
               objects_separated zero_addr g prev_obj obj;
               assert (U64.v new_fp > U64.v prev_fp)
             end else begin
               objects_separated zero_addr g obj prev_obj;
               assert (U64.v prev_fp > U64.v obj + block_wz * 8);
               assert (U64.v new_fp < U64.v obj + block_wz * 8);
               assert (U64.v new_fp < U64.v prev_fp)
             end);
            assert (new_fp <> prev_fp);
            read_write_different g' (prev_obj <: hp_addr) (new_fp <: hp_addr) new_fp;
            assert (read_word g2 (new_fp <: obj_addr) == next_fp);
            // Step 4: Establish fl_chain_terminates g2 new_fp fuel
            // Transfer fl_chain_terminates g next_fp (fuel-1) to g2 via transfer_excl
            chain_avoids_prev g prev_fp cur_fp next_fp (fuel - 1);
            fl_chain_terminates_transfer_excl g g2 next_fp prev_fp (fuel - 1);
            // fl_chain_terminates g2 next_fp (fuel-1)
            // Build fl_chain_terminates g2 new_fp fuel via step
            let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
            assert (next_hd_nat <= heap_size);
            assert (rem_obj_nat + 8 <= next_hd_nat);
            hd_address_spec (new_fp <: obj_addr);
            assert (U64.v (hd_address (new_fp <: obj_addr)) + 16 <= heap_size);
            assert (U64.v new_fp >= U64.v mword);
            assert (U64.v new_fp < heap_size);
            assert (U64.v new_fp % U64.v mword == 0);
            fl_chain_terminates_step g2 new_fp fuel;
            assert (fl_chain_terminates g2 new_fp fuel);
            // Build fl_chain_terminates g2 prev_fp (fuel+1)
            fl_chain_terminates_step g2 prev_fp (fuel + 1);
            // Now get fl_chain_terminates g2 head_fp big_fuel
            if d = 0 then begin
              // d = 0 → prev_fp = head_fp. Weaken (fuel+1) to big_fuel.
              assert (walk_chain g head_fp d = prev_fp);
              walk_chain_zero g head_fp;
              assert (walk_chain g head_fp 0 = head_fp);
              assert (prev_fp = head_fp);
              assert (fl_chain_terminates g2 head_fp (fuel + 1));
              fl_chain_terminates_weaken g2 head_fp (fuel + 1) big_fuel
            end else begin
              // d > 0: use unfold_steps to equate head chain with prev chain
              assert (walk_chain g head_fp d = prev_fp);
              walk_chain_valid_prefix g head_fp (big_fuel - fuel) d;
              assert (walk_chain_valid g head_fp d);
              fl_chain_no_early_repeat g head_fp d big_fuel;
              walk_chain_valid_preserved g g2 head_fp prev_fp d big_fuel;
              assert (d <= big_fuel);
              fl_chain_terminates_unfold_steps g2 head_fp d big_fuel
              // fl_chain_terminates g2 head_fp big_fuel = fl_chain_terminates g2 prev_fp (fuel+1) = true
            end
          end else begin
            // ----- Exact-fit sub-case -----
            alloc_exact_preserves_wf g obj wz next_fp;
            alloc_from_block_exact g obj wz next_fp;
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
            // Establish locality of write_word at prev_fp
            write_word_locality g' (prev_obj <: hp_addr) new_fp;
            // new_fp = next_fp in exact-fit. Show new_fp != prev_fp.
            (if new_fp = prev_fp then begin
               assert (read_word g (prev_fp <: obj_addr) == cur_fp);
               assert (read_word g obj == next_fp);
               assert (next_fp == prev_fp);
               fl_chain_2cycle_not_terminates g prev_fp cur_fp (fuel - 1);
               assert false
             end else ());
            assert (new_fp <> prev_fp);
            // Step 4: fl_chain_terminates g2 new_fp fuel
            chain_avoids_prev g prev_fp cur_fp next_fp (fuel - 1);
            fl_chain_terminates_transfer_excl g g2 next_fp prev_fp (fuel - 1);
            fl_chain_terminates_weaken g2 next_fp (fuel - 1) fuel;
            assert (fl_chain_terminates g2 new_fp fuel);
            // Build fl_chain_terminates g2 prev_fp (fuel+1)
            fl_chain_terminates_step g2 prev_fp (fuel + 1);
            // Now get fl_chain_terminates g2 head_fp big_fuel
            if d = 0 then begin
              // d = 0 → prev_fp = head_fp. Weaken (fuel+1) to big_fuel.
              assert (walk_chain g head_fp d = prev_fp);
              walk_chain_zero g head_fp;
              assert (walk_chain g head_fp 0 = head_fp);
              assert (prev_fp = head_fp);
              assert (fl_chain_terminates g2 head_fp (fuel + 1));
              fl_chain_terminates_weaken g2 head_fp (fuel + 1) big_fuel
            end else begin
              // d > 0: use unfold_steps
              assert (walk_chain g head_fp d = prev_fp);
              walk_chain_valid_prefix g head_fp (big_fuel - fuel) d;
              assert (walk_chain_valid g head_fp d);
              fl_chain_no_early_repeat g head_fp d big_fuel;
              walk_chain_valid_preserved g g2 head_fp prev_fp d big_fuel;
              assert (d <= big_fuel);
              fl_chain_terminates_unfold_steps g2 head_fp d big_fuel
            end
          end
        end
        else ()
      end
      else begin
        // ===== Advance: block too small, continue search =====
        assert (cur_fp <> next_fp);
        assert (read_word g obj == next_fp);
        assert (U64.v hd + 16 <= heap_size);
        // Maintain walk_chain invariants for the recursive call
        walk_chain_append g head_fp (big_fuel - fuel) 1;
        walk_chain_one_step g cur_fp;
        walk_chain_valid_snoc g head_fp (big_fuel - fuel);
        alloc_search_preserves_fl_chain_terminates g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

/// Top-level theorem
let alloc_spec_preserves_fl_chain_terminates (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires well_formed_heap g /\
                    fl_valid g fp (heap_size / U64.v mword) /\
                    fl_chain_terminates g fp (heap_size / U64.v mword))
          (ensures (let r = alloc_spec g fp requested_wz in
                    fl_chain_terminates r.heap_out r.fp_out (heap_size / U64.v mword)))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    let big_fuel = heap_size / U64.v mword in
    assert (big_fuel - big_fuel == 0);
    walk_chain_zero g fp;
    walk_chain_valid_zero g fp;
    alloc_search_preserves_fl_chain_terminates g fp 0UL fp wz (heap_size / U64.v mword)


/// Obj-not-in-chain proof remains in Core for now.
