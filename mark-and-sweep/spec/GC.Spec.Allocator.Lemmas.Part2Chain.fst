(*
   GC.Spec.Allocator.Lemmas.Part2Chain — body/other read framing + chain_avoids proofs.
*)
module GC.Spec.Allocator.Lemmas.Part2Chain

friend GC.Spec.Allocator.Lemmas.Core

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
open GC.Spec.Allocator.Lemmas.Header
open GC.Spec.Allocator.Lemmas.Split
open GC.Spec.Allocator.Lemmas.Part1
open GC.Spec.Allocator.Lemmas.Core
module U64 = FStar.UInt64
module Seq = FStar.Seq
open GC.Spec.Allocator.Lemmas.Part2Pre

/// Module-level default: all functions get z3rlimit 20 unless overridden
#push-options "--z3rlimit 20 --z3refresh"

/// ---------------------------------------------------------------------------
/// Section P4: alloc_spec body/other framing
///
/// alloc_from_block only writes to the header, remainder header, and remainder
/// link field. It does NOT write to the body [obj, obj + wz*8).
/// alloc_search additionally writes to prev_fp (a link in a different block).
/// ---------------------------------------------------------------------------

/// Helper: alloc_from_block preserves reads in [obj, obj + wz*8).
/// In both exact and split cases, the writes are at hd_address(obj) (= obj - 8),
/// and for split: rem_hd (= obj + wz*8) and rem_field (= obj + (wz+1)*8).
/// None of these overlap [obj, obj + wz*8).
#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
private let alloc_from_block_read_body
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (addr: hp_addr)
  : Lemma (requires (let hdr = read_word g (hd_address obj) in
                     let bwz = U64.v (getWosize hdr) in
                     bwz >= wz /\ wz >= 1 /\
                     U64.v addr >= U64.v obj /\
                     U64.v addr + 8 <= U64.v obj + wz * 8))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    read_word g' addr == read_word g addr))
  = let hd = hd_address obj in
    let hdr = read_word g hd in
    let bwz = U64.v (getWosize hdr) in
    let leftover = bwz - wz in
    hd_address_spec obj;
    assert (U64.v hd = U64.v obj - 8);
    // addr >= obj > obj - 8 = hd, so addr doesn't overlap hd
    assert (U64.v addr >= U64.v obj /\ U64.v obj > U64.v hd);
    if leftover >= 2 then begin
      // Split case
      let rhn = U64.v hd + (1 + wz) * 8 in
      assert (rhn == U64.v obj + wz * 8);
      // addr + 8 <= obj + wz*8 = rhn, so addr doesn't overlap rem_hd
      assert (U64.v addr + 8 <= rhn);
      let ron = rhn + 8 in
      // addr + 8 <= rhn < ron, so addr doesn't overlap rem_field
      assert (U64.v addr + 8 <= ron);
      if rhn >= heap_size then begin
        // rem_hd OOB: only hd written
        alloc_from_block_split_rem_hd_oob g obj wz next_fp;
        read_write_different g hd addr (make_header (U64.uint_to_t wz) white_bits 0UL)
      end else if rhn + 8 >= heap_size then begin
        // rem_obj OOB: hd and rem_hd written
        alloc_from_block_split_rem_obj_oob g obj wz next_fp;
        let ahdr = make_header (U64.uint_to_t wz) white_bits 0UL in
        let g1 = write_word g hd ahdr in
        read_write_different g hd addr ahdr;
        let rh : hp_addr = U64.uint_to_t rhn in
        let rw = bwz - wz - 1 in
        let rhdr = make_header (U64.uint_to_t rw) blue_bits 0UL in
        read_write_different g1 rh addr rhdr
      end else begin
        // Normal split: hd, rem_hd, rem_field all written
        alloc_from_block_split_normal g obj wz next_fp;
        let ahdr = make_header (U64.uint_to_t wz) white_bits 0UL in
        let g1 = write_word g hd ahdr in
        read_write_different g hd addr ahdr;
        let rh : hp_addr = U64.uint_to_t rhn in
        let rw = bwz - wz - 1 in
        let rhdr = make_header (U64.uint_to_t rw) blue_bits 0UL in
        let g2 = write_word g1 rh rhdr in
        read_write_different g1 rh addr rhdr;
        let ro : hp_addr = U64.uint_to_t ron in
        read_write_different g2 ro addr next_fp
      end
    end else begin
      // Exact case: only hd written
      alloc_from_block_exact g obj wz next_fp;
      let bwz_u = U64.uint_to_t bwz in
      let ahdr = make_header bwz_u white_bits 0UL in
      read_write_different g hd addr ahdr
    end
#pop-options

/// Helper: alloc_from_block preserves reads at addresses that don't overlap
/// any of the written locations. For addresses in the body of a DIFFERENT
/// object that is separated from obj.
#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
private let alloc_from_block_read_other_body
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (addr: hp_addr)
  : Lemma (requires (let hdr = read_word g (hd_address obj) in
                     let bwz = U64.v (getWosize hdr) in
                     bwz >= wz /\ wz >= 1 /\
                     // addr doesn't overlap hd_address(obj) 
                     (U64.v addr + 8 <= U64.v (hd_address obj) \/ U64.v addr >= U64.v obj) /\
                     // addr doesn't overlap [obj + wz*8, obj + (wz+2)*8) (remainder region)
                     (U64.v addr + 8 <= U64.v obj + wz * 8 \/
                      U64.v addr >= U64.v obj + (wz + 2) * 8)))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    read_word g' addr == read_word g addr))
  = let hd = hd_address obj in
    let hdr = read_word g hd in
    let bwz = U64.v (getWosize hdr) in
    let leftover = bwz - wz in
    hd_address_spec obj;
    if leftover >= 2 then begin
      let rhn = U64.v hd + (1 + wz) * 8 in
      assert (rhn == U64.v obj + wz * 8);
      let ron = rhn + 8 in
      if rhn >= heap_size then begin
        alloc_from_block_split_rem_hd_oob g obj wz next_fp;
        read_write_different g hd addr (make_header (U64.uint_to_t wz) white_bits 0UL)
      end else if rhn + 8 >= heap_size then begin
        alloc_from_block_split_rem_obj_oob g obj wz next_fp;
        let ahdr = make_header (U64.uint_to_t wz) white_bits 0UL in
        let g1 = write_word g hd ahdr in
        read_write_different g hd addr ahdr;
        let rh : hp_addr = U64.uint_to_t rhn in
        let rw = bwz - wz - 1 in
        let rhdr = make_header (U64.uint_to_t rw) blue_bits 0UL in
        read_write_different g1 rh addr rhdr
      end else begin
        alloc_from_block_split_normal g obj wz next_fp;
        let ahdr = make_header (U64.uint_to_t wz) white_bits 0UL in
        let g1 = write_word g hd ahdr in
        read_write_different g hd addr ahdr;
        let rh : hp_addr = U64.uint_to_t rhn in
        let rw = bwz - wz - 1 in
        let rhdr = make_header (U64.uint_to_t rw) blue_bits 0UL in
        let g2 = write_word g1 rh rhdr in
        read_write_different g1 rh addr rhdr;
        let ro : hp_addr = U64.uint_to_t ron in
        read_write_different g2 ro addr next_fp
      end
    end else begin
      alloc_from_block_exact g obj wz next_fp;
      let ahdr = make_header (U64.uint_to_t bwz) white_bits 0UL in
      read_write_different g hd addr ahdr
    end
#pop-options

/// Inductive: alloc_search preserves reads in the body of the allocated object.
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
private let rec alloc_search_read_body
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat) (addr: hp_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    fl_valid g cur_fp fuel /\
                    wz >= 1 /\
                    (prev_fp <> 0UL ==>
                      (prev_fp <> cur_fp /\
                       U64.v prev_fp >= U64.v mword /\
                       U64.v prev_fp < heap_size /\
                       U64.v prev_fp % U64.v mword = 0 /\
                       Seq.mem prev_fp (objects zero_addr g) /\
                       U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1)) /\
                    (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                     r.obj_out <> 0UL /\
                     U64.v addr >= U64.v r.obj_out /\
                     U64.v addr + 8 <= U64.v r.obj_out + wz * 8))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    read_word r.heap_out addr == read_word g addr))
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
      let next_fp =
        if U64.v hd + 16 <= heap_size then read_word g obj
        else 0UL
      in
      if block_wz >= wz then begin
        // Found a suitable block — cur_fp is obj_out
        let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
        assert (r.obj_out == cur_fp);
        // alloc_from_block doesn't touch [obj, obj + wz*8)
        alloc_from_block_read_body g obj wz next_fp addr;
        let (g', new_fp) = alloc_from_block g obj wz next_fp in
        // prev_fp write: addr is in [obj, obj+wz*8), prev_fp ≠ obj (since prev_fp <> cur_fp)
        if prev_fp = 0UL then ()
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          // prev_fp is a different object from cur_fp
          // addr >= obj = cur_fp, prev_fp <> cur_fp
          // Need: addr <> prev_fp. Two cases:
          // If prev_fp < obj: prev_fp + wz(prev_fp)*8 <= obj (from objects_separated)
          //   but prev_fp itself < obj <= addr, so addr >= obj > prev_fp
          //   and we need addr ≠ prev_fp as a write address.
          //   The write is at prev_fp, which is the obj_addr of the previous block.
          //   addr >= obj = cur_fp > prev_fp (need to show this) ... actually no.
          //   We just need U64.v addr + 8 <= U64.v prev_fp \/ U64.v addr >= U64.v prev_fp + 8
          //   prev_fp <> cur_fp = obj. If prev_fp < obj: prev_fp < obj <= addr, 
          //   and prev_fp + 8 <= obj (since aligned), so addr >= obj >= prev_fp + 8.
          //   If prev_fp > obj: prev_fp >= obj + block_wz*8 + 8 (next object start)
          //   and addr + 8 <= obj + wz*8 <= obj + block_wz*8 < prev_fp.
          assert (prev_fp <> cur_fp);
          if U64.v prev_fp < U64.v obj then begin
            // prev_fp < obj <= addr, and since aligned: prev_fp + 8 <= obj <= addr
            assert (U64.v addr >= U64.v obj);
            assert (U64.v obj >= U64.v mword);
            assert (U64.v prev_fp < U64.v obj);
            // prev_fp and obj are both obj_addrs, both >= mword, both aligned
            // Actually: prev_fp + 8 <= obj since both are word-aligned and prev_fp < obj
            assert (U64.v prev_fp + 8 <= U64.v obj);
            assert (U64.v addr >= U64.v prev_fp + 8);
            read_write_different g' (prev_fp <: hp_addr) addr new_fp
          end else begin
            // prev_fp > obj, and objects_separated gives prev_fp > obj + block_wz*8
            // addr + 8 <= obj + wz*8 <= obj + block_wz*8 < prev_fp
            objects_separated zero_addr g obj prev_fp;
            wosize_of_object_spec obj g;
            assert (U64.v prev_fp > U64.v obj + block_wz * 8);
            assert (U64.v addr + 8 <= U64.v obj + wz * 8);
            assert (wz <= block_wz);
            assert (U64.v addr + 8 <= U64.v prev_fp);
            read_write_different g' (prev_fp <: hp_addr) addr new_fp
          end
        end else ()
      end
      else begin
        // Block too small, continue search with next
        if U64.v hd + 16 <= heap_size then
          fl_valid_elim g cur_fp fuel
        else ();
        alloc_search_read_body g head_fp cur_fp next_fp wz (fuel - 1) addr
      end
    end
#pop-options

/// Top-level: alloc_spec preserves reads in the body of the allocated object.
let alloc_spec_read_body (g: heap) (fp: U64.t) (requested_wz: nat) (addr: hp_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    fl_valid g fp (heap_size / U64.v mword) /\
                    fl_chain_terminates g fp (heap_size / U64.v mword) /\
                    requested_wz >= 1 /\
                    (alloc_spec g fp requested_wz).obj_out <> 0UL /\
                    (let r = alloc_spec g fp requested_wz in
                     U64.v addr >= U64.v r.obj_out /\
                     U64.v addr + 8 <= U64.v r.obj_out + requested_wz * 8))
          (ensures (let r = alloc_spec g fp requested_wz in
                    read_word r.heap_out addr == read_word g addr))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_read_body g fp 0UL fp wz (heap_size / U64.v mword) addr

/// Inductive: alloc_search preserves reads in the body of a different object
/// that is not in the free-list chain.
#push-options "--z3rlimit 120 --fuel 1 --ifuel 0"
private let rec alloc_search_read_other
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  (other: obj_addr) (addr: hp_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    fl_valid g cur_fp fuel /\
                    wz >= 1 /\
                    Seq.mem other (objects zero_addr g) /\
                    chain_avoids g cur_fp other fuel = true /\
                    U64.v addr >= U64.v other /\
                    U64.v addr + 8 <= U64.v other + U64.v (wosize_of_object other g) * 8 /\
                    (prev_fp <> 0UL ==>
                      (prev_fp <> other /\
                       U64.v prev_fp >= U64.v mword /\
                       U64.v prev_fp < heap_size /\
                       U64.v prev_fp % U64.v mword = 0 /\
                       Seq.mem prev_fp (objects zero_addr g) /\
                       U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1)))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    read_word r.heap_out addr == read_word g addr))
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
      // chain_avoids gives cur_fp ≠ other
      chain_avoids_head_ne g cur_fp other fuel;
      assert (cur_fp <> other);
      let next_fp =
        if U64.v hd + 16 <= heap_size then read_word g obj
        else 0UL
      in
      if block_wz >= wz then begin
        // Found a suitable block (cur_fp ≠ other)
        // alloc_from_block: writes at hd, maybe rem_hd, rem_field
        // addr is in [other, other + wz(other)*8)
        // other ≠ cur_fp, so objects_separated applies
        wosize_of_object_spec other g;
        wosize_of_object_spec obj g;
        let other_wz = U64.v (wosize_of_object other g) in
        if U64.v other < U64.v obj then begin
          // other < obj: objects_separated gives obj > other + other_wz * 8
          objects_separated zero_addr g other obj;
          assert (U64.v obj > U64.v other + other_wz * 8);
          // addr + 8 <= other + other_wz*8 < obj
          // hd = obj - 8: addr + 8 <= other + other_wz*8 <= obj - 8 = hd
          assert (U64.v addr + 8 <= U64.v other + other_wz * 8);
          assert (U64.v other + other_wz * 8 <= U64.v hd);
          // So addr doesn't overlap hd, rem_hd, or rem_field (all >= hd)
          alloc_from_block_read_other_body g obj wz next_fp addr
        end else begin
          // other > obj: objects_separated gives other > obj + block_wz * 8
          objects_separated zero_addr g obj other;
          assert (U64.v other > U64.v obj + block_wz * 8);
          assert (U64.v addr >= U64.v other);
          assert (U64.v other > U64.v obj + block_wz * 8);
          if block_wz - wz >= 2 then begin
            // Split case: block_wz >= wz + 2
            assert (U64.v addr >= U64.v obj + (wz + 2) * 8);
            alloc_from_block_read_other_body g obj wz next_fp addr
          end else begin
            // Exact case: only header written. addr >= other > obj > hd + 8
            alloc_from_block_exact g obj wz next_fp;
            let bwz_u = U64.uint_to_t (U64.v (getWosize (read_word g hd))) in
            let ahdr = make_header bwz_u white_bits 0UL in
            assert (U64.v addr >= U64.v obj);
            assert (U64.v obj = U64.v hd + 8);
            read_write_different g hd addr ahdr
          end
        end;
        let (g', new_fp) = alloc_from_block g obj wz next_fp in
        // Handle prev_fp write
        if prev_fp = 0UL then ()
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          // prev_fp ≠ other (from precondition)
          // addr is in body of other: [other, other + wz(other)*8)
          // prev_fp is the address of a different object
          if U64.v prev_fp < U64.v other then begin
            // prev_fp < other: objects_separated gives other > prev_fp + wz(prev_fp)*8
            // addr >= other, prev_fp + 8 <= other (aligned), so addr >= prev_fp + 8
            assert (U64.v addr >= U64.v other);
            assert (U64.v other > U64.v prev_fp);
            assert (U64.v prev_fp + 8 <= U64.v other);
            read_write_different g' (prev_fp <: hp_addr) addr new_fp
          end else begin
            // prev_fp > other: objects_separated gives prev_fp > other + other_wz * 8
            objects_separated zero_addr g other prev_fp;
            assert (U64.v prev_fp > U64.v other + other_wz * 8);
            assert (U64.v addr + 8 <= U64.v other + other_wz * 8);
            assert (U64.v addr + 8 <= U64.v prev_fp);
            read_write_different g' (prev_fp <: hp_addr) addr new_fp
          end
        end else ()
      end
      else begin
        // Block too small, continue search
        if U64.v hd + 16 <= heap_size then begin
          fl_valid_elim g cur_fp fuel;
          chain_avoids_tail g cur_fp other fuel
        end else ();
        alloc_search_read_other g head_fp cur_fp next_fp wz (fuel - 1) other addr
      end
    end
#pop-options

/// Top-level: alloc_spec preserves reads in the body of a different object
/// not in the free-list chain.
let alloc_spec_read_other (g: heap) (fp: U64.t) (requested_wz: nat)
                          (other: obj_addr) (addr: hp_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    fl_valid g fp (heap_size / U64.v mword) /\
                    fl_chain_terminates g fp (heap_size / U64.v mword) /\
                    requested_wz >= 1 /\
                    Seq.mem other (objects zero_addr g) /\
                    chain_avoids g fp other (heap_size / U64.v mword) = true /\
                    U64.v addr >= U64.v other /\
                    U64.v addr + 8 <= U64.v other + U64.v (wosize_of_object other g) * 8)
          (ensures (let r = alloc_spec g fp requested_wz in
                    read_word r.heap_out addr == read_word g addr))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_read_other g fp 0UL fp wz (heap_size / U64.v mword) other addr

/// ---------------------------------------------------------------------------
/// Section P5: alloc_spec_preserves_chain_avoids_other
///
/// If excl was not in the free-list chain before alloc, it's not in the chain after.
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 1600 --fuel 1 --ifuel 0"
private let rec alloc_search_preserves_chain_avoids_other
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  (excl: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    fl_valid g cur_fp fuel /\
                    fl_chain_terminates g cur_fp fuel /\
                    fl_valid g head_fp (heap_size / U64.v mword) /\
                    fl_chain_terminates g head_fp (heap_size / U64.v mword) /\
                    wz >= 1 /\
                    fuel <= heap_size / U64.v mword /\
                    // excl avoids the chain from cur_fp
                    chain_avoids g cur_fp excl fuel = true /\
                    // excl avoids the entire chain from head_fp
                    chain_avoids g head_fp excl (heap_size / U64.v mword) = true /\
                    // excl is a valid object
                    U64.v excl >= U64.v mword /\ U64.v excl < heap_size /\
                    U64.v excl % U64.v mword == 0 /\
                    Seq.mem (excl <: obj_addr) (objects zero_addr g) /\
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
                    walk_chain g head_fp (heap_size / U64.v mword - fuel) = cur_fp /\
                    walk_chain_valid g head_fp (heap_size / U64.v mword - fuel) /\
                    (prev_fp <> 0UL ==> fuel < heap_size / U64.v mword /\
                                        walk_chain g head_fp (heap_size / U64.v mword - fuel - 1) = prev_fp))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    r.obj_out <> 0UL ==>
                    chain_avoids r.heap_out r.fp_out excl (heap_size / U64.v mword) = true))
          (decreases fuel)
  = let big_fuel = heap_size / U64.v mword in
    if fuel = 0 then ()
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
      wosize_of_object_spec obj g;
      wosize_of_object_bound obj g;
      getWosize_bound hdr;
      // excl ≠ cur_fp (from chain_avoids)
      chain_avoids_head_ne g cur_fp excl fuel;
      assert (cur_fp <> excl);
      let next_fp =
        if U64.v hd + 16 <= heap_size then read_word g obj
        else 0UL
      in
      assert (U64.v hd + 16 <= heap_size);
      assert (fl_valid g next_fp (fuel - 1));
      assert (fl_chain_terminates g next_fp (fuel - 1));
      // chain_avoids g next_fp excl (fuel-1) from tail
      chain_avoids_tail g cur_fp excl fuel;
      assert (chain_avoids g next_fp excl (fuel - 1) = true);
      if block_wz >= wz then begin
        // ===== Found a suitable block =====
        let (g', new_fp) = alloc_from_block g obj wz next_fp in
        fl_valid_any_fuel g next_fp (fuel - 1) big_fuel;
        fl_chain_terminates_weaken g next_fp (fuel - 1) big_fuel;
        // cur_fp not in suffix
        fl_chain_predecessor_not_in_suffix_b g cur_fp fuel;
        assert (chain_avoids g next_fp cur_fp (fuel - 1) = true);
        if prev_fp = 0UL then begin
          // ===== prev_fp = 0: fp_out = new_fp =====
          if block_wz - wz >= 2 then begin
            // ----- Split: new_fp = rem_obj -----
            alloc_split_facts_part1 g obj wz next_fp;
            alloc_from_block_objects_facts_part1 g obj wz next_fp;
            alloc_from_block_split_normal g obj wz next_fp;
            let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
            let rem_obj_nat = rem_hd_nat + 8 in
            let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
            assert (new_fp == rem_obj);
            // rem_obj ≠ excl (rem_obj is within cur_fp's block, excl is a different object)
            // rem_obj is at cur_fp + (wz+1)*8 which is within [hd, hd + (block_wz+1)*8)
            // excl ≠ cur_fp and both in objects, so objects_separated gives disjointness
            (if U64.v excl < U64.v cur_fp then begin
               objects_separated zero_addr g excl obj;
               assert (U64.v cur_fp > U64.v excl + U64.v (wosize_of_object excl g) * 8);
               assert (rem_obj_nat > U64.v excl)
             end else begin
               objects_separated zero_addr g obj excl;
               assert (U64.v excl > U64.v obj + block_wz * 8);
               assert (rem_obj_nat < U64.v obj + block_wz * 8)
             end);
            assert (rem_obj <> excl);
            // Transfer chain_avoids for next_fp chain to g'
            let transfer_aux (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr g))
              (ensures Seq.mem a (objects zero_addr g') /\
                       (U64.v (wosize_of_object a g) >= 1 ==>
                         U64.v (wosize_of_object a g') >= 1) /\
                       (U64.v (wosize_of_object a g) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g' a == read_word g a))
            = alloc_split_fl_transfer_pre_part1 g obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux);
            // Transfer: chain_avoids g next_fp excl (fuel-1) → chain_avoids g' next_fp excl (fuel-1)
            // Using transfer_excl2 with cur_fp excluded (writes at cur_fp's block)
            chain_avoids_transfer_excl2 g g' next_fp excl cur_fp (fuel - 1);
            fl_chain_terminates_transfer g g' next_fp (fuel - 1);
            chain_avoids_strengthen g' next_fp excl (fuel - 1) (big_fuel - 1);
            // rem_obj has valid header bounds
            let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
            assert (next_hd_nat <= heap_size);
            assert (rem_obj_nat + 8 <= next_hd_nat);
            hd_address_spec (new_fp <: obj_addr);
            assert (U64.v (hd_address (new_fp <: obj_addr)) + 16 <= heap_size);
            // Unfold: chain_avoids g' rem_obj excl big_fuel
            //   = (rem_obj ≠ excl) && chain_avoids g' next_fp excl (big_fuel-1)
            //   where read_word g' rem_obj = next_fp (from alloc_from_block_split_normal)
            let g1 = write_word g hd (make_header (U64.uint_to_t wz) white_bits 0UL) in
            let g2 = write_word g1 (U64.uint_to_t rem_hd_nat <: hp_addr) (make_header (U64.uint_to_t (block_wz - wz - 1)) blue_bits 0UL) in
            let g3 = write_word g2 rem_obj next_fp in
            assert (g' == g3);
            read_write_same g2 rem_obj next_fp;
            assert (read_word g' (new_fp <: obj_addr) == next_fp);
            chain_avoids_unfold_step g' new_fp excl big_fuel
          end else begin
            // ----- Exact-fit: new_fp = next_fp -----
            alloc_from_block_exact g obj wz next_fp;
            let transfer_aux_e (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr g))
              (ensures Seq.mem a (objects zero_addr g') /\
                       (U64.v (wosize_of_object a g) >= 1 ==>
                         U64.v (wosize_of_object a g') >= 1) /\
                       (U64.v (wosize_of_object a g) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g' a == read_word g a))
            = alloc_exact_fl_transfer_pre_part1 g obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux_e);
            chain_avoids_transfer_excl2 g g' next_fp excl cur_fp (fuel - 1);
            fl_chain_terminates_transfer g g' next_fp (fuel - 1);
            chain_avoids_strengthen g' next_fp excl (fuel - 1) big_fuel
          end
        end
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          // ===== prev_fp != 0: fp_out = head_fp, heap_out = g2 =====
          let prev_obj : obj_addr = prev_fp in
          let g2 = write_word g' (prev_obj <: hp_addr) new_fp in
          let d = big_fuel - fuel - 1 in
          // excl ≠ prev_fp: excl avoids the chain from head_fp which visits prev_fp
          // prev_fp = walk_chain g head_fp d, chain_avoids g head_fp excl big_fuel
          // Use chain_avoids_weaken to get chain_avoids g head_fp excl d
          // Then chain_avoids_unfold_steps to get chain_avoids g prev_fp excl (big_fuel - d)
          // Then chain_avoids_head_ne gives prev_fp ≠ excl
          walk_chain_valid_prefix g head_fp (big_fuel - fuel) d;
          chain_avoids_weaken g head_fp excl big_fuel d;
          chain_avoids_unfold_steps g head_fp excl d big_fuel;
          assert (chain_avoids g prev_fp excl (big_fuel - d) = true);
          chain_avoids_head_ne g prev_fp excl (big_fuel - d);
          assert (prev_fp <> excl);
          if block_wz - wz >= 2 then begin
            // ----- Split sub-case (prev != 0) -----
            alloc_split_facts_part1 g obj wz next_fp;
            alloc_from_block_objects_facts_part1 g obj wz next_fp;
            alloc_from_block_split_normal g obj wz next_fp;
            let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
            let rem_obj_nat = rem_hd_nat + 8 in
            let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
            assert (new_fp == rem_obj);
            let transfer_aux_s (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr g))
              (ensures Seq.mem a (objects zero_addr g') /\
                       (U64.v (wosize_of_object a g) >= 1 ==>
                         U64.v (wosize_of_object a g') >= 1) /\
                       (U64.v (wosize_of_object a g) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g' a == read_word g a))
            = alloc_split_fl_transfer_pre_part1 g obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux_s);
            write_word_locality g' (prev_obj <: hp_addr) new_fp;
            // Transfer chain_avoids for next_fp to g2 (excluding excl and prev_fp)
            // The chain from next_fp avoids both excl and prev_fp
            // Reads at chain nodes (≠ excl, ≠ prev_fp) are preserved in g2
            chain_avoids_prev g prev_fp cur_fp next_fp (fuel - 1);
            chain_avoids_transfer_excl2 g g2 next_fp excl prev_fp (fuel - 1);
            fl_chain_terminates_transfer_excl g g2 next_fp prev_fp (fuel - 1);
            // chain_avoids g2 next_fp excl (fuel-1) now established
            // Build chain_avoids g2 head_fp excl big_fuel
            // The chain from head_fp in g2: visits prefix (same as g), then prev_fp (link → new_fp),
            // then new_fp = rem_obj (link → next_fp), then next_fp tail
            // All prefix nodes ≠ excl (from chain_avoids g head_fp excl big_fuel)
            // prev_fp ≠ excl (shown above)
            // rem_obj ≠ excl (objects_separated on cur_fp vs excl)
            (if U64.v excl < U64.v cur_fp then begin
               objects_separated zero_addr g excl obj;
               assert (rem_obj_nat > U64.v excl)
             end else begin
               objects_separated zero_addr g obj excl;
               assert (U64.v excl > U64.v obj + block_wz * 8);
               assert (rem_obj_nat < U64.v obj + block_wz * 8)
             end);
            assert (rem_obj <> excl);
            // chain_avoids g2 next_fp excl (fuel-1) from transfer above
            // Now build chain_avoids g2 head_fp excl big_fuel
            let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
            assert (next_hd_nat <= heap_size);
            assert (rem_obj_nat + 8 <= next_hd_nat);
            hd_address_spec (new_fp <: obj_addr);
            assert (U64.v (hd_address (new_fp <: obj_addr)) + 16 <= heap_size);
            read_write_same (write_word (write_word g hd (make_header (U64.uint_to_t wz) white_bits 0UL)) (U64.uint_to_t rem_hd_nat <: hp_addr) (make_header (U64.uint_to_t (block_wz - wz - 1)) blue_bits 0UL)) rem_obj next_fp;
            (if U64.v prev_fp < U64.v cur_fp then begin
               objects_separated zero_addr g prev_obj obj;
               assert (U64.v new_fp > U64.v prev_fp)
             end else begin
               objects_separated zero_addr g obj prev_obj;
               assert (U64.v new_fp < U64.v prev_fp)
             end);
            read_write_different g' (prev_obj <: hp_addr) (new_fp <: hp_addr) new_fp;
            assert (read_word g2 (new_fp <: obj_addr) == next_fp);
            read_write_same g' (prev_obj <: hp_addr) new_fp;
            assert (read_word g2 (prev_fp <: obj_addr) == new_fp);
            // chain_avoids g2 next_fp excl (fuel-1) is from transfer
            // unfold new_fp: chain_avoids g2 new_fp excl fuel = chain_avoids g2 next_fp excl (fuel-1)
            chain_avoids_unfold_step g2 new_fp excl fuel;
            assert (chain_avoids g2 new_fp excl fuel = true);
            hd_address_spec prev_obj;
            // unfold prev_fp: chain_avoids g2 prev_fp excl (fuel+1) = chain_avoids g2 new_fp excl fuel
            chain_avoids_unfold_step g2 prev_fp excl (fuel + 1);
            assert (chain_avoids g2 prev_fp excl (fuel + 1) = true);
            if d = 0 then begin
              fl_chain_terminates_step g2 new_fp fuel;
              fl_chain_terminates_step g2 prev_fp (fuel + 1);
              chain_avoids_strengthen g2 prev_fp excl (fuel + 1) big_fuel
            end else begin
              // d > 0: transfer prefix and unfold
              chain_avoids_weaken g head_fp excl big_fuel d;
              walk_chain_valid_prefix g head_fp (big_fuel - fuel) d;
              fl_chain_no_early_repeat g head_fp d big_fuel;
              fl_valid_weaken g head_fp big_fuel d;
              chain_avoids_transfer_excl2 g g2 head_fp excl prev_fp d;
              walk_chain_valid_preserved g g2 head_fp prev_fp d big_fuel;
              chain_avoids_unfold_steps g2 head_fp excl d big_fuel
            end
          end else begin
            // ----- Exact-fit sub-case (prev != 0) -----
            alloc_from_block_exact g obj wz next_fp;
            let transfer_aux_e (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr g))
              (ensures Seq.mem a (objects zero_addr g') /\
                       (U64.v (wosize_of_object a g) >= 1 ==>
                         U64.v (wosize_of_object a g') >= 1) /\
                       (U64.v (wosize_of_object a g) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g' a == read_word g a))
            = alloc_exact_fl_transfer_pre_part1 g obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux_e);
            write_word_locality g' (prev_obj <: hp_addr) new_fp;
            // new_fp = next_fp (exact case)
            assert (new_fp == next_fp);
            (if new_fp = prev_fp then begin
               assert (read_word g (prev_fp <: obj_addr) == cur_fp);
               assert (next_fp == prev_fp);
               fl_chain_2cycle_not_terminates g prev_fp cur_fp (fuel - 1);
               assert false
             end else ());
            assert (new_fp <> prev_fp);
            read_write_same g' (prev_obj <: hp_addr) new_fp;
            assert (read_word g2 (prev_fp <: obj_addr) == new_fp);
            // Transfer chain_avoids for next_fp to g2 (excluding excl and prev_fp)
            chain_avoids_prev g prev_fp cur_fp next_fp (fuel - 1);
            chain_avoids_transfer_excl2 g g2 next_fp excl prev_fp (fuel - 1);
            fl_chain_terminates_transfer_excl g g2 next_fp prev_fp (fuel - 1);
            // chain_avoids g2 next_fp excl (fuel-1) → strengthen to fuel
            chain_avoids_strengthen g2 next_fp excl (fuel - 1) fuel;
            hd_address_spec prev_obj;
            chain_avoids_unfold_step g2 prev_fp excl (fuel + 1);
            assert (chain_avoids g2 prev_fp excl (fuel + 1) = true);
            // Prefix handling
            if d = 0 then begin
              // d = 0 means head_fp = prev_fp. chain_avoids g2 prev_fp excl (fuel+1)
              // → strengthen to big_fuel
              fl_chain_terminates_weaken g2 next_fp (fuel - 1) fuel;
              fl_chain_terminates_step g2 prev_fp (fuel + 1);
              chain_avoids_strengthen g2 prev_fp excl (fuel + 1) big_fuel
            end else begin
              chain_avoids_weaken g head_fp excl big_fuel d;
              walk_chain_valid_prefix g head_fp (big_fuel - fuel) d;
              fl_chain_no_early_repeat g head_fp d big_fuel;
              fl_valid_weaken g head_fp big_fuel d;
              chain_avoids_transfer_excl2 g g2 head_fp excl prev_fp d;
              walk_chain_valid_preserved g g2 head_fp prev_fp d big_fuel;
              chain_avoids_unfold_steps g2 head_fp excl d big_fuel
            end
          end
        end
        else ()
      end
      else begin
        // ===== Block too small: advance to next =====
        assert (cur_fp <> next_fp);
        assert (read_word g obj == next_fp);
        assert (U64.v hd + 16 <= heap_size);
        walk_chain_append g head_fp (big_fuel - fuel) 1;
        walk_chain_one_step g cur_fp;
        walk_chain_valid_snoc g head_fp (big_fuel - fuel);
        // chain_avoids for next_fp already established above
        chain_avoids_weaken g next_fp excl (fuel - 1) (fuel - 1);
        // chain_avoids g head_fp excl big_fuel still holds (unchanged)
        alloc_search_preserves_chain_avoids_other g head_fp cur_fp next_fp wz (fuel - 1) excl
      end
    end
#pop-options

/// Helper: when alloc_search fails (obj_out = 0UL), heap and fp are unchanged.
#restart-solver
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
private let rec alloc_search_no_alloc_unchanged
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    r.obj_out = 0UL ==> (r.heap_out == g /\ r.fp_out == head_fp)))
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
      if block_wz >= wz then ()  // obj_out = cur_fp <> 0UL, vacuous
      else begin
        let next_fp =
          if U64.v hd + 16 <= heap_size then read_word g obj else 0UL in
        alloc_search_no_alloc_unchanged g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

/// Top-level: alloc_spec preserves chain_avoids for a different object.
#restart-solver
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
let alloc_spec_preserves_chain_avoids_other (g: heap) (fp: U64.t) (requested_wz: nat)
                                            (excl: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    fl_valid g fp (heap_size / U64.v mword) /\
                    fl_chain_terminates g fp (heap_size / U64.v mword) /\
                    requested_wz >= 1 /\
                    chain_avoids g fp excl (heap_size / U64.v mword) = true /\
                    U64.v excl >= U64.v mword /\ U64.v excl < heap_size /\
                    U64.v excl % U64.v mword == 0 /\
                    Seq.mem (excl <: obj_addr) (objects zero_addr g))
          (ensures (let r = alloc_spec g fp requested_wz in
                    chain_avoids r.heap_out r.fp_out excl (heap_size / U64.v mword) = true))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    let big_fuel = heap_size / U64.v mword in
    assert (walk_chain g fp 0 == fp);
    assert (walk_chain_valid g fp 0);
    assert (big_fuel - big_fuel = 0);
    alloc_search_preserves_chain_avoids_other g fp 0UL fp wz big_fuel excl;
    alloc_search_no_alloc_unchanged g fp 0UL fp wz big_fuel
#pop-options

#pop-options // Module-level z3rlimit 20
