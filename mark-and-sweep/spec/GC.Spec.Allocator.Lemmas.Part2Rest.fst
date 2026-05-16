(*
   GC.Spec.Allocator.Lemmas.Part2Rest — remaining wfh_part4/read/blue/no_black proofs.
*)
module GC.Spec.Allocator.Lemmas.Part2Rest

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

/// ===========================================================================
/// Section P4: alloc_spec preserves well_formed_heap_part4 (no infix objects)
/// ===========================================================================

/// ---------------------------------------------------------------------------
/// P4a: alloc_from_block_preserves_wfh_part4
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0 --split_queries always"
private let alloc_from_block_preserves_wfh_part4
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    well_formed_heap_part4 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     U64.v (getWosize hdr) >= wz) /\
                    wz >= 1)
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    well_formed_heap_part4 g'))
  = let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let (g', _) = alloc_from_block g obj wz next_fp in
    hd_address_spec obj;
    hd_address_bounds obj;
    if block_wz - wz >= 2 then begin
      // Split case
      alloc_split_facts_part1 g obj wz next_fp;
      let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
      let rem_obj_nat = rem_hd_nat + 8 in
      let rem_obj_addr : obj_addr = U64.uint_to_t rem_obj_nat in
      let aux (h: obj_addr) : Lemma
        (requires Seq.mem h (objects zero_addr g'))
        (ensures ~(is_infix h g'))
      = tag_of_object_spec h g';
        is_infix_spec h g';
        hd_address_spec h;
        if h = obj then begin
          // Header = make_header wz white_bits 0UL → tag = 0
          make_header_getTag (U64.uint_to_t wz) white_bits 0UL;
          infix_tag_val ()
        end else if h = rem_obj_addr then begin
          // Header = make_header rem_wz blue_bits 0UL → tag = 0
          let rem_wz = block_wz - wz - 1 in
          make_header_getTag (U64.uint_to_t rem_wz) blue_bits 0UL;
          infix_tag_val ()
        end else begin
          // Header unchanged from g, use part4 of g
          let aux_before (p: hp_addr) : Lemma
            (requires U64.v p < U64.v hd)
            (ensures read_word g' p == read_word g p)
          = alloc_split_g3_agrees_part1 g obj wz next_fp p
          in
          FStar.Classical.forall_intro (FStar.Classical.move_requires aux_before);
          objects_addresses_gt_start zero_addr g obj;
          split_new_mem_in_old_or_rem_part1 zero_addr g g' obj wz block_wz h;
          assert (Seq.mem h (objects zero_addr g));
          wosize_of_object_spec obj g;
          if U64.v h < U64.v obj then begin
            objects_separated zero_addr g h obj;
            alloc_split_g3_agrees_part1 g obj wz next_fp (hd_address h)
          end else begin
            objects_separated zero_addr g obj h;
            alloc_split_g3_agrees_part1 g obj wz next_fp (hd_address h)
          end;
          // Now read_word g' (hd_address h) == read_word g (hd_address h)
          tag_of_object_spec h g;
          is_infix_spec h g
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    end else begin
      // Exact fit case: g' = write_word g hd (make_header block_wz white_bits 0UL)
      alloc_from_block_exact g obj wz next_fp;
      let new_hdr = make_header (U64.uint_to_t block_wz) white_bits 0UL in
      make_header_getWosize (U64.uint_to_t block_wz) white_bits 0UL;
      header_write_same_wosize_preserves_objects g obj new_hdr;
      let aux (h: obj_addr) : Lemma
        (requires Seq.mem h (objects zero_addr g'))
        (ensures ~(is_infix h g'))
      = tag_of_object_spec h g';
        is_infix_spec h g';
        hd_address_spec h;
        if h = obj then begin
          make_header_getTag (U64.uint_to_t block_wz) white_bits 0UL;
          read_write_same g hd new_hdr;
          infix_tag_val ()
        end else begin
          if U64.v h < U64.v obj then
            objects_separated zero_addr g h obj
          else
            objects_separated zero_addr g obj h;
          read_write_different g hd (hd_address h) new_hdr;
          tag_of_object_spec h g;
          is_infix_spec h g
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// P4b: write_body_preserves_wfh_part4
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
private let write_body_preserves_wfh_part4
  (g: heap) (obj: obj_addr) (addr: hp_addr) (v: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    well_formed_heap_part4 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    U64.v addr >= U64.v obj /\
                    U64.v addr < U64.v obj + (U64.v (wosize_of_object obj g) * 8) /\
                    U64.v addr % 8 = 0)
          (ensures well_formed_heap_part4 (write_word g addr v))
  = write_body_preserves_objects_local zero_addr g obj addr v;
    let g' = write_word g addr v in
    assert (objects zero_addr g' == objects zero_addr g);
    let aux (h: obj_addr) : Lemma
      (requires Seq.mem h (objects zero_addr g'))
      (ensures ~(is_infix h g'))
    = hd_address_spec h;
      hd_address_spec obj;
      tag_of_object_spec h g';
      tag_of_object_spec h g;
      is_infix_spec h g';
      is_infix_spec h g;
      if h = obj then
        read_write_different g addr (hd_address h) v
      else begin
        if U64.v h < U64.v obj then begin
          objects_separated zero_addr g h obj;
          read_write_different g addr (hd_address h) v
        end else begin
          objects_separated zero_addr g obj h;
          read_write_different g addr (hd_address h) v
        end
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// P4c: alloc_search_preserves_wfh_part4 — recursive proof
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"
private let rec alloc_search_preserves_wfh_part4
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    well_formed_heap_part4 g /\
                    fl_valid g cur_fp fuel /\
                    fl_chain_terminates g cur_fp fuel /\
                    wz >= 1 /\
                    (prev_fp <> 0UL ==>
                      (prev_fp <> cur_fp /\
                       U64.v prev_fp >= U64.v mword /\
                       U64.v prev_fp < heap_size /\
                       U64.v prev_fp % U64.v mword = 0 /\
                       Seq.mem prev_fp (objects zero_addr g) /\
                       U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1)))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    well_formed_heap_part4 r.heap_out))
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
        alloc_from_block_preserves_wfh_part4 g obj wz next_fp;
        alloc_from_block_preserves_wfh_part1 g obj wz next_fp;
        let (g', new_fp) = alloc_from_block g obj wz next_fp in
        if prev_fp = 0UL then ()
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          let prev : obj_addr = prev_fp in
          alloc_from_block_objects_facts_part1 g obj wz next_fp;
          assert (Seq.mem prev (objects zero_addr g'));
          wosize_of_object_spec prev g;
          wosize_of_object_bound prev g;
          hd_address_spec prev;
          if block_wz - wz >= 2 then begin
            let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
            if U64.v prev < U64.v obj then begin
              objects_separated zero_addr g prev obj;
              alloc_split_g3_agrees_part1 g obj wz next_fp (hd_address prev)
            end else begin
              wosize_of_object_spec obj g;
              objects_separated zero_addr g obj prev;
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
          write_body_preserves_wfh_part4 g' prev (prev <: hp_addr) new_fp;
          write_body_preserves_wfh_part1 g' prev (prev <: hp_addr) new_fp
        end
        else ()
      end
      else begin
        fl_valid_next g cur_fp fuel;
        assert (cur_fp <> next_fp);
        alloc_search_preserves_wfh_part4 g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// P4d: Top-level alloc_spec_preserves_wfh_part4
/// ---------------------------------------------------------------------------

let alloc_spec_preserves_wfh_part4 (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    well_formed_heap_part4 g /\
                    fl_valid g fp (heap_size / U64.v mword) /\
                    fl_chain_terminates g fp (heap_size / U64.v mword))
          (ensures (let r = alloc_spec g fp requested_wz in
                    well_formed_heap_part4 r.heap_out))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_preserves_wfh_part4 g fp 0UL fp wz (heap_size / U64.v mword)

/// ---------------------------------------------------------------------------
/// Allocation framing: field reads for non-allocated objects
/// ---------------------------------------------------------------------------

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

/// General helper: alloc_search preserves reads at addresses that:
/// 1. Are in the body of some object `owner` in objects(g)
/// 2. addr > owner (i.e., not at field 0 of owner)
/// 3. owner ≠ cur_fp OR addr doesn't overlap [hd(owner) .. owner+(wz+2)*8)
///
/// Key insight: addr > owner ensures addr ≠ prev_fp even if owner = prev_fp.
#restart-solver
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"
private let rec alloc_search_read_field_gt0
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  (src: obj_addr) (j: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    fl_valid g cur_fp fuel /\
                    fl_chain_terminates g cur_fp fuel /\
                    wz >= 1 /\
                    Seq.mem src (objects zero_addr g) /\
                    j > 0 /\
                    j < U64.v (wosize_of_object src g) /\
                    U64.v src + j * 8 + 8 <= heap_size /\
                    (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                     r.obj_out <> 0UL /\ src <> r.obj_out) /\
                    (prev_fp <> 0UL ==>
                      (U64.v prev_fp >= U64.v mword /\
                       U64.v prev_fp < heap_size /\
                       U64.v prev_fp % U64.v mword = 0 /\
                       Seq.mem prev_fp (objects zero_addr g) /\
                       U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1)))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    let addr : hp_addr = U64.uint_to_t (U64.v src + j * 8) in
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
      let addr : hp_addr = U64.uint_to_t (U64.v src + j * 8) in
      if block_wz >= wz then begin
        // Found suitable block: cur_fp is obj_out.
        // Since src ≠ obj_out = cur_fp:
        assert (src <> obj);
        wosize_of_object_spec src g;
        wosize_of_object_spec obj g;
        // objects_separated: addr doesn't overlap alloc_from_block writes
        if U64.v src < U64.v obj then begin
          objects_separated zero_addr g src obj;
          // src + wosize(src)*8 <= hd(obj) = obj - 8
          // addr = src + j*8 < src + wosize(src)*8 <= obj - 8 = hd
          // So addr + 8 <= hd, and addr < rem_hd, addr < rem_field
          alloc_from_block_read_other_body g obj wz next_fp addr
        end else begin
          objects_separated zero_addr g obj src;
          // src > obj + block_wz * 8 (since obj < src, separated)
          // addr = src + j*8 >= src > obj + block_wz*8 >= obj + (wz+2)*8 (for split)
          // In exact case: only hd written, which is < obj < src <= addr
          alloc_from_block_read_other_body g obj wz next_fp addr
        end;
        let (g', new_fp) = alloc_from_block g obj wz next_fp in
        // Handle prev_fp write
        if prev_fp = 0UL then ()
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          // addr = src + j*8 with j > 0, so addr >= src + 8.
          // Case 1: src = prev_fp → addr >= prev_fp + 8 → addr ≠ prev_fp
          // Case 2: src ≠ prev_fp → objects_separated gives non-overlap
          if src = prev_fp then begin
            // addr = src + j*8 >= src + 8 = prev_fp + 8
            assert (U64.v addr >= U64.v prev_fp + 8);
            read_write_different g' (prev_fp <: hp_addr) addr new_fp
          end else begin
            if U64.v prev_fp < U64.v src then begin
              objects_separated zero_addr g prev_fp src;
              // prev_fp + wosize(prev)*8 <= src - 8 < src <= addr
              assert (U64.v prev_fp + 8 <= U64.v src);
              assert (U64.v addr >= U64.v src);
              read_write_different g' (prev_fp <: hp_addr) addr new_fp
            end else begin
              objects_separated zero_addr g src prev_fp;
              // src + wosize(src)*8 <= prev_fp - 8
              // addr = src + j*8 < src + wosize(src)*8 <= prev_fp - 8 < prev_fp
              assert (U64.v addr + 8 <= U64.v prev_fp);
              read_write_different g' (prev_fp <: hp_addr) addr new_fp
            end
          end
        end else ()
      end
      else begin
        // Block too small, advance
        if U64.v hd + 16 <= heap_size then begin
          fl_valid_elim g cur_fp fuel;
          fl_chain_terminates_elim g cur_fp fuel
        end else ();
        alloc_search_read_field_gt0 g head_fp cur_fp next_fp wz (fuel - 1) src j
      end
    end
#pop-options

/// Top-level: alloc_spec preserves reads at field j > 0 of non-allocated objects.
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let alloc_spec_read_field_gt0 (g: heap) (fp: U64.t) (requested_wz: nat)
                              (src: obj_addr) (j: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    fl_valid g fp (heap_size / U64.v mword) /\
                    fl_chain_terminates g fp (heap_size / U64.v mword) /\
                    requested_wz >= 1 /\
                    (alloc_spec g fp requested_wz).obj_out <> 0UL /\
                    Seq.mem src (objects zero_addr g) /\
                    src <> (alloc_spec g fp requested_wz).obj_out /\
                    j > 0 /\
                    j < U64.v (wosize_of_object src g) /\
                    U64.v src + j * 8 + 8 <= heap_size)
          (ensures (let r = alloc_spec g fp requested_wz in
                    let addr : hp_addr = U64.uint_to_t (U64.v src + j * 8) in
                    read_word r.heap_out addr == read_word g addr))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_read_field_gt0 g fp 0UL fp wz (heap_size / U64.v mword) src j
#pop-options

/// Re-export Part1 vals (must appear after alloc_spec_read_field_gt0 per .fsti ordering)
let alloc_from_block_rem_in_objects_part1 = GC.Spec.Allocator.Lemmas.Part1.alloc_from_block_rem_in_objects_part1
let alloc_from_block_preserves_objects_part1 = GC.Spec.Allocator.Lemmas.Part1.alloc_from_block_preserves_objects_part1


/// ---------------------------------------------------------------------------
/// New objects are blue: alloc_from_block (split case)
/// ---------------------------------------------------------------------------

/// In the split case, new objects (not in original objects) are the remainder
/// and it has a blue header.
#restart-solver
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0 --split_queries always"
private let alloc_from_block_new_objects_blue_split
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (h: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     let block_wz = U64.v (getWosize hdr) in
                     block_wz >= wz /\ block_wz - wz >= 2) /\
                    (let (g', _) = alloc_from_block g obj wz next_fp in
                     Seq.mem h (objects zero_addr g') /\
                     ~(Seq.mem h (objects zero_addr g))))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    is_blue h g' = true))
  = alloc_split_facts_part1 g obj wz next_fp;
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
    let rem_obj_nat = rem_hd_nat + 8 in
    let rem_wz = block_wz - wz - 1 in
    let (g3, _) = alloc_from_block g obj wz next_fp in
    hd_address_spec obj;
    // From split_new_mem_in_old_or_rem_part1: h ∈ objects(g) ∨ h = rem_obj
    let aux_before (p: hp_addr) : Lemma
      (requires U64.v p < U64.v hd)
      (ensures read_word g3 p == read_word g p)
    = alloc_split_g3_agrees_part1 g obj wz next_fp p
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_before);
    objects_addresses_gt_start zero_addr g obj;
    split_new_mem_in_old_or_rem_part1 zero_addr g g3 obj wz block_wz h;
    // h ∉ objects(g), so h = rem_obj
    assert (U64.v h == rem_obj_nat);
    // The remainder header at rem_hd has blue_bits
    let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
    let rem_hdr = make_header (U64.uint_to_t rem_wz) blue_bits 0UL in
    // From alloc_split_facts_part1, read_word g3 rem_hd == rem_hdr
    assert (read_word g3 rem_hd == rem_hdr);
    // rem_hd = hd_address h (h = rem_obj = rem_hd + 8)
    hd_address_spec h;
    assert (hd_address h == rem_hd);
    // getColor rem_hdr = Blue
    make_header_color_blue (U64.uint_to_t rem_wz);
    // So color_of_object h g3 = Blue => is_blue h g3
    color_of_object_spec h g3;
    is_blue_iff h g3
#pop-options

/// In the exact case, no new objects appear.
#restart-solver
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0 --split_queries always"
private let alloc_from_block_no_new_objects_exact
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (h: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     let block_wz = U64.v (getWosize hdr) in
                     block_wz >= wz /\ block_wz - wz < 2) /\
                    (let (g', _) = alloc_from_block g obj wz next_fp in
                     Seq.mem h (objects zero_addr g')))
          (ensures Seq.mem h (objects zero_addr g))
  = let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    hd_address_spec obj;
    hd_address_bounds obj;
    alloc_from_block_exact g obj wz next_fp;
    // Exact fit: g' = write_word g hd (make_header block_wz white_bits 0)
    let alloc_hdr = make_header (U64.uint_to_t block_wz) white_bits 0UL in
    make_header_getWosize (U64.uint_to_t block_wz) white_bits 0UL;
    // New header has same wosize → objects are the same
    header_write_same_wosize_preserves_objects g obj alloc_hdr
#pop-options

/// Combined: alloc_from_block new objects are blue.
#restart-solver
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
private let alloc_from_block_new_objects_blue
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (h: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     U64.v (getWosize hdr) >= wz /\ wz >= 1) /\
                    (let (g', _) = alloc_from_block g obj wz next_fp in
                     Seq.mem h (objects zero_addr g') /\
                     ~(Seq.mem h (objects zero_addr g))))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    is_blue h g' = true))
  = let hdr = read_word g (hd_address obj) in
    let block_wz = U64.v (getWosize hdr) in
    if block_wz - wz >= 2 then
      alloc_from_block_new_objects_blue_split g obj wz next_fp h
    else
      alloc_from_block_no_new_objects_exact g obj wz next_fp h  // absurd
#pop-options

/// Helper: writing at prev_fp preserves is_blue for h whose header is separate.
#restart-solver
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0 --split_queries always"
private let write_prev_preserves_blue
  (g': heap) (h: obj_addr) (prev_fp: U64.t) (val_fp: U64.t)
  : Lemma (requires is_blue h g' = true /\
                    prev_fp <> 0UL /\
                    U64.v prev_fp >= U64.v mword /\
                    U64.v prev_fp < heap_size /\
                    U64.v prev_fp % U64.v mword = 0 /\
                    prev_fp <> hd_address h)
          (ensures (let g2 = write_word g' (prev_fp <: hp_addr) val_fp in
                    is_blue h g2 = true))
  = let hd = hd_address h in
    hd_address_spec h;
    hd_address_bounds h;
    let g2 = write_word g' (prev_fp <: hp_addr) val_fp in
    let p = U64.v (prev_fp <: hp_addr) in
    let hv = U64.v hd in
    FStar.Math.Lemmas.lemma_div_exact p 8;
    FStar.Math.Lemmas.lemma_div_exact hv 8;
    let kp = p / 8 in
    let kh = hv / 8 in
    if kp > kh then begin
      FStar.Math.Lemmas.lemma_mult_le_right 8 (kh + 1) kp;
      FStar.Math.Lemmas.distributivity_add_left kh 1 8
    end else begin
      FStar.Math.Lemmas.lemma_mult_le_right 8 (kp + 1) kh;
      FStar.Math.Lemmas.distributivity_add_left kp 1 8
    end;
    read_write_different g' (prev_fp <: hp_addr) hd val_fp;
    color_of_object_spec h g2;
    color_of_object_spec h g';
    is_blue_iff h g2;
    is_blue_iff h g'
#pop-options

/// ---------------------------------------------------------------------------
/// alloc_search_new_objects_blue_part1: recursive proof
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 300 --fuel 1 --ifuel 0 --split_queries always"
private let rec alloc_search_new_objects_blue_part1
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    fl_valid g cur_fp fuel /\
                    fl_chain_terminates g cur_fp fuel /\
                    wz >= 1 /\
                    (prev_fp <> 0UL ==>
                      (prev_fp <> cur_fp /\
                       U64.v prev_fp >= U64.v mword /\
                       U64.v prev_fp < heap_size /\
                       U64.v prev_fp % U64.v mword = 0 /\
                       Seq.mem prev_fp (objects zero_addr g) /\
                       U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1)))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    r.obj_out <> 0UL ==>
                    (forall (x: obj_addr).
                      Seq.mem x (objects zero_addr r.heap_out) /\
                      ~(Seq.mem x (objects zero_addr g)) ==>
                      is_blue x r.heap_out = true)))
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
        let (g', new_rem_fp) = alloc_from_block g obj wz next_fp in
        // Prove: new objects in g' are blue
        let aux_blue (x: obj_addr) : Lemma
          (requires Seq.mem x (objects zero_addr g') /\ ~(Seq.mem x (objects zero_addr g)))
          (ensures is_blue x g' = true)
        = alloc_from_block_new_objects_blue g obj wz next_fp x
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux_blue);
        if prev_fp = 0UL then ()
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          // heap_out = write_word g' prev_fp new_rem_fp
          let prev : obj_addr = prev_fp in
          // prev ≠ obj → prev's header is separate from obj's block
          // Therefore the prev_fp write preserves objects and colors
          assert (Seq.mem prev (objects zero_addr g));
          alloc_from_block_objects_facts_part1 g obj wz next_fp;
          assert (Seq.mem prev (objects zero_addr g'));
          wosize_of_object_spec prev g;
          wosize_of_object_bound prev g;
          hd_address_spec prev;
          // Show prev_fp header unchanged by alloc_from_block
          if block_wz - wz >= 2 then begin
            let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
            if U64.v prev < U64.v obj then begin
              objects_separated zero_addr g prev obj;
              alloc_split_g3_agrees_part1 g obj wz next_fp (hd_address prev)
            end else begin
              wosize_of_object_spec obj g;
              objects_separated zero_addr g obj prev;
              alloc_split_g3_agrees_part1 g obj wz next_fp (hd_address prev)
            end
          end else begin
            if U64.v prev < U64.v obj then
              objects_separated zero_addr g prev obj
            else
              objects_separated zero_addr g obj prev;
            alloc_from_block_exact g obj wz next_fp;
            let alloc_hdr = make_header (U64.uint_to_t block_wz) white_bits 0UL in
            read_write_different g hd (hd_address prev) alloc_hdr
          end;
          wosize_of_object_spec prev g';
          // write at prev_fp preserves objects
          write_body_preserves_objects_local zero_addr g' prev (prev <: hp_addr) new_rem_fp;
          // For any new object x: show is_blue x in write_word g'
          let heap_out = write_word g' (prev <: hp_addr) new_rem_fp in
          let aux_xfer (x: obj_addr) : Lemma
            (requires Seq.mem x (objects zero_addr heap_out) /\
                     ~(Seq.mem x (objects zero_addr g)))
            (ensures is_blue x heap_out = true)
          = // objects(heap_out) == objects(g'), so x ∈ objects(g')
            assert (Seq.mem x (objects zero_addr g'));
            // x ∉ objects(g) → is_blue x g'
            assert (is_blue x g' = true);
            // write at prev_fp preserves is_blue for x (prev_fp ≠ hd_address x)
            hd_address_spec x;
            // x is new (not in objects(g)), and prev ∈ objects(g)
            // In the split case, x is the remainder with hd_address in block interior
            // In the exact case, impossible (no new objects)
            // Either way, prev_fp ≠ hd_address(x):
            //   - If x is the remainder: hd(x) is in the block interior
            //   - prev ∈ objects(g), prev ≠ obj, so prev is separate from obj's block
            //   - So hd(prev) and prev are outside the block, while hd(x) is inside
            //   - prev_fp = prev, and we need prev_fp ≠ hd_address(x)
            //   - hd(x) is in [hd(obj)+wz*8+8, hd(obj)+block_wz*8)
            //   - prev is outside [hd(obj), obj+block_wz*8)
            // So prev ≠ hd(x).
            if block_wz - wz >= 2 then begin
              alloc_split_facts_part1 g obj wz next_fp;
              let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
              let rem_obj_nat = rem_hd_nat + 8 in
              // hd(x) = rem_hd (since x is rem_obj)
              let aux_before (p: hp_addr) : Lemma
                (requires U64.v p < U64.v hd)
                (ensures read_word g' p == read_word g p)
              = alloc_split_g3_agrees_part1 g obj wz next_fp p
              in
              FStar.Classical.forall_intro (FStar.Classical.move_requires aux_before);
              objects_addresses_gt_start zero_addr g obj;
              split_new_mem_in_old_or_rem_part1 zero_addr g g' obj wz block_wz x;
              assert (U64.v x == rem_obj_nat);
              assert (U64.v (hd_address x) == rem_hd_nat);
              // prev is separate from obj's block
              if U64.v prev < U64.v obj then begin
                objects_separated zero_addr g prev obj;
                assert (U64.v prev + U64.v (wosize_of_object prev g) * 8 < U64.v obj)
              end else begin
                objects_separated zero_addr g obj prev;
                assert (U64.v prev > U64.v obj + block_wz * 8);
                wosize_of_object_spec obj g
              end;
              assert (prev_fp <> hd_address x);
              write_prev_preserves_blue g' x prev_fp new_rem_fp
            end else begin
              // Exact fit: no new objects, contradiction
              alloc_from_block_no_new_objects_exact g obj wz next_fp x
            end
          in
          FStar.Classical.forall_intro (FStar.Classical.move_requires aux_xfer)
        end
        else ()
      end
      else begin
        if U64.v hd + 16 <= heap_size then
          alloc_search_new_objects_blue_part1 g head_fp cur_fp next_fp wz (fuel - 1)
        else ()
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Top-level: alloc_spec_new_objects_blue_part1
/// ---------------------------------------------------------------------------

let alloc_spec_new_objects_blue_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    fl_valid g fp (heap_size / U64.v mword) /\
                    fl_chain_terminates g fp (heap_size / U64.v mword) /\
                    requested_wz >= 1 /\
                    (alloc_spec g fp requested_wz).obj_out <> 0UL)
          (ensures (let r = alloc_spec g fp requested_wz in
                    forall (x: obj_addr).
                      Seq.mem x (objects zero_addr r.heap_out) /\
                      ~(Seq.mem x (objects zero_addr g)) ==>
                      is_blue x r.heap_out = true))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_new_objects_blue_part1 g fp 0UL fp wz (heap_size / U64.v mword)

/// ---------------------------------------------------------------------------
/// alloc_from_block_objects_backward_part1:
/// Backward inclusion — new objects in g' that weren't in g must be the remainder.
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0 --split_queries always"
let alloc_from_block_objects_backward_part1
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (h: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     let bwz = U64.v (getWosize hdr) in
                     bwz >= wz /\ wz >= 1 /\ bwz - wz >= 2) /\
                    (let (g', _) = alloc_from_block g obj wz next_fp in
                     Seq.mem h (objects zero_addr g') /\
                     ~(Seq.mem h (objects zero_addr g))))
          (ensures h == snd (alloc_from_block g obj wz next_fp))
  = alloc_split_facts_part1 g obj wz next_fp;
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
    let rem_obj_nat = rem_hd_nat + 8 in
    let (g3, rem_fp) = alloc_from_block g obj wz next_fp in
    hd_address_spec obj;
    // Use split_new_mem_in_old_or_rem_part1: h ∈ objects(g) ∨ h = rem_obj
    let aux_before (p: hp_addr) : Lemma
      (requires U64.v p < U64.v hd)
      (ensures read_word g3 p == read_word g p)
    = alloc_split_g3_agrees_part1 g obj wz next_fp p
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_before);
    objects_addresses_gt_start zero_addr g obj;
    split_new_mem_in_old_or_rem_part1 zero_addr g g3 obj wz block_wz h;
    // h ∉ objects(g), so h must be rem_obj
    assert (U64.v h == rem_obj_nat);
    // rem_fp = rem_obj from alloc_split_facts_part1
    assert (rem_fp == U64.uint_to_t rem_obj_nat);
    // Therefore h = rem_fp = snd(alloc_from_block ...)
    assert (U64.v h == U64.v rem_fp)
#pop-options


/// ===========================================================================
/// Section: alloc_spec preserves no_black_objects (part1 variant)
/// ===========================================================================

/// ---------------------------------------------------------------------------
/// Helper: writing within a body field preserves no_black_objects.
/// No well_formed_heap needed — just objects_separated + read_write_different.
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--split_queries always --z3rlimit 40 --fuel 0 --ifuel 0"
private let field_write_preserves_no_black_part1
  (g: heap) (obj: obj_addr) (addr: hp_addr) (v: U64.t)
  : Lemma (requires GC.Spec.Mark.no_black_objects g /\
                    Seq.mem obj (objects zero_addr g) /\
                    U64.v addr >= U64.v obj /\
                    U64.v addr < U64.v obj + U64.v (wosize_of_object obj g) * 8 /\
                    U64.v addr % 8 = 0)
          (ensures GC.Spec.Mark.no_black_objects (write_word g addr v))
  = let g' = write_word g addr v in
    write_body_preserves_objects_local zero_addr g obj addr v;
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
/// alloc_from_block preserves no_black_objects under well_formed_heap_part1.
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--split_queries always --z3rlimit 80 --fuel 0 --ifuel 0"
private let alloc_from_block_preserves_no_black_part1
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires GC.Spec.Mark.no_black_objects g /\
                    well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     U64.v (getWosize hdr) >= wz /\ wz >= 1))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    GC.Spec.Mark.no_black_objects g'))
  = let hdr = read_word g (hd_address obj) in
    let block_wz = U64.v (getWosize hdr) in
    let hd = hd_address obj in
    let (g', rem_fp) = alloc_from_block g obj wz next_fp in
    hd_address_spec obj;
    getWosize_bound hdr;
    wosize_of_object_spec obj g;
    if block_wz - wz >= 2 then begin
      // Split case
      alloc_split_facts_part1 g obj wz next_fp;
      let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
      let rem_obj_nat = rem_hd_nat + 8 in
      let rem_wz = block_wz - wz - 1 in
      let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
      let rem_obj_addr : obj_addr = U64.uint_to_t rem_obj_nat in
      // Frame: reads before hd_address(obj) are preserved
      let aux_before (p: hp_addr) : Lemma
        (requires U64.v p < U64.v hd)
        (ensures read_word g' p == read_word g p)
      = alloc_split_g3_agrees_part1 g obj wz next_fp p
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux_before);
      // Color facts for new/modified objects
      make_header_getColor (U64.uint_to_t wz) white_bits 0UL;
      getColor_raw (make_header (U64.uint_to_t wz) white_bits 0UL);
      make_header_getColor (U64.uint_to_t rem_wz) blue_bits 0UL;
      getColor_raw (make_header (U64.uint_to_t rem_wz) blue_bits 0UL);
      let aux (h: obj_addr) : Lemma
        (requires Seq.mem h (objects zero_addr g'))
        (ensures ~(is_black h g'))
      = objects_addresses_gt_start zero_addr g obj;
        split_new_mem_in_old_or_rem_part1 zero_addr g g' obj wz block_wz h;
        if U64.v h = rem_obj_nat then begin
          // New remainder object: blue header → not black
          hd_address_spec rem_obj_addr;
          color_of_object_spec rem_obj_addr g';
          is_black_iff rem_obj_addr g'
        end else begin
          assert (Seq.mem h (objects zero_addr g));
          if h = obj then begin
            // Allocated block: white header → not black
            color_of_object_spec obj g';
            is_black_iff obj g'
          end else begin
            // Pre-existing other object: header unchanged → not black
            hd_address_spec h;
            if U64.v h < U64.v obj then begin
              objects_separated zero_addr g h obj;
              alloc_split_g3_agrees_part1 g obj wz next_fp (hd_address h)
            end else begin
              objects_separated zero_addr g obj h;
              assert (U64.v (hd_address h) > U64.v hd + block_wz * 8);
              alloc_split_g3_agrees_part1 g obj wz next_fp (hd_address h)
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
      getWosize_bound hdr;
      make_header_getWosize (U64.uint_to_t block_wz) white_bits 0UL;
      header_write_same_wosize_preserves_objects g obj alloc_hdr;
      read_write_same g hd alloc_hdr;
      make_header_getColor (U64.uint_to_t block_wz) white_bits 0UL;
      getColor_raw alloc_hdr;
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
/// alloc_search preserves no_black_objects (part1 variant)
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
private let rec alloc_search_preserves_no_black_part1
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires GC.Spec.Mark.no_black_objects g /\
                    well_formed_heap_part1 g /\
                    wz >= 1 /\
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
                    GC.Spec.Mark.no_black_objects r.heap_out))
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
      wosize_of_object_spec obj g;
      assert (Seq.mem obj (objects zero_addr g));
      let next_fp =
        if U64.v hd + 16 <= heap_size then read_word g obj
        else 0UL
      in
      if block_wz >= wz then begin
        alloc_from_block_preserves_no_black_part1 g obj wz next_fp;
        let (g', new_fp) = alloc_from_block g obj wz next_fp in
        if prev_fp = 0UL then ()
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          let prev : obj_addr = prev_fp in
          alloc_from_block_objects_facts_part1 g obj wz next_fp;
          assert (Seq.mem prev (objects zero_addr g'));
          alloc_from_block_preserves_wfh_part1 g obj wz next_fp;
          hd_address_spec prev;
          wosize_of_object_spec prev g;
          wosize_of_object_bound prev g;
          wfh_part1_obj_bound g prev;
          if block_wz - wz >= 2 then begin
            let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
            let rem_obj_nat = rem_hd_nat + 8 in
            if U64.v prev < U64.v obj then begin
              objects_separated zero_addr g prev obj;
              alloc_split_g3_agrees_part1 g obj wz next_fp (hd_address prev)
            end else begin
              objects_separated zero_addr g obj prev;
              assert (U64.v prev > U64.v obj + block_wz * 8);
              assert (U64.v (hd_address prev) > U64.v obj + block_wz * 8 - 8);
              assert (U64.v (hd_address prev) <> U64.v hd);
              assert (U64.v (hd_address prev) <> rem_hd_nat);
              assert (U64.v (hd_address prev) <> rem_obj_nat);
              alloc_split_g3_agrees_part1 g obj wz next_fp (hd_address prev)
            end
          end else begin
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
          field_write_preserves_no_black_part1 g' prev (prev <: hp_addr) new_fp
        end
        else ()
      end
      else begin
        fl_valid_elim g cur_fp fuel;
        (if U64.v hd + 16 <= heap_size then
          fl_chain_terminates_elim g cur_fp fuel);
        alloc_search_preserves_no_black_part1 g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Top-level: alloc_spec preserves no_black_objects (part1 variant)
/// ---------------------------------------------------------------------------

let alloc_spec_preserves_no_black_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires GC.Spec.Mark.no_black_objects g /\
                    well_formed_heap_part1 g /\
                    fl_valid g fp (heap_size / U64.v mword) /\
                    fl_chain_terminates g fp (heap_size / U64.v mword))
          (ensures (let r = alloc_spec g fp requested_wz in
                    GC.Spec.Mark.no_black_objects r.heap_out))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_preserves_no_black_part1 g fp 0UL fp wz (heap_size / U64.v mword)

#pop-options // Module-level z3rlimit 20
