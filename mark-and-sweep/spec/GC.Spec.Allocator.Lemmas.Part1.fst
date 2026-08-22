(*
   GC.Spec.Allocator.Lemmas.Part1 — Section P1 proofs.

   alloc_spec / alloc_from_block preserve object membership under
   well_formed_heap_part1 (weaker precondition than well_formed_heap).
*)
module GC.Spec.Allocator.Lemmas.Part1

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
open GC.Spec.Allocator.Lemmas.Header
module U64 = FStar.UInt64
module Seq = FStar.Seq

/// Module-level default: all functions get z3rlimit 20 unless overridden
#push-options "--z3rlimit 20 --z3refresh"

/// ===========================================================================
/// Local helpers (private, not in .fsti)
/// ===========================================================================

/// If getWosize is the same at every header position, objects walk is the same
private let rec wosize_eq_implies_objects_eq
  (start: hp_addr) (g g': heap)
  : Lemma (requires Seq.length g' == Seq.length g /\
                    (forall (p: hp_addr). getWosize (read_word g' p) == getWosize (read_word g p)))
          (ensures objects start g' == objects start g)
          (decreases (Seq.length g - U64.v start))
  = if U64.v start + 8 >= Seq.length g then ()
    else begin
      let wz = getWosize (read_word g start) in
      let next_start_nat = U64.v start + (U64.v wz + 1) * 8 in
      if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then ()
      else if next_start_nat >= heap_size then ()
      else wosize_eq_implies_objects_eq (U64.uint_to_t next_start_nat) g g'
    end

/// A write to hd_address(obj) with same getWosize preserves objects from 0
private let header_write_same_wosize_preserves_objects
  (g: heap) (obj: obj_addr) (new_hdr: U64.t)
  : Lemma (requires getWosize new_hdr == getWosize (read_word g (hd_address obj)))
          (ensures objects zero_addr (write_word g (hd_address obj) new_hdr) == objects zero_addr g)
  = let hd = hd_address obj in
    let g' = write_word g hd new_hdr in
    hd_address_spec obj;
    let aux (p: hp_addr) : Lemma (getWosize (read_word g' p) == getWosize (read_word g p))
      = if U64.v p = U64.v hd then
          read_write_same g hd new_hdr
        else
          read_write_different g hd p new_hdr
    in
    FStar.Classical.forall_intro aux;
    wosize_eq_implies_objects_eq zero_addr g g'

/// If objects(start, g) is non-empty (contains any h), then f_address start
/// is also a member (it's the first element).
#restart-solver
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
private let objects_nonempty_first_mem
  (start: hp_addr) (g: heap) (h: obj_addr)
  : Lemma (requires Seq.mem h (objects start g))
          (ensures Seq.mem (f_address start) (objects start g))
  = if U64.v start + 8 >= Seq.length g then ()
    else begin
      let header = read_word g start in
      let wz = getWosize header in
      let next_nat = U64.v start + (U64.v wz + 1) * 8 in
      if next_nat > Seq.length g || next_nat >= pow2 64 then ()
      else begin
        f_address_spec start;
        let first : obj_addr = f_address start in
        if next_nat >= heap_size then
          mem_cons_lemma first first (Seq.empty #obj_addr)
        else
          mem_cons_lemma first first (objects (U64.uint_to_t next_nat <: hp_addr) g)
      end
    end
#pop-options

/// If h ∈ objects(later, g) and later is at a reachable object boundary from start
/// (i.e., f_address later ∈ objects start g), then h ∈ objects(start, g).
#restart-solver
#push-options "--z3rlimit 200 --fuel 3 --ifuel 1"
private let rec objects_later_in_earlier
  (start: hp_addr) (g: heap) (later: hp_addr) (h: obj_addr)
  : Lemma (requires U64.v start <= U64.v later /\
                    Seq.mem h (objects later g) /\
                    (U64.v start = U64.v later \/ Seq.mem (f_address later) (objects start g)))
          (ensures Seq.mem h (objects start g))
          (decreases (Seq.length g - U64.v start))
  = if U64.v start = U64.v later then ()
    else if U64.v start + 8 >= Seq.length g then ()
    else begin
      let header = read_word g start in
      let wz_start = getWosize header in
      let next_nat = U64.v start + (U64.v wz_start + 1) * 8 in
      if next_nat > Seq.length g || next_nat >= pow2 64 then
        ()
      else begin
        f_address_spec start;
        let first : obj_addr = f_address start in
        if next_nat >= heap_size then begin
          mem_cons_lemma (f_address later) first (Seq.empty #obj_addr);
          f_address_spec later;
          assert (f_address later = first);
          assert (U64.v later = U64.v start)
        end
        else begin
          let next_hp : hp_addr = U64.uint_to_t next_nat in
          mem_cons_lemma (f_address later) first (objects next_hp g);
          if f_address later = first then begin
            f_address_spec later;
            assert (U64.v later = U64.v start)
          end
          else begin
            objects_addresses_gt_start next_hp g (f_address later);
            f_address_spec later;
            assert (U64.v next_hp <= U64.v later);
            objects_later_in_earlier next_hp g later h;
            mem_cons_lemma h first (objects next_hp g)
          end
        end
      end
    end
#pop-options

/// Part1 variant: same as split_next_hd_objects_eq but only requires well_formed_heap_part1
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
private let split_next_hd_objects_eq_part1
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     let block_wz = U64.v (getWosize hdr) in
                     block_wz >= wz /\ block_wz - wz >= 2))
          (ensures (let hd = hd_address obj in
                    let hdr = read_word g hd in
                    let block_wz = U64.v (getWosize hdr) in
                    let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
                    let (g3, _) = alloc_from_block g obj wz next_fp in
                    next_hd_nat < heap_size ==>
                    (let next_hd : hp_addr = U64.uint_to_t next_hd_nat in
                     objects next_hd g3 == objects next_hd g)))
  = let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
    hd_address_spec obj;
    hd_address_bounds obj;
    wfh_part1_obj_bound g obj;
    wosize_of_object_spec obj g;
    getWosize_bound hdr;
    let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
    let rem_obj_nat = rem_hd_nat + 8 in
    assert (next_hd_nat >= rem_obj_nat + 8);
    assert (rem_hd_nat < heap_size);
    assert (rem_obj_nat < heap_size);
    alloc_from_block_split_normal g obj wz next_fp;
    let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
    let g1 = write_word g hd alloc_hdr in
    aligned_plus_mul8 (U64.v hd) (1 + wz);
    let rem_hd : hp_addr = mk_hp_addr rem_hd_nat in
    let rem_wz = block_wz - wz - 1 in
    let rem_hdr = make_header (U64.uint_to_t rem_wz) blue_bits 0UL in
    let g2 = write_word g1 rem_hd rem_hdr in
    aligned_plus_mul8 rem_hd_nat 1;
    let rem_obj : hp_addr = mk_hp_addr rem_obj_nat in
    let g3 = write_word g2 rem_obj next_fp in
    if next_hd_nat < heap_size then begin
      let next_hd : hp_addr = U64.uint_to_t next_hd_nat in
      write_word_preserves_objects_before next_hd g2 rem_obj next_fp;
      write_word_preserves_objects_before next_hd g1 rem_hd rem_hdr;
      write_word_preserves_objects_before next_hd g hd alloc_hdr
    end
#pop-options

/// ===========================================================================
/// Section P1: alloc_spec_preserves_objects under well_formed_heap_part1
/// ===========================================================================

/// ---------------------------------------------------------------------------
/// P1a: split_old_mem_in_new_part1
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 100 --fuel 3 --ifuel 1"
private let rec split_old_mem_in_new_part1
  (start: hp_addr) (g g3: heap)
  (obj: obj_addr) (wz block_wz: nat)
  (h: obj_addr)
  : Lemma (requires
      Seq.length g3 == Seq.length g /\
      well_formed_heap_part1 g /\
      Seq.mem obj (objects zero_addr g) /\
      (let hd = hd_address obj in
       let hdr = read_word g hd in
       U64.v (getWosize hdr) == block_wz /\
       block_wz >= wz /\ block_wz - wz >= 2 /\
       (let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
        let rem_obj_nat = rem_hd_nat + 8 in
        let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
        rem_hd_nat < heap_size /\
        rem_obj_nat < heap_size /\
        next_hd_nat <= heap_size /\
        (forall (p: hp_addr). U64.v p < U64.v hd ==> read_word g3 p == read_word g p) /\
        getWosize (read_word g3 hd) == U64.uint_to_t wz /\
        (rem_hd_nat < heap_size ==>
          getWosize (read_word g3 (U64.uint_to_t rem_hd_nat <: hp_addr)) == U64.uint_to_t (block_wz - wz - 1)) /\
        (next_hd_nat < heap_size ==>
          objects (U64.uint_to_t next_hd_nat <: hp_addr) g3 == objects (U64.uint_to_t next_hd_nat <: hp_addr) g) /\
        U64.v start <= U64.v hd)) /\
      Seq.mem h (objects start g) /\
      (U64.v start = U64.v zero_addr \/ Seq.mem (f_address start) (objects zero_addr g)))
    (ensures Seq.mem h (objects start g3))
    (decreases (Seq.length g - U64.v start))
  = let hd = hd_address obj in
    hd_address_spec obj;
    if U64.v start + 8 >= Seq.length g then ()
    else begin
      let header_g = read_word g start in
      let wz_g = getWosize header_g in
      let next_nat = U64.v start + (U64.v wz_g + 1) * 8 in
      if next_nat > Seq.length g || next_nat >= pow2 64 then ()
      else begin
        f_address_spec start;
        let first : obj_addr = f_address start in
        mem_cons_lemma h first
          (if next_nat >= heap_size then Seq.empty
           else objects (U64.uint_to_t next_nat <: hp_addr) g);
        if U64.v start = U64.v hd then begin
          let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
          let rem_obj_nat = rem_hd_nat + 8 in
          let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
          assert (first == obj);
          let header_g3 = read_word g3 hd in
          assert (getWosize header_g3 == U64.uint_to_t wz);
          let next_g3 = U64.v hd + (wz + 1) * 8 in
          assert (next_g3 == rem_hd_nat);
          if h = first then begin
            assert (U64.v start + 8 < Seq.length g3);
            assert (next_g3 <= Seq.length g3);
            assert (next_g3 < pow2 64);
            if next_g3 >= heap_size then
              mem_cons_lemma h obj (Seq.empty #obj_addr)
            else begin
              let rem_hd_hp : hp_addr = U64.uint_to_t rem_hd_nat in
              mem_cons_lemma h obj (objects rem_hd_hp g3)
            end
          end else begin
            assert (next_nat == next_hd_nat);
            if next_hd_nat >= heap_size then ()
            else begin
              let next_hd : hp_addr = U64.uint_to_t next_hd_nat in
              assert (Seq.mem h (objects next_hd g));
              assert (objects next_hd g3 == objects next_hd g);
              assert (Seq.mem h (objects next_hd g3));
              let rem_hd_hp : hp_addr = U64.uint_to_t rem_hd_nat in
              f_address_spec rem_hd_hp;
              let rem_obj_addr : obj_addr = f_address rem_hd_hp in
              assert (U64.v rem_obj_addr == rem_obj_nat);
              let rem_wz = block_wz - wz - 1 in
              let next_from_rem = rem_hd_nat + (rem_wz + 1) * 8 in
              assert (next_from_rem == next_hd_nat);
              if next_hd_nat >= heap_size then
                mem_cons_lemma h rem_obj_addr (Seq.empty #obj_addr)
              else
                mem_cons_lemma h rem_obj_addr (objects next_hd g3);
              mem_cons_lemma h obj (objects rem_hd_hp g3)
            end
          end
        end else begin
          assert (U64.v start < U64.v hd);
          assert (read_word g3 start == read_word g start);
          let header_g3 = read_word g3 start in
          assert (header_g3 == header_g);
          assert (getWosize header_g3 == wz_g);
          if h = first then begin
            if next_nat >= heap_size then
              mem_cons_lemma h first (Seq.empty #obj_addr)
            else
              mem_cons_lemma h first (objects (U64.uint_to_t next_nat <: hp_addr) g3)
          end else begin
            if next_nat >= heap_size then ()
            else begin
              let next_hp : hp_addr = U64.uint_to_t next_nat in
              assert (Seq.mem h (objects next_hp g));
              mem_cons_lemma first first
                (if next_nat >= heap_size then Seq.empty
                 else objects (U64.uint_to_t next_nat <: hp_addr) g);
              assert (Seq.mem first (objects start g));
              // Establish start >= zero_addr for objects_later_in_earlier
              (match () with
               | _ ->
                 if U64.v start = U64.v zero_addr then ()
                 else begin
                   objects_addresses_gt_start zero_addr g (f_address start);
                   f_address_spec start
                 end);
              assert (U64.v zero_addr <= U64.v start);
              objects_later_in_earlier zero_addr g start first;
              assert (Seq.mem first (objects zero_addr g));
              hd_address_spec first;
              wosize_of_object_spec first g;
              objects_separated zero_addr g first obj;
              assert (U64.v hd % 8 == 0);
              assert (U64.v start % 8 == 0);
              FStar.Math.Lemmas.cancel_mul_mod (U64.v wz_g) 8;
              assert ((U64.v start + U64.v wz_g * 8) % 8 == 0);
              assert (U64.v hd > U64.v start + U64.v wz_g * 8);
              assert (next_nat <= U64.v hd);
              objects_nonempty_first_mem next_hp g h;
              mem_cons_lemma (f_address next_hp) first (objects next_hp g);
              objects_later_in_earlier zero_addr g start (f_address next_hp);
              split_old_mem_in_new_part1 next_hp g g3 obj wz block_wz h;
              mem_cons_lemma h first (objects next_hp g3)
            end
          end
        end
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// P1b: alloc_split_facts_part1
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let alloc_split_facts_part1
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     let block_wz = U64.v (getWosize hdr) in
                     block_wz >= wz /\ block_wz - wz >= 2))
          (ensures (let hd = hd_address obj in
                    let hdr = read_word g hd in
                    let block_wz = U64.v (getWosize hdr) in
                    let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
                    let rem_obj_nat = rem_hd_nat + 8 in
                    let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
                    let rem_wz = block_wz - wz - 1 in
                    rem_hd_nat >= 8 /\
                    rem_obj_nat >= 16 /\
                    rem_hd_nat < heap_size /\
                    rem_obj_nat < heap_size /\
                    next_hd_nat <= heap_size /\
                    rem_hd_nat % 8 == 0 /\
                    rem_obj_nat % 8 == 0 /\
                    rem_hd_nat < pow2 64 /\
                    rem_obj_nat < pow2 64 /\
                    next_hd_nat < pow2 64 /\
                    wz < pow2 54 /\
                    rem_wz < pow2 54 /\
                    getWosize (make_header (U64.uint_to_t wz) white_bits 0UL) == U64.uint_to_t wz /\
                    getWosize (make_header (U64.uint_to_t rem_wz) blue_bits 0UL) == U64.uint_to_t rem_wz /\
                    (let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
                     let g1 = write_word g hd alloc_hdr in
                     let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
                     let rem_hdr = make_header (U64.uint_to_t rem_wz) blue_bits 0UL in
                     let g2 = write_word g1 rem_hd rem_hdr in
                     let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
                     let g3 = write_word g2 rem_obj next_fp in
                     alloc_from_block g obj wz next_fp == (g3, rem_obj) /\
                     Seq.length g3 == Seq.length g /\
                     read_word g3 hd == alloc_hdr /\
                     read_word g3 rem_hd == rem_hdr /\
                     getWosize (read_word g3 hd) == U64.uint_to_t wz /\
                     getWosize (read_word g3 rem_hd) == U64.uint_to_t rem_wz /\
                     (next_hd_nat < heap_size ==>
                       (let next_hd_hp : hp_addr = U64.uint_to_t next_hd_nat in
                        objects next_hd_hp g3 ==
                        objects next_hd_hp g)))))
  = let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    hd_address_spec obj;
    hd_address_bounds obj;
    wosize_of_object_spec obj g;
    assert (U64.v hd + 8 + block_wz * 8 <= Seq.length g);
    getWosize_bound hdr;
    let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
    let rem_obj_nat = rem_hd_nat + 8 in
    let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
    let rem_wz = block_wz - wz - 1 in
    assert (wz < pow2 54);
    assert (rem_wz < pow2 54);
    make_header_getWosize (U64.uint_to_t wz) white_bits 0UL;
    make_header_getWosize (U64.uint_to_t rem_wz) blue_bits 0UL;
    alloc_from_block_split_normal g obj wz next_fp;
    let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
    let g1 = write_word g hd alloc_hdr in
    let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
    let rem_hdr = make_header (U64.uint_to_t rem_wz) blue_bits 0UL in
    let g2 = write_word g1 rem_hd rem_hdr in
    let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
    let g3 = write_word g2 rem_obj next_fp in
    read_write_different g2 rem_obj hd next_fp;
    read_write_different g1 rem_hd hd rem_hdr;
    read_write_same g hd alloc_hdr;
    read_write_different g2 rem_obj rem_hd next_fp;
    read_write_same g1 rem_hd rem_hdr;
    split_next_hd_objects_eq_part1 g obj wz next_fp
#pop-options

/// ---------------------------------------------------------------------------
/// P1c: alloc_split_g3_agrees_part1
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let alloc_split_g3_agrees_part1
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (p: hp_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hd = hd_address obj in
                     let hdr = read_word g hd in
                     let block_wz = U64.v (getWosize hdr) in
                     block_wz >= wz /\ block_wz - wz >= 2 /\
                     (let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
                      let rem_obj_nat = rem_hd_nat + 8 in
                      U64.v p <> U64.v hd /\
                      U64.v p <> rem_hd_nat /\
                      U64.v p <> rem_obj_nat)))
          (ensures (let (g3, _) = alloc_from_block g obj wz next_fp in
                    read_word g3 p == read_word g p))
  = let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    hd_address_spec obj;
    hd_address_bounds obj;
    wosize_of_object_spec obj g;
    getWosize_bound hdr;
    let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
    let rem_obj_nat = rem_hd_nat + 8 in
    alloc_from_block_split_normal g obj wz next_fp;
    let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
    let g1 = write_word g hd alloc_hdr in
    aligned_plus_mul8 (U64.v hd) (1 + wz);
    let rem_hd : hp_addr = mk_hp_addr rem_hd_nat in
    let rem_wz = block_wz - wz - 1 in
    let rem_hdr = make_header (U64.uint_to_t rem_wz) blue_bits 0UL in
    let g2 = write_word g1 rem_hd rem_hdr in
    aligned_plus_mul8 rem_hd_nat 1;
    let rem_obj : hp_addr = mk_hp_addr rem_obj_nat in
    let g3 = write_word g2 rem_obj next_fp in
    read_write_different g2 rem_obj p next_fp;
    read_write_different g1 rem_hd p rem_hdr;
    read_write_different g hd p alloc_hdr
#pop-options

/// ---------------------------------------------------------------------------
/// P1d: alloc_split_old_in_new_part1
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 25 --fuel 0 --ifuel 0"
let alloc_split_old_in_new_part1
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (h: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     let block_wz = U64.v (getWosize hdr) in
                     block_wz >= wz /\ block_wz - wz >= 2) /\
                    Seq.mem h (objects zero_addr g))
          (ensures (let (g3, _) = alloc_from_block g obj wz next_fp in
                    Seq.mem h (objects zero_addr g3)))
  = alloc_split_facts_part1 g obj wz next_fp;
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
    let rem_obj_nat = rem_hd_nat + 8 in
    let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
    let rem_wz = block_wz - wz - 1 in
    let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
    let g1 = write_word g hd alloc_hdr in
    let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
    let rem_hdr = make_header (U64.uint_to_t rem_wz) blue_bits 0UL in
    let g2 = write_word g1 rem_hd rem_hdr in
    let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
    let g3 = write_word g2 rem_obj next_fp in
    hd_address_spec obj;
    let aux_before (p: hp_addr) : Lemma
      (requires U64.v p < U64.v hd)
      (ensures read_word g3 p == read_word g p)
    = alloc_split_g3_agrees_part1 g obj wz next_fp p
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_before);
    objects_addresses_gt_start zero_addr g obj;
    assert (U64.v zero_addr <= U64.v hd);
    split_old_mem_in_new_part1 zero_addr g g3 obj wz block_wz h
#pop-options

/// ---------------------------------------------------------------------------
/// P1e: alloc_from_block_objects_facts_part1
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let alloc_from_block_objects_facts_part1
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     U64.v (getWosize hdr) >= wz))
          (ensures (let (g', rem_fp) = alloc_from_block g obj wz next_fp in
                    (forall (h: obj_addr). Seq.mem h (objects zero_addr g) ==> Seq.mem h (objects zero_addr g'))))
  = let hdr = read_word g (hd_address obj) in
    let block_wz = U64.v (getWosize hdr) in
    let (g', rem_fp) = alloc_from_block g obj wz next_fp in
    if block_wz - wz >= 2 then begin
      // Split case
      let aux (h: obj_addr) : Lemma
        (requires Seq.mem h (objects zero_addr g))
        (ensures Seq.mem h (objects zero_addr g'))
      = alloc_split_old_in_new_part1 g obj wz next_fp h
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    end else begin
      // Exact fit case: objects are the same
      alloc_from_block_exact g obj wz next_fp;
      let alloc_hdr = make_header (U64.uint_to_t block_wz) white_bits 0UL in
      make_header_getWosize (U64.uint_to_t block_wz) white_bits 0UL;
      header_write_same_wosize_preserves_objects g obj alloc_hdr
    end
#pop-options

/// ---------------------------------------------------------------------------
/// P1e2: write_body_preserves_objects_local
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 20 --fuel 2 --ifuel 0"
let rec write_body_preserves_objects_local
  (start: hp_addr) (g: heap) (obj: obj_addr) (addr: hp_addr) (v: U64.t)
  : Lemma (requires
      Seq.mem obj (objects start g) /\
      U64.v addr >= U64.v obj /\
      U64.v addr < U64.v obj + (U64.v (wosize_of_object obj g) * 8) /\
      U64.v addr % 8 = 0)
    (ensures objects start (write_word g addr v) == objects start g)
    (decreases (Seq.length g - U64.v start))
  =
  if U64.v start + 8 >= Seq.length g then ()
  else begin
    let header = read_word g start in
    let wz = getWosize header in
    let obj_size_nat = U64.v wz + 1 in
    let next_start_nat = U64.v start + (obj_size_nat * 8) in
    if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then ()
    else begin
      let obj_addr_raw = f_address start in
      f_address_spec start;
      let oa : obj_addr = obj_addr_raw in
      hd_address_spec oa;
      if oa = obj then begin
        // addr >= obj = start + 8, so addr > start
        read_write_different g addr start v;
        if next_start_nat >= heap_size then ()
        else begin
          let next_start : hp_addr = U64.uint_to_t next_start_nat in
          wosize_of_object_spec obj g;
          assert (U64.v addr < next_start_nat);
          write_word_preserves_objects_before next_start g addr v
        end
      end else begin
        if next_start_nat >= heap_size then begin
          mem_cons_lemma obj oa (Seq.empty #obj_addr);
          assert (obj = oa)
        end else begin
          let next_start : hp_addr = U64.uint_to_t next_start_nat in
          mem_cons_lemma obj oa (objects next_start g);
          objects_addresses_gt_start start g obj;
          read_write_different g addr start v;
          write_body_preserves_objects_local next_start g obj addr v
        end
      end
    end
  end
#pop-options

/// ---------------------------------------------------------------------------
/// alloc_from_block_preserves_objects_part1
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let alloc_from_block_preserves_objects_part1
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     U64.v (getWosize hdr) >= wz))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    (forall (h: obj_addr). Seq.mem h (objects zero_addr g) ==> Seq.mem h (objects zero_addr g'))))
  = alloc_from_block_objects_facts_part1 g obj wz next_fp
#pop-options

/// ---------------------------------------------------------------------------
/// alloc_from_block_rem_in_objects_part1
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let alloc_from_block_rem_in_objects_part1
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     let bwz = U64.v (getWosize hdr) in
                     bwz >= wz /\ bwz - wz >= 2))
          (ensures (let (g', rem_fp) = alloc_from_block g obj wz next_fp in
                    is_pointer_field rem_fp /\
                    Seq.mem rem_fp (objects zero_addr g')))
  = alloc_split_facts_part1 g obj wz next_fp;
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
    let rem_obj_nat = rem_hd_nat + 8 in
    let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
    let rem_wz = block_wz - wz - 1 in
    let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
    let g3 = fst (alloc_from_block g obj wz next_fp) in
    hd_address_spec obj;
    f_address_spec rem_hd;
    let rem_obj_addr : obj_addr = f_address rem_hd in
    // rem_obj is in objects(rem_hd, g3) as the head element
    if next_hd_nat >= heap_size then
      mem_cons_lemma rem_obj_addr rem_obj_addr (Seq.empty #obj_addr)
    else begin
      let next_hd_hp : hp_addr = U64.uint_to_t next_hd_nat in
      mem_cons_lemma rem_obj_addr rem_obj_addr (objects next_hd_hp g3)
    end;
    // rem_obj ∈ objects(rem_hd, g3) → ∈ objects(hd, g3)
    mem_cons_lemma rem_obj_addr obj (objects rem_hd g3);
    // obj ∈ objects(0, g3) for objects_later_in_earlier precondition
    alloc_split_old_in_new_part1 g obj wz next_fp obj;
    f_address_spec hd;
    // objects(hd, g3) ⊆ objects(0, g3) via objects_later_in_earlier
    objects_addresses_gt_start zero_addr g obj;
    assert (U64.v zero_addr <= U64.v hd);
    objects_later_in_earlier zero_addr g3 hd rem_obj_addr
#pop-options

/// Module-level pop (matches the #push-options at the top)
#pop-options
