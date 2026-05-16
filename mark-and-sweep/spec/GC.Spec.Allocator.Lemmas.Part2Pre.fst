(*
   GC.Spec.Allocator.Lemmas.Part2Pre — helpers + wfh_part1 + fl_valid proofs.
*)
module GC.Spec.Allocator.Lemmas.Part2Pre

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

/// Module-level default: all functions get z3rlimit 20 unless overridden
#push-options "--z3rlimit 20 --z3refresh"

/// ===========================================================================
/// Section P2: alloc_spec preserves well_formed_heap_part1
/// ===========================================================================

/// ---------------------------------------------------------------------------
/// P2-pre: split_new_mem_in_old_or_rem_part1
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 200 --fuel 3 --ifuel 1"
let rec split_new_mem_in_old_or_rem_part1
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
      Seq.mem h (objects start g3) /\
      (U64.v start = U64.v zero_addr \/ Seq.mem (f_address start) (objects zero_addr g)) /\
      Seq.mem obj (objects start g))
    (ensures (let rem_hd_nat = U64.v (hd_address obj) + (1 + wz) * 8 in
              let rem_obj_nat = rem_hd_nat + 8 in
              Seq.mem h (objects start g) \/ U64.v h == rem_obj_nat))
    (decreases (Seq.length g3 - U64.v start))
  = let hd = hd_address obj in
    hd_address_spec obj;
    if U64.v start + 8 >= Seq.length g3 then ()
    else begin
      let header_g3 = read_word g3 start in
      let wz_g3 = getWosize header_g3 in
      let next_nat_g3 = U64.v start + (U64.v wz_g3 + 1) * 8 in
      if next_nat_g3 > Seq.length g3 || next_nat_g3 >= pow2 64 then ()
      else begin
        f_address_spec start;
        let first : obj_addr = f_address start in
        mem_cons_lemma h first
          (if next_nat_g3 >= heap_size then Seq.empty
           else objects (U64.uint_to_t next_nat_g3 <: hp_addr) g3);
        if U64.v start = U64.v hd then begin
          let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
          let rem_obj_nat = rem_hd_nat + 8 in
          let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
          assert (first == obj);
          assert (next_nat_g3 == rem_hd_nat);
          if h = first then begin
            let header_g = read_word g start in
            let wz_g = getWosize header_g in
            let next_nat_g = U64.v start + (U64.v wz_g + 1) * 8 in
            assert (next_nat_g == next_hd_nat);
            if next_hd_nat >= heap_size then
              mem_cons_lemma h obj (Seq.empty #obj_addr)
            else
              mem_cons_lemma h obj (objects (U64.uint_to_t next_hd_nat <: hp_addr) g)
          end else begin
            if rem_hd_nat >= heap_size then ()
            else begin
              let rem_hd_hp : hp_addr = U64.uint_to_t rem_hd_nat in
              assert (Seq.mem h (objects rem_hd_hp g3));
              f_address_spec rem_hd_hp;
              let rem_obj_addr : obj_addr = f_address rem_hd_hp in
              assert (U64.v rem_obj_addr == rem_obj_nat);
              let rem_wz = block_wz - wz - 1 in
              let next_from_rem = rem_hd_nat + (rem_wz + 1) * 8 in
              assert (next_from_rem == next_hd_nat);
              mem_cons_lemma h rem_obj_addr
                (if next_hd_nat >= heap_size then Seq.empty
                 else objects (U64.uint_to_t next_hd_nat <: hp_addr) g3);
              if h = rem_obj_addr then begin
                assert (U64.v h == rem_obj_nat)
              end else begin
                if next_hd_nat >= heap_size then ()
                else begin
                  let next_hd : hp_addr = U64.uint_to_t next_hd_nat in
                  assert (Seq.mem h (objects next_hd g3));
                  assert (objects next_hd g3 == objects next_hd g);
                  assert (Seq.mem h (objects next_hd g));
                  let header_g = read_word g start in
                  let next_nat_g = U64.v start + (U64.v (getWosize header_g) + 1) * 8 in
                  assert (next_nat_g == next_hd_nat);
                  mem_cons_lemma h obj (objects next_hd g)
                end
              end
            end
          end
        end else begin
          assert (read_word g3 start == read_word g start);
          if h = first then begin
            let header_g = read_word g start in
            let next_nat_g = U64.v start + (U64.v (getWosize header_g) + 1) * 8 in
            if next_nat_g >= heap_size then
              mem_cons_lemma h first (Seq.empty #obj_addr)
            else
              mem_cons_lemma h first (objects (U64.uint_to_t next_nat_g <: hp_addr) g)
          end else begin
            if next_nat_g3 >= heap_size then ()
            else begin
              let next_hp : hp_addr = U64.uint_to_t next_nat_g3 in
              let header_g_here = read_word g start in
              assert (header_g3 == header_g_here);
              let wz_g_here = getWosize header_g_here in
              assert (wz_g3 == wz_g_here);
              mem_cons_lemma first first
                (if next_nat_g3 >= heap_size then Seq.empty
                 else objects (U64.uint_to_t next_nat_g3 <: hp_addr) g);
              assert (Seq.mem first (objects start g));
              // Need U64.v zero_addr <= U64.v start for objects_later_in_earlier
              (if U64.v start = U64.v zero_addr then ()
               else begin
                 f_address_spec start;
                 objects_addresses_gt_start zero_addr g (f_address start)
               end);
              assert (U64.v zero_addr <= U64.v start);
              objects_later_in_earlier zero_addr g start first;
              hd_address_spec first;
              wosize_of_object_spec first g;
              objects_separated zero_addr g first obj;
              assert (U64.v hd % 8 == 0);
              assert (U64.v start % 8 == 0);
              FStar.Math.Lemmas.cancel_mul_mod (U64.v wz_g_here) 8;
              assert ((U64.v start + U64.v wz_g_here * 8) % 8 == 0);
              assert (U64.v hd > U64.v start + U64.v wz_g_here * 8);
              assert (next_nat_g3 <= U64.v hd);
              let next_nat_g = U64.v start + (U64.v wz_g_here + 1) * 8 in
              assert (next_nat_g == next_nat_g3);
              mem_cons_lemma obj first
                (if next_nat_g >= heap_size then Seq.empty
                 else objects (U64.uint_to_t next_nat_g <: hp_addr) g);
              assert (obj <> first);
              objects_nonempty_first_mem next_hp g obj;
              mem_cons_lemma (f_address next_hp) first (objects next_hp g);
              if U64.v start = U64.v zero_addr then ()
              else objects_addresses_gt_start zero_addr g (f_address start);
              objects_later_in_earlier zero_addr g start (f_address next_hp);
              split_new_mem_in_old_or_rem_part1 next_hp g g3 obj wz block_wz h;
              let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
              let rem_obj_nat = rem_hd_nat + 8 in
              if U64.v h = rem_obj_nat then ()
              else begin
                let next_nat_g2 = U64.v start + (U64.v wz_g_here + 1) * 8 in
                assert (next_nat_g2 == next_nat_g3);
                mem_cons_lemma h first (objects next_hp g)
              end
            end
          end
        end
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// P2a: alloc_split preserves wfh_part1 (under just part1)
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--split_queries always --z3rlimit 100 --fuel 0 --ifuel 0"
let alloc_split_wf_part1_v2
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     let block_wz = U64.v (getWosize hdr) in
                     block_wz >= wz /\ block_wz - wz >= 2))
          (ensures (let (g3, _) = alloc_from_block g obj wz next_fp in
                    well_formed_heap_part1 g3))
  = alloc_split_facts_part1 g obj wz next_fp;
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
    let rem_obj_nat = rem_hd_nat + 8 in
    let rem_wz = block_wz - wz - 1 in
    let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
    let rem_obj_addr : obj_addr = U64.uint_to_t rem_obj_nat in
    let (g3, _) = alloc_from_block g obj wz next_fp in
    hd_address_spec obj;
    let aux (h: obj_addr) : Lemma
      (requires Seq.mem h (objects zero_addr g3))
      (ensures (let w = wosize_of_object h g3 in
                U64.v (hd_address h) + 8 + U64.v w * 8 <= Seq.length g3))
    = wosize_of_object_spec h g3;
      hd_address_spec h;
      if h = obj then begin
        // wosize in g3 = wz. hd + 8 + wz*8 <= hd + 8 + block_wz*8 <= heap_size
        ()
      end else if h = rem_obj_addr then begin
        // wosize in g3 = rem_wz. rem_hd + 8 + rem_wz*8 = hd + (block_wz+1)*8 <= heap_size
        ()
      end else begin
        // h is from old objects. Use split_new_mem_in_old_or_rem_part1 to show h ∈ objects(0, g)
        let aux_before (p: hp_addr) : Lemma
          (requires U64.v p < U64.v hd)
          (ensures read_word g3 p == read_word g p)
        = alloc_split_g3_agrees_part1 g obj wz next_fp p
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux_before);
        objects_addresses_gt_start zero_addr g obj;
        split_new_mem_in_old_or_rem_part1 zero_addr g g3 obj wz block_wz h;
        assert (Seq.mem h (objects zero_addr g));
        // Header of h is unchanged
        hd_address_spec h;
        wosize_of_object_spec h g;
        wosize_of_object_spec obj g;
        if U64.v h < U64.v obj then begin
          objects_separated zero_addr g h obj;
          alloc_split_g3_agrees_part1 g obj wz next_fp (hd_address h)
        end else begin
          objects_separated zero_addr g obj h;
          assert (U64.v (hd_address h) > U64.v hd + block_wz * 8 - 8);
          assert (U64.v (hd_address h) <> U64.v hd);
          assert (U64.v (hd_address h) <> rem_hd_nat);
          assert (U64.v (hd_address h) <> rem_obj_nat);
          alloc_split_g3_agrees_part1 g obj wz next_fp (hd_address h)
        end
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// P2b: alloc_exact preserves wfh_part1 (under just part1)
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let alloc_exact_preserves_wfh_part1
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     let block_wz = U64.v (getWosize hdr) in
                     block_wz >= wz /\ block_wz - wz < 2))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    well_formed_heap_part1 g'))
  = let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let new_hdr = make_header (U64.uint_to_t block_wz) white_bits 0UL in
    alloc_from_block_exact g obj wz next_fp;
    hd_address_spec obj;
    hd_address_bounds obj;
    getWosize_bound hdr;
    make_header_getWosize (U64.uint_to_t block_wz) white_bits 0UL;
    header_write_same_wosize_preserves_objects g obj new_hdr;
    let g' = write_word g hd new_hdr in
    // objects(0, g') == objects(0, g), and for each h: wosize(h, g') == wosize(h, g)
    // since the only modified header is at hd with same wosize.
    // So part1 transfers trivially.
    let aux (h: obj_addr) : Lemma
      (requires Seq.mem h (objects zero_addr g'))
      (ensures (let w = wosize_of_object h g' in
                U64.v (hd_address h) + 8 + U64.v w * 8 <= Seq.length g'))
    = hd_address_spec h;
      wosize_of_object_spec h g';
      wosize_of_object_spec h g;
      if h = obj then
        read_write_same g hd new_hdr
      else begin
        if U64.v h < U64.v obj then
          objects_separated zero_addr g h obj
        else
          objects_separated zero_addr g obj h;
        read_write_different g hd (hd_address h) new_hdr
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// P2c: alloc_from_block preserves wfh_part1 (under just part1)
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let alloc_from_block_preserves_wfh_part1
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     U64.v (getWosize hdr) >= wz))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    well_formed_heap_part1 g'))
  = let hdr = read_word g (hd_address obj) in
    let block_wz = U64.v (getWosize hdr) in
    if block_wz - wz >= 2 then
      alloc_split_wf_part1_v2 g obj wz next_fp
    else
      alloc_exact_preserves_wfh_part1 g obj wz next_fp
#pop-options

/// ---------------------------------------------------------------------------
/// P2d: write within object body preserves wfh_part1
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let write_body_preserves_wfh_part1
  (g: heap) (obj: obj_addr) (addr: hp_addr) (v: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    U64.v addr >= U64.v obj /\
                    U64.v addr < U64.v obj + (U64.v (wosize_of_object obj g) * 8) /\
                    U64.v addr % 8 = 0)
          (ensures well_formed_heap_part1 (write_word g addr v))
  = // write_body doesn't change headers (addr >= obj > hd_address(obj))
    // so objects walk is unchanged, and all bounds remain valid
    write_body_preserves_objects_local zero_addr g obj addr v;
    let g' = write_word g addr v in
    assert (objects zero_addr g' == objects zero_addr g);
    let aux (h: obj_addr) : Lemma
      (requires Seq.mem h (objects zero_addr g'))
      (ensures (let w = wosize_of_object h g' in
                U64.v (hd_address h) + 8 + U64.v w * 8 <= Seq.length g'))
    = hd_address_spec h;
      hd_address_spec obj;
      wosize_of_object_spec h g;
      wosize_of_object_spec h g';
      // addr >= obj = hd_address(obj) + 8, so addr > hd_address(obj)
      // For any h: hd_address(h) ≠ addr because:
      //   if h = obj: hd_address(obj) < obj <= addr
      //   if h ≠ obj: by objects_separated, hd_address(h) is either < hd_address(obj) or > obj + wosize*8 - 8 > addr
      if h = obj then
        // hd_address(obj) < obj <= addr
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
/// P2e: alloc_search_preserves_wfh_part1 — recursive proof
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"
private let rec alloc_search_preserves_wfh_part1
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
                    well_formed_heap_part1 r.heap_out))
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
        alloc_from_block_preserves_wfh_part1 g obj wz next_fp;
        let (g', new_fp) = alloc_from_block g obj wz next_fp in
        if prev_fp = 0UL then ()
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          let prev : obj_addr = prev_fp in
          // prev ∈ objects(0, g')
          alloc_from_block_objects_facts_part1 g obj wz next_fp;
          assert (Seq.mem prev (objects zero_addr g'));
          // wosize(prev, g') == wosize(prev, g)
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
          // write_body preserves wfh_part1
          write_body_preserves_wfh_part1 g' prev (prev <: hp_addr) new_fp
        end
        else ()
      end
      else begin
        fl_valid_next g cur_fp fuel;
        assert (cur_fp <> next_fp);
        alloc_search_preserves_wfh_part1 g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// P2f: Top-level alloc_spec_preserves_wfh_part1
/// ---------------------------------------------------------------------------

let alloc_spec_preserves_wfh_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    fl_valid g fp (heap_size / U64.v mword) /\
                    fl_chain_terminates g fp (heap_size / U64.v mword))
          (ensures (let r = alloc_spec g fp requested_wz in
                    well_formed_heap_part1 r.heap_out))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_preserves_wfh_part1 g fp 0UL fp wz (heap_size / U64.v mword)

/// ---------------------------------------------------------------------------
/// P2g: alloc_split_fl_transfer_pre_part1 — split case fl_valid_transfer
///      under well_formed_heap_part1 only
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 400 --fuel 0 --ifuel 0"
let alloc_split_fl_transfer_pre_part1
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (a: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     let block_wz = U64.v (getWosize hdr) in
                     block_wz >= wz /\ block_wz - wz >= 2) /\
                    wz >= 1 /\
                    Seq.mem a (objects zero_addr g) /\
                    U64.v a >= U64.v mword /\
                    U64.v a < heap_size /\
                    U64.v a % U64.v mword = 0)
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    Seq.mem a (objects zero_addr g') /\
                    (U64.v (wosize_of_object a g) >= 1 ==>
                      U64.v (wosize_of_object a g') >= 1) /\
                    (U64.v (wosize_of_object a g) >= 1 /\
                     U64.v (hd_address a) + 16 <= heap_size ==>
                      read_word g' a == read_word g a)))
  = alloc_split_facts_part1 g obj wz next_fp;
    alloc_from_block_objects_facts_part1 g obj wz next_fp;
    let (g', _) = alloc_from_block g obj wz next_fp in
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
    let rem_obj_nat = rem_hd_nat + 8 in
    hd_address_spec obj;
    hd_address_bounds obj;
    wosize_of_object_spec obj g;
    getWosize_bound hdr;
    if U64.v (wosize_of_object a g) >= 1 then begin
      hd_address_spec a;
      wosize_of_object_spec a g;
      wosize_of_object_bound a g;
      if a = obj then begin
        // Header changed to alloc_hdr with wosize = wz >= 1.
        assert (U64.v obj <> U64.v hd);
        assert (wz >= 1);
        assert (rem_hd_nat == U64.v hd + (1 + wz) * 8);
        assert ((1 + wz) * 8 >= 16);
        assert (rem_hd_nat >= U64.v hd + 16);
        assert (rem_hd_nat >= U64.v obj + 8);
        assert (U64.v obj <> rem_hd_nat);
        assert (rem_obj_nat > rem_hd_nat);
        assert (U64.v obj <> rem_obj_nat);
        alloc_split_g3_agrees_part1 g obj wz next_fp (obj <: hp_addr);
        alloc_from_block_split_normal g obj wz next_fp;
        let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
        let g1 = write_word g hd alloc_hdr in
        let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
        let rem_wz = block_wz - wz - 1 in
        let rem_hdr = make_header (U64.uint_to_t rem_wz) blue_bits 0UL in
        let g2 = write_word g1 rem_hd rem_hdr in
        let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
        let g3 = write_word g2 rem_obj next_fp in
        read_write_different g2 rem_obj hd next_fp;
        read_write_different g1 rem_hd hd rem_hdr;
        read_write_same g hd alloc_hdr;
        make_header_getWosize (U64.uint_to_t wz) white_bits 0UL;
        wosize_of_object_spec obj g3
      end else begin
        if U64.v a < U64.v obj then begin
          objects_separated zero_addr g a obj;
          // a + wosize(a)*8 < obj, hd = obj - 8, rem_hd > hd, rem_obj > rem_hd
          // so hd_address(a) = a - 8 < a < obj - 8 = hd < rem_hd < rem_obj
          // and a < obj - 8 = hd < rem_hd < rem_obj
          alloc_split_g3_agrees_part1 g obj wz next_fp (hd_address a);
          alloc_split_g3_agrees_part1 g obj wz next_fp (a <: hp_addr);
          wosize_of_object_spec a g;
          wosize_of_object_spec a g'
        end else begin
          objects_separated zero_addr g obj a;
          // a > obj + wosize(obj)*8 = obj + block_wz*8 = hd + (block_wz+1)*8
          // rem_obj = hd + (1+wz)*8 + 8 <= hd + (block_wz)*8 < a
          // so hd < rem_hd < rem_obj < a, and hd_address(a) = a - 8 >= hd + block_wz*8
          alloc_split_g3_agrees_part1 g obj wz next_fp (hd_address a);
          alloc_split_g3_agrees_part1 g obj wz next_fp (a <: hp_addr);
          wosize_of_object_spec a g;
          wosize_of_object_spec a g'
        end
      end
    end else ()
#pop-options

/// ---------------------------------------------------------------------------
/// P2h: alloc_exact_fl_transfer_pre_part1 — exact-fit case fl_valid_transfer
///      under well_formed_heap_part1 only
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 400 --fuel 0 --ifuel 0"
let alloc_exact_fl_transfer_pre_part1
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (a: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     let block_wz = U64.v (getWosize hdr) in
                     block_wz >= wz /\ block_wz - wz < 2) /\
                    Seq.mem a (objects zero_addr g) /\
                    U64.v a >= U64.v mword /\
                    U64.v a < heap_size /\
                    U64.v a % U64.v mword = 0)
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    Seq.mem a (objects zero_addr g') /\
                    (U64.v (wosize_of_object a g) >= 1 ==>
                      U64.v (wosize_of_object a g') >= 1) /\
                    (U64.v (wosize_of_object a g) >= 1 /\
                     U64.v (hd_address a) + 16 <= heap_size ==>
                      read_word g' a == read_word g a)))
  = let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let alloc_hdr = make_header (U64.uint_to_t block_wz) white_bits 0UL in
    alloc_from_block_exact g obj wz next_fp;
    let g' = write_word g hd alloc_hdr in
    hd_address_spec obj;
    hd_address_bounds obj;
    getWosize_bound hdr;
    make_header_getWosize (U64.uint_to_t block_wz) white_bits 0UL;
    header_write_same_wosize_preserves_objects g obj alloc_hdr;
    if U64.v (wosize_of_object a g) >= 1 then begin
      hd_address_spec a;
      wosize_of_object_spec a g;
      wosize_of_object_bound a g;
      if a = obj then begin
        // Header changed but wosize preserved (block_wz = block_wz)
        read_write_same g hd alloc_hdr;
        read_write_different g hd (a <: hp_addr) alloc_hdr;
        wosize_of_object_spec a g'
      end else begin
        // a ≠ obj: header at hd_address(a) ≠ hd, and a ≠ hd
        if U64.v a < U64.v obj then
          objects_separated zero_addr g a obj
        else
          objects_separated zero_addr g obj a;
        read_write_different g hd (hd_address a) alloc_hdr;
        read_write_different g hd (a <: hp_addr) alloc_hdr;
        wosize_of_object_spec a g;
        wosize_of_object_spec a g'
      end
    end else ()
#pop-options

/// ---------------------------------------------------------------------------
/// P2h2: fl_valid_field_write_part1 — like fl_valid_field_write but only needs
///       well_formed_heap_part1 (not full well_formed_heap)
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
private let rec fl_valid_field_write_part1
  (g: heap) (p: obj_addr) (v: U64.t) (fp: U64.t) (fuel tail_fuel: nat)
  : Lemma
    (requires fl_valid g fp fuel /\
              well_formed_heap_part1 g /\
              Seq.mem p (objects zero_addr g) /\
              U64.v (wosize_of_object p g) >= 1 /\
              v <> p /\
              fl_valid (write_word g (p <: hp_addr) v) v tail_fuel /\
              tail_fuel >= fuel)
    (ensures fl_valid (write_word g (p <: hp_addr) v) fp fuel)
    (decreases fuel)
  = let g' = write_word g (p <: hp_addr) v in
    if fuel = 0 then ()
    else if fp = 0UL then ()
    else if U64.v fp < U64.v mword then ()
    else if U64.v fp >= heap_size then ()
    else if U64.v fp % U64.v mword <> 0 then ()
    else begin
      let obj_fp : obj_addr = fp in
      let hd_fp = hd_address obj_fp in
      // objects preserved by field write
      wfh_part1_obj_bound g p;
      wosize_of_object_bound p g;
      write_word_preserves_objects_part1 g p (p <: hp_addr) v;
      assert (objects zero_addr g' == objects zero_addr g);
      assert (Seq.mem fp (objects zero_addr g'));
      // wosize preserved: hd_fp ≠ p (the write position)
      hd_address_spec obj_fp;
      if U64.v fp <> U64.v p then begin
        if U64.v fp > U64.v p then
          objects_separated zero_addr g p obj_fp
        else
          objects_separated zero_addr g obj_fp p
      end;
      read_write_different g (p <: hp_addr) (hd_fp <: hp_addr) v;
      wosize_of_object_spec obj_fp g;
      wosize_of_object_spec obj_fp g';
      assert (U64.v (wosize_of_object obj_fp g') >= 1);
      if U64.v hd_fp + 16 <= heap_size then begin
        if fp = p then begin
          read_write_same g (p <: hp_addr) v;
          fl_valid_weaken g' v tail_fuel (fuel - 1)
        end else begin
          read_write_different g (p <: hp_addr) (obj_fp <: hp_addr) v;
          fl_valid_field_write_part1 g p v (read_word g obj_fp) (fuel - 1) tail_fuel
        end
      end
      else ()
    end
#pop-options

/// fl_valid_field_write_tail_part1: establishes fl_valid g' v fuel
/// where g' = write_word g p v, using only well_formed_heap_part1.
#restart-solver
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
private let rec fl_valid_field_write_tail_part1
  (g: heap) (p: obj_addr) (v: U64.t) (fuel: nat)
  : Lemma
    (requires well_formed_heap_part1 g /\
              Seq.mem p (objects zero_addr g) /\
              U64.v (wosize_of_object p g) >= 1 /\
              v <> p /\
              fl_valid g v fuel)
    (ensures fl_valid (write_word g (p <: hp_addr) v) v fuel)
    (decreases fuel)
  = let g' = write_word g (p <: hp_addr) v in
    if fuel = 0 then ()
    else if v = 0UL then ()
    else if U64.v v < U64.v mword then ()
    else if U64.v v >= heap_size then ()
    else if U64.v v % U64.v mword <> 0 then ()
    else begin
      let obj_v : obj_addr = v in
      let hd_v = hd_address obj_v in
      // objects preserved
      wfh_part1_obj_bound g p;
      wosize_of_object_bound p g;
      write_word_preserves_objects_part1 g p (p <: hp_addr) v;
      assert (objects zero_addr g' == objects zero_addr g);
      // wosize preserved at v: hd_v ≠ p
      hd_address_spec obj_v;
      if U64.v v <> U64.v p then begin
        if U64.v v > U64.v p then
          objects_separated zero_addr g p obj_v
        else
          objects_separated zero_addr g obj_v p
      end;
      read_write_different g (p <: hp_addr) (hd_v <: hp_addr) v;
      wosize_of_object_spec obj_v g;
      wosize_of_object_spec obj_v g';
      if U64.v hd_v + 16 <= heap_size then begin
        // v ≠ p, so link at v unchanged
        read_write_different g (p <: hp_addr) (obj_v <: hp_addr) v;
        let link = read_word g obj_v in
        assert (read_word g' obj_v == link);
        assert (link <> v);
        // IH: fl_valid g' v (fuel-1)
        fl_valid_weaken g v fuel (fuel - 1);
        fl_valid_field_write_tail_part1 g p v (fuel - 1);
        // fl_valid g' link (fuel-1) via fl_valid_field_write_part1
        fl_valid_field_write_part1 g p v link (fuel - 1) (fuel - 1)
      end
      else ()
    end
#pop-options

/// ---------------------------------------------------------------------------
/// P2i: alloc_search_preserves_fl_valid_part1 — recursive proof that alloc_search
///      preserves fl_valid under well_formed_heap_part1 only
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 400 --fuel 1 --ifuel 0"
private let rec alloc_search_preserves_fl_valid_part1
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 g /\
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
      // Use well_formed_heap_part1 to get the size bound (replaces wf_object_size_bound)
      assert (U64.v hd + 8 + block_wz * 8 <= heap_size);
      getWosize_bound hdr;
      let next_fp =
        if U64.v hd + 16 <= heap_size then read_word g obj
        else 0UL
      in
      assert (U64.v hd + 16 <= heap_size);
      assert (fl_valid g next_fp (fuel - 1));
      assert (fl_chain_terminates g next_fp (fuel - 1));
      if block_wz >= wz then begin
        // ===== Found a suitable block =====
        // Establish: is_pointer_field next_fp ==> Seq.mem next_fp (objects zero_addr g)
        // Using FL-based reasoning instead of next_fp_in_objects
        (if next_fp = 0UL then ()
         else if U64.v next_fp < U64.v mword then ()
         else if U64.v next_fp >= heap_size then ()
         else if U64.v next_fp % U64.v mword <> 0 then ()
         else fl_valid_elim g next_fp (fuel - 1));
        assert (is_pointer_field next_fp ==> Seq.mem next_fp (objects zero_addr g));
        alloc_from_block_preserves_wfh_part1 g obj wz next_fp;
        let (g', new_fp) = alloc_from_block g obj wz next_fp in
        // Upgrade fl_valid g next_fp (fuel-1) to fl_valid g next_fp big_fuel
        fl_valid_any_fuel g next_fp (fuel - 1) big_fuel;
        assert (fl_valid g next_fp big_fuel);
        if prev_fp = 0UL then begin
          // ===== prev_fp = 0UL: fp_out = new_fp =====
          if block_wz - wz >= 2 then begin
            // ===== Split case: new_fp = rem_obj =====
            alloc_split_facts_part1 g obj wz next_fp;
            alloc_from_block_objects_facts_part1 g obj wz next_fp;
            let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
            let rem_obj_nat = rem_hd_nat + 8 in
            let rem_wz = block_wz - wz - 1 in
            // Prove Seq.mem new_fp (objects zero_addr g') inline
            // (replaces alloc_from_block_objects_facts which gave is_pointer_field rem_fp ==> ...)
            // new_fp = rem_obj from alloc_split_facts_part1
            // rem_obj ∈ objects(0, g') via:
            //   1. obj ∈ objects(0, g') from alloc_from_block_objects_facts_part1
            //   2. rem_obj ∈ objects(rem_hd, g') as head element
            //   3. objects(hd, g') = cons obj (objects(rem_hd, g')) since wosize(obj, g') = wz
            //   4. rem_obj ∈ objects(hd, g')
            //   5. f_address hd = obj ∈ objects(0, g')
            //   6. objects_later_in_earlier zero_addr g' hd rem_obj
            alloc_split_old_in_new_part1 g obj wz next_fp obj;
            assert (Seq.mem obj (objects zero_addr g'));
            // Reconstruct g' to reason about rem_obj membership
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
            let rem_obj_addr : obj_addr = rem_obj in
            f_address_spec hd;
            f_address_spec rem_hd;
            let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
            // rem_obj is head of objects(rem_hd, g3)
            if next_hd_nat >= heap_size then
              mem_cons_lemma rem_obj_addr rem_obj_addr (Seq.empty #obj_addr)
            else begin
              let next_hd_hp : hp_addr = U64.uint_to_t next_hd_nat in
              mem_cons_lemma rem_obj_addr rem_obj_addr (objects next_hd_hp g3)
            end;
            // rem_obj ∈ objects(hd, g3): objects(hd, g3) = cons obj (objects(rem_hd, g3))
            mem_cons_lemma rem_obj_addr obj (objects rem_hd g3);
            // objects_later_in_earlier: hd <= hd, and f_address hd = obj ∈ objects(0, g3)
            objects_addresses_gt_start zero_addr g obj;
            hd_address_spec obj;
            objects_later_in_earlier zero_addr g3 hd rem_obj_addr;
            assert (Seq.mem new_fp (objects zero_addr g'));
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
            = alloc_split_fl_transfer_pre_part1 g obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux);
            fl_valid_transfer g g' next_fp big_fuel;
            assert (fl_valid g' next_fp big_fuel);
            fl_valid_weaken g' next_fp big_fuel (big_fuel - 1);
            // Build fl_valid g' new_fp big_fuel via fl_valid_step
            // 1. read_word g' new_fp = next_fp (link to tail)
            read_write_same g2 rem_obj next_fp;
            assert (read_word g' new_fp == next_fp);
            // 2. wosize_of_object new_fp g' = rem_wz >= 1
            hd_address_spec (rem_obj <: obj_addr);
            assert (hd_address (rem_obj <: obj_addr) == rem_hd);
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
            assert (next_hd_nat <= heap_size);
            assert (rem_obj_nat + 8 <= next_hd_nat);
            assert (U64.v (hd_address (new_fp <: obj_addr)) + 16 <= heap_size);
            // 5. next_fp <> new_fp
            assert (next_fp <> cur_fp);
            (if next_fp = 0UL then ()
             else if U64.v next_fp < U64.v mword then ()
             else if U64.v next_fp >= heap_size then ()
             else if U64.v next_fp % U64.v mword <> 0 then ()
             else begin
               // next_fp is valid and in objects(0,g)
               assert (Seq.mem next_fp (objects zero_addr g));
               if U64.v next_fp < U64.v obj then begin
                 assert (U64.v next_fp < U64.v new_fp)
               end else begin
                 objects_separated zero_addr g obj (next_fp <: obj_addr);
                 assert (U64.v next_fp > U64.v obj + block_wz * 8);
                 assert (U64.v new_fp < U64.v obj + block_wz * 8);
                 assert (U64.v next_fp > U64.v new_fp)
               end
             end);
            assert (next_fp <> new_fp);
            // 6. Build fl_valid g' new_fp big_fuel via fl_valid_step
            fl_valid_step g' new_fp big_fuel
          end else begin
            // ===== Exact-fit case: new_fp = next_fp =====
            alloc_exact_preserves_wfh_part1 g obj wz next_fp;
            alloc_from_block_exact g obj wz next_fp;
            // Transfer fl_valid g next_fp big_fuel to g'
            let transfer_aux (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr g))
              (ensures Seq.mem a (objects zero_addr g') /\
                       (U64.v (wosize_of_object a g) >= 1 ==>
                         U64.v (wosize_of_object a g') >= 1) /\
                       (U64.v (wosize_of_object a g) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g' a == read_word g a))
            = alloc_exact_fl_transfer_pre_part1 g obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux);
            fl_valid_transfer g g' next_fp big_fuel;
            ()
          end
        end
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          // ===== prev_fp ≠ 0UL: fp_out = head_fp, heap_out = write_word g' prev_fp new_fp =====
          let prev_obj : obj_addr = prev_fp in
          let g2 = write_word g' (prev_obj <: hp_addr) new_fp in
          if block_wz - wz >= 2 then begin
            // ----- Split sub-case -----
            alloc_split_facts_part1 g obj wz next_fp;
            alloc_from_block_objects_facts_part1 g obj wz next_fp;
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
            = alloc_split_fl_transfer_pre_part1 g obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux_s);
            fl_valid_transfer g g' head_fp big_fuel;
            assert (fl_valid g' head_fp big_fuel);
            // Step 2: Build fl_valid g' new_fp big_fuel (same as prev_fp=0 split case)
            fl_valid_transfer g g' next_fp big_fuel;
            fl_valid_weaken g' next_fp big_fuel (big_fuel - 1);
            // Prove Seq.mem new_fp (objects zero_addr g')
            alloc_split_old_in_new_part1 g obj wz next_fp obj;
            assert (Seq.mem obj (objects zero_addr g'));
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
            let rem_obj_addr : obj_addr = rem_obj in
            f_address_spec hd;
            f_address_spec rem_hd;
            let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
            // rem_obj is head of objects(rem_hd, g3)
            if next_hd_nat >= heap_size then
              mem_cons_lemma rem_obj_addr rem_obj_addr (Seq.empty #obj_addr)
            else begin
              let next_hd_hp : hp_addr = U64.uint_to_t next_hd_nat in
              mem_cons_lemma rem_obj_addr rem_obj_addr (objects next_hd_hp g3)
            end;
            mem_cons_lemma rem_obj_addr obj (objects rem_hd g3);
            objects_addresses_gt_start zero_addr g obj;
            hd_address_spec obj;
            objects_later_in_earlier zero_addr g3 hd rem_obj_addr;
            assert (Seq.mem new_fp (objects zero_addr g'));
            // wosize of new_fp in g': need wosize_of_object new_fp g' >= 1
            make_header_getWosize (U64.uint_to_t rem_wz) blue_bits 0UL;
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
            (if next_fp = 0UL then ()
             else if U64.v next_fp < U64.v mword then ()
             else if U64.v next_fp >= heap_size then ()
             else if U64.v next_fp % U64.v mword <> 0 then ()
             else begin
               if U64.v next_fp <= U64.v obj then begin
                 objects_separated zero_addr g (next_fp <: obj_addr) obj;
                 assert (U64.v obj > U64.v next_fp + U64.v (wosize_of_object (next_fp <: obj_addr) g) * 8);
                 assert (U64.v new_fp < U64.v obj + block_wz * 8);
                 assert (U64.v next_fp < U64.v obj);
                 assert (U64.v new_fp >= U64.v obj)
               end else begin
                 objects_separated zero_addr g obj (next_fp <: obj_addr);
                 assert (U64.v next_fp > U64.v obj + block_wz * 8);
                 assert (U64.v new_fp < U64.v obj + block_wz * 8)
               end
             end);
            assert (next_fp <> new_fp);
            fl_valid_step g' new_fp big_fuel;
            assert (fl_valid g' new_fp big_fuel);
            // Step 3: prev_fp ∈ objects(0, g') with wosize >= 1
            assert (Seq.mem prev_fp (objects zero_addr g'));
            alloc_split_fl_transfer_pre_part1 g obj wz next_fp prev_obj;
            assert (U64.v (wosize_of_object prev_obj g') >= 1);
            // Step 4: new_fp ≠ prev_fp
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
            // Use _part1 variants of fl_valid_field_write
            fl_valid_field_write_tail_part1 g' prev_obj new_fp big_fuel;
            fl_valid_field_write_part1 g' prev_obj new_fp head_fp big_fuel big_fuel





          end else begin
            // ----- Exact-fit sub-case -----
            alloc_exact_preserves_wfh_part1 g obj wz next_fp;
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
            = alloc_exact_fl_transfer_pre_part1 g obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux_e);
            fl_valid_transfer g g' head_fp big_fuel;
            assert (fl_valid g' head_fp big_fuel);
            // Step 2: fl_valid g' new_fp big_fuel
            fl_valid_transfer g g' next_fp big_fuel;
            assert (fl_valid g' new_fp big_fuel);
            // Step 3: prev_fp ∈ objects(0, g') with wosize >= 1
            assert (Seq.mem prev_fp (objects zero_addr g'));
            alloc_exact_fl_transfer_pre_part1 g obj wz next_fp prev_obj;
            assert (U64.v (wosize_of_object prev_obj g') >= 1);
            // Step 4: new_fp ≠ prev_fp
            (if new_fp = prev_fp then begin
              assert (read_word g (prev_fp <: obj_addr) == cur_fp);
              assert (read_word g obj == next_fp);
              assert (next_fp == prev_fp);
              fl_chain_2cycle_not_terminates g prev_fp cur_fp (fuel - 1);
              assert (fl_chain_terminates g next_fp (fuel - 1) = false);
              assert false
            end else ());
            assert (new_fp <> prev_fp);
            // Use _part1 variants of fl_valid_field_write
            fl_valid_field_write_tail_part1 g' prev_obj new_fp big_fuel;
            fl_valid_field_write_part1 g' prev_obj new_fp head_fp big_fuel big_fuel
          end
        end
        else ()
      end
      else begin
        // ===== Advance: block too small, continue search =====
        assert (cur_fp <> next_fp);
        assert (read_word g obj == next_fp);
        assert (U64.v hd + 16 <= heap_size);
        alloc_search_preserves_fl_valid_part1 g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// P2j: Top-level alloc_spec_preserves_fl_valid_part1
/// ---------------------------------------------------------------------------

let alloc_spec_preserves_fl_valid_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    fl_valid g fp (heap_size / U64.v mword) /\
                    fl_chain_terminates g fp (heap_size / U64.v mword))
          (ensures (let r = alloc_spec g fp requested_wz in
                    fl_valid r.heap_out r.fp_out (heap_size / U64.v mword)))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_preserves_fl_valid_part1 g fp 0UL fp wz (heap_size / U64.v mword)

#pop-options // Module-level z3rlimit 20
