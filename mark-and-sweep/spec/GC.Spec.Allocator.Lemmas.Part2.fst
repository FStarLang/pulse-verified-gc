(*
   GC.Spec.Allocator.Lemmas.Part2 — Section P2-P5 proofs.

   alloc_spec preserves well_formed_heap_part1, fl_valid, fl_chain_terminates,
   and various framing properties under the weaker part1 precondition.
*)
module GC.Spec.Allocator.Lemmas.Part2


open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
open GC.Spec.Allocator.Lemmas.Header
open GC.Spec.Allocator.Lemmas.Split
open GC.Spec.Allocator.Lemmas.Part1
open GC.Spec.Allocator.Lemmas.Common
open GC.Spec.Allocator.Lemmas.Chain
open GC.Spec.Allocator.Lemmas.SearchBase
module U64 = FStar.UInt64
module Seq = FStar.Seq
module Header = GC.Lib.Header

/// Module-level default: all functions get z3rlimit 20 unless overridden
#push-options "--z3rlimit 20 --z3refresh"

#restart-solver
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
private let chain_avoids_shrink (g: heap) (fp excl: U64.t) (s_small s_big: nat)
  : Lemma (requires chain_avoids g fp excl s_big = true /\ s_small <= s_big)
          (ensures chain_avoids g fp excl s_small = true)
  = chain_avoids_weaken g fp excl s_big s_small
#pop-options

#restart-solver
#push-options "--z3rlimit 400 --fuel 0 --ifuel 0"
private let make_header_getColor (wz: U64.t{U64.v wz < pow2 54})
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

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
private let make_header_color_blue (wz: U64.t{U64.v wz < pow2 54})
  : Lemma (getColor (make_header wz blue_bits 0UL) == Header.Blue)
  = let hdr = make_header wz blue_bits 0UL in
    getColor_raw hdr;
    make_header_getColor wz blue_bits 0UL
#pop-options

/// ===========================================================================
/// Section P2: alloc_spec preserves well_formed_heap_part1
/// ===========================================================================

/// ---------------------------------------------------------------------------
/// P2-pre: split_new_mem_in_old_or_rem_part1
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--split_queries always --z3rlimit 200 --fuel 3 --ifuel 1"
private let rec split_new_mem_in_old_or_rem_part1
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
private let alloc_split_wf_part1_v2
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
private let alloc_exact_preserves_wfh_part1
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
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
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
private let write_body_preserves_wfh_part1
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
#push-options "--z3rlimit 400 --fuel 1 --ifuel 0"
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
        assert (U64.v hd + 16 <= heap_size);
        assert (fl_valid g next_fp (fuel - 1));
        fl_chain_terminates_elim g cur_fp fuel;
        assert (fl_chain_terminates g next_fp (fuel - 1));
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
private let alloc_split_fl_transfer_pre_part1
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
private let alloc_exact_fl_transfer_pre_part1
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
    if fuel = 0 then
      fl_valid_zero g' fp
    else if fp = 0UL then
      fl_valid_null g' fuel
    else if U64.v fp < U64.v mword then
      fl_valid_terminal g' fp fuel
    else if U64.v fp >= heap_size then
      fl_valid_terminal g' fp fuel
    else if U64.v fp % U64.v mword <> 0 then
      fl_valid_terminal g' fp fuel
    else begin
      let obj_fp : obj_addr = fp in
      let hd_fp = hd_address obj_fp in
      fl_valid_gives_mem g fp fuel;
      fl_valid_gives_wosize g fp fuel;
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
        fl_valid_next g fp fuel;
        assert (read_word g obj_fp <> fp);
        assert (fl_valid g (read_word g obj_fp) (fuel - 1));
        if fp = p then begin
          read_write_same g (p <: hp_addr) v;
          assert (read_word g' obj_fp == v);
          fl_valid_weaken g' v tail_fuel (fuel - 1)
        end else begin
          read_write_different g (p <: hp_addr) (obj_fp <: hp_addr) v;
          assert (read_word g' obj_fp == read_word g obj_fp);
          fl_valid_field_write_part1 g p v (read_word g obj_fp) (fuel - 1) tail_fuel
        end
      end;
      assert (Seq.mem fp (objects zero_addr g'));
      assert (U64.v (wosize_of_object (fp <: obj_addr) g') >= 1);
      assert (U64.v hd_fp + 16 <= heap_size ==>
                read_word g' obj_fp <> fp /\
                fl_valid g' (read_word g' obj_fp) (fuel - 1));
      fl_valid_step g' fp fuel;
      assert (fl_valid g' fp fuel)
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
    if fuel = 0 then
      fl_valid_zero g' v
    else if v = 0UL then
      fl_valid_null g' fuel
    else if U64.v v < U64.v mword then
      fl_valid_terminal g' v fuel
    else if U64.v v >= heap_size then
      fl_valid_terminal g' v fuel
    else if U64.v v % U64.v mword <> 0 then
      fl_valid_terminal g' v fuel
    else begin
      let obj_v : obj_addr = v in
      let hd_v = hd_address obj_v in
      fl_valid_gives_mem g v fuel;
      fl_valid_gives_wosize g v fuel;
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
      assert (Seq.mem v (objects zero_addr g'));
      assert (U64.v (wosize_of_object (v <: obj_addr) g') >= 1);
      if U64.v hd_v + 16 <= heap_size then begin
        fl_valid_next g v fuel;
        // v ≠ p, so link at v unchanged
        read_write_different g (p <: hp_addr) (obj_v <: hp_addr) v;
        let link = read_word g obj_v in
        assert (read_word g' obj_v == link);
        assert (link <> v);
        assert (fl_valid g link (fuel - 1));
        // IH: fl_valid g' v (fuel-1)
        fl_valid_weaken g v fuel (fuel - 1);
        fl_valid_field_write_tail_part1 g p v (fuel - 1);
        // fl_valid g' link (fuel-1) via fl_valid_field_write_part1
        fl_valid_field_write_part1 g p v link (fuel - 1) (fuel - 1)
      end;
      assert (U64.v hd_v + 16 <= heap_size ==>
                read_word g' obj_v <> v /\
                fl_valid g' (read_word g' obj_v) (fuel - 1));
      fl_valid_step g' v fuel;
      assert (fl_valid g' v fuel)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// P2i: alloc_search_preserves_fl_valid_part1 — recursive proof that alloc_search
///      preserves fl_valid under well_formed_heap_part1 only
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"
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
      fl_chain_terminates_elim g cur_fp fuel;
      assert (fl_chain_terminates g next_fp (fuel - 1));
      if block_wz >= wz then begin
        // ===== Found a suitable block =====
        // Establish: is_pointer_field next_fp ==> Seq.mem next_fp (objects zero_addr g)
        // Using FL-based reasoning instead of next_fp_in_objects
        (if next_fp = 0UL then ()
         else if U64.v next_fp < U64.v mword then ()
         else if U64.v next_fp >= heap_size then ()
         else if U64.v next_fp % U64.v mword <> 0 then ()
         else if fuel - 1 = 0 then begin
           fl_chain_terminates_valid_zero g next_fp;
           assert false
         end
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

/// ---------------------------------------------------------------------------
/// P2k: alloc_search_preserves_fl_chain_terminates_part1 — recursive proof that
///      alloc_search preserves fl_chain_terminates under well_formed_heap_part1 only
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"
private let rec alloc_search_preserves_fl_chain_terminates_part1
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 g /\
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
      fl_chain_terminates_elim g cur_fp fuel;
      assert (fl_chain_terminates g next_fp (fuel - 1));
      if block_wz >= wz then begin
        // ===== Found a suitable block =====
        // Establish: is_pointer_field next_fp ==> Seq.mem next_fp (objects zero_addr g)
        // Using FL-based reasoning instead of next_fp_in_objects
        (if next_fp = 0UL then ()
         else if U64.v next_fp < U64.v mword then ()
         else if U64.v next_fp >= heap_size then ()
         else if U64.v next_fp % U64.v mword <> 0 then ()
         else if fuel - 1 = 0 then begin
           fl_chain_terminates_valid_zero g next_fp;
           assert false
         end
         else fl_valid_elim g next_fp (fuel - 1));
        assert (is_pointer_field next_fp ==> Seq.mem next_fp (objects zero_addr g));
        alloc_from_block_preserves_wfh_part1 g obj wz next_fp;
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
            alloc_split_facts_part1 g obj wz next_fp;
            alloc_from_block_objects_facts_part1 g obj wz next_fp;
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
            alloc_exact_preserves_wfh_part1 g obj wz next_fp;
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
            alloc_split_facts_part1 g obj wz next_fp;
            alloc_from_block_objects_facts_part1 g obj wz next_fp;
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
            = alloc_split_fl_transfer_pre_part1 g obj wz next_fp a
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
              assert (fuel + 1 <= big_fuel);
              walk_chain_zero g head_fp;
              assert (head_fp == prev_fp);
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
            alloc_exact_preserves_wfh_part1 g obj wz next_fp;
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
              assert (fuel + 1 <= big_fuel);
              walk_chain_zero g head_fp;
              assert (head_fp == prev_fp);
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
        alloc_search_preserves_fl_chain_terminates_part1 g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// P2l: Top-level alloc_spec_preserves_fl_chain_terminates_part1
/// ---------------------------------------------------------------------------

let alloc_spec_preserves_fl_chain_terminates_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    fl_valid g fp (heap_size / U64.v mword) /\
                    fl_chain_terminates g fp (heap_size / U64.v mword))
          (ensures (let r = alloc_spec g fp requested_wz in
                    fl_chain_terminates r.heap_out r.fp_out (heap_size / U64.v mword)))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    walk_chain_zero g fp;
    walk_chain_valid_zero g fp;
    alloc_search_preserves_fl_chain_terminates_part1 g fp 0UL fp wz (heap_size / U64.v mword)

/// ===========================================================================
/// Section P3: alloc_spec_obj_not_in_chain under well_formed_heap_part1
/// ===========================================================================

/// ---------------------------------------------------------------------------
/// P3a: alloc_search_obj_not_in_chain_part1 — recursive proof that alloc_search
///      removes obj_out from the chain, under well_formed_heap_part1 only.
///      Mirrors alloc_search_obj_not_in_chain but uses part1 helpers.
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 80 --fuel 1 --ifuel 0"
private let rec alloc_search_obj_not_in_chain_part1
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 g /\
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
                    walk_chain g head_fp (heap_size / U64.v mword - fuel) = cur_fp /\
                    walk_chain_valid g head_fp (heap_size / U64.v mword - fuel) /\
                    (prev_fp <> 0UL ==> fuel < heap_size / U64.v mword /\
                                        walk_chain g head_fp (heap_size / U64.v mword - fuel - 1) = prev_fp))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    r.obj_out <> 0UL ==>
                    chain_avoids r.heap_out r.fp_out r.obj_out (heap_size / U64.v mword) = true))
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
      // Use well_formed_heap_part1 to get size bound (replaces wf_object_size_bound)
      assert (U64.v hd + 8 + block_wz * 8 <= heap_size);
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
        // ===== Found a suitable block: obj_out = cur_fp =====
        // (No need for next_fp_in_objects or alloc_from_block_preserves_wf under part1)
        let (g', new_fp) = alloc_from_block g obj wz next_fp in
        fl_valid_any_fuel g next_fp (fuel - 1) big_fuel;
        fl_chain_terminates_weaken g next_fp (fuel - 1) big_fuel;
        // Key: cur_fp not in successor chain
        fl_chain_predecessor_not_in_suffix_b g cur_fp fuel;
        not_in_fl_chain_b_is_chain_avoids g next_fp cur_fp (fuel - 1);
        assert (chain_avoids g next_fp cur_fp (fuel - 1) = true);
        if prev_fp = 0UL then begin
          // ===== prev_fp = 0: fp_out = new_fp =====
          if block_wz - wz >= 2 then begin
            // ----- Split: new_fp = rem_obj -----
            alloc_split_facts_part1 g obj wz next_fp;
            alloc_from_block_objects_facts_part1 g obj wz next_fp;
            alloc_from_block_split_normal g obj wz next_fp;
            let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
            let g1 = write_word g hd alloc_hdr in
            let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
            let rem_obj_nat = rem_hd_nat + 8 in
            let rem_wz = block_wz - wz - 1 in
            let rem_hdr = make_header (U64.uint_to_t rem_wz) blue_bits 0UL in
            let g2 = write_word g1 (U64.uint_to_t rem_hd_nat <: hp_addr) rem_hdr in
            let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
            let g3 = write_word g2 rem_obj next_fp in
            assert (g' == g3);
            assert (new_fp == rem_obj);
            assert (U64.v new_fp > U64.v cur_fp);
            read_write_same g2 rem_obj next_fp;
            assert (read_word g' new_fp == next_fp);
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
            chain_avoids_transfer_excl g g' next_fp cur_fp (fuel - 1);
            fl_chain_terminates_transfer g g' next_fp (fuel - 1);
            chain_avoids_strengthen g' next_fp cur_fp (fuel - 1) (big_fuel - 1);
            let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
            assert (next_hd_nat <= heap_size);
            assert (rem_obj_nat + 8 <= next_hd_nat);
            hd_address_spec (new_fp <: obj_addr);
            assert (U64.v (hd_address (new_fp <: obj_addr)) + 16 <= heap_size);
            chain_avoids_unfold_step g' new_fp cur_fp big_fuel
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
            chain_avoids_transfer_excl g g' next_fp cur_fp (fuel - 1);
            fl_chain_terminates_transfer g g' next_fp (fuel - 1);
            chain_avoids_strengthen g' next_fp cur_fp (fuel - 1) big_fuel
          end
        end
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          // ===== prev_fp != 0: fp_out = head_fp, heap_out = g2 =====
          let prev_obj : obj_addr = prev_fp in
          let g2 = write_word g' (prev_obj <: hp_addr) new_fp in
          let d = big_fuel - fuel - 1 in
          if block_wz - wz >= 2 then begin
            // ----- Split sub-case (prev != 0) -----
            alloc_split_facts_part1 g obj wz next_fp;
            alloc_from_block_objects_facts_part1 g obj wz next_fp;
            alloc_from_block_split_normal g obj wz next_fp;
            let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
            let g1 = write_word g hd alloc_hdr in
            let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
            let rem_obj_nat = rem_hd_nat + 8 in
            let rem_wz = block_wz - wz - 1 in
            let rem_hdr = make_header (U64.uint_to_t rem_wz) blue_bits 0UL in
            let g2_tmp = write_word g1 (U64.uint_to_t rem_hd_nat <: hp_addr) rem_hdr in
            let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
            let g3 = write_word g2_tmp rem_obj next_fp in
            assert (g' == g3);
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
            assert (U64.v new_fp > U64.v cur_fp);
            read_write_different g' (prev_obj <: hp_addr) (new_fp <: hp_addr) new_fp;
            read_write_same g2_tmp rem_obj next_fp;
            assert (read_word g2 (new_fp <: obj_addr) == next_fp);
            read_write_same g' (prev_obj <: hp_addr) new_fp;
            assert (read_word g2 (prev_fp <: obj_addr) == new_fp);
            // Transfer chain_avoids for next_fp chain to g2
            chain_avoids_prev g prev_fp cur_fp next_fp (fuel - 1);
            chain_avoids_transfer_excl2 g g2 next_fp cur_fp prev_fp (fuel - 1);
            fl_chain_terminates_transfer_excl g g2 next_fp prev_fp (fuel - 1);
            // chain_avoids g2 new_fp cur_fp big_fuel
            let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
            assert (next_hd_nat <= heap_size);
            assert (rem_obj_nat + 8 <= next_hd_nat);
            hd_address_spec (new_fp <: obj_addr);
            assert (U64.v (hd_address (new_fp <: obj_addr)) + 16 <= heap_size);
            chain_avoids_strengthen g2 next_fp cur_fp (fuel - 1) (big_fuel - 1);
            chain_avoids_unfold_step g2 new_fp cur_fp big_fuel;
            assert (chain_avoids g2 new_fp cur_fp big_fuel = true);
            // chain_avoids g2 prev_fp cur_fp (fuel + 1)
            chain_avoids_shrink g2 new_fp cur_fp fuel big_fuel;
            chain_avoids_unfold_step g2 prev_fp cur_fp (fuel + 1);
            assert (chain_avoids g2 prev_fp cur_fp (fuel + 1) = true);
            // Get chain_avoids g2 head_fp cur_fp big_fuel
            if d = 0 then begin
              // d = 0: head_fp = prev_fp. Strengthen (fuel+1) to big_fuel.
              assert (fuel + 1 <= big_fuel);
              walk_chain_zero g head_fp;
              assert (head_fp == prev_fp);
              fl_chain_terminates_step g2 new_fp fuel;
              fl_chain_terminates_step g2 prev_fp (fuel + 1);
              chain_avoids_strengthen g2 prev_fp cur_fp (fuel + 1) big_fuel
            end else begin
              // d > 0: use prefix walk transfer + unfold
              walk_chain_valid_prefix g head_fp (big_fuel - fuel) d;
              fl_chain_no_early_repeat g head_fp d big_fuel;
              walk_chain_valid_preserved g g2 head_fp prev_fp d big_fuel;
              assert (walk_chain_valid g2 head_fp d);
              assert (walk_chain g2 head_fp d = prev_fp);
              fl_chain_no_early_repeat g head_fp (d + 1) big_fuel;
              chain_avoids_shrink g head_fp cur_fp d (d + 1);
              fl_valid_weaken g head_fp big_fuel d;
              chain_avoids_transfer_excl2 g g2 head_fp cur_fp prev_fp d;
              chain_avoids_unfold_steps g2 head_fp cur_fp d big_fuel
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
            (if new_fp = prev_fp then begin
               assert (read_word g (prev_fp <: obj_addr) == cur_fp);
               assert (read_word g obj == next_fp);
               assert (next_fp == prev_fp);
               fl_chain_2cycle_not_terminates g prev_fp cur_fp (fuel - 1);
               assert false
             end else ());
            assert (new_fp <> prev_fp);
            read_write_same g' (prev_obj <: hp_addr) new_fp;
            assert (read_word g2 (prev_fp <: obj_addr) == new_fp);
            chain_avoids_prev g prev_fp cur_fp next_fp (fuel - 1);
            chain_avoids_transfer_excl2 g g2 next_fp cur_fp prev_fp (fuel - 1);
            fl_chain_terminates_transfer_excl g g2 next_fp prev_fp (fuel - 1);
            // chain_avoids g2 new_fp cur_fp big_fuel (new_fp = next_fp)
            chain_avoids_strengthen g2 next_fp cur_fp (fuel - 1) big_fuel;
            assert (chain_avoids g2 new_fp cur_fp big_fuel = true);
            // chain_avoids g2 prev_fp cur_fp (fuel + 1)
            chain_avoids_shrink g2 new_fp cur_fp fuel big_fuel;
            chain_avoids_unfold_step g2 prev_fp cur_fp (fuel + 1);
            assert (chain_avoids g2 prev_fp cur_fp (fuel + 1) = true);
            // Get chain_avoids g2 head_fp cur_fp big_fuel
            if d = 0 then begin
              // d = 0: head_fp = prev_fp. Strengthen (fuel+1) to big_fuel.
              assert (fuel + 1 <= big_fuel);
              walk_chain_zero g head_fp;
              assert (head_fp == prev_fp);
              fl_chain_terminates_weaken g2 next_fp (fuel - 1) fuel;
              fl_chain_terminates_step g2 prev_fp (fuel + 1);
              chain_avoids_strengthen g2 prev_fp cur_fp (fuel + 1) big_fuel
            end else begin
              // d > 0: use prefix walk transfer + unfold
              walk_chain_valid_prefix g head_fp (big_fuel - fuel) d;
              fl_chain_no_early_repeat g head_fp d big_fuel;
              walk_chain_valid_preserved g g2 head_fp prev_fp d big_fuel;
              fl_chain_no_early_repeat g head_fp (d + 1) big_fuel;
              chain_avoids_shrink g head_fp cur_fp d (d + 1);
              fl_valid_weaken g head_fp big_fuel d;
              chain_avoids_transfer_excl2 g g2 head_fp cur_fp prev_fp d;
              chain_avoids_unfold_steps g2 head_fp cur_fp d big_fuel
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
        walk_chain_append g head_fp (big_fuel - fuel) 1;
        walk_chain_one_step g cur_fp;
        walk_chain_valid_snoc g head_fp (big_fuel - fuel);
        alloc_search_obj_not_in_chain_part1 g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// P3b: Top-level alloc_spec_obj_not_in_chain_part1
/// ---------------------------------------------------------------------------

let alloc_spec_obj_not_in_chain_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    fl_valid g fp (heap_size / U64.v mword) /\
                    fl_chain_terminates g fp (heap_size / U64.v mword) /\
                    requested_wz >= 1 /\
                    (alloc_spec g fp requested_wz).obj_out <> 0UL)
          (ensures (let r = alloc_spec g fp requested_wz in
                    chain_avoids r.heap_out r.fp_out r.obj_out (heap_size / U64.v mword) = true))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    walk_chain_zero g fp;
    walk_chain_valid_zero g fp;
    alloc_search_obj_not_in_chain_part1 g fp 0UL fp wz (heap_size / U64.v mword)

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
#push-options "--z3rlimit 80 --fuel 1 --ifuel 0"
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
      fl_chain_terminates_elim g cur_fp fuel;
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
        not_in_fl_chain_b_is_chain_avoids g next_fp cur_fp (fuel - 1);
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
            chain_avoids_unfold_step g' new_fp excl big_fuel;
            assert (chain_avoids g' new_fp excl big_fuel = true)
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
            chain_avoids_strengthen g' next_fp excl (fuel - 1) big_fuel;
            assert (chain_avoids g' next_fp excl big_fuel = true);
            assert (new_fp == next_fp)
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
              chain_avoids_strengthen g2 prev_fp excl (fuel + 1) big_fuel;
              walk_chain_zero g head_fp;
              assert (head_fp == prev_fp);
              assert (chain_avoids g2 head_fp excl big_fuel = true)
            end else begin
              // d > 0: transfer prefix and unfold
              chain_avoids_weaken g head_fp excl big_fuel d;
              walk_chain_valid_prefix g head_fp (big_fuel - fuel) d;
              fl_chain_no_early_repeat g head_fp d big_fuel;
              fl_valid_weaken g head_fp big_fuel d;
              chain_avoids_transfer_excl2 g g2 head_fp excl prev_fp d;
              walk_chain_valid_preserved g g2 head_fp prev_fp d big_fuel;
              assert (walk_chain g2 head_fp d == prev_fp);
              assert (big_fuel - d == fuel + 1);
              assert (chain_avoids g2 prev_fp excl (big_fuel - d) = true);
              chain_avoids_unfold_steps g2 head_fp excl d big_fuel;
              assert (chain_avoids g2 head_fp excl big_fuel = true)
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
              chain_avoids_strengthen g2 prev_fp excl (fuel + 1) big_fuel;
              walk_chain_zero g head_fp;
              assert (head_fp == prev_fp);
              assert (chain_avoids g2 head_fp excl big_fuel = true)
            end else begin
              chain_avoids_weaken g head_fp excl big_fuel d;
              walk_chain_valid_prefix g head_fp (big_fuel - fuel) d;
              fl_chain_no_early_repeat g head_fp d big_fuel;
              fl_valid_weaken g head_fp big_fuel d;
              chain_avoids_transfer_excl2 g g2 head_fp excl prev_fp d;
              walk_chain_valid_preserved g g2 head_fp prev_fp d big_fuel;
              assert (walk_chain g2 head_fp d == prev_fp);
              assert (big_fuel - d == fuel + 1);
              assert (chain_avoids g2 prev_fp excl (big_fuel - d) = true);
              chain_avoids_unfold_steps g2 head_fp excl d big_fuel;
              assert (chain_avoids g2 head_fp excl big_fuel = true)
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
        alloc_search_advance g head_fp prev_fp cur_fp wz fuel;
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
    walk_chain_zero g fp;
    walk_chain_valid_zero g fp;
    assert (walk_chain g fp 0 == fp);
    assert (walk_chain_valid g fp 0);
    assert (big_fuel - big_fuel = 0);
    alloc_search_preserves_chain_avoids_other g fp 0UL fp wz big_fuel excl;
    alloc_search_no_alloc_unchanged g fp 0UL fp wz big_fuel
#pop-options

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
        assert (U64.v hd + 16 <= heap_size);
        assert (fl_valid g next_fp (fuel - 1));
        fl_chain_terminates_elim g cur_fp fuel;
        assert (fl_chain_terminates g next_fp (fuel - 1));
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
let alloc_from_block_rem_in_objects_part1 = alloc_from_block_rem_in_objects_part1
let alloc_from_block_preserves_objects_part1 = alloc_from_block_preserves_objects_part1


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
        if U64.v hd + 16 <= heap_size then begin
          fl_valid_next g cur_fp fuel;
          assert (cur_fp <> next_fp);
          assert (fl_valid g next_fp (fuel - 1));
          fl_chain_terminates_elim g cur_fp fuel;
          assert (fl_chain_terminates g next_fp (fuel - 1));
          alloc_search_new_objects_blue_part1 g head_fp cur_fp next_fp wz (fuel - 1)
        end
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
