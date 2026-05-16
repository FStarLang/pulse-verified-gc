/// ---------------------------------------------------------------------------
/// GC.Gen.AllocProps — Properties of alloc_spec needed for promotion proofs
/// ---------------------------------------------------------------------------
///
/// Wrapper lemmas that derive needed allocator properties from
/// existing GC.Spec.Allocator.Lemmas infrastructure.

module GC.Gen.AllocProps

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
open GC.Lib.Header

module AllocLemmas = GC.Spec.Allocator.Lemmas

/// ---------------------------------------------------------------------------
/// When alloc_spec succeeds, the returned obj_out is a valid obj_addr
/// ---------------------------------------------------------------------------

/// The allocator only returns cur_fp after checking:
///   U64.v cur_fp >= U64.v mword, < heap_size, % mword == 0
/// So obj_out satisfies the obj_addr refinement.
///
/// Proof strategy: unfold alloc_spec into alloc_search and observe that
/// obj_out is set to cur_fp which already passed all guard checks.
#push-options "--z3rlimit 50 --fuel 4 --ifuel 1"
let rec alloc_search_obj_valid
  (g: heap) (head_fp: U64.t) (prev_fp: U64.t)
  (cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma
    (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
              r.obj_out <> 0UL ==>
              (U64.v r.obj_out >= U64.v mword /\
               U64.v r.obj_out < heap_size /\
               U64.v r.obj_out % U64.v mword == 0)))
    (decreases fuel)
  =
  if fuel = 0 then ()
  else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
  else if U64.v cur_fp >= heap_size then ()
  else if U64.v cur_fp % U64.v mword <> 0 then ()
  else begin
    let obj : obj_addr = cur_fp in
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let next_fp =
      if U64.v hd + 16 <= heap_size then read_word g obj
      else 0UL
    in
    if block_wz >= wz then ()
    else
      alloc_search_obj_valid g head_fp cur_fp next_fp wz (fuel - 1)
  end
#pop-options

/// Top-level: alloc_spec returns a valid obj_addr when successful
let alloc_spec_obj_valid (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (ensures (let r = alloc_spec g fp requested_wz in
                    r.obj_out <> 0UL ==>
                    (U64.v r.obj_out >= U64.v mword /\
                     U64.v r.obj_out < heap_size /\
                     U64.v r.obj_out % U64.v mword == 0)))
  =
  let wz = if requested_wz = 0 then 1 else requested_wz in
  alloc_search_obj_valid g fp 0UL fp wz (heap_size / U64.v mword)

/// ---------------------------------------------------------------------------
/// When alloc_spec succeeds, obj_out is in objects zero_addr heap_out
/// ---------------------------------------------------------------------------

/// The allocated object was a free-list node, hence already in objects zero_addr g.
/// alloc_spec_preserves_objects shows all old objects survive.
/// So obj_out is in objects zero_addr heap_out.
///
/// Proof: obj_out = cur_fp which is in the free list. fl_valid ensures
/// free-list nodes are in objects. alloc_spec_preserves_objects preserves them.
#push-options "--z3rlimit 50 --fuel 4 --ifuel 1"
let rec alloc_search_obj_in_objects_pre
  (g: heap) (head_fp: U64.t) (prev_fp: U64.t)
  (cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma
    (requires well_formed_heap g /\
              AllocLemmas.fl_valid g cur_fp fuel)
    (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
              r.obj_out <> 0UL ==>
              (U64.v r.obj_out >= U64.v mword /\
               U64.v r.obj_out < heap_size /\
               U64.v r.obj_out % U64.v mword == 0 /\
               Seq.mem (r.obj_out <: obj_addr) (objects zero_addr g))))
    (decreases fuel)
  =
  if fuel = 0 then ()
  else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
  else if U64.v cur_fp >= heap_size then ()
  else if U64.v cur_fp % U64.v mword <> 0 then ()
  else begin
    AllocLemmas.fl_valid_elim g cur_fp fuel;
    // fl_valid_elim gives: Seq.mem cur_fp (objects zero_addr g)
    let obj : obj_addr = cur_fp in
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let next_fp =
      if U64.v hd + 16 <= heap_size then read_word g obj
      else 0UL
    in
    if block_wz >= wz then
      // Found: obj_out = cur_fp which is in objects zero_addr g
      ()
    else begin
      // Continue search — need fl_valid for next_fp
      if U64.v hd + 16 <= heap_size then
        alloc_search_obj_in_objects_pre g head_fp cur_fp next_fp wz (fuel - 1)
      else ()
    end
  end
#pop-options

/// After alloc, the returned object is in objects of the output heap
let alloc_spec_obj_in_objects (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires well_formed_heap g /\
                    AllocLemmas.fl_valid g fp (heap_size / U64.v mword))
          (ensures (let r = alloc_spec g fp requested_wz in
                    r.obj_out <> 0UL ==>
                    (U64.v r.obj_out >= U64.v mword /\
                     U64.v r.obj_out < heap_size /\
                     U64.v r.obj_out % U64.v mword == 0 /\
                     Seq.mem (r.obj_out <: obj_addr) (objects zero_addr r.heap_out))))
  =
  let wz = if requested_wz = 0 then 1 else requested_wz in
  let fuel = heap_size / U64.v mword in
  // First: show obj_out was in objects zero_addr g
  alloc_search_obj_in_objects_pre g fp zero_addr fp wz fuel;
  // Second: alloc_spec_preserves_objects shows old objects survive
  AllocLemmas.alloc_spec_preserves_objects g fp requested_wz

/// ---------------------------------------------------------------------------
/// After alloc, wosize of the allocated object >= requested_wz
/// ---------------------------------------------------------------------------

/// alloc_from_block either:
/// - Uses exact fit: writes header with block_wz >= requested_wz
/// - Splits: writes header with exactly requested_wz
/// In both cases: wosize_of_object obj_out heap_out >= requested_wz
///
/// This is harder to prove from outside — we'd need to unfold alloc_from_block.
///
/// Key insight: alloc_from_block either:
/// - Exact fit (bwz - wz < 2): writes header with bwz >= wz
/// - Split: writes header with exactly wz
/// In both cases, wosize_of_object obj heap_out >= wz.
///
/// Strategy: prove a helper for alloc_from_block, then use it in alloc_search.

module SA = GC.Spec.Allocator

/// Helper: after alloc_from_block, the header at obj has wosize >= wz
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1 --split_queries always"
let alloc_from_block_wosize_lemma
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires (let hdr = read_word g (hd_address obj) in
                     U64.v (getWosize hdr) >= wz))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    U64.v (wosize_of_object obj g') >= wz))
  =
  let hd = hd_address obj in
  let hdr = read_word g hd in
  let bwz = U64.v (getWosize hdr) in
  hd_address_spec obj;
  hd_address_bounds obj;
  if bwz - wz < 2 then begin
    // Exact fit case
    SA.alloc_from_block_exact g obj wz next_fp;
    let ahdr = make_header (U64.uint_to_t bwz) white_bits 0UL in
    let g1 = write_word g hd ahdr in
    assert (alloc_from_block g obj wz next_fp == (g1, next_fp));
    wosize_of_object_spec obj g1;
    read_write_same g hd ahdr;
    AllocLemmas.make_header_getWosize (U64.uint_to_t bwz) white_bits 0UL
  end
  else begin
    // Split case: all variants write ahdr = make_header wz white_bits 0UL at hd
    let ahdr = make_header (U64.uint_to_t wz) white_bits 0UL in
    let g1 = write_word g hd ahdr in
    let rhn = U64.v hd + (1 + wz) * 8 in
    if rhn >= heap_size then begin
      SA.alloc_from_block_split_rem_hd_oob g obj wz next_fp;
      assert (alloc_from_block g obj wz next_fp == (g1, next_fp));
      wosize_of_object_spec obj g1;
      read_write_same g hd ahdr;
      AllocLemmas.make_header_getWosize (U64.uint_to_t wz) white_bits 0UL
    end
    else if rhn + 8 >= heap_size then begin
      SA.alloc_from_block_split_rem_obj_oob g obj wz next_fp;
      let rh : hp_addr = U64.uint_to_t rhn in
      let rw = bwz - wz - 1 in
      let rhdr = make_header (U64.uint_to_t rw) blue_bits 0UL in
      let g2 = write_word g1 rh rhdr in
      assert (alloc_from_block g obj wz next_fp == (g2, U64.uint_to_t (rhn + 8)));
      // Header at hd in g2: rh > hd
      assert (U64.v rh > U64.v hd);
      wosize_of_object_spec obj g2;
      read_write_different g1 rh hd rhdr;
      read_write_same g hd ahdr;
      AllocLemmas.make_header_getWosize (U64.uint_to_t wz) white_bits 0UL
    end
    else begin
      SA.alloc_from_block_split_normal g obj wz next_fp;
      let rh : hp_addr = U64.uint_to_t rhn in
      let rw = bwz - wz - 1 in
      let rhdr = make_header (U64.uint_to_t rw) blue_bits 0UL in
      let g2 = write_word g1 rh rhdr in
      let ron = rhn + 8 in
      let ro : hp_addr = U64.uint_to_t ron in
      let g3 = write_word g2 ro next_fp in
      assert (alloc_from_block g obj wz next_fp == (g3, ro));
      // Both rh and ro are > hd
      assert (U64.v rh > U64.v hd);
      assert (U64.v ro > U64.v hd);
      wosize_of_object_spec obj g3;
      read_write_different g2 ro hd next_fp;
      read_write_different g1 rh hd rhdr;
      read_write_same g hd ahdr;
      AllocLemmas.make_header_getWosize (U64.uint_to_t wz) white_bits 0UL
    end
  end
#pop-options

/// Upper bound: after alloc_from_block, wosize <= wz + 1
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1 --split_queries always"
let alloc_from_block_wosize_upper_lemma
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires (let hdr = read_word g (hd_address obj) in
                     U64.v (getWosize hdr) >= wz))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    U64.v (wosize_of_object obj g') <= wz + 1))
  =
  let hd = hd_address obj in
  let hdr = read_word g hd in
  let bwz = U64.v (getWosize hdr) in
  hd_address_spec obj;
  hd_address_bounds obj;
  if bwz - wz < 2 then begin
    SA.alloc_from_block_exact g obj wz next_fp;
    let ahdr = make_header (U64.uint_to_t bwz) white_bits 0UL in
    let g1 = write_word g hd ahdr in
    assert (alloc_from_block g obj wz next_fp == (g1, next_fp));
    wosize_of_object_spec obj g1;
    read_write_same g hd ahdr;
    AllocLemmas.make_header_getWosize (U64.uint_to_t bwz) white_bits 0UL
    // bwz - wz < 2, so bwz <= wz + 1
  end
  else begin
    let ahdr = make_header (U64.uint_to_t wz) white_bits 0UL in
    let g1 = write_word g hd ahdr in
    let rhn = U64.v hd + (1 + wz) * 8 in
    if rhn >= heap_size then begin
      SA.alloc_from_block_split_rem_hd_oob g obj wz next_fp;
      assert (alloc_from_block g obj wz next_fp == (g1, next_fp));
      wosize_of_object_spec obj g1;
      read_write_same g hd ahdr;
      AllocLemmas.make_header_getWosize (U64.uint_to_t wz) white_bits 0UL
    end
    else if rhn + 8 >= heap_size then begin
      SA.alloc_from_block_split_rem_obj_oob g obj wz next_fp;
      let rh : hp_addr = U64.uint_to_t rhn in
      let rw = bwz - wz - 1 in
      let rhdr = make_header (U64.uint_to_t rw) blue_bits 0UL in
      let g2 = write_word g1 rh rhdr in
      assert (alloc_from_block g obj wz next_fp == (g2, U64.uint_to_t (rhn + 8)));
      assert (U64.v rh > U64.v hd);
      wosize_of_object_spec obj g2;
      read_write_different g1 rh hd rhdr;
      read_write_same g hd ahdr;
      AllocLemmas.make_header_getWosize (U64.uint_to_t wz) white_bits 0UL
    end
    else begin
      SA.alloc_from_block_split_normal g obj wz next_fp;
      let rh : hp_addr = U64.uint_to_t rhn in
      let rw = bwz - wz - 1 in
      let rhdr = make_header (U64.uint_to_t rw) blue_bits 0UL in
      let g2 = write_word g1 rh rhdr in
      let ron = rhn + 8 in
      let ro : hp_addr = U64.uint_to_t ron in
      let g3 = write_word g2 ro next_fp in
      assert (alloc_from_block g obj wz next_fp == (g3, ro));
      assert (U64.v rh > U64.v hd);
      assert (U64.v ro > U64.v hd);
      wosize_of_object_spec obj g3;
      read_write_different g2 ro hd next_fp;
      read_write_different g1 rh hd rhdr;
      read_write_same g hd ahdr;
      AllocLemmas.make_header_getWosize (U64.uint_to_t wz) white_bits 0UL
    end
  end
#pop-options

/// After alloc_search finds a block and returns obj_out, the output heap
/// has a write_word to prev_fp (if non-zero). This doesn't affect hd_address(obj),
/// provided prev_fp and hd_address(obj) are separated (which holds in alloc_search
/// because prev_fp is a different free-list node than cur_fp/obj).
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
private let write_prev_preserves_wosize
  (g_after_alloc: heap) (obj: obj_addr) (prev_fp: U64.t) (val_fp: U64.t)
  (wz: nat)
  : Lemma (requires U64.v (wosize_of_object obj g_after_alloc) >= wz /\
                    prev_fp <> 0UL /\
                    U64.v prev_fp >= U64.v mword /\
                    U64.v prev_fp < heap_size /\
                    U64.v prev_fp % U64.v mword = 0 /\
                    prev_fp <> hd_address obj)
          (ensures (let g2 = write_word g_after_alloc (prev_fp <: hp_addr) val_fp in
                    U64.v (wosize_of_object obj g2) >= wz))
  =
  let hd = hd_address obj in
  hd_address_spec obj;
  hd_address_bounds obj;
  let g2 = write_word g_after_alloc (prev_fp <: hp_addr) val_fp in
  wosize_of_object_spec obj g2;
  wosize_of_object_spec obj g_after_alloc;
  let p = U64.v (prev_fp <: hp_addr) in
  let h = U64.v hd in
  FStar.Math.Lemmas.lemma_div_exact p 8;
  FStar.Math.Lemmas.lemma_div_exact h 8;
  let kp = p / 8 in
  let kh = h / 8 in
  if kp > kh then begin
    FStar.Math.Lemmas.lemma_mult_le_right 8 (kh + 1) kp;
    FStar.Math.Lemmas.distributivity_add_left kh 1 8
  end else begin
    FStar.Math.Lemmas.lemma_mult_le_right 8 (kp + 1) kh;
    FStar.Math.Lemmas.distributivity_add_left kp 1 8
  end;
  read_write_different g_after_alloc (prev_fp <: hp_addr) hd val_fp
#pop-options

/// Upper-bound version: write to prev_fp preserves wosize <= wz + 1
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
private let write_prev_preserves_wosize_upper
  (g_after_alloc: heap) (obj: obj_addr) (prev_fp: U64.t) (val_fp: U64.t)
  (wz: nat)
  : Lemma (requires U64.v (wosize_of_object obj g_after_alloc) <= wz + 1 /\
                    prev_fp <> 0UL /\
                    U64.v prev_fp >= U64.v mword /\
                    U64.v prev_fp < heap_size /\
                    U64.v prev_fp % U64.v mword = 0 /\
                    prev_fp <> hd_address obj)
          (ensures (let g2 = write_word g_after_alloc (prev_fp <: hp_addr) val_fp in
                    U64.v (wosize_of_object obj g2) <= wz + 1))
  =
  let hd = hd_address obj in
  hd_address_spec obj;
  hd_address_bounds obj;
  let g2 = write_word g_after_alloc (prev_fp <: hp_addr) val_fp in
  wosize_of_object_spec obj g2;
  wosize_of_object_spec obj g_after_alloc;
  let p = U64.v (prev_fp <: hp_addr) in
  let h = U64.v hd in
  FStar.Math.Lemmas.lemma_div_exact p 8;
  FStar.Math.Lemmas.lemma_div_exact h 8;
  let kp = p / 8 in
  let kh = h / 8 in
  if kp > kh then begin
    FStar.Math.Lemmas.lemma_mult_le_right 8 (kh + 1) kp;
    FStar.Math.Lemmas.distributivity_add_left kh 1 8
  end else begin
    FStar.Math.Lemmas.lemma_mult_le_right 8 (kp + 1) kh;
    FStar.Math.Lemmas.distributivity_add_left kp 1 8
  end;
  read_write_different g_after_alloc (prev_fp <: hp_addr) hd val_fp
#pop-options

/// Main recursive proof
#push-options "--z3rlimit 50 --fuel 4 --ifuel 1 --split_queries always"
let rec alloc_search_obj_wosize
  (g: heap) (head_fp: U64.t) (prev_fp: U64.t)
  (cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma
    (requires well_formed_heap g /\
              AllocLemmas.fl_valid g cur_fp fuel /\
              (prev_fp <> 0UL ==>
                (prev_fp <> cur_fp /\
                 U64.v prev_fp >= U64.v mword /\
                 U64.v prev_fp < heap_size /\
                 U64.v prev_fp % U64.v mword = 0 /\
                 Seq.mem prev_fp (objects zero_addr g) /\
                 U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1)))
    (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
              r.obj_out <> 0UL ==>
              (U64.v r.obj_out >= U64.v mword /\
               U64.v r.obj_out < heap_size /\
               U64.v r.obj_out % U64.v mword == 0 /\
               U64.v (wosize_of_object (r.obj_out <: obj_addr) r.heap_out) >= wz)))
    (decreases fuel)
  =
  if fuel = 0 then ()
  else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
  else if U64.v cur_fp >= heap_size then ()
  else if U64.v cur_fp % U64.v mword <> 0 then ()
  else begin
    AllocLemmas.fl_valid_elim g cur_fp fuel;
    let obj : obj_addr = cur_fp in
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let next_fp =
      if U64.v hd + 16 <= heap_size then read_word g obj
      else 0UL
    in
    if block_wz >= wz then begin
      // Found. Use alloc_from_block_wosize_lemma.
      alloc_from_block_wosize_lemma g obj wz next_fp;
      let (g', new_rem_fp) = alloc_from_block g obj wz next_fp in
      // After alloc_from_block: wosize_of_object obj g' >= wz
      // If prev_fp = 0UL, heap_out = g', done.
      if prev_fp = 0UL then ()
      else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size && U64.v prev_fp % U64.v mword = 0 then begin
        // prev_fp is a distinct object from obj (= cur_fp) in the objects list.
        // By objects_separated + wosize >= 1, their regions don't overlap,
        // so prev_fp <> hd_address(obj).
        let prev_obj : obj_addr = prev_fp in
        hd_address_spec obj;
        wosize_of_object_spec prev_obj g;
        if U64.v prev_fp < U64.v obj then begin
          objects_separated zero_addr g prev_obj obj;
          // obj > prev_fp + wosize(prev)*8 >= prev_fp + 8
          // hd(obj) = obj - 8 > prev_fp
          assert (prev_fp <> hd_address obj)
        end else begin
          objects_separated zero_addr g obj prev_obj;
          // prev_fp > obj + wosize(obj)*8 >= obj + 8 > obj - 8 = hd(obj)
          wosize_of_object_spec obj g;
          assert (prev_fp <> hd_address obj)
        end;
        write_prev_preserves_wosize g' obj prev_fp new_rem_fp wz
      end
      else ()
    end
    else begin
      // Block too small, continue
      if U64.v hd + 16 <= heap_size then
        alloc_search_obj_wosize g head_fp cur_fp next_fp wz (fuel - 1)
      else ()
    end
  end
#pop-options

#push-options "--z3rlimit 50 --fuel 4"
let alloc_spec_obj_wosize (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires well_formed_heap g /\
                    AllocLemmas.fl_valid g fp (heap_size / U64.v mword))
          (ensures (let r = alloc_spec g fp requested_wz in
                    r.obj_out <> 0UL ==>
                    (U64.v r.obj_out >= U64.v mword /\
                     U64.v r.obj_out < heap_size /\
                     U64.v r.obj_out % U64.v mword == 0 /\
                     U64.v (wosize_of_object (r.obj_out <: obj_addr) r.heap_out) >= 
                       (if requested_wz = 0 then 1 else requested_wz))))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_obj_wosize g fp 0UL fp wz (heap_size / U64.v mword)
#pop-options

/// ---------------------------------------------------------------------------
/// Part1-only versions: weaker preconditions (no full well_formed_heap)
/// ---------------------------------------------------------------------------

/// obj_out was in objects of the ORIGINAL heap (from fl_valid alone, no wfh needed)
#push-options "--z3rlimit 50 --fuel 4 --ifuel 1"
let rec alloc_search_obj_in_objects_pre_part1
  (g: heap) (head_fp: U64.t) (prev_fp: U64.t)
  (cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma
    (requires AllocLemmas.fl_valid g cur_fp fuel)
    (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
              r.obj_out <> 0UL ==>
              (U64.v r.obj_out >= U64.v mword /\
               U64.v r.obj_out < heap_size /\
               U64.v r.obj_out % U64.v mword == 0 /\
               Seq.mem (r.obj_out <: obj_addr) (objects zero_addr g))))
    (decreases fuel)
  =
  if fuel = 0 then ()
  else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
  else if U64.v cur_fp >= heap_size then ()
  else if U64.v cur_fp % U64.v mword <> 0 then ()
  else begin
    AllocLemmas.fl_valid_elim g cur_fp fuel;
    let obj : obj_addr = cur_fp in
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let next_fp =
      if U64.v hd + 16 <= heap_size then read_word g obj
      else 0UL
    in
    if block_wz >= wz then ()
    else begin
      if U64.v hd + 16 <= heap_size then
        alloc_search_obj_in_objects_pre_part1 g head_fp cur_fp next_fp wz (fuel - 1)
      else ()
    end
  end
#pop-options

/// After alloc, obj_out is in objects of the output heap (part1 only)
let alloc_spec_obj_in_objects_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    AllocLemmas.fl_valid g fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates g fp (heap_size / U64.v mword))
          (ensures (let r = alloc_spec g fp requested_wz in
                    r.obj_out <> 0UL ==>
                    (U64.v r.obj_out >= U64.v mword /\
                     U64.v r.obj_out < heap_size /\
                     U64.v r.obj_out % U64.v mword == 0 /\
                     Seq.mem (r.obj_out <: obj_addr) (objects zero_addr r.heap_out))))
  =
  let wz = if requested_wz = 0 then 1 else requested_wz in
  let fuel = heap_size / U64.v mword in
  // obj_out was in objects(0, g) (from fl_valid)
  alloc_search_obj_in_objects_pre_part1 g fp zero_addr fp wz fuel;
  // alloc preserves objects (part1 version)
  AllocLemmas.alloc_spec_preserves_objects_part1 g fp requested_wz

/// wosize of obj_out >= requested (no wfh — only fl_valid needed)
#push-options "--z3rlimit 50 --fuel 4 --ifuel 1 --split_queries always"
private let rec alloc_search_obj_wosize_part1
  (g: heap) (head_fp: U64.t) (prev_fp: U64.t)
  (cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma
    (requires AllocLemmas.fl_valid g cur_fp fuel /\
              (prev_fp <> 0UL ==>
                (prev_fp <> cur_fp /\
                 U64.v prev_fp >= U64.v mword /\
                 U64.v prev_fp < heap_size /\
                 U64.v prev_fp % U64.v mword = 0 /\
                 Seq.mem prev_fp (objects zero_addr g) /\
                 U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1)))
    (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
              r.obj_out <> 0UL ==>
              (U64.v r.obj_out >= U64.v mword /\
               U64.v r.obj_out < heap_size /\
               U64.v r.obj_out % U64.v mword == 0 /\
               U64.v (wosize_of_object (r.obj_out <: obj_addr) r.heap_out) >= wz)))
    (decreases fuel)
  =
  if fuel = 0 then ()
  else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
  else if U64.v cur_fp >= heap_size then ()
  else if U64.v cur_fp % U64.v mword <> 0 then ()
  else begin
    AllocLemmas.fl_valid_elim g cur_fp fuel;
    let obj : obj_addr = cur_fp in
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let next_fp =
      if U64.v hd + 16 <= heap_size then read_word g obj
      else 0UL
    in
    if block_wz >= wz then begin
      alloc_from_block_wosize_lemma g obj wz next_fp;
      let (g', new_rem_fp) = alloc_from_block g obj wz next_fp in
      if prev_fp = 0UL then ()
      else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size && U64.v prev_fp % U64.v mword = 0 then begin
        let prev_obj : obj_addr = prev_fp in
        hd_address_spec obj;
        wosize_of_object_spec prev_obj g;
        if U64.v prev_fp < U64.v obj then begin
          objects_separated zero_addr g prev_obj obj;
          assert (prev_fp <> hd_address obj)
        end else begin
          objects_separated zero_addr g obj prev_obj;
          wosize_of_object_spec obj g;
          assert (prev_fp <> hd_address obj)
        end;
        write_prev_preserves_wosize g' obj prev_fp new_rem_fp wz
      end
      else ()
    end
    else begin
      if U64.v hd + 16 <= heap_size then
        alloc_search_obj_wosize_part1 g head_fp cur_fp next_fp wz (fuel - 1)
      else ()
    end
  end
#pop-options

let alloc_spec_obj_wosize_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires AllocLemmas.fl_valid g fp (heap_size / U64.v mword))
          (ensures (let r = alloc_spec g fp requested_wz in
                    r.obj_out <> 0UL ==>
                    (U64.v r.obj_out >= U64.v mword /\
                     U64.v r.obj_out < heap_size /\
                     U64.v r.obj_out % U64.v mword == 0 /\
                     U64.v (wosize_of_object (r.obj_out <: obj_addr) r.heap_out) >= 
                       (if requested_wz = 0 then 1 else requested_wz))))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_obj_wosize_part1 g fp 0UL fp wz (heap_size / U64.v mword)

/// Upper bound on wosize after alloc_search: wosize <= wz + 1
#push-options "--z3rlimit 50 --fuel 4 --ifuel 1 --split_queries always"
private let rec alloc_search_obj_wosize_upper_part1
  (g: heap) (head_fp: U64.t) (prev_fp: U64.t)
  (cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma
    (requires AllocLemmas.fl_valid g cur_fp fuel /\
              (prev_fp <> 0UL ==>
                (prev_fp <> cur_fp /\
                 U64.v prev_fp >= U64.v mword /\
                 U64.v prev_fp < heap_size /\
                 U64.v prev_fp % U64.v mword = 0 /\
                 Seq.mem prev_fp (objects zero_addr g) /\
                 U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1)))
    (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
              r.obj_out <> 0UL ==>
              (U64.v r.obj_out >= U64.v mword /\
               U64.v r.obj_out < heap_size /\
               U64.v r.obj_out % U64.v mword == 0 /\
               (let obj_out : obj_addr = r.obj_out in
                U64.v (wosize_of_object obj_out r.heap_out) <= wz + 1))))
    (decreases fuel)
  =
  if fuel = 0 then ()
  else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
  else if U64.v cur_fp >= heap_size then ()
  else if U64.v cur_fp % U64.v mword <> 0 then ()
  else begin
    AllocLemmas.fl_valid_elim g cur_fp fuel;
    let obj : obj_addr = cur_fp in
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let next_fp =
      if U64.v hd + 16 <= heap_size then read_word g obj
      else 0UL
    in
    if block_wz >= wz then begin
      alloc_from_block_wosize_lemma g obj wz next_fp;
      alloc_from_block_wosize_upper_lemma g obj wz next_fp;
      let (g', new_rem_fp) = alloc_from_block g obj wz next_fp in
      if prev_fp = 0UL then ()
      else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size && U64.v prev_fp % U64.v mword = 0 then begin
        let prev_obj : obj_addr = prev_fp in
        hd_address_spec obj;
        wosize_of_object_spec prev_obj g;
        if U64.v prev_fp < U64.v obj then begin
          objects_separated zero_addr g prev_obj obj;
          assert (prev_fp <> hd_address obj)
        end else begin
          objects_separated zero_addr g obj prev_obj;
          wosize_of_object_spec obj g;
          assert (prev_fp <> hd_address obj)
        end;
        write_prev_preserves_wosize_upper g' obj prev_fp new_rem_fp wz
      end
      else ()
    end
    else begin
      if U64.v hd + 16 <= heap_size then
        alloc_search_obj_wosize_upper_part1 g head_fp cur_fp next_fp wz (fuel - 1)
      else ()
    end
  end
#pop-options

/// Top-level: after alloc_spec, wosize <= requested_wz + 1
let alloc_spec_obj_wosize_upper_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires AllocLemmas.fl_valid g fp (heap_size / U64.v mword))
          (ensures (let wz = if requested_wz = 0 then 1 else requested_wz in
                    let r = alloc_spec g fp requested_wz in
                    r.obj_out <> 0UL ==>
                    (U64.v r.obj_out >= U64.v mword /\
                     U64.v r.obj_out < heap_size /\
                     U64.v r.obj_out % U64.v mword == 0 /\
                     (let obj_out : obj_addr = r.obj_out in
                      U64.v (wosize_of_object obj_out r.heap_out) <= wz + 1))))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_obj_wosize_upper_part1 g fp 0UL fp wz (heap_size / U64.v mword)

/// ---------------------------------------------------------------------------
/// alloc_spec returns an object that is IN the pre-alloc chain.
/// Equivalently: if chain_avoids g fp excl fuel = true, then excl ≠ obj_out.
/// ---------------------------------------------------------------------------
///
/// Proof strategy: induction on alloc_search. The invariant is
/// chain_avoids g cur_fp excl fuel = true. At the found step,
/// chain_avoids_head_ne gives cur_fp ≠ excl = obj_out ≠ excl.
/// At the advance step, chain_avoids_tail gives the invariant for next_fp.

#push-options "--z3rlimit 50 --fuel 4 --ifuel 1"
let rec alloc_search_obj_ne_excl
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat) (excl: U64.t)
  : Lemma
    (requires well_formed_heap_part1 g /\
              AllocLemmas.fl_valid g cur_fp fuel /\
              AllocLemmas.chain_avoids g cur_fp excl fuel = true /\
              wz >= 1)
    (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
              r.obj_out <> 0UL ==> r.obj_out <> excl))
    (decreases fuel)
  =
  if fuel = 0 then ()
  else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
  else if U64.v cur_fp >= heap_size then ()
  else if U64.v cur_fp % U64.v mword <> 0 then ()
  else begin
    // cur_fp is a valid obj_addr with fuel > 0
    AllocLemmas.fl_valid_elim g cur_fp fuel;
    // fl_valid_elim gives: Seq.mem cur_fp (objects zero_addr g), wosize >= 1
    // From well_formed_heap_part1 + wosize >= 1: hd + 16 <= heap_size
    let obj : obj_addr = cur_fp in
    hd_address_spec obj;
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let next_fp =
      if U64.v hd + 16 <= heap_size then read_word g obj
      else 0UL
    in
    // chain_avoids_head_ne: cur_fp ≠ excl
    AllocLemmas.chain_avoids_head_ne g cur_fp excl fuel;
    if block_wz >= wz then
      // Found: obj_out = cur_fp, and cur_fp ≠ excl from chain_avoids_head_ne
      ()
    else begin
      // Advance: need chain_avoids g next_fp excl (fuel-1)
      if U64.v hd + 16 <= heap_size then begin
        AllocLemmas.chain_avoids_tail g cur_fp excl fuel;
        alloc_search_obj_ne_excl g head_fp cur_fp next_fp wz (fuel - 1) excl
      end
      else ()
    end
  end
#pop-options

/// Top-level: if chain_avoids g fp excl fuel = true, then alloc_spec obj_out ≠ excl
let alloc_spec_obj_ne_excl (g: heap) (fp: U64.t) (requested_wz: nat) (excl: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    AllocLemmas.fl_valid g fp (heap_size / U64.v mword) /\
                    AllocLemmas.chain_avoids g fp excl (heap_size / U64.v mword) = true)
          (ensures (let r = alloc_spec g fp requested_wz in
                    r.obj_out <> 0UL ==> r.obj_out <> excl))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_obj_ne_excl g fp 0UL fp wz (heap_size / U64.v mword) excl

/// ---------------------------------------------------------------------------
/// Pre-alloc wosize of obj_out >= requested_wz
/// ---------------------------------------------------------------------------
///
/// The allocator returns obj_out = cur_fp only when block_wz >= wz.
/// block_wz = wosize_of_object(cur_fp, g). So wosize_of_object(obj_out, g) >= wz.

#push-options "--z3rlimit 50 --fuel 4 --ifuel 1"
private let rec alloc_search_obj_wosize_pre_part1
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma
    (requires AllocLemmas.fl_valid g cur_fp fuel /\ wz >= 1)
    (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
              r.obj_out <> 0UL ==>
              (U64.v r.obj_out >= U64.v mword /\
               U64.v r.obj_out < heap_size /\
               U64.v r.obj_out % U64.v mword == 0 /\
               U64.v (wosize_of_object (r.obj_out <: obj_addr) g) >= wz)))
    (decreases fuel)
  =
  if fuel = 0 then ()
  else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
  else if U64.v cur_fp >= heap_size then ()
  else if U64.v cur_fp % U64.v mword <> 0 then ()
  else begin
    AllocLemmas.fl_valid_elim g cur_fp fuel;
    let obj : obj_addr = cur_fp in
    hd_address_spec obj;
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    wosize_of_object_spec obj g;
    let next_fp =
      if U64.v hd + 16 <= heap_size then read_word g obj
      else 0UL
    in
    if block_wz >= wz then
      // Found: obj_out = cur_fp, wosize_of_object(cur_fp, g) = block_wz >= wz
      ()
    else begin
      if U64.v hd + 16 <= heap_size then
        alloc_search_obj_wosize_pre_part1 g head_fp cur_fp next_fp wz (fuel - 1)
      else ()
    end
  end
#pop-options

/// Top-level: pre-alloc wosize of allocated object >= requested
let alloc_spec_obj_wosize_pre_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires AllocLemmas.fl_valid g fp (heap_size / U64.v mword))
          (ensures (let wz = (if requested_wz = 0 then 1 else requested_wz) in
                    let r = alloc_spec g fp requested_wz in
                    r.obj_out <> 0UL ==>
                    (U64.v r.obj_out >= U64.v mword /\
                     U64.v r.obj_out < heap_size /\
                     U64.v r.obj_out % U64.v mword == 0 /\
                     U64.v (wosize_of_object (r.obj_out <: obj_addr) g) >= wz)))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_obj_wosize_pre_part1 g fp 0UL fp wz (heap_size / U64.v mword)

/// ---------------------------------------------------------------------------
/// OOM lemma: when alloc_spec fails, heap and fp are unchanged
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 4 --ifuel 1"
private let rec alloc_search_oom_unchanged
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma
    (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
              r.obj_out == 0UL ==>
              (r.heap_out == g /\ r.fp_out == head_fp)))
    (decreases fuel)
  =
  if fuel = 0 then ()
  else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
  else if U64.v cur_fp >= heap_size then ()
  else if U64.v cur_fp % U64.v mword <> 0 then ()
  else begin
    let obj : obj_addr = cur_fp in
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let next_fp =
      if U64.v hd + 16 <= heap_size then read_word g obj
      else 0UL
    in
    if block_wz >= wz then
      // Found: obj_out = cur_fp ≠ 0UL, so the implication is vacuous
      ()
    else
      alloc_search_oom_unchanged g head_fp cur_fp next_fp wz (fuel - 1)
  end
#pop-options

/// Top-level: when alloc_spec fails (obj_out = 0UL), heap and fp are unchanged
let alloc_spec_oom_unchanged (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (ensures (let r = alloc_spec g fp requested_wz in
                    r.obj_out == 0UL ==>
                    (r.heap_out == g /\ r.fp_out == fp)))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_oom_unchanged g fp 0UL fp wz (heap_size / U64.v mword)

/// ---------------------------------------------------------------------------
/// Allocator properties for blue_fields_closed proofs
/// ---------------------------------------------------------------------------

/// After alloc_from_block, the allocated object has color White.
/// alloc_from_block writes a new header with color White.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let alloc_from_block_obj_not_blue (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    U64.v (getWosize (read_word g (hd_address obj))) >= wz /\
                    wz >= 1)
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    color_of_object obj g' == White /\
                    is_blue obj g' = false))
  = let hd = hd_address obj in
    hd_address_spec obj;
    hd_address_bounds obj;
    let hdr = read_word g hd in
    let bwz = U64.v (getWosize hdr) in
    wfh_part1_obj_bound g obj;
    let (g', _) = alloc_from_block g obj wz next_fp in
    let leftover = bwz - wz in
    if leftover < 2 then begin
      GC.Spec.Allocator.alloc_from_block_exact g obj wz next_fp;
      let alloc_hdr = make_header (U64.uint_to_t bwz) white_bits 0UL in
      read_write_same g hd alloc_hdr;
      AllocLemmas.make_header_getColor (U64.uint_to_t bwz) white_bits 0UL;
      getColor_raw alloc_hdr
    end else begin
      let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
      if rem_hd_nat >= heap_size then begin
        GC.Spec.Allocator.alloc_from_block_split_rem_hd_oob g obj wz next_fp;
        let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
        read_write_same g hd alloc_hdr;
        AllocLemmas.make_header_getColor (U64.uint_to_t wz) white_bits 0UL;
        getColor_raw alloc_hdr
      end else begin
        let rem_obj_nat = rem_hd_nat + 8 in
        if rem_obj_nat >= heap_size then begin
          GC.Spec.Allocator.alloc_from_block_split_rem_obj_oob g obj wz next_fp;
          let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
          let g1 = write_word g hd alloc_hdr in
          read_write_same g hd alloc_hdr;
          let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
          let rem_hdr = make_header (U64.uint_to_t (leftover - 1)) blue_bits 0UL in
          read_write_different g1 rem_hd hd rem_hdr;
          AllocLemmas.make_header_getColor (U64.uint_to_t wz) white_bits 0UL;
          getColor_raw alloc_hdr
        end else begin
          GC.Spec.Allocator.alloc_from_block_split_normal g obj wz next_fp;
          let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
          let g1 = write_word g hd alloc_hdr in
          read_write_same g hd alloc_hdr;
          let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
          let rem_hdr = make_header (U64.uint_to_t (leftover - 1)) blue_bits 0UL in
          read_write_different g1 rem_hd hd rem_hdr;
          let rem_field : hp_addr = U64.uint_to_t rem_obj_nat in
          FStar.Math.Lemmas.pow2_lt_compat 64 57;
          let g2 = write_word g1 rem_hd rem_hdr in
          read_write_different g2 rem_field hd next_fp;
          AllocLemmas.make_header_getColor (U64.uint_to_t wz) white_bits 0UL;
          getColor_raw alloc_hdr
        end
      end
    end;
    // Bridge: getColor (read_word g' hd) == White, so is_blue obj g' = false
    color_of_object_spec obj g';
    is_blue_iff obj g'
#pop-options

/// Writing to an address different from hd_address obj preserves color_of_object.
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let write_preserves_color (g: heap) (obj: obj_addr) (addr: hp_addr) (v: U64.t)
  : Lemma (requires U64.v addr + 8 <= U64.v (hd_address obj) \/
                    U64.v (hd_address obj) + 8 <= U64.v addr)
          (ensures (let g' = write_word g addr v in
                    color_of_object obj g' == color_of_object obj g))
  = hd_address_spec obj;
    read_write_different g addr (hd_address obj) v;
    let g' = write_word g addr v in
    color_of_object_spec obj g;
    color_of_object_spec obj g'
#pop-options

/// Writing the prev_fp link (which is at the prev_fp address, i.e. field[0])
/// does not affect obj's header → obj remains not-blue.
/// Requires prev_fp != hd_address obj (guaranteed by objects_separated at call sites).
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let write_prev_preserves_not_blue (g': heap) (obj: obj_addr) (prev_fp: U64.t) (new_rem_fp: U64.t)
  : Lemma (requires is_blue obj g' = false /\
                    U64.v prev_fp >= U64.v mword /\ U64.v prev_fp < heap_size /\
                    U64.v prev_fp % U64.v mword = 0 /\
                    (prev_fp <: obj_addr) <> obj /\
                    (U64.v prev_fp + 8 <= U64.v (hd_address obj) \/
                     U64.v (hd_address obj) + 8 <= U64.v prev_fp))
          (ensures (let g2 = write_word g' (prev_fp <: hp_addr) new_rem_fp in
                    is_blue obj g2 = false))
  = hd_address_spec obj;
    read_write_different g' (prev_fp <: hp_addr) (hd_address obj) new_rem_fp;
    let g2 = write_word g' (prev_fp <: hp_addr) new_rem_fp in
    color_of_object_spec obj g';
    color_of_object_spec obj g2;
    is_blue_iff obj g';
    is_blue_iff obj g2
#pop-options

/// alloc_from_block preserves reads at addresses outside the modified range.
/// The modified range is: hd_address(obj) (header) and possibly a remainder header/field.
/// If addr is outside obj's block entirely, read_word is unchanged.
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let alloc_from_block_read_frame (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
                                (addr: hp_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    U64.v (getWosize (read_word g (hd_address obj))) >= wz /\
                    wz >= 1 /\
                    (U64.v addr + 8 <= U64.v (hd_address obj) \/
                     U64.v addr >= U64.v obj + U64.v (getWosize (read_word g (hd_address obj))) * 8))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    read_word g' addr == read_word g addr))
  = let hd = hd_address obj in
    hd_address_spec obj;
    hd_address_bounds obj;
    let hdr = read_word g hd in
    let bwz = U64.v (getWosize hdr) in
    wfh_part1_obj_bound g obj;
    let leftover = bwz - wz in
    if leftover < 2 then begin
      GC.Spec.Allocator.alloc_from_block_exact g obj wz next_fp;
      let alloc_hdr = make_header (U64.uint_to_t bwz) white_bits 0UL in
      read_write_different g hd addr alloc_hdr
    end else begin
      let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
      if rem_hd_nat >= heap_size then begin
        GC.Spec.Allocator.alloc_from_block_split_rem_hd_oob g obj wz next_fp;
        let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
        read_write_different g hd addr alloc_hdr
      end else begin
        let rem_obj_nat = rem_hd_nat + 8 in
        if rem_obj_nat >= heap_size then begin
          GC.Spec.Allocator.alloc_from_block_split_rem_obj_oob g obj wz next_fp;
          let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
          let g1 = write_word g hd alloc_hdr in
          read_write_different g hd addr alloc_hdr;
          let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
          let rem_hdr = make_header (U64.uint_to_t (leftover - 1)) blue_bits 0UL in
          read_write_different g1 rem_hd addr rem_hdr
        end else begin
          GC.Spec.Allocator.alloc_from_block_split_normal g obj wz next_fp;
          let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
          let g1 = write_word g hd alloc_hdr in
          read_write_different g hd addr alloc_hdr;
          let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
          let rem_hdr = make_header (U64.uint_to_t (leftover - 1)) blue_bits 0UL in
          let g2 = write_word g1 rem_hd rem_hdr in
          read_write_different g1 rem_hd addr rem_hdr;
          let rem_field : hp_addr = U64.uint_to_t rem_obj_nat in
          FStar.Math.Lemmas.pow2_lt_compat 64 57;
          read_write_different g2 rem_field addr next_fp
        end
      end
    end
#pop-options

/// Helper: writing a value with the same getWosize at an aligned address preserves objects.
/// By induction on objects: at each header position, either the read is unchanged
/// (read_write_different) or the wosize is preserved (read_write_same + hypothesis).
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
private let rec write_header_same_wosize_preserves_objects_aux
  (start: hp_addr) (g: heap) (addr: hp_addr) (v: U64.t)
  : Lemma (requires getWosize v == getWosize (read_word g addr))
          (ensures objects start (write_word g addr v) == objects start g)
          (decreases (Seq.length g - U64.v start))
  = let g' = write_word g addr v in
    if U64.v start + 8 >= Seq.length g then ()
    else begin
      // Show: getWosize (read_word g' start) == getWosize (read_word g start)
      if start = addr then
        read_write_same g addr v
        // read_word g' start == v, and getWosize v == getWosize (read_word g start)
      else
        read_write_different g addr start v;
        // read_word g' start == read_word g start

      let wz = getWosize (read_word g start) in
      let next_start_nat = U64.v start + ((U64.v wz + 1) * 8) in
      if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then ()
      else begin
        f_address_spec start;
        if next_start_nat >= heap_size then ()
        else
          write_header_same_wosize_preserves_objects_aux
            (U64.uint_to_t next_start_nat) g addr v
      end
    end
#pop-options

/// In exact-fit case (bwz - wz < 2), objects list is unchanged.
/// alloc_from_block only writes the header (same wosize), preserving object list structure.
/// Proof: header write with same wosize -> objects recursion takes identical steps.
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let alloc_from_block_exact_objects_eq_part1 (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let bwz = U64.v (getWosize (read_word g (hd_address obj))) in
                     bwz >= wz /\ bwz - wz < 2) /\
                    wz >= 1)
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    objects zero_addr g' == objects zero_addr g))
  = let hd = hd_address obj in
    let hdr = read_word g hd in
    let bwz = U64.v (getWosize hdr) in
    hd_address_spec obj;
    hd_address_bounds obj;
    SA.alloc_from_block_exact g obj wz next_fp;
    let ahdr = make_header (U64.uint_to_t bwz) white_bits 0UL in
    let g1 = write_word g hd ahdr in
    assert (alloc_from_block g obj wz next_fp == (g1, next_fp));
    getWosize_bound hdr;
    AllocLemmas.make_header_getWosize (U64.uint_to_t bwz) white_bits 0UL;
    assert (getWosize ahdr == getWosize hdr);
    write_header_same_wosize_preserves_objects_aux zero_addr g hd ahdr
#pop-options

/// Top-level: alloc_spec result obj is not blue (the allocator writes White color).
/// Proof: alloc_spec calls alloc_search which calls alloc_from_block at the found block.
/// alloc_from_block_obj_not_blue proves the block-level result.
#push-options "--z3rlimit 50 --fuel 4 --ifuel 1"
let rec alloc_search_obj_not_blue
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma
    (requires well_formed_heap_part1 g /\
             AllocLemmas.fl_valid g cur_fp fuel /\
             AllocLemmas.fl_chain_terminates g cur_fp fuel /\
             wz >= 1)
    (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
              r.obj_out <> 0UL ==>
              (U64.v r.obj_out >= U64.v mword /\
               U64.v r.obj_out < heap_size /\
               U64.v r.obj_out % U64.v mword = 0)))
    (decreases fuel)
  = if fuel = 0 then ()
    else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
    else if U64.v cur_fp >= heap_size then ()
    else if U64.v cur_fp % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = cur_fp in
      let hd = hd_address obj in
      hd_address_spec obj;
      hd_address_bounds obj;
      let hdr = read_word g hd in
      let bwz = U64.v (getWosize hdr) in
      let next_fp = if U64.v hd + 16 <= heap_size then read_word g obj else 0UL in
      AllocLemmas.fl_valid_elim g cur_fp fuel;
      AllocLemmas.fl_valid_gives_mem g cur_fp fuel;
      if bwz >= wz then ()
      else begin
        if U64.v hd + 16 <= heap_size then begin
          AllocLemmas.fl_chain_terminates_elim g cur_fp fuel;
          alloc_search_obj_not_blue g head_fp cur_fp next_fp wz (fuel - 1)
        end else ()
      end
    end
#pop-options

/// alloc_search result has color White (the allocator writes White)
#push-options "--z3rlimit 50 --fuel 4 --ifuel 1"
let rec alloc_search_obj_white
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma
    (requires well_formed_heap_part1 g /\
             AllocLemmas.fl_valid g cur_fp fuel /\
             AllocLemmas.fl_chain_terminates g cur_fp fuel /\
             wz >= 1 /\
             (prev_fp <> 0UL ==>
               (U64.v prev_fp >= U64.v mword /\
                U64.v prev_fp < heap_size /\
                U64.v prev_fp % U64.v mword = 0 /\
                Seq.mem prev_fp (objects zero_addr g) /\
                U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1)))
    (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
              r.obj_out <> 0UL ==>
              (let out = r.obj_out in
               U64.v out >= U64.v mword /\
               U64.v out < heap_size /\
               U64.v out % U64.v mword = 0 /\
               color_of_object (out <: obj_addr) r.heap_out == White)))
    (decreases fuel)
  = alloc_search_obj_not_blue g head_fp prev_fp cur_fp wz fuel;
    if fuel = 0 then ()
    else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
    else if U64.v cur_fp >= heap_size then ()
    else if U64.v cur_fp % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = cur_fp in
      let hd = hd_address obj in
      hd_address_spec obj;
      hd_address_bounds obj;
      let hdr = read_word g hd in
      let bwz = U64.v (getWosize hdr) in
      let next_fp = if U64.v hd + 16 <= heap_size then read_word g obj else 0UL in
      AllocLemmas.fl_valid_elim g cur_fp fuel;
      AllocLemmas.fl_valid_gives_mem g cur_fp fuel;
      if bwz >= wz then begin
        // Found a block: alloc_from_block writes White header
        alloc_from_block_obj_not_blue g obj wz next_fp;
        let (g', new_rem_fp) = alloc_from_block g obj wz next_fp in
        // alloc_from_block gives color_of_object obj g' == White
        if prev_fp <> 0UL && U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
           U64.v prev_fp % U64.v mword = 0 then begin
          // Result heap = write_word g' prev_fp new_rem_fp
          // Need: prev_fp is separated from hd_address obj
          // Both prev_fp and obj are in objects zero_addr g, both have wosize >= 1
          AllocLemmas.fl_valid_gives_wosize g cur_fp fuel;
          // wosize_of_object_as_wosize is definitionally equal to wosize_of_object
          assert (U64.v (wosize_of_object_as_wosize obj g) >= 1);
          if U64.v prev_fp < U64.v obj then begin
            assert (U64.v (wosize_of_object_as_wosize prev_fp g) >= 1);
            objects_separated zero_addr g prev_fp obj;
            assert (U64.v prev_fp + 8 <= U64.v (hd_address obj))
          end else begin
            objects_separated zero_addr g obj prev_fp;
            assert (U64.v (hd_address obj) + 8 <= U64.v prev_fp)
          end;
          write_preserves_color g' obj (prev_fp <: hp_addr) new_rem_fp
        end else ()
      end else begin
        if U64.v hd + 16 <= heap_size then begin
          AllocLemmas.fl_chain_terminates_elim g cur_fp fuel;
          AllocLemmas.fl_valid_gives_mem g cur_fp fuel;
          alloc_search_obj_white g head_fp cur_fp next_fp wz (fuel - 1)
        end else ()
      end
    end
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let alloc_spec_obj_not_blue_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    AllocLemmas.fl_valid g fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates g fp (heap_size / U64.v mword))
          (ensures (let r = alloc_spec g fp requested_wz in
                    r.obj_out <> 0UL ==>
                    (U64.v r.obj_out >= U64.v mword /\
                     U64.v r.obj_out < heap_size /\
                     U64.v r.obj_out % U64.v mword = 0 /\
                     color_of_object (r.obj_out <: obj_addr) r.heap_out == White)))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_obj_white g fp 0UL fp wz (heap_size / U64.v mword)
#pop-options

/// Helper: alloc_from_block preserves read at hd_address of a different object.
/// Proof: all writes (hd, rem_hd, rem_field) are within obj's block, which is
/// separated from excl's header by objects_separated.
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
private let alloc_from_block_read_header_other
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (excl: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    Seq.mem excl (objects zero_addr g) /\
                    (obj <: U64.t) <> (excl <: U64.t) /\
                    (let hdr = read_word g (hd_address obj) in
                     U64.v (getWosize hdr) >= wz /\ wz >= 1))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    read_word g' (hd_address excl) == read_word g (hd_address excl)))
  = let hd_obj = hd_address obj in
    let hd_excl = hd_address excl in
    let hdr = read_word g hd_obj in
    let bwz = U64.v (getWosize hdr) in
    hd_address_spec obj;
    hd_address_spec excl;
    hd_address_bounds obj;
    hd_address_bounds excl;
    // Key: objects_separated gives non-overlap
    wosize_of_object_spec obj g;
    wosize_of_object_spec excl g;
    if U64.v excl < U64.v obj then begin
      objects_separated zero_addr g excl obj;
      // excl + wz(excl)*8 < obj, so hd_excl = excl - 8 < obj - 8 = hd_obj
      // and hd_excl + 8 = excl <= obj - wz(excl)*8 - 8 <= obj - 16 < hd_obj
      assert (U64.v hd_excl + 8 <= U64.v hd_obj)
    end else begin
      objects_separated zero_addr g obj excl;
      // obj + wz(obj)*8 < excl = bwz*8 < excl, so hd_excl = excl - 8 >= obj + bwz*8
      // and all writes are in [hd_obj, obj + (bwz+1)*8) which is ≤ hd_excl
      assert (U64.v hd_obj + 8 <= U64.v hd_excl)
    end;
    // Now case split on exact vs split
    let leftover = bwz - wz in
    if leftover < 2 then begin
      SA.alloc_from_block_exact g obj wz next_fp;
      let ahdr = make_header (U64.uint_to_t bwz) white_bits 0UL in
      read_write_different g hd_obj hd_excl ahdr
    end else begin
      let rhn = U64.v hd_obj + (1 + wz) * 8 in
      if rhn >= heap_size then begin
        SA.alloc_from_block_split_rem_hd_oob g obj wz next_fp;
        let ahdr = make_header (U64.uint_to_t wz) white_bits 0UL in
        read_write_different g hd_obj hd_excl ahdr
      end else if rhn + 8 >= heap_size then begin
        SA.alloc_from_block_split_rem_obj_oob g obj wz next_fp;
        let ahdr = make_header (U64.uint_to_t wz) white_bits 0UL in
        let g1 = write_word g hd_obj ahdr in
        read_write_different g hd_obj hd_excl ahdr;
        let rh : hp_addr = U64.uint_to_t rhn in
        let rw = bwz - wz - 1 in
        let rhdr = make_header (U64.uint_to_t rw) blue_bits 0UL in
        // rh = obj + wz*8 which is between hd_obj and excl (or before hd_excl)
        if U64.v excl < U64.v obj then
          assert (U64.v hd_excl + 8 <= U64.v hd_obj)
        else
          assert (U64.v rh < U64.v hd_excl);  // rh = hd_obj + (1+wz)*8 < hd_excl
        read_write_different g1 rh hd_excl rhdr
      end else begin
        SA.alloc_from_block_split_normal g obj wz next_fp;
        let ahdr = make_header (U64.uint_to_t wz) white_bits 0UL in
        let g1 = write_word g hd_obj ahdr in
        read_write_different g hd_obj hd_excl ahdr;
        let rh : hp_addr = U64.uint_to_t rhn in
        let rw = bwz - wz - 1 in
        let rhdr = make_header (U64.uint_to_t rw) blue_bits 0UL in
        let g2 = write_word g1 rh rhdr in
        if U64.v excl < U64.v obj then
          assert (U64.v hd_excl + 8 <= U64.v rh)  // hd_excl < hd_obj < rh
        else
          assert (U64.v rh + 8 <= U64.v hd_excl);  // rh+8 = obj+(wz+1)*8 <= obj+bwz*8 <= hd_excl
        read_write_different g1 rh hd_excl rhdr;
        let ron = rhn + 8 in
        let ro : hp_addr = U64.uint_to_t ron in
        if U64.v excl < U64.v obj then
          assert (U64.v hd_excl + 8 <= U64.v ro)
        else
          assert (U64.v ro + 8 <= U64.v hd_excl);  // ro+8 = obj+(wz+2)*8 <= obj+bwz*8 <= hd_excl (since bwz >= wz+2)
        read_write_different g2 ro hd_excl next_fp
      end
    end
#pop-options

/// Inductive: alloc_search preserves the header of excl when excl ≠ obj_out.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0 --split_queries always"
private let rec alloc_search_read_header_other
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat) (excl: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    AllocLemmas.fl_valid g cur_fp fuel /\
                    AllocLemmas.fl_chain_terminates g cur_fp fuel /\
                    wz >= 1 /\
                    Seq.mem excl (objects zero_addr g) /\
                    (excl <: U64.t) <> (alloc_search g head_fp prev_fp cur_fp wz fuel).obj_out /\
                    (prev_fp <> 0UL ==>
                      (U64.v prev_fp >= U64.v mword /\
                       U64.v prev_fp < heap_size /\
                       U64.v prev_fp % U64.v mword = 0 /\
                       Seq.mem prev_fp (objects zero_addr g) /\
                       U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1)))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    r.obj_out <> 0UL ==>
                    read_word r.heap_out (hd_address excl) ==
                    read_word g (hd_address excl)))
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
      AllocLemmas.fl_valid_gives_mem g cur_fp fuel;
      AllocLemmas.fl_valid_gives_wosize g cur_fp fuel;
      let next_fp =
        if U64.v hd + 16 <= heap_size then read_word g obj
        else 0UL
      in
      if block_wz >= wz then begin
        // Found suitable block: cur_fp = obj_out, excl ≠ cur_fp
        let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
        assert (r.obj_out == cur_fp);
        assert ((excl <: U64.t) <> cur_fp);
        // alloc_from_block preserves hd_address excl
        alloc_from_block_read_header_other g obj wz next_fp excl;
        let (g', new_fp) = alloc_from_block g obj wz next_fp in
        // Handle prev_fp write
        if prev_fp = 0UL then ()
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          // prev_fp ∈ objects, excl ∈ objects. Write at prev_fp, read at hd(excl).
          hd_address_spec excl;
          // prev_fp is the obj_addr, hd_excl = excl - 8
          // If prev_fp = excl: write at excl, read at excl-8. read_write_different: excl-8+8 = excl ≤ excl ✓
          // If prev_fp ≠ excl: objects_separated gives separation
          if (prev_fp <: U64.t) = (excl <: U64.t) then begin
            // Write at prev_fp = excl, read at excl - 8
            assert (U64.v (hd_address excl) + 8 <= U64.v prev_fp);
            read_write_different g' (prev_fp <: hp_addr) (hd_address excl) new_fp
          end else begin
            wosize_of_object_spec excl g;
            wosize_of_object_spec (prev_fp <: obj_addr) g;
            if U64.v prev_fp < U64.v excl then begin
              objects_separated zero_addr g (prev_fp <: obj_addr) excl;
              // prev_fp + wz(prev_fp)*8 < excl. wz >= 1 so prev_fp + 8 < excl.
              // 8-aligned: excl >= prev_fp + 16, so hd_excl = excl - 8 >= prev_fp + 8
              assert (U64.v prev_fp + 8 <= U64.v (hd_address excl));
              read_write_different g' (prev_fp <: hp_addr) (hd_address excl) new_fp
            end else begin
              // prev_fp > excl, so hd_address excl + 8 = excl < prev_fp
              assert (U64.v (hd_address excl) + 8 <= U64.v prev_fp);
              read_write_different g' (prev_fp <: hp_addr) (hd_address excl) new_fp
            end
          end
        end else ()
      end else begin
        // Block too small, continue
        if U64.v hd + 16 <= heap_size then begin
          AllocLemmas.fl_valid_elim g cur_fp fuel;
          AllocLemmas.fl_chain_terminates_elim g cur_fp fuel
        end else ();
        alloc_search_read_header_other g head_fp cur_fp next_fp wz (fuel - 1) excl
      end
    end
#pop-options

/// Top-level: alloc_spec preserves the header of other objects.
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let alloc_spec_read_header_other_part1 (g: heap) (fp: U64.t) (requested_wz: nat) (excl: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    AllocLemmas.fl_valid g fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates g fp (heap_size / U64.v mword) /\
                    Seq.mem excl (objects zero_addr g) /\
                    (excl <: U64.t) <> (alloc_spec g fp requested_wz).obj_out)
          (ensures (let r = alloc_spec g fp requested_wz in
                    r.obj_out <> 0UL ==>
                    read_word r.heap_out (hd_address excl) ==
                    read_word g (hd_address excl)))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_read_header_other g fp 0UL fp wz (heap_size / U64.v mword) excl
#pop-options
