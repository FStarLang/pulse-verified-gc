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
#push-options "--z3rlimit 200 --fuel 4 --ifuel 1"
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
  else if cur_fp = 0UL then ()
  else if U64.v cur_fp < U64.v mword then ()
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
/// When alloc_spec succeeds, obj_out is in objects 0UL heap_out
/// ---------------------------------------------------------------------------

/// The allocated object was a free-list node, hence already in objects 0UL g.
/// alloc_spec_preserves_objects shows all old objects survive.
/// So obj_out is in objects 0UL heap_out.
///
/// Proof: obj_out = cur_fp which is in the free list. fl_valid ensures
/// free-list nodes are in objects. alloc_spec_preserves_objects preserves them.
#push-options "--z3rlimit 200 --fuel 4 --ifuel 1"
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
  else if cur_fp = 0UL then ()
  else if U64.v cur_fp < U64.v mword then ()
  else if U64.v cur_fp >= heap_size then ()
  else if U64.v cur_fp % U64.v mword <> 0 then ()
  else begin
    AllocLemmas.fl_valid_elim g cur_fp fuel;
    // fl_valid_elim gives: Seq.mem cur_fp (objects 0UL g)
    let obj : obj_addr = cur_fp in
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let next_fp =
      if U64.v hd + 16 <= heap_size then read_word g obj
      else 0UL
    in
    if block_wz >= wz then
      // Found: obj_out = cur_fp which is in objects 0UL g
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
  // First: show obj_out was in objects 0UL g
  alloc_search_obj_in_objects_pre g fp 0UL fp wz fuel;
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
#push-options "--z3rlimit 300 --fuel 1 --ifuel 1 --split_queries always"
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

/// After alloc_search finds a block and returns obj_out, the output heap
/// has a write_word to prev_fp (if non-zero). This doesn't affect hd_address(obj),
/// provided prev_fp and hd_address(obj) are separated (which holds in alloc_search
/// because prev_fp is a different free-list node than cur_fp/obj).
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
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
  // prev_fp and hd are distinct hp_addrs, both 8-aligned.
  // read_write_different needs |prev_fp - hd| >= 8.
  // Since prev_fp >= 8 (mword), hd = obj - 8 >= 0, both are multiples of 8.
  // They're unequal, so they differ by at least 8 (next/prev multiple of 8).
  assert (U64.v (prev_fp <: hp_addr) % 8 == 0);
  assert (U64.v hd % 8 == 0);
  assert (U64.v (prev_fp <: hp_addr) <> U64.v hd);
  // For two distinct multiples of 8, separation by at least 8:
  // We use the fact that both are valid hp_addrs (< heap_size, >= 0, aligned)
  // and unequal => differ by >= 8
  let p = U64.v (prev_fp <: hp_addr) in
  let h = U64.v hd in
  FStar.Math.Lemmas.lemma_div_exact p 8;
  FStar.Math.Lemmas.lemma_div_exact h 8;
  let kp = p / 8 in
  let kh = h / 8 in
  // p = kp * 8, h = kh * 8, kp <> kh
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
#push-options "--z3rlimit 200 --fuel 4 --ifuel 1 --split_queries always"
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
                 Seq.mem prev_fp (objects 0UL g) /\
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
  else if cur_fp = 0UL then ()
  else if U64.v cur_fp < U64.v mword then ()
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
          objects_separated 0UL g prev_obj obj;
          // obj > prev_fp + wosize(prev)*8 >= prev_fp + 8
          // hd(obj) = obj - 8 > prev_fp
          assert (prev_fp <> hd_address obj)
        end else begin
          objects_separated 0UL g obj prev_obj;
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

#push-options "--z3rlimit 200 --fuel 4"
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
