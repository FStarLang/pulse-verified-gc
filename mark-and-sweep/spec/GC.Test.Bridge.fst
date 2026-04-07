(*
   GC.Test.Bridge — Bridge lemmas connecting the allocator to the GC.

   Proves that init_heap_spec on a zeroed heap produces a well-formed,
   GC-ready heap configuration: valid objects list, well_formed_heap,
   valid free list, and no black/gray objects.
*)
module GC.Test.Bridge

open FStar.Seq
open FStar.Mul
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
open GC.Spec.Allocator.Lemmas
open GC.Spec.Mark
open GC.Spec.SweepInv
open GC.Spec.HeapModel
open GC.Spec.HeapGraph
open GC.Spec.Graph

module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Seq = FStar.Seq
module Header = GC.Lib.Header

/// =========================================================================
/// Lemma 1: zeroed_heap_read_word
/// =========================================================================

#push-options "--z3rlimit 50"
let zeroed_heap_read_word (addr: hp_addr)
  : Lemma (read_word (Seq.create heap_size 0uy) addr == 0UL)
  = let g : heap = Seq.create heap_size 0uy in
    read_word_spec g addr;
    // Explicitly trigger Seq.create axiom at each byte offset
    let v = U64.v addr in
    assert (Seq.index g v == 0uy);
    assert (Seq.index g (v + 1) == 0uy);
    assert (Seq.index g (v + 2) == 0uy);
    assert (Seq.index g (v + 3) == 0uy);
    assert (Seq.index g (v + 4) == 0uy);
    assert (Seq.index g (v + 5) == 0uy);
    assert (Seq.index g (v + 6) == 0uy);
    assert (Seq.index g (v + 7) == 0uy);
    assert_norm (combine_bytes 0uy 0uy 0uy 0uy 0uy 0uy 0uy 0uy == 0UL)
#pop-options

/// =========================================================================
/// Helper: Arithmetic characterization of make_header value
/// =========================================================================

#push-options "--z3rlimit 50"
private let make_header_value_bridge (wz: U64.t{U64.v wz < pow2 54})
                                     (c: U64.t{U64.v c < 4})
                                     (t: U64.t{U64.v t < 256})
  : Lemma (U64.v (make_header wz c t) == U64.v wz * 1024 + U64.v c * 256 + U64.v t)
  = let open FStar.UInt in
    let w = U64.v wz in
    let cv = U64.v c in
    let tv = U64.v t in
    shift_left_value_lemma #64 w 10;
    assert_norm (pow2 10 = 1024);
    assert_norm (pow2 54 * 1024 = pow2 64);
    assert (w * 1024 < pow2 64);
    FStar.Math.Lemmas.small_mod (w * 1024) (pow2 64);
    shift_left_value_lemma #64 cv 8;
    assert_norm (pow2 8 = 256);
    assert (cv * 256 < pow2 64);
    FStar.Math.Lemmas.small_mod (cv * 256) (pow2 64);
    logor_disjoint #64 (shift_left #64 cv 8) tv 8;
    assert (logor #64 (shift_left #64 cv 8) tv == cv * 256 + tv);
    logor_disjoint #64 (shift_left #64 w 10) (cv * 256 + tv) 10;
    assert (logor #64 (shift_left #64 w 10) (cv * 256 + tv) == w * 1024 + cv * 256 + tv)
#pop-options

#push-options "--z3rlimit 400"
private let make_header_getColor_bridge (wz: U64.t{U64.v wz < pow2 54})
                                        (c: U64.t{U64.v c < 4})
                                        (t: U64.t{U64.v t < 256})
  : Lemma (Header.get_color (U64.v (make_header wz c t)) == U64.v c)
  = let hdr = make_header wz c t in
    make_header_value_bridge wz c t;
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

#push-options "--z3rlimit 50"
private let make_header_color_blue (wz: U64.t{U64.v wz < pow2 54})
  : Lemma (getColor (make_header wz blue_bits 0UL) == Header.Blue)
  = let hdr = make_header wz blue_bits 0UL in
    getColor_raw hdr;
    make_header_getColor_bridge wz blue_bits 0UL;
    assert (Header.get_color (U64.v hdr) == 2)
#pop-options

/// =========================================================================
/// Helper: wz bounds from heap_size
/// =========================================================================

private let wz_bounds ()
  : Lemma (requires heap_size >= 16)
          (ensures (let total_words = heap_size / U64.v mword in
                    let wz = total_words - 1 in
                    total_words >= 2 /\
                    wz >= 1 /\
                    wz < pow2 54 /\
                    wz < pow2 64 /\
                    total_words * 8 == heap_size /\
                    (wz + 1) * 8 == heap_size))
  = let total_words = heap_size / U64.v mword in
    FStar.Math.Lemmas.lemma_div_exact heap_size 8;
    FStar.Math.Lemmas.lemma_div_le heap_size (pow2 57) 8;
    assert_norm (pow2 57 / 8 = pow2 54);
    assert (total_words <= pow2 54);
    FStar.Math.Lemmas.pow2_lt_compat 64 54

/// =========================================================================
/// Helpers: Reading after init_heap_spec
/// =========================================================================

#push-options "--z3rlimit 50"
private let init_header_at_zero (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in
                    let total_words = heap_size / U64.v mword in
                    let wz = total_words - 1 in
                    let hdr = make_header (U64.uint_to_t wz) blue_bits 0UL in
                    read_word g' zero_addr == hdr))
  = wz_bounds ();
    let total_words = heap_size / U64.v mword in
    let wz = total_words - 1 in
    let hdr = make_header (U64.uint_to_t wz) blue_bits 0UL in
    let g1 = write_word g zero_addr hdr in
    assert (U64.v mword < heap_size);
    let g2 = write_word g1 (mword <: hp_addr) 0UL in
    read_write_different g1 mword zero_addr 0UL;
    read_write_same g zero_addr hdr
#pop-options

#push-options "--z3rlimit 50"
private let init_link_at_mword (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in
                    read_word g' mword == 0UL))
  = wz_bounds ();
    let total_words = heap_size / U64.v mword in
    let wz = total_words - 1 in
    let hdr = make_header (U64.uint_to_t wz) blue_bits 0UL in
    let g1 = write_word g zero_addr hdr in
    assert (U64.v mword < heap_size);
    let g2 = write_word g1 (mword <: hp_addr) 0UL in
    read_write_same g1 mword 0UL
#pop-options

#push-options "--z3rlimit 30"
private let init_wosize_lemma (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in
                    let total_words = heap_size / U64.v mword in
                    let wz = total_words - 1 in
                    U64.v (getWosize (read_word g' zero_addr)) == wz))
  = wz_bounds ();
    init_header_at_zero g;
    let total_words = heap_size / U64.v mword in
    let wz = total_words - 1 in
    make_header_getWosize (U64.uint_to_t wz) blue_bits 0UL
#pop-options

/// =========================================================================
/// Lemma 2: init_objects_eq
/// =========================================================================

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let init_objects_eq (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', fp) = init_heap_spec g in
                    fp == mword /\
                    objects 0UL g' == Seq.cons (mword <: obj_addr) Seq.empty))
  = let (g', fp) = init_heap_spec g in
    assert (fp == mword);
    wz_bounds ();
    init_wosize_lemma g;
    let total_words = heap_size / U64.v mword in
    let wz = total_words - 1 in
    assert (U64.v (getWosize (read_word g' zero_addr)) == wz);
    f_address_spec zero_addr;
    assert (U64.v (f_address zero_addr) == 8);
    let next_start_nat = (wz + 1) * 8 in
    assert (next_start_nat == heap_size);
    assert (next_start_nat >= heap_size)
#pop-options

#push-options "--z3rlimit 10"
private let init_mem_mword (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in
                    Seq.mem mword (objects 0UL g')))
  = init_objects_eq g;
    let (g', _) = init_heap_spec g in
    Seq.lemma_mem_snoc Seq.empty (mword <: hp_addr)
#pop-options

/// =========================================================================
/// Helper: All field reads after init give 0UL
/// =========================================================================

#push-options "--z3rlimit 50"
private let init_field_read (g: heap) (addr: hp_addr)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16 /\
                    U64.v addr >= 8)
          (ensures (let (g', _) = init_heap_spec g in
                    read_word g' addr == 0UL))
  = wz_bounds ();
    let total_words = heap_size / U64.v mword in
    let wz = total_words - 1 in
    let hdr = make_header (U64.uint_to_t wz) blue_bits 0UL in
    let g1 = write_word g zero_addr hdr in
    assert (U64.v mword < heap_size);
    let g2 = write_word g1 (mword <: hp_addr) 0UL in
    if U64.v addr = 8 then
      read_write_same g1 mword 0UL
    else begin
      read_write_different g1 mword addr 0UL;
      read_write_different g zero_addr addr hdr;
      zeroed_heap_read_word addr
    end
#pop-options

/// =========================================================================
/// Helper: no pointer fields in the init heap
/// =========================================================================

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
private let rec no_pointer_fields_no_efptu
  (g: heap) (h: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (target: obj_addr)
  : Lemma
    (requires
      (forall (idx: nat{idx < U64.v wz}).
        (let far = U64.add_mod h (U64.mul_mod (U64.uint_to_t idx) mword) in
         U64.v far < heap_size /\ U64.v far % 8 == 0 ==>
         read_word g (far <: hp_addr) == 0UL)))
    (ensures GC.Spec.Fields.exists_field_pointing_to_unchecked g h wz target = false)
    (decreases U64.v wz)
  = if wz = 0UL then ()
    else begin
      let idx = U64.sub wz 1UL in
      let far = U64.add_mod h (U64.mul_mod idx mword) in
      if U64.v far >= heap_size || U64.v far % 8 <> 0 then ()
      else
        no_pointer_fields_no_efptu g h idx target
    end
#pop-options

#push-options "--z3rlimit 50"
private let init_all_fields_zero (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in
                    let total_words = heap_size / U64.v mword in
                    let wz = total_words - 1 in
                    let h : obj_addr = mword in
                    forall (idx: nat{idx < wz}).
                      (let far = U64.add_mod h (U64.mul_mod (U64.uint_to_t idx) mword) in
                       U64.v far < heap_size /\ U64.v far % 8 == 0 /\
                       read_word g' (far <: hp_addr) == 0UL)))
  = wz_bounds ();
    let (g', _) = init_heap_spec g in
    let total_words = heap_size / U64.v mword in
    let wz = total_words - 1 in
    let h : obj_addr = mword in
    let aux (idx: nat{idx < wz}) : Lemma
      (let far = U64.add_mod h (U64.mul_mod (U64.uint_to_t idx) mword) in
       U64.v far < heap_size /\ U64.v far % 8 == 0 /\
       read_word g' (far <: hp_addr) == 0UL)
    = assert (idx < pow2 54);
      FStar.Math.Lemmas.pow2_lt_compat 64 54;
      FStar.Math.Lemmas.small_mod (idx * 8) (pow2 64);
      assert (U64.v (U64.mul_mod (U64.uint_to_t idx) mword) == idx * 8);
      assert (8 + idx * 8 < pow2 64);
      FStar.Math.Lemmas.small_mod (8 + idx * 8) (pow2 64);
      assert (U64.v (U64.add_mod h (U64.mul_mod (U64.uint_to_t idx) mword)) == 8 + idx * 8);
      let far_nat = 8 + idx * 8 in
      assert (far_nat < heap_size);
      FStar.Math.Lemmas.lemma_mod_plus_distr_l 8 (idx * 8) 8;
      assert (far_nat % 8 == 0);
      assert (far_nat >= 8);
      let far : hp_addr = U64.uint_to_t far_nat in
      init_field_read g far
    in
    Classical.forall_intro aux
#pop-options

/// =========================================================================
/// Lemma 3: init_wf — well_formed_heap after init
/// =========================================================================

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let init_wf (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in well_formed_heap g'))
  = let (g', _) = init_heap_spec g in
    wz_bounds ();
    init_objects_eq g;
    init_wosize_lemma g;
    init_header_at_zero g;
    let total_words = heap_size / U64.v mword in
    let wz = total_words - 1 in
    let objs = objects 0UL g' in
    assert (objs == Seq.cons (mword <: obj_addr) Seq.empty);
    hd_address_spec (mword <: obj_addr);
    wosize_of_object_spec (mword <: obj_addr) g';
    assert (U64.v (wosize_of_object mword g') == wz);

    // Part 2: no pointer fields
    init_all_fields_zero g;
    let wz_val : U64.t = U64.uint_to_t wz in
    let efptu_false (target: obj_addr) : Lemma
      (GC.Spec.Fields.exists_field_pointing_to_unchecked g' mword wz_val target = false)
    = no_pointer_fields_no_efptu g' mword wz_val target
    in
    Classical.forall_intro efptu_false;

    // Part 3/4: tag = 0 ≠ infix_tag
    make_header_getTag (U64.uint_to_t wz) blue_bits 0UL;
    tag_of_object_spec (mword <: obj_addr) g';
    infix_tag_val ();
    is_infix_spec (mword <: obj_addr) g';
    assert (~(is_infix mword g'));

    infix_wf_intro g' objs (fun h ->
      assert (h == mword);
      is_infix_spec h g';
      tag_of_object_spec h g'
    );

    reveal_opaque (`%well_formed_heap) well_formed_heap
#pop-options

/// =========================================================================
/// Lemma 4: init_fl_valid
/// =========================================================================

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let init_fl_valid (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', fp) = init_heap_spec g in
                    fl_valid g' fp (heap_size / U64.v mword)))
  = let (g', fp) = init_heap_spec g in
    assert (fp == mword);
    let fuel = heap_size / U64.v mword in
    assert (fuel >= 2);
    init_mem_mword g;
    init_wosize_lemma g;
    wosize_of_object_spec (mword <: obj_addr) g';
    hd_address_spec (mword <: obj_addr);
    let total_words = heap_size / U64.v mword in
    let wz = total_words - 1 in
    assert (U64.v (wosize_of_object mword g') == wz);
    assert (wz >= 1);
    init_link_at_mword g;
    assert (read_word g' mword == 0UL);
    assert (U64.v (hd_address (mword <: obj_addr)) == 0);
    assert (0 + 16 <= heap_size);
    assert (read_word g' (mword <: obj_addr) <> mword);
    // The next pointer is 0UL: fl_valid g' 0UL (fuel-1) holds by fl_valid_null
    fl_valid_null g' (fuel - 1);
    // Now establish fl_valid for the head node via fl_valid_step
    fl_valid_step g' mword fuel
#pop-options

/// =========================================================================
/// Lemma 5: init_no_black
/// =========================================================================

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let init_no_black (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in no_black_objects g'))
  = let (g', _) = init_heap_spec g in
    wz_bounds ();
    init_objects_eq g;
    init_header_at_zero g;
    let total_words = heap_size / U64.v mword in
    let wz = total_words - 1 in
    make_header_color_blue (U64.uint_to_t wz);
    color_of_object_spec (mword <: obj_addr) g';
    hd_address_spec (mword <: obj_addr);
    is_black_iff (mword <: obj_addr) g';
    let aux (obj: obj_addr)
      : Lemma (requires Seq.mem obj (objects 0UL g'))
              (ensures ~(is_black obj g'))
      = Seq.lemma_mem_snoc Seq.empty (mword <: hp_addr);
        assert (obj == mword);
        is_black_iff obj g'
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

/// =========================================================================
/// Lemma 6: init_no_gray
/// =========================================================================

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let init_no_gray (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in no_gray_objects g'))
  = let (g', _) = init_heap_spec g in
    wz_bounds ();
    init_objects_eq g;
    init_header_at_zero g;
    let total_words = heap_size / U64.v mword in
    let wz = total_words - 1 in
    make_header_color_blue (U64.uint_to_t wz);
    color_of_object_spec (mword <: obj_addr) g';
    hd_address_spec (mword <: obj_addr);
    is_gray_iff (mword <: obj_addr) g';
    let aux (obj: obj_addr)
      : Lemma (requires Seq.mem obj (objects 0UL g'))
              (ensures ~(is_gray obj g'))
      = Seq.lemma_mem_snoc Seq.empty (mword <: hp_addr);
        assert (obj == mword);
        is_gray_iff obj g'
    in
    Classical.forall_intro (Classical.move_requires aux);
    no_gray_intro g'
#pop-options

/// =========================================================================
/// Lemma 7: init_no_pointer_to_blue
/// =========================================================================

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let init_no_pointer_to_blue (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in no_pointer_to_blue g'))
  = let (g', _) = init_heap_spec g in
    wz_bounds ();
    init_objects_eq g;
    init_wosize_lemma g;
    init_all_fields_zero g;
    let total_words = heap_size / U64.v mword in
    let wz = total_words - 1 in
    let aux (src dst: obj_addr) : Lemma
      (Seq.mem src (objects 0UL g') /\ points_to g' src dst ==> ~(is_blue dst g'))
    = if Seq.mem src (objects 0UL g') && points_to g' src dst then begin
        Seq.lemma_mem_snoc Seq.empty (mword <: hp_addr);
        assert (src == mword);
        wosize_of_object_spec src g';
        hd_address_spec src;
        wosize_of_object_bound src g';
        no_pointer_fields_no_efptu g' src (wosize_of_object src g') dst
      end
    in
    Classical.forall_intro_2 aux
#pop-options

/// =========================================================================
/// Lemma 8: objects nonempty after init
/// =========================================================================

#push-options "--z3rlimit 10"
let init_objects_nonempty (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in
                    Seq.length (objects 0UL g') > 0))
  = init_objects_eq g
#pop-options

/// =========================================================================
/// Lemma 9: graph_wf after init (no edges → vacuously well-formed)
/// =========================================================================

/// Helper: all fields of the init heap's single object are 0UL (not pointer fields)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
private let rec init_get_pointer_fields_aux_empty
  (g: heap) (i: U64.t{U64.v i >= 1}) (ws: U64.t)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16 /\
                    (let (g', _) = init_heap_spec g in
                     U64.v i <= U64.v ws + 1 /\
                     (forall (j: U64.t{U64.v j >= U64.v i /\ U64.v j <= U64.v ws}).
                       get_field g' mword j == 0UL)))
          (ensures (let (g', _) = init_heap_spec g in
                    get_pointer_fields_aux g' mword i ws == Seq.empty))
          (decreases (U64.v ws - U64.v i + 1))
  = let (g', _) = init_heap_spec g in
    if U64.v i > U64.v ws then ()
    else begin
      assert (get_field g' mword i == 0UL);
      assert (~(is_pointer_field (get_field g' mword i)));
      if U64.v i < U64.v ws then
        init_get_pointer_fields_aux_empty g (U64.add i 1UL) ws
      else ()
    end
#pop-options

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let init_graph_wf (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in
                    graph_wf (create_graph g')))
  = let (g', _) = init_heap_spec g in
    wz_bounds ();
    init_objects_eq g;
    init_wosize_lemma g;
    init_header_at_zero g;
    init_all_fields_zero g;
    wosize_of_object_spec (mword <: obj_addr) g';
    hd_address_spec (mword <: obj_addr);
    let total_words = heap_size / U64.v mword in
    let wz = total_words - 1 in
    let ws = wosize_of_object (mword <: obj_addr) g' in
    assert (ws == U64.uint_to_t wz);
    // Show object fits in heap
    object_fits_in_heap_intro mword g';
    // Show not no_scan (tag = 0, no_scan_tag = 251)
    make_header_getTag (U64.uint_to_t wz) blue_bits 0UL;
    tag_of_object_spec (mword <: obj_addr) g';
    no_scan_tag_val ();
    is_no_scan_spec (mword <: obj_addr) g';
    assert (tag_of_object mword g' == 0UL);
    assert (~(is_no_scan mword g'));
    // Show all get_field values are 0UL
    let field_zero (j: U64.t{U64.v j >= 1 /\ U64.v j <= U64.v ws})
      : Lemma (get_field g' mword j == 0UL)
      = let hd = hd_address (mword <: obj_addr) in
        let fa = U64.add hd (U64.mul mword j) in
        assert (U64.v fa == U64.v j * 8);
        assert (U64.v fa >= 8);
        assert (U64.v hd + U64.v mword * U64.v j + U64.v mword <= heap_size);
        init_field_read g (fa <: hp_addr)
    in
    Classical.forall_intro (Classical.move_requires field_zero);
    // get_pointer_fields returns empty
    init_get_pointer_fields_aux_empty g 1UL ws;
    assert (get_pointer_fields g' mword == Seq.empty);
    // graph edges empty → graph_wf vacuously true
    assert (object_edges g' mword == make_edges mword Seq.empty);
    ()
#pop-options

/// =========================================================================
/// Lemma 11: init_dense — heap_objects_dense after init_heap_spec
/// =========================================================================
/// With the weakened heap_objects_dense (guarded by membership in objects 0UL g),
/// init density is trivially satisfied: the only position whose f_address is in
/// objects 0UL g' = [8] is start=0, and for that position the next position is
/// at heap_size (out of bounds), making the implication vacuously true.

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let init_dense (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in heap_objects_dense g'))
  = let (g', fp) = init_heap_spec g in
    init_objects_eq g;
    wz_bounds ();
    init_header_at_zero g;
    // objects 0UL g' == [mword], a singleton
    let objs = objects 0UL g' in
    // Characterize membership: mem y objs ↔ y = mword
    Seq.lemma_mem_snoc (Seq.empty #obj_addr) (mword <: obj_addr);
    assert (Seq.equal (Seq.snoc (Seq.empty #obj_addr) (mword <: obj_addr))
                      (Seq.cons (mword <: obj_addr) (Seq.empty #obj_addr)));
    // Key header facts
    let total_words = heap_size / U64.v mword in
    let wz_nat = total_words - 1 in
    let wz_u64 = U64.uint_to_t wz_nat in
    let hdr = make_header wz_u64 blue_bits 0UL in
    make_header_getWosize wz_u64 blue_bits 0UL;
    assert (getWosize hdr == wz_u64);
    assert (read_word g' zero_addr == hdr);
    assert ((wz_nat + 1) * 8 == heap_size);
    let aux (start: hp_addr) : Lemma
      (U64.v start + 8 < heap_size ==>
       Seq.mem (f_address start) (objects 0UL g') ==>
       Seq.length (objects start g') > 0 ==>
       (let wz = getWosize (read_word g' start) in
        let next = U64.v start + FStar.Mul.((U64.v wz + 1) * 8) in
        next + 8 < heap_size ==>
        Seq.length (objects (U64.uint_to_t next) g') > 0 /\
        Seq.mem (f_address (U64.uint_to_t next)) (objects 0UL g')))
    = if U64.v start + 8 < heap_size && Seq.mem (f_address start) (objects 0UL g') then begin
        // f_address start = start + 8 ∈ [mword] means start = 0
        f_address_spec start;
        assert (f_address start == (mword <: obj_addr));
        assert (U64.v start == 0);
        // At start = 0: read_word g' 0 == hdr, getWosize hdr == wz_u64
        assert (start == zero_addr);
        assert (getWosize (read_word g' start) == wz_u64);
        // next = 0 + (wz+1)*8 = heap_size
        let next = U64.v start + FStar.Mul.((U64.v wz_u64 + 1) * 8) in
        assert (next == heap_size);
        // next + 8 >= heap_size → implication is vacuously true
        assert (~ (next + 8 < heap_size))
      end
    in
    FStar.Classical.forall_intro aux;
    heap_objects_dense_intro g'
#pop-options

/// =========================================================================
/// Lemma 12: init_fl_chain_terminates
/// =========================================================================

/// The initial free list is mword → 0UL, which terminates in 1 step.
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let init_fl_chain_terminates (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', fp) = init_heap_spec g in
                    fl_chain_terminates g' fp (heap_size / U64.v mword)))
  = let (g', fp) = init_heap_spec g in
    assert (fp == mword);
    let fuel = heap_size / U64.v mword in
    assert (fuel >= 2);
    hd_address_spec (mword <: obj_addr);
    assert (U64.v (hd_address (mword <: obj_addr)) == 0);
    assert (0 + 16 <= heap_size);
    init_link_at_mword g;
    assert (read_word g' mword == 0UL);
    // 0UL is terminal
    fl_chain_terminates_terminal g' 0UL (fuel - 1);
    // Step: mword → 0UL terminates
    fl_chain_terminates_step g' mword fuel
#pop-options
