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
open GC.Spec.Sweep

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

#push-options "--z3rlimit 50"
private let make_header_color_white (wz: U64.t{U64.v wz < pow2 54})
  : Lemma (getColor (make_header wz white_bits 0UL) == Header.White)
  = let hdr = make_header wz white_bits 0UL in
    getColor_raw hdr;
    make_header_getColor_bridge wz white_bits 0UL;
    assert (Header.get_color (U64.v hdr) == 0)
#pop-options

/// =========================================================================
/// Helper: wz bounds from heap_size
/// =========================================================================

private let wz_bounds ()
  : Lemma (ensures (let total_words = heap_size / U64.v mword in
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

#push-options "--z3rlimit 100 --fuel 4 --ifuel 2"
private let init_header_at_zero (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy)
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
    assert (U64.v mword == 8);
    assert (heap_size >= 16);
    assert (U64.v mword < heap_size);
    assert (U64.v mword % U64.v mword == 0);
    let m : hp_addr = mword in
    let g2 = write_word g1 m 0UL in
    read_write_different g1 m zero_addr 0UL;
    read_write_same g zero_addr hdr
#pop-options

#push-options "--z3rlimit 50"
private let init_link_at_mword (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy)
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
  : Lemma (requires g == Seq.create heap_size 0uy)
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
  : Lemma (requires g == Seq.create heap_size 0uy)
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
  : Lemma (requires g == Seq.create heap_size 0uy)
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
  : Lemma (requires g == Seq.create heap_size 0uy /\
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
  : Lemma (requires g == Seq.create heap_size 0uy)
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
  : Lemma (requires g == Seq.create heap_size 0uy)
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
  : Lemma (requires g == Seq.create heap_size 0uy)
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
  : Lemma (requires g == Seq.create heap_size 0uy)
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
  : Lemma (requires g == Seq.create heap_size 0uy)
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
  : Lemma (requires g == Seq.create heap_size 0uy)
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
  : Lemma (requires g == Seq.create heap_size 0uy)
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
  : Lemma (requires g == Seq.create heap_size 0uy /\
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
  : Lemma (requires g == Seq.create heap_size 0uy)
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
  : Lemma (requires g == Seq.create heap_size 0uy)
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
  : Lemma (requires g == Seq.create heap_size 0uy)
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

/// =========================================================================
/// Sweep → fl_valid bridge lemmas (Lemmas 13–19)
/// =========================================================================

/// =========================================================================
/// Lemma 13: mark_empty_identity
/// =========================================================================

/// mark with an empty stack is the identity on the heap.
let mark_empty_identity (g: heap)
  : Lemma (mark g Seq.empty == g)
  = mark_aux_empty g Seq.empty (heap_size / U64.v mword)

/// =========================================================================
/// Lemma 14: chain_not_visits helpers
/// =========================================================================

/// Monotonicity: more fuel doesn't find new visits if the shorter search didn't.
let rec chain_not_visits_weaken (g: heap) (fp: U64.t) (skip: obj_addr)
  (fuel_strong fuel_weak: nat)
  : Lemma (requires fuel_weak <= fuel_strong /\
                    chain_not_visits g fp skip fuel_strong)
          (ensures chain_not_visits g fp skip fuel_weak)
          (decreases fuel_weak)
  = if fuel_weak = 0 then ()
    else if fp = 0UL || U64.v fp < U64.v mword || U64.v fp >= heap_size
         || U64.v fp % U64.v mword <> 0 then ()
    else if fp = skip then ()
    else
      let hd = hd_address (fp <: obj_addr) in
      if U64.v hd + 16 > heap_size then ()
      else chain_not_visits_weaken g (read_word g (fp <: obj_addr)) skip
             (fuel_strong - 1) (fuel_weak - 1)

/// =========================================================================
/// Lemma 15: fl_valid_transfer_skip — fl_valid frame with one excluded object
/// =========================================================================

/// fl_valid transfers when a single object `skip` is excluded from preservation,
/// provided the chain doesn't visit `skip`.
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec fl_valid_transfer_skip (g g': heap) (fp: U64.t) (skip: obj_addr) (fuel: nat)
  : Lemma
    (requires fl_valid g fp fuel /\
              chain_not_visits g fp skip fuel /\
              objects 0UL g' == objects 0UL g /\
              (forall (a: obj_addr).
                 (Seq.mem a (objects 0UL g) /\ a <> skip) ==>
                 (Seq.mem a (objects 0UL g') /\
                  (U64.v (wosize_of_object a g) >= 1 ==>
                    U64.v (wosize_of_object a g') >= 1) /\
                  (U64.v (wosize_of_object a g) >= 1 /\
                   U64.v (hd_address a) + 16 <= heap_size ==>
                    read_word g' a == read_word g a))))
    (ensures fl_valid g' fp fuel)
    (decreases fuel)
  = if fuel = 0 then fl_valid_zero g' fp
    else if fp = 0UL then fl_valid_terminal g' fp fuel
    else if U64.v fp < U64.v mword then fl_valid_terminal g' fp fuel
    else if U64.v fp >= heap_size then fl_valid_terminal g' fp fuel
    else if U64.v fp % U64.v mword <> 0 then fl_valid_terminal g' fp fuel
    else begin
      assert (fp <> skip);  // from chain_not_visits
      fl_valid_elim g fp fuel;
      let obj_fp : obj_addr = fp in
      let hd_fp = hd_address obj_fp in
      assert (Seq.mem fp (objects 0UL g'));
      assert (U64.v (wosize_of_object obj_fp g') >= 1);
      if U64.v hd_fp + 16 <= heap_size then begin
        assert (read_word g' obj_fp == read_word g obj_fp);
        assert (read_word g obj_fp <> fp);
        assert (read_word g' obj_fp <> fp);
        let link = read_word g obj_fp in
        fl_valid_transfer_skip g g' link skip (fuel - 1);
        assert (fl_valid g' (read_word g' obj_fp) (fuel - 1))
      end;
      fl_valid_step g' fp fuel
    end
#pop-options

/// =========================================================================
/// Lemma 16: chain node ≠ hd_address(obj) when wosize ≥ 1
/// =========================================================================

/// Key separation lemma: a chain node with wosize ≥ 1 cannot be at hd_address(obj)
/// for any other object obj. This is because adjacent objects with that relationship
/// would require wosize = 0.
let chain_node_ne_hd_address (g: heap) (node obj: obj_addr)
  : Lemma (requires Seq.mem node (objects 0UL g) /\ Seq.mem obj (objects 0UL g) /\
                    U64.v (wosize_of_object node g) >= 1 /\ node <> obj)
          (ensures U64.v node <> U64.v (hd_address obj))
  = hd_address_spec obj;
    if U64.v node < U64.v obj then begin
      objects_separated 0UL g node obj;
      // obj > node + wosize(node)*8 ≥ node + 8
      // hd_address(obj) = obj - 8 ≥ node + 1 (strict)
      // But actually obj > node + wosize*8 and hd_address = obj - 8
      // node + 8 ≤ obj (since node < obj and both 8-aligned)
      // If node = hd_address(obj) = obj - 8: obj = node + 8
      // Then obj > node + wosize*8 → node + 8 > node + wosize*8 → 8 > wosize*8 → wosize = 0
      // Contradiction with wosize ≥ 1
      assert (U64.v obj > U64.v node + U64.v (wosize_of_object node g) * 8)
    end else begin
      objects_separated 0UL g obj node;
      // node > obj + wosize(obj)*8
      // hd_address(obj) = obj - 8 < obj ≤ node
      // If node = obj - 8: node < obj, contradicts node > obj
      assert (U64.v node > U64.v obj + U64.v (wosize_of_object obj g) * 8)
    end

/// =========================================================================
/// Lemma 17: sweep_object preserves fl_valid of the existing chain
/// =========================================================================

/// sweep_object on `obj` preserves fl_valid of any chain that doesn't visit `obj`.
/// Uses chain_node_ne_hd_address to show writes don't affect chain nodes.
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let sweep_object_preserves_fl_valid_chain
  (g: heap) (obj: obj_addr) (fp_chain: U64.t) (fp_arg: U64.t) (fuel: nat)
  : Lemma
    (requires well_formed_heap g /\
              Seq.mem obj (objects 0UL g) /\
              fp_in_heap fp_arg g /\
              fl_valid g fp_chain fuel /\
              chain_not_visits g fp_chain obj fuel)
    (ensures fl_valid (fst (sweep_object g obj fp_arg)) fp_chain fuel)
  = let g' = fst (sweep_object g obj fp_arg) in
    sweep_object_preserves_objects g obj fp_arg;
    let aux (a: obj_addr)
      : Lemma (requires Seq.mem a (objects 0UL g) /\ a <> obj)
              (ensures Seq.mem a (objects 0UL g') /\
                       (U64.v (wosize_of_object a g) >= 1 ==>
                         U64.v (wosize_of_object a g') >= 1) /\
                       (U64.v (wosize_of_object a g) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g' a == read_word g a))
      = assert (Seq.mem a (objects 0UL g'));
        sweep_object_preserves_other_header g obj fp_arg a;
        if U64.v (wosize_of_object a g) >= 1 &&
           U64.v (hd_address a) + 16 <= heap_size then
          sweep_object_preserves_other_body_read g obj fp_arg a (a <: hp_addr)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    fl_valid_transfer_skip g g' fp_chain obj fuel
#pop-options

/// =========================================================================
/// Lemma 18: chain_not_visits preserved by sweep_object
/// =========================================================================

/// chain_not_visits transfers across sweep_object when the chain doesn't visit obj.
/// Key insight: chain nodes have wosize ≥ 1 (from fl_valid), so chain nodes ≠ hd_address(obj),
/// meaning sweep_object's writes don't affect chain nodes' links.
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec chain_not_visits_preserved_by_sweep_object
  (g: heap) (obj: obj_addr) (fp_arg: U64.t) (fp_chain: U64.t) (skip: obj_addr) (fuel: nat)
  : Lemma
    (requires well_formed_heap g /\
              Seq.mem obj (objects 0UL g) /\
              fp_in_heap fp_arg g /\
              fl_valid g fp_chain fuel /\
              chain_not_visits g fp_chain obj fuel /\
              chain_not_visits g fp_chain skip fuel)
    (ensures chain_not_visits (fst (sweep_object g obj fp_arg)) fp_chain skip fuel)
    (decreases fuel)
  = if fuel = 0 then ()
    else if fp_chain = 0UL || U64.v fp_chain < U64.v mword || U64.v fp_chain >= heap_size
         || U64.v fp_chain % U64.v mword <> 0 then ()
    else begin
      assert (fp_chain <> obj);   // from chain_not_visits ... obj
      assert (fp_chain <> skip);  // from chain_not_visits ... skip
      let hd_c = hd_address (fp_chain <: obj_addr) in
      if U64.v hd_c + 16 > heap_size then ()
      else begin
        let g' = fst (sweep_object g obj fp_arg) in
        // Eliminate fl_valid to get wosize ≥ 1
        fl_valid_elim g fp_chain fuel;
        // fp_chain ≠ hd_address(obj) (from wosize ≥ 1 + objects_separated)
        chain_node_ne_hd_address g (fp_chain <: obj_addr) obj;
        // read_word preserved at fp_chain
        sweep_object_preserves_other_body_read g obj fp_arg (fp_chain <: obj_addr) (fp_chain <: hp_addr);
        assert (read_word g' (fp_chain <: obj_addr) == read_word g (fp_chain <: obj_addr));
        // Recurse on the link
        chain_not_visits_preserved_by_sweep_object g obj fp_arg
          (read_word g (fp_chain <: obj_addr)) skip (fuel - 1)
      end
    end
#pop-options


/// =========================================================================
/// Lemma 19: sweep_aux_produces_fl_valid — the main inductive theorem
/// =========================================================================

let big_fuel : nat = heap_size / U64.v mword

/// Helper: is_vertex_set head is not in tail.
/// Follows directly from the definition of is_vertex_set.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let vertex_set_head_not_in_tail (objs: seq obj_addr)
  : Lemma (requires Seq.length objs > 0 /\
                    is_vertex_set (coerce_to_vertex_list objs))
          (ensures ~(Seq.mem (Seq.head objs) (Seq.tail objs)))
  = let hd = Seq.head objs in
    let tl = Seq.tail objs in
    coerce_cons_lemma hd tl;
    assert (Seq.equal (Seq.cons hd tl) objs);
    let verts = coerce_to_vertex_list objs in
    assert (is_vertex_set verts);
    assert (Seq.length verts > 0);
    // is_vertex_set unfolds: not (mem (head verts) (tail verts)) && ...
    // With fuel 2, F* can unfold is_vertex_set once
    assert (not (Seq.mem (Seq.head verts) (Seq.tail verts)));
    // head/tail of coerce match head/tail of objs
    assert (Seq.head verts == hd);
    assert (Seq.equal (Seq.tail verts) (coerce_to_vertex_list tl));
    assert (~(Seq.mem hd (coerce_to_vertex_list tl)));
    coerce_mem_lemma tl hd
#pop-options

/// Helper: is_vertex_set of tail.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let head_in_vertex_set_tail (objs: seq obj_addr)
  : Lemma (requires Seq.length objs > 0 /\
                    is_vertex_set (coerce_to_vertex_list objs))
          (ensures is_vertex_set (coerce_to_vertex_list (Seq.tail objs)))
  = let hd = Seq.head objs in
    let tl = Seq.tail objs in
    coerce_cons_lemma hd tl;
    assert (Seq.equal (Seq.cons hd tl) objs);
    // coerce objs == cons hd (coerce tl)
    let verts = coerce_to_vertex_list objs in
    assert (verts == Seq.cons hd (coerce_to_vertex_list tl));
    assert (Seq.equal (Seq.tail verts) (coerce_to_vertex_list tl));
    is_vertex_set_tail verts
#pop-options

/// After sweep_aux, the returned fp satisfies fl_valid.
/// Key preconditions:
///   - fl_valid g fp big_fuel (existing chain is valid)
///   - All white objects in objs have wosize >= 1
///   - No non-blue object in objs is visited by the chain from fp
///     (free-list chains only visit blue objects; non-blue objects are separate)
///   - is_vertex_set ensures objects are distinct (no repeats)
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let rec sweep_aux_produces_fl_valid
  (g: heap) (objs: seq obj_addr) (fp: U64.t)
  : Lemma
    (requires well_formed_heap g /\
              fl_valid g fp big_fuel /\
              fp_in_heap fp g /\
              (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
              is_vertex_set (coerce_to_vertex_list objs) /\
              // White objects have wosize >= 1
              (forall (o: obj_addr). Seq.mem o objs /\ is_white o g ==>
                U64.v (wosize_of_object o g) >= 1) /\
              // Non-blue objects are not in the chain
              (forall (o: obj_addr). Seq.mem o objs /\ ~(is_blue o g) ==>
                chain_not_visits g fp o big_fuel))
    (ensures (let (g', fp') = sweep_aux g objs fp in
              fl_valid g' fp' big_fuel))
    (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let obj = Seq.head objs in
      let rest = Seq.tail objs in
      let (g1, fp1) = sweep_object g obj fp in

      // Objects preserved
      sweep_object_preserves_objects g obj fp;
      sweep_object_preserves_wf g obj fp;
      assert (objects 0UL g1 == objects 0UL g);

      // Head is in objects
      assert (Seq.mem obj (objects 0UL g));

      if is_infix obj g then begin
        // Infix: (g1, fp1) = (g, fp), fl_valid unchanged
        assert (g1 == g /\ fp1 == fp);
        head_in_vertex_set_tail objs;
        sweep_aux_produces_fl_valid g1 rest fp1
      end
      else if is_white obj g then begin
        // White: fp1 = obj, g1 = makeBlue(set_field g obj 1 fp)
        assert (fp1 == obj);

        // obj is white hence non-blue, so chain doesn't visit obj
        is_white_iff obj g;
        is_blue_iff obj g;
        assert (color_of_object obj g = Header.White);
        assert (~(is_blue obj g));
        assert (chain_not_visits g fp obj big_fuel);
        // fl_valid of the OLD chain (fp) transfers to g1
        sweep_object_preserves_fl_valid_chain g obj fp fp big_fuel;
        assert (fl_valid g1 fp big_fuel);

        // Construct fl_valid g1 obj big_fuel via fl_valid_step:
        assert (Seq.mem obj (objects 0UL g1));
        sweep_object_preserves_self_wosize g obj fp;
        assert (U64.v (wosize_of_object obj g1) >= 1);
        // chain_not_visits gives fp ≠ obj (first hop)
        assert (fp <> obj);
        fl_valid_weaken g1 fp big_fuel (big_fuel - 1);
        // big_fuel > 0 (heap_size >= 16, mword = 8)
        assert (big_fuel > 0);
        // For fl_valid_step, we need:
        //   hd + 16 ≤ heap_size ==> read_word g1 obj ≠ obj ∧ fl_valid g1 (read_word g1 obj) (big_fuel-1)
        // sweep_object on white obj: set_field writes fp at obj, makeBlue writes at hd_address(obj)
        // So read_word g1 obj == fp
        let hd_obj = hd_address obj in
        hd_address_spec obj;
        if U64.v hd_obj + 16 <= heap_size then begin
          sweep_object_white_field0 g obj fp;
          assert (read_word g1 obj == fp);
          assert (read_word g1 obj <> obj);
          assert (fl_valid g1 (read_word g1 obj) (big_fuel - 1))
        end;
        fl_valid_step g1 (obj <: U64.t) big_fuel;

        // fp_in_heap obj g1
        assert (fp_in_heap fp1 g1);

        // Establish IH preconditions for rest
        head_in_vertex_set_tail objs;

        // White objects in rest: still white, wosize preserved, not in new chain
        let aux_white (o: obj_addr)
          : Lemma (requires Seq.mem o rest /\ is_white o g1)
                  (ensures U64.v (wosize_of_object o g1) >= 1)
          = vertex_set_head_not_in_tail objs;
            assert (o <> obj);
            sweep_object_color_locality g obj o fp;
            // color_of_object o g1 == color_of_object o g
            is_white_iff o g1;
            is_white_iff o g;
            assert (is_white o g);
            sweep_object_preserves_other_header g obj fp o
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux_white);

        // Non-blue objects in rest: not in the new chain (obj → fp → ...)
        let aux_chain (o: obj_addr)
          : Lemma (requires Seq.mem o rest /\ ~(is_blue o g1))
                  (ensures chain_not_visits g1 fp1 o big_fuel)
          = vertex_set_head_not_in_tail objs;
            assert (o <> obj);
            // o is non-blue in g1; color locality shows same color in g
            sweep_object_color_locality g obj o fp;
            is_blue_iff o g1;
            is_blue_iff o g;
            assert (~(is_blue o g));
            // From precondition: chain_not_visits g fp o big_fuel
            assert (chain_not_visits g fp o big_fuel);
            // Weaken fuel for the recursive step
            chain_not_visits_weaken g fp o big_fuel (big_fuel - 1);
            fl_valid_weaken g fp big_fuel (big_fuel - 1);
            chain_not_visits_weaken g fp obj big_fuel (big_fuel - 1);
            // Transfer chain_not_visits from g to g1
            chain_not_visits_preserved_by_sweep_object g obj fp fp o (big_fuel - 1);
            // Now chain_not_visits g1 fp o (big_fuel - 1)
            assert (chain_not_visits g1 fp o (big_fuel - 1));
            // New chain: fp1 = obj, o ≠ obj.
            // chain_not_visits g1 obj o big_fuel unfolds to:
            //   obj ≠ o, hd_address(obj) + 16 ≤ heap_size,
            //   then chain_not_visits g1 (read_word g1 obj) o (big_fuel - 1)
            //   = chain_not_visits g1 fp o (big_fuel - 1)
            assert (chain_not_visits g1 fp1 o big_fuel)
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux_chain);
        sweep_aux_produces_fl_valid g1 rest fp1
      end
      else if is_black obj g then begin
        // Black: g1 = makeWhite obj g, fp1 = fp (only header write)
        assert (fp1 == fp);

        // obj is black hence non-blue, so chain doesn't visit obj
        is_black_iff obj g;
        is_blue_iff obj g;
        assert (color_of_object obj g = Header.Black);
        assert (~(is_blue obj g));
        assert (chain_not_visits g fp obj big_fuel);
        sweep_object_preserves_fl_valid_chain g obj fp fp big_fuel;
        assert (fl_valid g1 fp big_fuel);
        assert (fp_in_heap fp1 g1);

        head_in_vertex_set_tail objs;

        // White objects in rest: wosize preserved
        let aux_white (o: obj_addr)
          : Lemma (requires Seq.mem o rest /\ is_white o g1)
                  (ensures U64.v (wosize_of_object o g1) >= 1)
          = vertex_set_head_not_in_tail objs;
            assert (o <> obj);
            sweep_object_color_locality g obj o fp;
            is_white_iff o g1;
            is_white_iff o g;
            assert (is_white o g);
            sweep_object_preserves_other_header g obj fp o
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux_white);

        // Non-blue objects in rest: chain_not_visits transfers
        let aux_chain (o: obj_addr)
          : Lemma (requires Seq.mem o rest /\ ~(is_blue o g1))
                  (ensures chain_not_visits g1 fp1 o big_fuel)
          = vertex_set_head_not_in_tail objs;
            assert (o <> obj);
            sweep_object_color_locality g obj o fp;
            is_blue_iff o g1;
            is_blue_iff o g;
            assert (~(is_blue o g));
            assert (chain_not_visits g fp o big_fuel);
            // Transfer: chain_not_visits g fp o big_fuel → chain_not_visits g1 fp o big_fuel
            chain_not_visits_preserved_by_sweep_object g obj fp fp o big_fuel;
            assert (chain_not_visits g1 fp o big_fuel)
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux_chain);
        sweep_aux_produces_fl_valid g1 rest fp1
      end
      else begin
        // Blue/Gray: (g1, fp1) = (g, fp), nothing changes
        assert (g1 == g /\ fp1 == fp);
        head_in_vertex_set_tail objs;
        sweep_aux_produces_fl_valid g1 rest fp1
      end
    end
#pop-options

/// =========================================================================
/// Lemma 19: sweep_produces_fl_valid — top-level sweep wrapper
/// =========================================================================

/// After sweep, the returned free pointer is fl_valid.
/// Preconditions model the post-mark state: fl_valid initial chain,
/// white objects have wosize >= 1, and the chain only visits blue objects.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let sweep_produces_fl_valid
  (g: heap) (fp: U64.t)
  : Lemma
    (requires well_formed_heap g /\
              fl_valid g fp big_fuel /\
              fp_in_heap fp g /\
              (forall (o: obj_addr). Seq.mem o (objects 0UL g) /\ is_white o g ==>
                U64.v (wosize_of_object o g) >= 1) /\
              (forall (o: obj_addr). Seq.mem o (objects 0UL g) /\ ~(is_blue o g) ==>
                chain_not_visits g fp o big_fuel))
    (ensures (let (g', fp') = sweep g fp in
              fl_valid g' fp' big_fuel))
  = objects_is_vertex_set g;
    sweep_aux_produces_fl_valid g (objects 0UL g) fp
#pop-options

/// =========================================================================
/// Lemma 20: init_all_blue — all objects are blue after init
/// =========================================================================

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let init_all_blue (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy)
          (ensures (let (g', _) = init_heap_spec g in
                    forall (obj: obj_addr). Seq.mem obj (objects 0UL g') ==> is_blue obj g'))
  = let (g', _) = init_heap_spec g in
    wz_bounds ();
    init_objects_eq g;
    init_header_at_zero g;
    let total_words = heap_size / U64.v mword in
    let wz = total_words - 1 in
    make_header_color_blue (U64.uint_to_t wz);
    color_of_object_spec (mword <: obj_addr) g';
    hd_address_spec (mword <: obj_addr);
    is_blue_iff (mword <: obj_addr) g';
    let aux (obj: obj_addr)
      : Lemma (requires Seq.mem obj (objects 0UL g'))
              (ensures is_blue obj g')
      = Seq.lemma_mem_snoc Seq.empty (mword <: hp_addr);
        assert (obj == mword);
        is_blue_iff obj g'
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

/// =========================================================================
/// Lemma 21: fl_valid_implies_fp_in_heap
/// =========================================================================

/// fl_valid of a well-formed fp (non-null, valid obj_addr) implies fp_in_heap.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let fl_valid_implies_fp_in_heap (g: heap) (fp: U64.t) (fuel: nat)
  : Lemma (requires fl_valid g fp fuel /\ fuel > 0 /\
                    (fp = 0UL \/ (U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                                  U64.v fp % U64.v mword = 0)))
          (ensures fp_in_heap fp g)
  = if fp = 0UL then ()
    else fl_valid_gives_mem g fp fuel
#pop-options

/// =========================================================================
/// Section III: Init + Alloc Bridge Lemmas
/// =========================================================================
/// Prove properties of the heap after init_heap_spec + alloc_spec,
/// enabling the alloc → collect transition.

/// alloc_search first-fit: when the first block in the free list
/// is big enough, alloc_search finds it on the first iteration.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let alloc_search_first_fit
  (g: heap) (fp: obj_addr) (wz: nat) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    U64.v (hd_address fp) + 16 <= heap_size /\
                    U64.v (getWosize (read_word g (hd_address fp))) >= wz)
          (ensures (let next_fp = read_word g fp in
                    let (g', rem_fp) = alloc_from_block g fp wz next_fp in
                    alloc_search g fp 0UL fp wz fuel ==
                      { heap_out = g'; fp_out = rem_fp; obj_out = fp }))
  = hd_address_spec fp;
    hd_address_bounds fp
#pop-options

/// init_alloc_spec_unfold: for the init heap, alloc_spec reduces to
/// alloc_from_block on the single free block.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let init_alloc_spec_unfold (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy /\
                    (let wz' = if wz = 0 then 1 else wz in
                     wz' <= heap_size / U64.v mword - 1))
          (ensures (let (g0, fp0) = init_heap_spec g in
                    let wz' = if wz = 0 then 1 else wz in
                    let (g', rem_fp) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
                    alloc_spec g0 fp0 wz ==
                      { heap_out = g'; fp_out = rem_fp; obj_out = mword }))
  = let (g0, fp0) = init_heap_spec g in
    wz_bounds ();
    init_wosize_lemma g;
    init_link_at_mword g;
    let wz' = if wz = 0 then 1 else wz in
    hd_address_spec (mword <: obj_addr);
    let fuel = heap_size / U64.v mword in
    alloc_search_first_fit g0 mword wz' fuel
#pop-options

/// After init + alloc_from_block, all field addresses read as 0UL.
/// Excludes header addresses (0 and rem_hd in split case).
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
private let init_alloc_from_block_field_zero (g: heap) (wz: nat) (addr: hp_addr)
  : Lemma (requires g == Seq.create heap_size 0uy /\
                    (let wz' = if wz = 0 then 1 else wz in
                     wz' <= heap_size / U64.v mword - 1 /\
                     U64.v addr >= U64.v mword /\
                     (let bwz = heap_size / U64.v mword - 1 in
                      let leftover = bwz - wz' in
                      // In split case, addr must not be the remainder header
                      (leftover >= 2 ==> U64.v addr <> (1 + wz') * 8))))
          (ensures (let (g0, _) = init_heap_spec g in
                    let wz' = if wz = 0 then 1 else wz in
                    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
                    read_word g' addr == 0UL))
  = let (g0, _) = init_heap_spec g in
    wz_bounds ();
    init_wosize_lemma g;
    init_header_at_zero g;
    init_field_read g addr;
    hd_address_spec (mword <: obj_addr);
    let wz' = if wz = 0 then 1 else wz in
    let bwz = heap_size / U64.v mword - 1 in
    let leftover = bwz - wz' in
    if leftover < 2 then begin
      // Exact fit: only writes at hd=0
      alloc_from_block_exact g0 mword wz' 0UL;
      let ahdr = make_header (U64.uint_to_t bwz) white_bits 0UL in
      read_write_different g0 zero_addr addr ahdr
    end
    else begin
      // Split: writes at hd=0, rem_hd=(1+wz')*8, rem_obj=(2+wz')*8
      alloc_from_block_split_normal g0 mword wz' 0UL;
      let ahdr = make_header (U64.uint_to_t wz') white_bits 0UL in
      let g1 = write_word g0 zero_addr ahdr in
      let rhn = (1 + wz') * 8 in
      let rh : hp_addr = U64.uint_to_t rhn in
      let rhdr = make_header (U64.uint_to_t (bwz - wz' - 1)) blue_bits 0UL in
      let g2 = write_word g1 rh rhdr in
      let ron = (2 + wz') * 8 in
      let ro : hp_addr = U64.uint_to_t ron in
      let g3 = write_word g2 ro 0UL in
      if U64.v addr = ron then
        // addr is the remainder link field: written with 0UL
        read_write_same g2 ro 0UL
      else begin
        // addr is not hd(=0), not rem_hd, not rem_obj
        read_write_different g2 ro addr 0UL;
        // addr <> rhn (from precondition: leftover >= 2 ==> addr <> rhn)
        read_write_different g1 rh addr rhdr;
        // addr >= 8 > 0
        read_write_different g0 zero_addr addr ahdr
      end
    end
#pop-options

/// For the exact fit case: read_word g' 0 has same wosize as init.
/// The objects list is unchanged because only color changed, not wosize.
#push-options "--z3rlimit 100 --fuel 2 --ifuel 0"
private let init_alloc_exact_wosize (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy /\
                    (let wz' = if wz = 0 then 1 else wz in
                     let bwz = heap_size / U64.v mword - 1 in
                     wz' <= bwz /\ bwz - wz' < 2))
          (ensures (let (g0, _) = init_heap_spec g in
                    let wz' = if wz = 0 then 1 else wz in
                    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
                    let bwz = heap_size / U64.v mword - 1 in
                    U64.v (getWosize (read_word g' zero_addr)) == bwz))
  = let (g0, _) = init_heap_spec g in
    wz_bounds ();
    init_wosize_lemma g;
    init_header_at_zero g;
    hd_address_spec (mword <: obj_addr);
    let wz' = if wz = 0 then 1 else wz in
    let bwz = heap_size / U64.v mword - 1 in
    alloc_from_block_exact g0 mword wz' 0UL;
    let ahdr = make_header (U64.uint_to_t bwz) white_bits 0UL in
    read_write_same g0 zero_addr ahdr;
    make_header_getWosize (U64.uint_to_t bwz) white_bits 0UL
#pop-options

/// For the exact fit case: objects list unchanged.
/// Proof: the only write is at header 0, and wosize is preserved → objects walk same.
#push-options "--z3rlimit 200 --fuel 3 --ifuel 1"
private let init_alloc_exact_objects (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy /\
                    (let wz' = if wz = 0 then 1 else wz in
                     let bwz = heap_size / U64.v mword - 1 in
                     wz' <= bwz /\ bwz - wz' < 2))
          (ensures (let (g0, _) = init_heap_spec g in
                    let wz' = if wz = 0 then 1 else wz in
                    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
                    objects 0UL g' == objects 0UL g0))
  = let (g0, _) = init_heap_spec g in
    wz_bounds ();
    init_objects_eq g;
    init_wosize_lemma g;
    init_header_at_zero g;
    hd_address_spec (mword <: obj_addr);
    let wz' = if wz = 0 then 1 else wz in
    let bwz = heap_size / U64.v mword - 1 in
    alloc_from_block_exact g0 mword wz' 0UL;
    let ahdr = make_header (U64.uint_to_t bwz) white_bits 0UL in
    let g' = write_word g0 zero_addr ahdr in
    // g' has same wosize at position 0 as g0
    read_write_same g0 zero_addr ahdr;
    make_header_getWosize (U64.uint_to_t bwz) white_bits 0UL;
    // Both heaps have getWosize(read_word _ 0) = bwz
    // next_start = (bwz+1)*8 = heap_size → objects = [mword]
    assert (U64.v (getWosize (read_word g' zero_addr)) == bwz);
    assert (U64.v (getWosize (read_word g0 zero_addr)) == bwz);
    // Both objects walks: start at 0, wosize bwz, next = heap_size, stop
    // F* should unfold objects once and see they're equal
    assert (objects 0UL g' == Seq.cons (mword <: hp_addr) Seq.empty);
    assert (objects 0UL g0 == Seq.cons (mword <: hp_addr) Seq.empty)
#pop-options

/// When the requested size exceeds the single init block (wz' > 127),
/// alloc_spec returns OOM: heap unchanged, fp unchanged, obj = 0.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let init_alloc_oom (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy /\
                    (let wz' = if wz = 0 then 1 else wz in
                     wz' > heap_size / U64.v mword - 1))
          (ensures (let (g0, fp0) = init_heap_spec g in
                    let r = alloc_spec g0 fp0 wz in
                    r.heap_out == g0 /\ r.fp_out == fp0 /\ r.obj_out == 0UL))
  = let (g0, fp0) = init_heap_spec g in
    wz_bounds ();
    init_wosize_lemma g;
    init_link_at_mword g;
    let wz' = if wz = 0 then 1 else wz in
    let fuel = heap_size / U64.v mword in
    // Step 1: block_wz = 127 < wz', so alloc_search advances past mword
    hd_address_spec (mword <: obj_addr);
    alloc_search_advance g0 fp0 0UL fp0 wz' fuel;
    // Step 2: next = spec_next_fp g0 mword = read_word g0 mword = 0UL
    spec_next_fp_eq g0 (mword <: obj_addr);
    // Step 3: cur = 0UL is invalid, so alloc_search returns OOM
    alloc_search_invalid g0 fp0 fp0 0UL wz' (fuel - 1)
#pop-options

/// For the split case: header reads in the post-alloc heap.
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
private let init_alloc_split_headers (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy /\
                    (let wz' = if wz = 0 then 1 else wz in
                     let bwz = heap_size / U64.v mword - 1 in
                     wz' <= bwz /\ bwz - wz' >= 2))
          (ensures (let (g0, _) = init_heap_spec g in
                    let wz' = if wz = 0 then 1 else wz in
                    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
                    let bwz = heap_size / U64.v mword - 1 in
                    let rhn = (1 + wz') * 8 in
                    let rh : hp_addr = U64.uint_to_t rhn in
                    // Header at 0: make_header wz' white 0
                    U64.v (getWosize (read_word g' zero_addr)) == wz' /\
                    // Header at rem_hd: make_header (bwz-wz'-1) blue 0
                    U64.v (getWosize (read_word g' rh)) == bwz - wz' - 1 /\
                    // Heap length unchanged
                    Seq.length g' == heap_size))
  = let (g0, _) = init_heap_spec g in
    wz_bounds ();
    init_wosize_lemma g;
    init_header_at_zero g;
    hd_address_spec (mword <: obj_addr);
    let wz' = if wz = 0 then 1 else wz in
    let bwz = heap_size / U64.v mword - 1 in
    alloc_from_block_split_normal g0 mword wz' 0UL;
    let ahdr = make_header (U64.uint_to_t wz') white_bits 0UL in
    let g1 = write_word g0 zero_addr ahdr in
    let rhn = (1 + wz') * 8 in
    let rh : hp_addr = U64.uint_to_t rhn in
    let rw = bwz - wz' - 1 in
    let rhdr = make_header (U64.uint_to_t rw) blue_bits 0UL in
    let g2 = write_word g1 rh rhdr in
    let ron = (2 + wz') * 8 in
    let ro : hp_addr = U64.uint_to_t ron in
    let g3 = write_word g2 ro 0UL in
    // Header at 0: chain reads back
    read_write_different g2 ro zero_addr 0UL;
    read_write_different g1 rh zero_addr rhdr;
    read_write_same g0 zero_addr ahdr;
    make_header_getWosize (U64.uint_to_t wz') white_bits 0UL;
    // Header at rem_hd: chain reads back
    read_write_different g2 ro rh 0UL;
    read_write_same g1 rh rhdr;
    make_header_getWosize (U64.uint_to_t rw) blue_bits 0UL
#pop-options

/// Split case helper: objects starting at the remainder header position.
/// objects rh g' == [rem_obj]
#push-options "--z3rlimit 100 --fuel 2 --ifuel 0 --split_queries always"
private let init_alloc_split_objects_tail (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy /\
                    (let wz' = if wz = 0 then 1 else wz in
                     let bwz = heap_size / U64.v mword - 1 in
                     wz' <= bwz /\ bwz - wz' >= 2))
          (ensures (let (g0, _) = init_heap_spec g in
                    let wz' = if wz = 0 then 1 else wz in
                    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
                    let rhn = (1 + wz') * 8 in
                    let rh : hp_addr = U64.uint_to_t rhn in
                    let ron = (2 + wz') * 8 in
                    let rem_obj : hp_addr = U64.uint_to_t ron in
                    objects rh g' == Seq.cons rem_obj Seq.empty))
  = let (g0, _) = init_heap_spec g in
    wz_bounds ();
    let wz' = if wz = 0 then 1 else wz in
    let bwz = heap_size / U64.v mword - 1 in
    init_alloc_split_headers g wz;
    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
    let rhn = (1 + wz') * 8 in
    let rh : hp_addr = U64.uint_to_t rhn in
    let ron = (2 + wz') * 8 in
    let rem_obj : hp_addr = U64.uint_to_t ron in
    // Guide objects unfolding at rh:
    // rh + 8 = ron < heap_size
    assert (rhn + 8 < heap_size);
    // wosize at rh
    assert (U64.v (getWosize (read_word g' rh)) == bwz - wz' - 1);
    // f_address rh = rh + 8 = rem_obj
    f_address_spec rh;
    assert (U64.v (f_address rh) == ron);
    // next_start = rhn + (bwz - wz' - 1 + 1) * 8 = rhn + (bwz - wz') * 8
    let rw = bwz - wz' - 1 in
    let next2 = rhn + (rw + 1) * 8 in
    assert (next2 == rhn + (bwz - wz') * 8);
    assert (next2 == (wz' + 1) * 8 + (bwz - wz') * 8);
    assert (next2 == (bwz + 1) * 8);
    assert (next2 == heap_size);
    assert (next2 >= heap_size)
#pop-options

/// For the split case: objects list = [mword, rem_obj].
#push-options "--z3rlimit 100 --fuel 2 --ifuel 0 --split_queries always"
private let init_alloc_split_objects (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy /\
                    (let wz' = if wz = 0 then 1 else wz in
                     let bwz = heap_size / U64.v mword - 1 in
                     wz' <= bwz /\ bwz - wz' >= 2))
          (ensures (let (g0, _) = init_heap_spec g in
                    let wz' = if wz = 0 then 1 else wz in
                    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
                    let ron = (2 + wz') * 8 in
                    let rem_obj : hp_addr = U64.uint_to_t ron in
                    objects 0UL g' == Seq.cons (mword <: hp_addr) (Seq.cons rem_obj Seq.empty)))
  = let (g0, _) = init_heap_spec g in
    wz_bounds ();
    let wz' = if wz = 0 then 1 else wz in
    let bwz = heap_size / U64.v mword - 1 in
    init_alloc_split_headers g wz;
    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
    let rhn = (1 + wz') * 8 in
    let rh : hp_addr = U64.uint_to_t rhn in
    let ron = (2 + wz') * 8 in
    let rem_obj : hp_addr = U64.uint_to_t ron in
    // Guide objects unfolding at 0:
    assert (0 + 8 < heap_size);
    assert (U64.v (getWosize (read_word g' zero_addr)) == wz');
    f_address_spec zero_addr;
    assert (U64.v (f_address zero_addr) == 8);
    // next_start = (wz'+1)*8 = rhn
    let next1 = (wz' + 1) * 8 in
    assert (next1 == rhn);
    assert (rhn < heap_size);
    assert (rhn < Seq.length g');
    // So objects 0UL g' = Seq.cons mword (objects rh g')
    // Now prove the tail
    init_alloc_split_objects_tail g wz
#pop-options

/// After init + alloc, objects list is always nonempty (all three cases).
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let init_alloc_objects_nonempty (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy)
          (ensures (let (g0, fp0) = init_heap_spec g in
                    let r = alloc_spec g0 fp0 wz in
                    Seq.length (objects 0UL r.heap_out) > 0))
  = let (g0, fp0) = init_heap_spec g in
    let wz' = if wz = 0 then 1 else wz in
    let bwz = heap_size / U64.v mword - 1 in
    wz_bounds ();
    if wz' > bwz then begin
      // OOM: heap unchanged, so objects same as init
      init_alloc_oom g wz;
      init_objects_nonempty g
    end
    else if bwz - wz' < 2 then begin
      // Exact fit: objects list unchanged from init
      init_alloc_spec_unfold g wz;
      init_alloc_exact_objects g wz;
      init_objects_nonempty g
    end
    else begin
      // Split: objects list = [mword; rem_obj], length 2
      init_alloc_spec_unfold g wz;
      init_alloc_split_objects g wz
    end
#pop-options

/// =========================================================================
/// Helper: field of mword reads 0UL in post-alloc heap
/// =========================================================================

#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
private let init_alloc_mword_field_zero_at (g: heap) (wz: nat) (idx: nat)
  : Lemma (requires g == Seq.create heap_size 0uy /\
                    (let wz' = if wz = 0 then 1 else wz in
                     let bwz = heap_size / U64.v mword - 1 in
                     wz' <= bwz /\
                     idx < (if bwz - wz' < 2 then bwz else wz')))
          (ensures (let (g0, _) = init_heap_spec g in
                    let wz' = if wz = 0 then 1 else wz in
                    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
                    let far = U64.add_mod mword (U64.mul_mod (U64.uint_to_t idx) mword) in
                    U64.v far < heap_size /\ U64.v far % 8 == 0 /\
                    read_word g' (far <: hp_addr) == 0UL))
  = wz_bounds ();
    let wz' = if wz = 0 then 1 else wz in
    let bwz = heap_size / U64.v mword - 1 in
    assert (idx < bwz);
    // Compute far = 8 + idx * 8 (same pattern as init_all_fields_zero)
    assert (idx < pow2 54);
    FStar.Math.Lemmas.pow2_lt_compat 64 54;
    FStar.Math.Lemmas.small_mod (idx * 8) (pow2 64);
    assert (U64.v (U64.mul_mod (U64.uint_to_t idx) mword) == idx * 8);
    assert (8 + idx * 8 < pow2 64);
    FStar.Math.Lemmas.small_mod (8 + idx * 8) (pow2 64);
    assert (U64.v (U64.add_mod mword (U64.mul_mod (U64.uint_to_t idx) mword)) == 8 + idx * 8);
    let far_nat = 8 + idx * 8 in
    assert (far_nat < heap_size);
    FStar.Math.Lemmas.lemma_mod_plus_distr_l 8 (idx * 8) 8;
    assert (far_nat % 8 == 0);
    let far : hp_addr = U64.uint_to_t far_nat in
    // In split case: idx < wz', so (idx+1)*8 < (1+wz')*8, i.e., far_nat <> (1+wz')*8
    (if bwz - wz' >= 2 then
       FStar.Math.Lemmas.lemma_mult_lt_right 8 (idx + 1) (1 + wz')
     else ());
    init_alloc_from_block_field_zero g wz far
#pop-options

/// =========================================================================
/// Helper: remainder object is blue after split allocation
/// =========================================================================

#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
private let init_alloc_split_rem_blue (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy /\
                    (let wz' = if wz = 0 then 1 else wz in
                     let bwz = heap_size / U64.v mword - 1 in
                     wz' <= bwz /\ bwz - wz' >= 2))
          (ensures (let (g0, _) = init_heap_spec g in
                    let wz' = if wz = 0 then 1 else wz in
                    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
                    let ron = (2 + wz') * 8 in
                    let rem_obj : obj_addr = U64.uint_to_t ron in
                    is_blue rem_obj g'))
  = let (g0, _) = init_heap_spec g in
    wz_bounds ();
    init_wosize_lemma g;
    init_header_at_zero g;
    hd_address_spec (mword <: obj_addr);
    let wz' = if wz = 0 then 1 else wz in
    let bwz = heap_size / U64.v mword - 1 in
    alloc_from_block_split_normal g0 mword wz' 0UL;
    let ahdr = make_header (U64.uint_to_t wz') white_bits 0UL in
    let g1 = write_word g0 zero_addr ahdr in
    let rhn = (1 + wz') * 8 in
    let rh : hp_addr = U64.uint_to_t rhn in
    let rw = bwz - wz' - 1 in
    let rhdr = make_header (U64.uint_to_t rw) blue_bits 0UL in
    let g2 = write_word g1 rh rhdr in
    let ron = (2 + wz') * 8 in
    let ro : hp_addr = U64.uint_to_t ron in
    let g3 = write_word g2 ro 0UL in
    // Chain reads: read_word g3 rh = rhdr
    read_write_different g2 ro rh 0UL;
    read_write_same g1 rh rhdr;
    assert (read_word g3 rh == rhdr);
    // Color of remainder header is Blue
    make_header_color_blue (U64.uint_to_t rw);
    // Connect to is_blue via rem_obj
    let rem_obj : obj_addr = U64.uint_to_t ron in
    hd_address_spec rem_obj;
    color_of_object_spec rem_obj g3;
    is_blue_iff rem_obj g3
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
/// After init + alloc (split), mword is NOT blue (it's white).
private let init_alloc_split_mword_not_blue (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy /\
                    (let wz' = if wz = 0 then 1 else wz in
                     let bwz = heap_size / U64.v mword - 1 in
                     wz' <= bwz /\ bwz - wz' >= 2))
          (ensures (let (g0, _) = init_heap_spec g in
                    let wz' = if wz = 0 then 1 else wz in
                    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
                    ~(is_blue (mword <: obj_addr) g')))
  = let (g0, _) = init_heap_spec g in
    wz_bounds ();
    init_wosize_lemma g;
    init_header_at_zero g;
    hd_address_spec (mword <: obj_addr);
    let wz' = if wz = 0 then 1 else wz in
    let bwz = heap_size / U64.v mword - 1 in
    alloc_from_block_split_normal g0 mword wz' 0UL;
    let ahdr = make_header (U64.uint_to_t wz') white_bits 0UL in
    let g1 = write_word g0 zero_addr ahdr in
    let rhn = (1 + wz') * 8 in
    let rh : hp_addr = U64.uint_to_t rhn in
    let rw = bwz - wz' - 1 in
    let rhdr = make_header (U64.uint_to_t rw) blue_bits 0UL in
    let g2 = write_word g1 rh rhdr in
    let ron = (2 + wz') * 8 in
    let ro : hp_addr = U64.uint_to_t ron in
    let g3 = write_word g2 ro 0UL in
    // Chain reads: read_word g3 zero_addr = ahdr
    read_write_different g2 ro zero_addr 0UL;
    read_write_different g1 rh zero_addr rhdr;
    read_write_same g0 zero_addr ahdr;
    assert (read_word g3 zero_addr == ahdr);
    // Color of allocated header is White ≠ Blue
    make_header_color_white (U64.uint_to_t wz');
    color_of_object_spec (mword <: obj_addr) g3;
    is_blue_iff (mword <: obj_addr) g3
#pop-options

/// After init + alloc, all fields of mword (the allocated object) read as 0UL.
/// This covers both exact and split cases.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let init_alloc_mword_fields_zero (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy /\
                    (let wz' = if wz = 0 then 1 else wz in
                     wz' <= heap_size / U64.v mword - 1))
          (ensures (let (g0, _) = init_heap_spec g in
                    let wz' = if wz = 0 then 1 else wz in
                    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
                    let bwz = heap_size / U64.v mword - 1 in
                    let actual_wz = if bwz - wz' < 2 then bwz else wz' in
                    forall (idx: nat{idx < actual_wz}).
                      (let far = U64.add_mod (mword <: obj_addr) (U64.mul_mod (U64.uint_to_t idx) mword) in
                       U64.v far < heap_size /\ U64.v far % 8 == 0 ==>
                       read_word g' (far <: hp_addr) == 0UL)))
  = let (g0, _) = init_heap_spec g in
    wz_bounds ();
    let wz' = if wz = 0 then 1 else wz in
    let bwz = heap_size / U64.v mword - 1 in
    let actual_wz = if bwz - wz' < 2 then bwz else wz' in
    let aux (idx: nat{idx < actual_wz}) : Lemma
      (let far = U64.add_mod (mword <: obj_addr) (U64.mul_mod (U64.uint_to_t idx) mword) in
       U64.v far < heap_size /\ U64.v far % 8 == 0 ==>
       (let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
        read_word g' (far <: hp_addr) == 0UL))
    = let far = U64.add_mod (mword <: obj_addr) (U64.mul_mod (U64.uint_to_t idx) mword) in
      if U64.v far < heap_size && U64.v far % 8 = 0 then begin
        assert (U64.v far == (1 + idx) * 8);
        assert (U64.v far >= 8);
        init_alloc_from_block_field_zero g wz (far <: hp_addr)
      end
    in
    Classical.forall_intro aux
#pop-options

/// After init + alloc, points_to g' mword dst = false for all dst.
/// Follows from all fields being 0UL → no pointer fields.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
private let init_alloc_no_points_to (g: heap) (wz: nat) (dst: obj_addr)
  : Lemma (requires g == Seq.create heap_size 0uy /\
                    (let wz' = if wz = 0 then 1 else wz in
                     wz' <= heap_size / U64.v mword - 1))
          (ensures (let (g0, _) = init_heap_spec g in
                    let wz' = if wz = 0 then 1 else wz in
                    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
                    ~(points_to g' mword dst)))
  = let (g0, _) = init_heap_spec g in
    wz_bounds ();
    init_alloc_mword_fields_zero g wz;
    let wz' = if wz = 0 then 1 else wz in
    let bwz = heap_size / U64.v mword - 1 in
    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
    if bwz - wz' < 2 then begin
      init_alloc_exact_wosize g wz;
      wosize_of_object_spec (mword <: obj_addr) g';
      hd_address_spec (mword <: obj_addr);
      wosize_of_object_bound (mword <: obj_addr) g';
      no_pointer_fields_no_efptu g' mword (wosize_of_object mword g') dst
    end
    else begin
      init_alloc_split_headers g wz;
      wosize_of_object_spec (mword <: obj_addr) g';
      hd_address_spec (mword <: obj_addr);
      wosize_of_object_bound (mword <: obj_addr) g';
      no_pointer_fields_no_efptu g' mword (wosize_of_object mword g') dst
    end
#pop-options

/// Exact-fit: no_pointer_to_blue for init+alloc
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
private let init_alloc_exact_no_pointer_to_blue (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy /\
                    (let wz' = if wz = 0 then 1 else wz in
                     let bwz = heap_size / U64.v mword - 1 in
                     wz' <= bwz /\ bwz - wz' < 2))
          (ensures (let (g0, _) = init_heap_spec g in
                    let wz' = if wz = 0 then 1 else wz in
                    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
                    no_pointer_to_blue g'))
  = let (g0, _) = init_heap_spec g in
    let wz' = if wz = 0 then 1 else wz in
    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
    wz_bounds ();
    init_alloc_mword_fields_zero g wz;
    init_alloc_exact_objects g wz;
    init_objects_eq g;
    init_alloc_exact_wosize g wz;
    wosize_of_object_spec (mword <: obj_addr) g';
    hd_address_spec (mword <: obj_addr);
    wosize_of_object_bound (mword <: obj_addr) g';
    let aux (src dst: obj_addr) : Lemma
      (Seq.mem src (objects 0UL g') /\ ~(is_blue src g') /\ points_to g' src dst ==>
       ~(is_blue dst g'))
    = if Seq.mem src (objects 0UL g') && points_to g' src dst then begin
        Seq.lemma_mem_snoc (Seq.empty #obj_addr) (mword <: obj_addr);
        assert (src == mword);
        no_pointer_fields_no_efptu g' mword (wosize_of_object mword g') dst
      end
    in
    Classical.forall_intro_2 aux
#pop-options

/// Split: no_pointer_to_blue for init+alloc
/// Helper for decomposing membership in a 2-element obj_addr sequence
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
private let mem_two_objects (src x y: obj_addr)
  : Lemma (requires Seq.mem src (Seq.cons #obj_addr x (Seq.cons #obj_addr y (Seq.empty #obj_addr))))
          (ensures src == x \/ src == y)
  = Seq.mem_cons #obj_addr y (Seq.empty #obj_addr);
    Seq.mem_cons #obj_addr x (Seq.cons #obj_addr y (Seq.empty #obj_addr))
#pop-options

/// Helper: given a 2-object heap where only mword is non-blue and mword has
/// no outgoing pointers, conclude no_pointer_to_blue.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
private let no_pointer_to_blue_two_objects
  (g': heap) (rem_obj: obj_addr)
  : Lemma
    (requires
      objects 0UL g' == Seq.cons #obj_addr mword (Seq.cons #obj_addr rem_obj (Seq.empty #obj_addr)) /\
      is_blue rem_obj g' /\
      ~(is_blue (mword <: obj_addr) g') /\
      (forall (dst: obj_addr). ~(points_to g' mword dst)))
    (ensures no_pointer_to_blue g')
  = let s2 = Seq.cons #obj_addr mword (Seq.cons #obj_addr rem_obj (Seq.empty #obj_addr)) in
    let aux (src dst: obj_addr) : Lemma
      (Seq.mem src (objects 0UL g') /\ ~(is_blue src g') /\ points_to g' src dst ==>
       ~(is_blue dst g'))
    = if Seq.mem src (objects 0UL g') && not (is_blue src g') && points_to g' src dst then begin
        assert (Seq.mem src s2);
        mem_two_objects src mword rem_obj;
        assert (src == mword \/ src == rem_obj);
        // rem_obj is blue, src is not blue, so src == mword
        assert (src == mword);
        // But mword has no outgoing pointers, contradiction
        assert False
      end
    in
    Classical.forall_intro_2 aux
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
/// Standalone: mword has no outgoing pointers after init+alloc split
private let init_alloc_split_mword_no_pts (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy /\
                    (let wz' = if wz = 0 then 1 else wz in
                     let bwz = heap_size / U64.v mword - 1 in
                     wz' <= bwz /\ bwz - wz' >= 2))
          (ensures (let (g0, _) = init_heap_spec g in
                    let wz' = if wz = 0 then 1 else wz in
                    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
                    forall (dst: obj_addr). ~(points_to g' mword dst)))
  = let (g0, _) = init_heap_spec g in
    let wz' = if wz = 0 then 1 else wz in
    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
    wz_bounds ();
    init_alloc_mword_fields_zero g wz;
    init_alloc_split_headers g wz;
    wosize_of_object_spec (mword <: obj_addr) g';
    hd_address_spec (mword <: obj_addr);
    wosize_of_object_bound (mword <: obj_addr) g';
    // Bridge: connect wosize_of_object to wz' so Z3 can match the quantifiers
    assert (U64.v (hd_address (mword <: obj_addr)) == 0);
    assert (wosize_of_object (mword <: obj_addr) g' == getWosize (read_word g' (hd_address (mword <: obj_addr))));
    make_header_getWosize (U64.uint_to_t wz') white_bits 0UL;
    assert (U64.v (wosize_of_object (mword <: obj_addr) g') == wz');
    let aux (dst: obj_addr) : Lemma (~(points_to g' mword dst))
      = no_pointer_fields_no_efptu g' mword (wosize_of_object mword g') dst
    in
    Classical.forall_intro aux
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0 --split_queries always"
private let init_alloc_split_no_pointer_to_blue (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy /\
                    (let wz' = if wz = 0 then 1 else wz in
                     let bwz = heap_size / U64.v mword - 1 in
                     wz' <= bwz /\ bwz - wz' >= 2))
          (ensures (let (g0, _) = init_heap_spec g in
                    let wz' = if wz = 0 then 1 else wz in
                    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
                    no_pointer_to_blue g'))
  = let (g0, _) = init_heap_spec g in
    let wz' = if wz = 0 then 1 else wz in
    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
    wz_bounds ();
    let ron = (2 + wz') * 8 in
    let rem_obj : obj_addr = U64.uint_to_t ron in
    init_alloc_split_objects g wz;
    assert (objects 0UL g' == Seq.cons #obj_addr mword (Seq.cons #obj_addr rem_obj (Seq.empty #obj_addr)));
    init_alloc_split_rem_blue g wz;
    assert (is_blue rem_obj g');
    init_alloc_split_mword_not_blue g wz;
    assert (~(is_blue (mword <: obj_addr) g'));
    init_alloc_split_mword_no_pts g wz;
    assert (forall (dst: obj_addr). ~(points_to g' mword dst));
    no_pointer_to_blue_two_objects g' rem_obj
#pop-options

/// After init + alloc, no_pointer_to_blue holds.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let init_alloc_no_pointer_to_blue (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy)
          (ensures (let (g0, fp0) = init_heap_spec g in
                    let r = alloc_spec g0 fp0 wz in
                    no_pointer_to_blue r.heap_out))
  = let (g0, fp0) = init_heap_spec g in
    let wz' = if wz = 0 then 1 else wz in
    let bwz = heap_size / U64.v mword - 1 in
    wz_bounds ();
    if wz' > bwz then begin
      init_alloc_oom g wz;
      init_no_pointer_to_blue g
    end
    else begin
      init_alloc_spec_unfold g wz;
      if bwz - wz' < 2 then
        init_alloc_exact_no_pointer_to_blue g wz
      else
        init_alloc_split_no_pointer_to_blue g wz
    end
#pop-options







/// General lemma: if all fields of an object are 0UL, get_pointer_fields returns empty.
/// This generalizes init_get_pointer_fields_aux_empty to work on any heap.
#push-options "--z3rlimit 50"
private let rec zero_fields_pointer_fields_empty
  (g: heap) (obj: obj_addr) (i: U64.t{U64.v i >= 1}) (ws: U64.t)
  : Lemma (requires U64.v i <= U64.v ws + 1 /\
                    (forall (j: U64.t{U64.v j >= U64.v i /\ U64.v j <= U64.v ws}).
                      get_field g obj j == 0UL))
          (ensures get_pointer_fields_aux g obj i ws == Seq.empty)
          (decreases (U64.v ws - U64.v i + 1))
  = if U64.v i > U64.v ws then ()
    else begin
      assert (get_field g obj i == 0UL);
      assert (~(is_pointer_field (get_field g obj i)));
      if U64.v i < U64.v ws then
        zero_fields_pointer_fields_empty g obj (U64.add i 1UL) ws
      else ()
    end
#pop-options

/// After init + alloc, graph_wf holds.
/// Helper: all_edges on objects with empty pointer fields yields empty edges.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 0"
private let all_edges_empty_one (g: heap) (obj: obj_addr)
  : Lemma (requires get_pointer_fields g obj == Seq.empty)
          (ensures all_edges g (Seq.cons obj Seq.empty) == Seq.empty)
  = assert (Seq.length (Seq.cons obj (Seq.empty #obj_addr)) > 0);
    assert (Seq.head (Seq.cons obj (Seq.empty #obj_addr)) == obj);
    assert (Seq.equal (Seq.tail (Seq.cons obj (Seq.empty #obj_addr))) Seq.empty);
    assert (object_edges g obj == make_edges obj Seq.empty);
    assert (make_edges obj Seq.empty == Seq.empty);
    assert (all_edges g Seq.empty == Seq.empty);
    Seq.append_empty_l (Seq.empty #edge)
#pop-options

#push-options "--z3rlimit 50 --fuel 2 --ifuel 0"
private let all_edges_empty_two (g: heap) (obj1 obj2: obj_addr)
  : Lemma (requires get_pointer_fields g obj1 == Seq.empty /\
                    get_pointer_fields g obj2 == Seq.empty)
          (ensures all_edges g (Seq.cons obj1 (Seq.cons obj2 Seq.empty)) == Seq.empty)
  = let s2 = Seq.cons obj2 (Seq.empty #obj_addr) in
    let s12 = Seq.cons obj1 s2 in
    assert (Seq.head s12 == obj1);
    assert (Seq.equal (Seq.tail s12) s2);
    all_edges_empty_one g obj2;
    assert (all_edges g s2 == Seq.empty);
    assert (object_edges g obj1 == make_edges obj1 Seq.empty);
    assert (make_edges obj1 Seq.empty == Seq.empty);
    Seq.append_empty_l (Seq.empty #edge)
#pop-options

/// Helper: graph with empty edges is well-formed
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let graph_wf_empty_edges (g: heap)
  : Lemma (requires all_edges g (objects 0UL g) == Seq.empty)
          (ensures graph_wf (create_graph g))
  = objects_is_vertex_set g;
    let objs = objects 0UL g in
    let gr = create_graph_from_heap g objs in
    assert (gr.edges == Seq.empty);
    let aux (e: edge) : Lemma (Seq.mem e gr.edges ==> Seq.mem (fst e) gr.vertices /\ Seq.mem (snd e) gr.vertices)
      = ()
    in
    Classical.forall_intro aux
#pop-options

/// Helper: after init + exact alloc, mword has empty pointer fields
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1 --split_queries always"
private let init_alloc_exact_empty_pointer_fields (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy /\
                    (let wz' = if wz = 0 then 1 else wz in
                     let bwz = heap_size / U64.v mword - 1 in
                     wz' <= bwz /\ bwz - wz' < 2))
          (ensures (let (g0, _) = init_heap_spec g in
                    let wz' = if wz = 0 then 1 else wz in
                    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
                    get_pointer_fields g' mword == Seq.empty))
  = let (g0, _) = init_heap_spec g in
    let wz' = if wz = 0 then 1 else wz in
    let bwz = heap_size / U64.v mword - 1 in
    wz_bounds ();
    init_alloc_spec_unfold g wz;
    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
    init_alloc_mword_fields_zero g wz;
    hd_address_spec (mword <: obj_addr);
    init_alloc_exact_wosize g wz;
    wosize_of_object_spec (mword <: obj_addr) g';
    wosize_of_object_bound (mword <: obj_addr) g';
    let exact_wz = U64.uint_to_t bwz in
    make_header_getTag exact_wz white_bits 0UL;
    tag_of_object_spec (mword <: obj_addr) g';
    no_scan_tag_val ();
    is_no_scan_spec (mword <: obj_addr) g';
    let field_zero (j: U64.t{U64.v j >= 1 /\ U64.v j <= U64.v (wosize_of_object mword g')})
      : Lemma (get_field g' mword j == 0UL)
      = let fa = U64.add (hd_address (mword <: obj_addr)) (U64.mul mword j) in
        assert (U64.v fa == U64.v j * 8);
        assert (U64.v fa >= 8);
        init_alloc_from_block_field_zero g wz (fa <: hp_addr)
    in
    Classical.forall_intro (Classical.move_requires field_zero);
    zero_fields_pointer_fields_empty g' mword 1UL (wosize_of_object mword g')
#pop-options

/// Helper: graph_wf for the exact-fit case
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
private let init_alloc_exact_graph_wf (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy /\
                    (let wz' = if wz = 0 then 1 else wz in
                     let bwz = heap_size / U64.v mword - 1 in
                     wz' <= bwz /\ bwz - wz' < 2))
          (ensures (let (g0, _) = init_heap_spec g in
                    let wz' = if wz = 0 then 1 else wz in
                    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
                    graph_wf (create_graph g')))
  = let (g0, _) = init_heap_spec g in
    let wz' = if wz = 0 then 1 else wz in
    wz_bounds ();
    init_alloc_spec_unfold g wz;
    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
    init_alloc_exact_empty_pointer_fields g wz;
    init_alloc_exact_objects g wz;
    init_objects_eq g;
    all_edges_empty_one g' mword;
    graph_wf_empty_edges g'
#pop-options

/// Helper: after init + split alloc, both objects have empty pointer fields
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1 --split_queries always"
private let init_alloc_split_empty_pointer_fields (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy /\
                    (let wz' = if wz = 0 then 1 else wz in
                     let bwz = heap_size / U64.v mword - 1 in
                     wz' <= bwz /\ bwz - wz' >= 2))
          (ensures (let (g0, _) = init_heap_spec g in
                    let wz' = if wz = 0 then 1 else wz in
                    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
                    let ron = (2 + wz') * 8 in
                    let rem_obj : obj_addr = U64.uint_to_t ron in
                    get_pointer_fields g' mword == Seq.empty /\
                    get_pointer_fields g' rem_obj == Seq.empty))
  = let (g0, _) = init_heap_spec g in
    let wz' = if wz = 0 then 1 else wz in
    let bwz = heap_size / U64.v mword - 1 in
    wz_bounds ();
    init_alloc_spec_unfold g wz;
    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
    init_alloc_mword_fields_zero g wz;
    hd_address_spec (mword <: obj_addr);
    init_alloc_split_headers g wz;
    let ron = (2 + wz') * 8 in
    let rem_obj : obj_addr = U64.uint_to_t ron in
    wosize_of_object_spec (mword <: obj_addr) g';
    wosize_of_object_bound (mword <: obj_addr) g';
    make_header_getTag (U64.uint_to_t wz') white_bits 0UL;
    tag_of_object_spec (mword <: obj_addr) g';
    no_scan_tag_val ();
    is_no_scan_spec (mword <: obj_addr) g';
    let field_zero_mword (j: U64.t{U64.v j >= 1 /\ U64.v j <= U64.v (wosize_of_object mword g')})
      : Lemma (get_field g' mword j == 0UL)
      = let fa = U64.add (hd_address (mword <: obj_addr)) (U64.mul mword j) in
        assert (U64.v fa == U64.v j * 8);
        assert (U64.v fa >= 8);
        init_alloc_from_block_field_zero g wz (fa <: hp_addr)
    in
    Classical.forall_intro (Classical.move_requires field_zero_mword);
    zero_fields_pointer_fields_empty g' mword 1UL (wosize_of_object mword g');
    wosize_of_object_spec rem_obj g';
    hd_address_spec rem_obj;
    wosize_of_object_bound rem_obj g';
    make_header_getTag (U64.uint_to_t (bwz - wz' - 1)) blue_bits 0UL;
    tag_of_object_spec rem_obj g';
    is_no_scan_spec rem_obj g';
    let field_zero_rem (j: U64.t{U64.v j >= 1 /\ U64.v j <= U64.v (wosize_of_object rem_obj g')})
      : Lemma (get_field g' rem_obj j == 0UL)
      = let fa = U64.add (hd_address rem_obj) (U64.mul mword j) in
        assert (U64.v fa == ron - 8 + U64.v j * 8);
        assert (U64.v fa == (1 + wz' + U64.v j) * 8);
        assert (U64.v fa >= 8);
        init_alloc_from_block_field_zero g wz (fa <: hp_addr)
    in
    Classical.forall_intro (Classical.move_requires field_zero_rem);
    zero_fields_pointer_fields_empty g' rem_obj 1UL (wosize_of_object rem_obj g')
#pop-options

/// Helper: graph_wf for the split case
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
private let init_alloc_split_graph_wf (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy /\
                    (let wz' = if wz = 0 then 1 else wz in
                     let bwz = heap_size / U64.v mword - 1 in
                     wz' <= bwz /\ bwz - wz' >= 2))
          (ensures (let (g0, _) = init_heap_spec g in
                    let wz' = if wz = 0 then 1 else wz in
                    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
                    graph_wf (create_graph g')))
  = let (g0, _) = init_heap_spec g in
    let wz' = if wz = 0 then 1 else wz in
    wz_bounds ();
    init_alloc_spec_unfold g wz;
    let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
    init_alloc_split_empty_pointer_fields g wz;
    init_alloc_split_objects g wz;
    let ron = (2 + wz') * 8 in
    let rem_obj : obj_addr = U64.uint_to_t ron in
    all_edges_empty_two g' mword rem_obj;
    graph_wf_empty_edges g'
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let init_alloc_graph_wf (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy)
          (ensures (let (g0, fp0) = init_heap_spec g in
                    let r = alloc_spec g0 fp0 wz in
                    graph_wf (create_graph r.heap_out)))
  = let (g0, fp0) = init_heap_spec g in
    let wz' = if wz = 0 then 1 else wz in
    let bwz = heap_size / U64.v mword - 1 in
    wz_bounds ();
    if wz' > bwz then begin
      init_alloc_oom g wz;
      init_graph_wf g
    end
    else begin
      init_alloc_spec_unfold g wz;
      if bwz - wz' < 2 then
        init_alloc_exact_graph_wf g wz
      else
        init_alloc_split_graph_wf g wz
    end
#pop-options

/// After init + alloc, heap_objects_dense holds.
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1 --split_queries always"
let init_alloc_dense (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy)
          (ensures (let (g0, fp0) = init_heap_spec g in
                    let r = alloc_spec g0 fp0 wz in
                    heap_objects_dense r.heap_out))
  = let (g0, fp0) = init_heap_spec g in
    let wz' = if wz = 0 then 1 else wz in
    let bwz = heap_size / U64.v mword - 1 in
    wz_bounds ();
    if wz' > bwz then begin
      init_alloc_oom g wz;
      init_dense g
    end
    else if bwz - wz' < 2 then begin
      init_alloc_spec_unfold g wz;
      init_alloc_exact_objects g wz;
      init_objects_eq g;
      let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
      init_alloc_exact_wosize g wz;
      let aux (start: hp_addr) : Lemma
        (U64.v start + 8 < heap_size ==>
         Seq.mem (f_address start) (objects 0UL g') ==>
         Seq.length (objects start g') > 0 ==>
         (let wz_h = getWosize (read_word g' start) in
          let next = U64.v start + (U64.v wz_h + 1) * 8 in
          next + 8 < heap_size ==>
          Seq.length (objects (U64.uint_to_t next) g') > 0 /\
          Seq.mem (f_address (U64.uint_to_t next)) (objects 0UL g')))
      = if U64.v start + 8 < heap_size && Seq.mem (f_address start) (objects 0UL g') then begin
          f_address_spec start;
          Seq.lemma_mem_snoc Seq.empty (mword <: hp_addr);
          assert (f_address start == (mword <: obj_addr));
          assert (U64.v start == 0);
          assert (getWosize (read_word g' zero_addr) == U64.uint_to_t bwz);
          let next = (bwz + 1) * 8 in
          assert (next == heap_size);
          assert (~ (next + 8 < heap_size))
        end
      in
      Classical.forall_intro aux;
      heap_objects_dense_intro g'
    end
    else begin
      init_alloc_spec_unfold g wz;
      init_alloc_split_objects g wz;
      init_alloc_split_headers g wz;
      let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
      let ron = (2 + wz') * 8 in
      let rem_obj : hp_addr = U64.uint_to_t ron in
      let objs = objects 0UL g' in
      Seq.lemma_mem_snoc (Seq.cons (mword <: hp_addr) Seq.empty) rem_obj;
      Seq.lemma_mem_snoc (Seq.empty #hp_addr) (mword <: hp_addr);
      let aux (start: hp_addr) : Lemma
        (U64.v start + 8 < heap_size ==>
         Seq.mem (f_address start) (objects 0UL g') ==>
         Seq.length (objects start g') > 0 ==>
         (let wz_h = getWosize (read_word g' start) in
          let next = U64.v start + (U64.v wz_h + 1) * 8 in
          next + 8 < heap_size ==>
          Seq.length (objects (U64.uint_to_t next) g') > 0 /\
          Seq.mem (f_address (U64.uint_to_t next)) (objects 0UL g')))
      = if U64.v start + 8 < heap_size && Seq.mem (f_address start) (objects 0UL g') then begin
          f_address_spec start;
          if f_address start = (mword <: obj_addr) then begin
            assert (U64.v start == 0);
            assert (getWosize (read_word g' zero_addr) == U64.uint_to_t wz');
            let rhn = (1 + wz') * 8 in
            assert ((wz' + 1) * 8 == rhn);
            assert (rhn + 8 < heap_size);
            f_address_spec (U64.uint_to_t rhn);
            assert (f_address (U64.uint_to_t rhn) == rem_obj);
            assert (Seq.mem rem_obj objs);
            init_alloc_split_objects_tail g wz
          end
          else begin
            assert (f_address start == rem_obj);
            assert (U64.v start == ron - 8);
            let rhn = (1 + wz') * 8 in
            assert (U64.v start == rhn);
            assert (getWosize (read_word g' (U64.uint_to_t rhn)) == U64.uint_to_t (bwz - wz' - 1));
            let next = rhn + (bwz - wz') * 8 in
            assert (next == (wz' + 1 + bwz - wz') * 8);
            assert (next == (bwz + 1) * 8);
            assert (next == heap_size);
            assert (~ (next + 8 < heap_size))
          end
        end
      in
      Classical.forall_intro aux;
      heap_objects_dense_intro g'
    end
#pop-options

/// After init + alloc, fp_in_heap holds.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let init_alloc_fp_in_heap (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy)
          (ensures (let (g0, fp0) = init_heap_spec g in
                    let r = alloc_spec g0 fp0 wz in
                    fp_in_heap r.fp_out r.heap_out))
  = let (g0, fp0) = init_heap_spec g in
    let wz' = if wz = 0 then 1 else wz in
    let bwz = heap_size / U64.v mword - 1 in
    wz_bounds ();
    if wz' > bwz then begin
      init_alloc_oom g wz;
      init_objects_eq g;
      Seq.lemma_mem_snoc (Seq.empty #hp_addr) (mword <: hp_addr)
    end
    else begin
      init_alloc_spec_unfold g wz;
      if bwz - wz' < 2 then
        alloc_from_block_exact g0 mword wz' 0UL
      else begin
        alloc_from_block_split_normal g0 mword wz' 0UL;
        init_alloc_split_objects g wz;
        let ron = (2 + wz') * 8 in
        let rem_obj : hp_addr = U64.uint_to_t ron in
        Seq.lemma_mem_snoc (Seq.cons (mword <: hp_addr) Seq.empty) rem_obj
      end
    end
#pop-options

/// After init + alloc, fp_valid holds.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let init_alloc_fp_valid (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy)
          (ensures (let (g0, fp0) = init_heap_spec g in
                    let r = alloc_spec g0 fp0 wz in
                    fp_valid r.fp_out r.heap_out))
  = let (g0, fp0) = init_heap_spec g in
    let wz' = if wz = 0 then 1 else wz in
    let bwz = heap_size / U64.v mword - 1 in
    wz_bounds ();
    if wz' > bwz then begin
      init_alloc_oom g wz;
      init_objects_eq g;
      Seq.lemma_mem_snoc (Seq.empty #hp_addr) (mword <: hp_addr);
      fp_valid_intro (mword <: obj_addr) g0
    end
    else begin
      init_alloc_spec_unfold g wz;
      if bwz - wz' < 2 then begin
        alloc_from_block_exact g0 mword wz' 0UL;
        let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
        fp_valid_not_pointer 0UL g'
      end
      else begin
        alloc_from_block_split_normal g0 mword wz' 0UL;
        init_alloc_split_objects g wz;
        let ron = (2 + wz') * 8 in
        let rem_obj : hp_addr = U64.uint_to_t ron in
        let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
        Seq.lemma_mem_snoc (Seq.cons (mword <: hp_addr) Seq.empty) rem_obj;
        fp_valid_intro (rem_obj <: obj_addr) g'
      end
    end
#pop-options

/// After init + alloc, no object is gray.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let init_alloc_no_gray (g: heap) (wz: nat) (obj: obj_addr)
  : Lemma (requires g == Seq.create heap_size 0uy /\
                    (let (g0, fp0) = init_heap_spec g in
                     let r = alloc_spec g0 fp0 wz in
                     Seq.mem obj (objects 0UL r.heap_out)))
          (ensures (let (g0, fp0) = init_heap_spec g in
                    let r = alloc_spec g0 fp0 wz in
                    ~(is_gray obj r.heap_out)))
  = let (g0, fp0) = init_heap_spec g in
    let wz' = if wz = 0 then 1 else wz in
    let bwz = heap_size / U64.v mword - 1 in
    wz_bounds ();
    if wz' > bwz then begin
      init_alloc_oom g wz;
      init_no_gray g;
      no_gray_elim obj g0
    end
    else begin
      init_alloc_spec_unfold g wz;
      let (g', _) = alloc_from_block g0 (mword <: obj_addr) wz' 0UL in
      if bwz - wz' < 2 then begin
        init_alloc_exact_objects g wz;
        init_objects_eq g;
        Seq.lemma_mem_snoc Seq.empty (mword <: hp_addr);
        hd_address_spec (mword <: obj_addr);
        alloc_from_block_exact g0 mword wz' 0UL;
        let ahdr = make_header (U64.uint_to_t bwz) white_bits 0UL in
        read_write_same g0 zero_addr ahdr;
        make_header_getColor_bridge (U64.uint_to_t bwz) white_bits 0UL;
        getColor_raw (read_word g' (hd_address (mword <: obj_addr)));
        color_of_object_spec (mword <: obj_addr) g';
        is_gray_iff (mword <: obj_addr) g'
      end
      else begin
        init_alloc_split_objects g wz;
        init_alloc_split_headers g wz;
        let ron = (2 + wz') * 8 in
        let rem_obj : hp_addr = U64.uint_to_t ron in
        Seq.lemma_mem_snoc (Seq.cons (mword <: hp_addr) Seq.empty) rem_obj;
        Seq.lemma_mem_snoc (Seq.empty #hp_addr) (mword <: hp_addr);
        hd_address_spec (mword <: obj_addr);
        alloc_from_block_split_normal g0 mword wz' 0UL;
        let ahdr = make_header (U64.uint_to_t wz') white_bits 0UL in
        let g1 = write_word g0 zero_addr ahdr in
        let rh : hp_addr = U64.uint_to_t ((1 + wz') * 8) in
        let rhdr = make_header (U64.uint_to_t (bwz - wz' - 1)) blue_bits 0UL in
        let g2 = write_word g1 rh rhdr in
        let ro : hp_addr = U64.uint_to_t ron in
        read_write_different g2 ro zero_addr 0UL;
        read_write_different g1 rh zero_addr rhdr;
        read_write_same g0 zero_addr ahdr;
        make_header_getColor_bridge (U64.uint_to_t wz') white_bits 0UL;
        getColor_raw (read_word g' (hd_address (mword <: obj_addr)));
        color_of_object_spec (mword <: obj_addr) g';
        is_gray_iff (mword <: obj_addr) g';
        if obj = (rem_obj <: obj_addr) then begin
          hd_address_spec rem_obj;
          read_write_different g2 ro rh 0UL;
          read_write_same g1 rh rhdr;
          make_header_getColor_bridge (U64.uint_to_t (bwz - wz' - 1)) blue_bits 0UL;
          getColor_raw (read_word g' (hd_address rem_obj));
          color_of_object_spec rem_obj g';
          is_gray_iff rem_obj g'
        end
      end
    end
#pop-options

/// After init + alloc, mark_inv holds (with empty stack).
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let init_alloc_mark_inv (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy)
          (ensures (let (g0, fp0) = init_heap_spec g in
                    let r = alloc_spec g0 fp0 wz in
                    let st = Seq.empty #obj_addr in
                    mark_inv r.heap_out st))
  = let (g0, fp0) = init_heap_spec g in
    let r = alloc_spec g0 fp0 wz in
    init_wf g;
    alloc_spec_preserves_wf g0 fp0 wz;
    init_alloc_dense g wz;
    init_alloc_objects_nonempty g wz;
    let no_gray_all (obj: obj_addr) : Lemma
      (requires Seq.mem obj (objects 0UL r.heap_out))
      (ensures ~(is_gray obj r.heap_out))
    = init_alloc_no_gray g wz obj
    in
    Classical.forall_intro (Classical.move_requires no_gray_all);
    let st = Seq.empty #obj_addr in
    mark_inv_intro r.heap_out st
#pop-options

/// After init + alloc, no_black_objects holds.
#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
let init_alloc_no_black (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy)
          (ensures (let (g0, fp0) = init_heap_spec g in
                    let r = alloc_spec g0 fp0 wz in
                    no_black_objects r.heap_out))
  = init_wf g;
    init_no_black g;
    init_fl_valid g;
    let (g0, fp0) = init_heap_spec g in
    alloc_spec_preserves_no_black g0 fp0 wz
#pop-options

/// =========================================================================
/// Master lemma: init + alloc enables collect
/// =========================================================================

#push-options "--z3rlimit 30 --fuel 1 --ifuel 0"
let init_alloc_enables_collect (g: heap) (wz: nat)
  : Lemma (requires g == Seq.create heap_size 0uy)
          (ensures (let (g0, fp0) = init_heap_spec g in
                    let r = alloc_spec g0 fp0 wz in
                    let st = Seq.empty #obj_addr in
                    mark_inv r.heap_out st /\
                    fp_valid r.fp_out r.heap_out /\
                    root_props r.heap_out st /\
                    fp_in_heap r.fp_out r.heap_out /\
                    no_black_objects r.heap_out /\
                    no_pointer_to_blue r.heap_out /\
                    graph_wf (create_graph r.heap_out) /\
                    is_vertex_set (coerce_to_vertex_list st) /\
                    subset_vertices (coerce_to_vertex_list st) (create_graph r.heap_out).vertices))
  = init_alloc_mark_inv g wz;
    init_alloc_fp_valid g wz;
    init_alloc_fp_in_heap g wz;
    init_alloc_no_black g wz;
    init_alloc_no_pointer_to_blue g wz;
    init_alloc_graph_wf g wz
#pop-options