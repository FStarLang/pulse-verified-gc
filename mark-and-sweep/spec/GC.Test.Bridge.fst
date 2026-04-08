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
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
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
