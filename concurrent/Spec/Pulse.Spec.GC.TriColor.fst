/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.TriColor - 4-Color Tri-Color Invariant for Parallel GC
/// ---------------------------------------------------------------------------
///
/// Extends common/'s 3-color model (White|Gray|Black) with Blue for per-thread
/// parallel marking. Blue acts as a temporary fence during per-thread traversal.
///
/// Key definitions:
///   tri_color_inv: no black object points to a truly-white object (blue OK)
///   is_blue: raw color bits == 3 (bypasses common/'s 3-color abstraction)
///   is_truly_white: white AND NOT blue (raw color bits == 0)
///   makeBlue: set raw color bits to 3
///
/// Key lemmas:
///   make_gray_preserves_tri_color, make_black_preserves_tri_color
///   make_blue_preserves_tri_color, reset_blue_white_preserves_tri_color

module Pulse.Spec.GC.TriColor

open FStar.Seq
open FStar.Classical
open FStar.Mul
module U64 = FStar.UInt64

open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Object
open Pulse.Spec.GC.Fields
open Pulse.Spec.GC.Heap  // After Fields so Heap.hd_address (obj_addr→hp_addr) wins
module Header = Pulse.Lib.Header
module ML = FStar.Math.Lemmas

/// Bridge: getWosize at Object level matches Header.get_wosize at value level
/// Needed because setColor64_preserves_wosize works with Header.get_wosize
private let getWosize_bridge (hdr: U64.t)
  : Lemma (U64.v (getWosize hdr) == Header.get_wosize (U64.v hdr))
  = getWosize_spec hdr;
    // getWosize hdr == U64.shift_right hdr 10ul
    // U64.v (U64.shift_right hdr 10ul) == UInt.shift_right (U64.v hdr) 10
    // UInt.shift_right_value_aux_3: shift_right a s = a / pow2 s (for 0 < s < n)
    FStar.UInt.shift_right_value_aux_3 #64 (U64.v hdr) 10

/// ===========================================================================
/// Section 1.5: Word-Aligned Address Separation
/// ===========================================================================
/// Two distinct hp_addrs (multiples of 8) are >= 8 bytes apart.
/// Needed for read_write_different proofs.

#push-options "--z3rlimit 50"
private let word_aligned_separate (a b: hp_addr)
  : Lemma (requires a <> b)
          (ensures U64.v a + 8 <= U64.v b \/ U64.v b + 8 <= U64.v a)
  = let va = U64.v a in
    let vb = U64.v b in
    let eight : pos = 8 in
    ML.lemma_mod_sub_distr vb va eight;
    ML.lemma_mod_sub_distr va vb eight;
    if vb > va then (
      if vb - va < 8 then ML.small_mod (vb - va) eight
    ) else (
      if va - vb < 8 then ML.small_mod (va - vb) eight
    )
#pop-options

/// ===========================================================================
/// Section 1: 4-Color Type
/// ===========================================================================

type tricolor_sem =
  | TCWhite  // 0 - Not yet visited
  | TCGray   // 1 - Visited but not scanned
  | TCBlack  // 2 - Fully scanned
  | TCBlue   // 3 - Per-thread fence (temporary)

/// ===========================================================================
/// Section 2: Raw Color Access
/// ===========================================================================
/// common/'s color_sem has only 3 constructors; getColor maps raw=3 to White.
/// We define raw-level predicates to distinguish blue from truly-white.

/// Raw 2-bit color value from header (0-3)
let raw_color_of_object (h: obj_addr) (g: heap) : GTot (c:U64.t{U64.v c < 4}) =
  Header.get_color64 (read_word g (hd_address h))

/// Is object blue? (raw color bits == 3)
let is_blue (h: obj_addr) (g: heap) : GTot bool =
  U64.v (raw_color_of_object h g) = 3

/// Is object truly white? (raw color bits == 0, not blue)
/// common/'s is_white returns true for BOTH raw=0 and raw=3.
let is_truly_white (h: obj_addr) (g: heap) : GTot bool =
  is_white h g && not (is_blue h g)

/// ===========================================================================
/// Section 3: Blue Color Operations
/// ===========================================================================

/// Set object color to any raw 2-bit value (0-3)
/// Generalizes common/'s set_object_color (which only accepts color_sem)
let set_object_color_raw (h: obj_addr) (g: heap) (c: U64.t{U64.v c < 4}) : GTot heap =
  let hd_addr = hd_address h in
  let old_header = read_word g hd_addr in
  let new_header = Header.set_color64 old_header c in
  write_word g hd_addr new_header

/// Make object blue (raw color = 3)
let makeBlue (h: obj_addr) (g: heap) : GTot heap =
  set_object_color_raw h g 3UL

/// makeBlue specification
let makeBlue_spec (h: obj_addr) (g: heap)
  : Lemma (makeBlue h g == write_word g (hd_address h) 
             (Header.set_color64 (read_word g (hd_address h)) 3UL))
  = ()

/// ===========================================================================
/// Section 4: Raw Color Characterization
/// ===========================================================================

/// Bridge: is_gray implies raw color == 1 (not blue)
#push-options "--z3rlimit 50"
let is_gray_implies_not_blue (h: obj_addr) (g: heap)
  : Lemma (requires is_gray h g)
          (ensures not (is_blue h g))
  = is_gray_iff h g;
    color_of_object_spec h g;
    let hdr = read_word g (hd_address h) in
    gray_or_black_valid hdr;
    Header.valid_color_unpack (Header.get_color (U64.v hdr));
    Header.unpack_pack_color (Header.get_color (U64.v hdr))
#pop-options

/// Bridge: is_black implies raw color == 2 (not blue)
#push-options "--z3rlimit 50"
let is_black_implies_not_blue (h: obj_addr) (g: heap)
  : Lemma (requires is_black h g)
          (ensures not (is_blue h g))
  = is_black_iff h g;
    color_of_object_spec h g;
    let hdr = read_word g (hd_address h) in
    gray_or_black_valid hdr;
    Header.valid_color_unpack (Header.get_color (U64.v hdr));
    Header.unpack_pack_color (Header.get_color (U64.v hdr))
#pop-options

/// When no blue objects exist, is_truly_white == is_white
let truly_white_eq_white_no_blue (h: obj_addr) (g: heap)
  : Lemma (requires not (is_blue h g))
          (ensures is_truly_white h g <==> is_white h g)
  = ()

/// 4-color exhaustiveness
let colors_exhaustive_4 (h: obj_addr) (g: heap)
  : Lemma (is_black h g \/ is_gray h g \/ is_truly_white h g \/ is_blue h g)
  = colors_exhaustive_and_exclusive h g

/// 4-color exclusiveness: is_blue is disjoint from is_gray and is_black
let colors_exclusive_4 (h: obj_addr) (g: heap)
  : Lemma (
      not (is_black h g && is_blue h g) /\
      not (is_gray h g && is_blue h g) /\
      not (is_truly_white h g && is_blue h g)
    )
  = if is_black h g then is_black_implies_not_blue h g
    else if is_gray h g then is_gray_implies_not_blue h g
    else ()

/// ===========================================================================
/// Section 5: makeBlue Preservation Lemmas
/// ===========================================================================

/// makeBlue preserves heap length
let makeBlue_preserves_length (h: obj_addr) (g: heap)
  : Lemma (Seq.length (makeBlue h g) == Seq.length g)
  = ()

/// makeBlue result is blue
let makeBlue_is_blue (h: obj_addr) (g: heap)
  : Lemma (is_blue h (makeBlue h g))
  = let g' = makeBlue h g in
    let hdr = read_word g (hd_address h) in
    let new_hdr = Header.set_color64 hdr 3UL in
    read_write_same g (hd_address h) new_hdr;
    Header.getColor64_setColor64 hdr 3UL

/// makeBlue result is not truly white
let makeBlue_not_truly_white (h: obj_addr) (g: heap)
  : Lemma (not (is_truly_white h (makeBlue h g)))
  = makeBlue_is_blue h g

/// makeBlue preserves read_word at different addresses
let makeBlue_preserves_other_read (h: obj_addr) (addr: hp_addr) (g: heap)
  : Lemma (requires hd_address h <> addr)
          (ensures read_word (makeBlue h g) addr == read_word g addr)
  = let hdr = read_word g (hd_address h) in
    let new_hdr = Header.set_color64 hdr 3UL in
    word_aligned_separate (hd_address h) addr;
    read_write_different g (hd_address h) addr new_hdr

/// makeBlue preserves color of other objects
let makeBlue_preserves_other_color (h other: obj_addr) (g: heap)
  : Lemma (requires h <> other)
          (ensures color_of_object other (makeBlue h g) == color_of_object other g)
  = hd_address_injective h other;
    makeBlue_preserves_other_read h (hd_address other) g;
    color_of_object_spec other g;
    color_of_object_spec other (makeBlue h g)

/// makeBlue preserves is_black of other objects
let makeBlue_preserves_other_is_black (h other: obj_addr) (g: heap)
  : Lemma (requires h <> other)
          (ensures is_black other (makeBlue h g) == is_black other g)
  = makeBlue_preserves_other_color h other g;
    is_black_iff other g;
    is_black_iff other (makeBlue h g)

/// makeBlue preserves is_truly_white of other objects
let makeBlue_preserves_other_is_truly_white (h other: obj_addr) (g: heap)
  : Lemma (requires h <> other)
          (ensures is_truly_white other (makeBlue h g) == is_truly_white other g)
  = makeBlue_preserves_other_color h other g;
    is_white_iff other g;
    is_white_iff other (makeBlue h g);
    hd_address_injective h other;
    makeBlue_preserves_other_read h (hd_address other) g

/// makeBlue preserves wosize at the modified header
let makeBlue_preserves_wosize_at_hd (h: obj_addr) (g: heap)
  : Lemma (getWosize (read_word (makeBlue h g) (hd_address h)) ==
           getWosize (read_word g (hd_address h)))
  = let hdr = read_word g (hd_address h) in
    let new_hdr = Header.set_color64 hdr 3UL in
    read_write_same g (hd_address h) new_hdr;
    // Need: getWosize new_hdr == getWosize hdr
    // Bridge through Header.get_wosize:
    getWosize_bridge hdr;
    getWosize_bridge new_hdr;
    Header.setColor64_preserves_wosize hdr 3UL;
    U64.v_inj (getWosize new_hdr) (getWosize hdr)

/// makeBlue preserves objects enumeration
/// Proof: same structure as color_change_preserves_objects_aux from common/Fields.
/// The key facts are: (1) read_word at non-header addresses is preserved,
/// (2) getWosize at the modified header is preserved.
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let rec makeBlue_preserves_objects_aux (start: hp_addr) (g: heap) (h: obj_addr)
  : Lemma (ensures objects start (makeBlue h g) == objects start g)
          (decreases (Seq.length g - U64.v start))
  = let g' = makeBlue h g in
    if U64.v start + 8 >= Seq.length g then begin
      makeBlue_preserves_length h g;
      ()
    end
    else begin
      // Read word at start: same if start ≠ hd_address h, wosize preserved if equal
      (if hd_address h = start then begin
        makeBlue_preserves_wosize_at_hd h g;
        let hdr = read_word g (hd_address h) in
        let new_hdr = Header.set_color64 hdr 3UL in
        read_write_same g (hd_address h) new_hdr
      end else
        makeBlue_preserves_other_read h start g);
      let wz = getWosize (read_word g start) in
      let next_start_nat = U64.v start + (U64.v wz + 1) * 8 in
      if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then ()
      else if next_start_nat >= heap_size then ()
      else begin
        makeBlue_preserves_length h g;
        makeBlue_preserves_objects_aux (U64.uint_to_t next_start_nat) g h
      end
    end
#pop-options

let makeBlue_preserves_objects (h: obj_addr) (g: heap)
  : Lemma (objects zero_addr (makeBlue h g) == objects zero_addr g)
  = makeBlue_preserves_objects_aux 0UL g h

let makeBlue_preserves_objects_mem (h: obj_addr) (g: heap) (x: obj_addr)
  : Lemma (Seq.mem x (objects zero_addr (makeBlue h g)) <==> Seq.mem x (objects zero_addr g))
  = makeBlue_preserves_objects h g

/// Is object blue (free/unallocated)? Checks raw color bits for value 3.
let is_blue (obj: obj_addr) (g: heap) : GTot bool =
  Header.get_color (U64.v (read_word g (hd_address obj))) = 3

/// ---------------------------------------------------------------------------
/// makeBlue field address separation and points_to preservation
/// ---------------------------------------------------------------------------

/// Helper: mul_mod doesn't overflow for field indices < pow2 54
private let mul_mod_field_idx (idx: U64.t{U64.v idx < pow2 54})
  : Lemma (U64.v (U64.mul_mod idx mword) == FStar.Mul.(U64.v idx * U64.v mword))
  = ML.pow2_lt_compat 57 54;
    assert (FStar.Mul.(U64.v idx * 8) < pow2 57);
    ML.pow2_lt_compat 64 57;
    ML.modulo_lemma (FStar.Mul.(U64.v idx * 8)) (pow2 64)

/// Field address of src does not equal hd_address of h (when src ≠ h, well-formed, both in objects)
private let field_addr_ne_hd (g: heap) (src h: obj_addr)
  (idx: U64.t{U64.v idx < pow2 54})
  : Lemma (requires src <> h /\
                    well_formed_heap g /\
                    Seq.mem src (objects zero_addr g) /\ Seq.mem h (objects zero_addr g) /\
                    U64.v idx < U64.v (wosize_of_object_as_wosize src g) /\
                    U64.v (field_address_raw src idx) < heap_size /\
                    U64.v (field_address_raw src idx) % 8 = 0)
          (ensures field_address_raw src idx <> hd_address h)
  = hd_address_spec h;
    ML.pow2_lt_compat 61 54;
    mul_mod_field_idx idx;
    wf_object_bound g src;
    wosize_of_object_spec src g;
    if U64.v src < U64.v h then begin
      objects_separated 0UL g src h;
      // h > src + wosize*8, so hd_address h = h-8 >= src + wosize*8
      // field_address_raw src idx = src + idx*8 <= src + (wosize-1)*8 < src + wosize*8
      ()
    end else begin
      objects_separated 0UL g h src;
      // src > h + wosize_h*8 > h > h-8 = hd_address h
      // field_address_raw src idx = src + idx*8 >= src > hd_address h
      ()
    end

/// Recursive helper: writing at hd_address h preserves exists_field_pointing_to_unchecked for other objects
#push-options "--z3rlimit 300 --fuel 2 --ifuel 1"
private let rec write_at_hd_preserves_efptu
  (g: heap) (h: obj_addr) (v: U64.t) (src: obj_addr)
  (wz: U64.t{U64.v wz < pow2 54}) (target: hp_addr)
  : Lemma (requires src <> h /\ well_formed_heap g /\
                    Seq.mem src (objects zero_addr g) /\ Seq.mem h (objects zero_addr g) /\
                    U64.v wz <= U64.v (wosize_of_object_as_wosize src g))
          (ensures exists_field_pointing_to_unchecked (write_word g (hd_address h) v) src wz target
                   == exists_field_pointing_to_unchecked g src wz target)
          (decreases U64.v wz)
  = if wz = 0UL then ()
    else begin
      let idx = U64.sub wz 1UL in
      ML.pow2_lt_compat 61 54;
      mul_mod_field_idx idx;
      let far = U64.add_mod src (U64.mul_mod idx mword) in
      if U64.v far >= heap_size || U64.v far % 8 <> 0 then ()
      else begin
        let field_addr : hp_addr = far in
        field_addr_ne_hd g src h idx;
        word_aligned_separate field_addr (hd_address h);
        read_write_different g (hd_address h) field_addr v;
        write_at_hd_preserves_efptu g h v src idx target
      end
    end
#pop-options

/// makeBlue preserves wosize_of_object for other objects
private let makeBlue_preserves_wosize_other (h other: obj_addr) (g: heap)
  : Lemma (requires h <> other)
          (ensures wosize_of_object other (makeBlue h g) == wosize_of_object other g)
  = wosize_of_object_spec other g;
    wosize_of_object_spec other (makeBlue h g);
    hd_address_injective h other;
    makeBlue_preserves_other_read h (hd_address other) g

/// makeBlue preserves wosize_of_object for the blue object itself
private let makeBlue_preserves_wosize_self (h: obj_addr) (g: heap)
  : Lemma (wosize_of_object h (makeBlue h g) == wosize_of_object h g)
  = wosize_of_object_spec h g;
    wosize_of_object_spec h (makeBlue h g);
    makeBlue_preserves_wosize_at_hd h g

/// makeBlue preserves points_to for other source objects
let makeBlue_preserves_points_to_other (h src dst: obj_addr) (g: heap)
  : Lemma (requires src <> h /\ well_formed_heap g /\
                    Seq.mem src (objects zero_addr g) /\ Seq.mem h (objects zero_addr g))
          (ensures points_to (makeBlue h g) src dst == points_to g src dst)
  = makeBlue_preserves_wosize_other h src g;
    wosize_of_object_bound src g;
    let wz = wosize_of_object src g in
    let hdr = read_word g (hd_address h) in
    let new_hdr = Header.set_color64 hdr 3UL in
    write_at_hd_preserves_efptu g h new_hdr src wz dst

/// Recursive helper: writing at hd_address h preserves exists_field_pointing_to_unchecked for h itself
/// (since fields of h are at addresses h, h+8, ..., all > hd_address h = h-8)
#push-options "--z3rlimit 300 --fuel 2 --ifuel 1"
private let rec write_at_own_hd_preserves_efptu
  (g: heap) (h: obj_addr) (v: U64.t)
  (wz: U64.t{U64.v wz < pow2 54}) (target: hp_addr)
  : Lemma (requires well_formed_heap g /\
                    Seq.mem h (objects zero_addr g) /\
                    U64.v wz <= U64.v (wosize_of_object_as_wosize h g))
          (ensures exists_field_pointing_to_unchecked (write_word g (hd_address h) v) h wz target
                   == exists_field_pointing_to_unchecked g h wz target)
          (decreases U64.v wz)
  = if wz = 0UL then ()
    else begin
      let idx = U64.sub wz 1UL in
      ML.pow2_lt_compat 61 54;
      mul_mod_field_idx idx;
      let far = U64.add_mod h (U64.mul_mod idx mword) in
      if U64.v far >= heap_size || U64.v far % 8 <> 0 then ()
      else begin
        let field_addr : hp_addr = far in
        // field_addr = h + idx*8 >= h > h - 8 = hd_address h
        hd_address_spec h;
        assert (U64.v field_addr >= U64.v h);
        assert (U64.v (hd_address h) = U64.v h - 8);
        assert (U64.v field_addr > U64.v (hd_address h));
        word_aligned_separate field_addr (hd_address h);
        read_write_different g (hd_address h) field_addr v;
        write_at_own_hd_preserves_efptu g h v idx target
      end
    end
#pop-options

/// makeBlue preserves points_to for the modified object (color doesn't affect fields)
let makeBlue_preserves_points_to_self (h dst: obj_addr) (g: heap)
  : Lemma (requires well_formed_heap g /\ Seq.mem h (objects zero_addr g))
          (ensures points_to (makeBlue h g) h dst == points_to g h dst)
  = makeBlue_preserves_wosize_self h g;
    wosize_of_object_bound h g;
    let wz = wosize_of_object h g in
    let hdr = read_word g (hd_address h) in
    let new_hdr = Header.set_color64 hdr 3UL in
    write_at_own_hd_preserves_efptu g h new_hdr wz dst

/// ===========================================================================
/// Section 6: Reset Blue → White Preservation
/// ===========================================================================

/// Reset a blue object back to white
let resetBlue (h: obj_addr) (g: heap) : GTot heap =
  makeWhite h g

/// resetBlue turns a blue object into a truly-white object
let resetBlue_is_truly_white (h: obj_addr) (g: heap)
  : Lemma (requires is_blue h g)
          (ensures is_truly_white h (resetBlue h g))
  = makeWhite_is_white h g;
    makeWhite_spec h g;
    let hdr = read_word g (hd_address h) in
    let new_hdr = colorHeader hdr Header.White in
    read_write_same g (hd_address h) new_hdr;
    colorHeader_spec hdr Header.White;
    Header.getColor64_setColor64 hdr (U64.uint_to_t (Header.pack_color Header.White))

/// ===========================================================================
/// Section 7: Tri-Color Invariant (4-Color Aware)
/// ===========================================================================

/// The strong tri-color invariant for the 4-color model:
/// No black object points to a truly-white object.
/// Blue targets are allowed (they represent per-thread fences).
let tri_color_inv (g: heap) : prop =
  let objs = objects zero_addr g in
  forall (obj: obj_addr). Seq.mem obj objs ==>
    (is_black obj g ==>
      (forall (child: obj_addr).
        points_to g obj child ==>
        not (is_truly_white child g)))

/// No blue objects in heap (quantifies over ALL obj_addrs, not just objects members)
let no_blue_objects (g: heap) : prop =
  forall (obj: obj_addr). not (is_blue obj g)

/// When no blue objects exist, tri_color_inv reduces to:
/// no black→white edges (the classical 3-color invariant)
let tri_color_inv_no_blue (g: heap)
  : Lemma (requires tri_color_inv g /\ no_blue_objects g)
          (ensures forall (obj: obj_addr). Seq.mem obj (objects zero_addr g) ==>
            (is_black obj g ==>
              (forall (child: obj_addr). points_to g obj child ==>
                not (is_white child g))))
  = let aux (obj: obj_addr) : Lemma
      (requires Seq.mem obj (objects zero_addr g) /\ is_black obj g)
      (ensures forall (child: obj_addr). points_to g obj child ==> not (is_white child g))
    = let child_aux (child: obj_addr) : Lemma
        (requires points_to g obj child)
        (ensures not (is_white child g))
      = ()
      in
      forall_intro (move_requires child_aux)
    in
    forall_intro (move_requires aux)

/// ===========================================================================
/// Section 8: Helper Predicates
/// ===========================================================================

/// No gray objects remain (mark phase complete)
let no_gray_objects (g: heap) : prop =
  let objs = objects zero_addr g in
  forall (obj: obj_addr). Seq.mem obj objs ==>
    not (is_gray obj g)

/// ===========================================================================
/// Section 9: Invariant Preservation Lemmas
/// ===========================================================================

/// ---------------------------------------------------------------------------
/// 9.1: White → Gray preserves tri-color invariant
/// ---------------------------------------------------------------------------

val make_gray_preserves_tri_color : (g: heap) -> (w_addr: obj_addr) ->
  Lemma (requires well_formed_heap g /\ tri_color_inv g /\ is_truly_white w_addr g /\
                  Seq.mem w_addr (objects zero_addr g))
        (ensures tri_color_inv (makeGray w_addr g))

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1 --split_queries always"
let make_gray_preserves_tri_color g w_addr =
  makeGray_eq w_addr g;
  color_change_preserves_objects g w_addr Header.Gray;
  let g' = makeGray w_addr g in
  let objs = objects zero_addr g in
  let aux (obj: obj_addr) : Lemma
    (requires Seq.mem obj objs)
    (ensures is_black obj g' ==>
      (forall (child: obj_addr). points_to g' obj child ==> not (is_truly_white child g')))
  = if obj = w_addr then begin
      // w_addr is now gray (not black) → vacuous
      makeGray_is_gray w_addr g;
      colors_exhaustive_and_exclusive w_addr g'
    end else begin
      color_change_preserves_other_color w_addr obj g Header.Gray;
      is_black_iff obj g;
      is_black_iff obj g';
      color_change_preserves_objects_mem g w_addr Header.Gray obj;
      if not (is_black obj g') then ()
      else begin
        let pt_preserved (child: obj_addr) : Lemma
          (points_to g' obj child == points_to g obj child)
        = color_change_preserves_points_to_other g w_addr Header.Gray obj child
        in
        forall_intro pt_preserved;
        let child_not_tw (child: obj_addr) : Lemma
          (requires points_to g' obj child)
          (ensures not (is_truly_white child g'))
        = pt_preserved child;
          if child = w_addr then begin
            makeGray_is_gray w_addr g;
            is_gray_implies_not_blue child g';
            colors_exhaustive_and_exclusive child g'
          end else begin
            color_change_preserves_other_color w_addr child g Header.Gray;
            is_white_iff child g;
            is_white_iff child g';
            // is_blue preserved: raw color at child unchanged because header unchanged
            hd_address_injective w_addr child;
            color_change_header_locality w_addr (hd_address child) g Header.Gray;
            // Now SMT knows: read_word g' (hd_address child) == read_word g (hd_address child)
            // So raw_color_of_object child g' == raw_color_of_object child g
            // And is_blue child g' == is_blue child g
            assert (read_word g' (hd_address child) == read_word g (hd_address child));
            assert (is_blue child g' == is_blue child g)
          end
        in
        forall_intro (move_requires child_not_tw)
      end
    end
  in
  forall_intro (move_requires aux);
  assert (objects zero_addr g' == objs)
#pop-options

/// ---------------------------------------------------------------------------
/// 9.2: Gray → Black preserves tri-color invariant
/// ---------------------------------------------------------------------------

val make_black_preserves_tri_color : (g: heap) -> (gr_addr: obj_addr) ->
  Lemma (requires well_formed_heap g /\ tri_color_inv g /\ is_gray gr_addr g /\
                  Seq.mem gr_addr (objects zero_addr g) /\
                  (forall (child: obj_addr).
                    points_to g gr_addr child ==>
                    (is_gray child g \/ is_black child g)))
        (ensures tri_color_inv (makeBlack gr_addr g))

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1 --split_queries always"
let make_black_preserves_tri_color g gr_addr =
  makeBlack_eq gr_addr g;
  color_change_preserves_objects g gr_addr Header.Black;
  let g' = makeBlack gr_addr g in
  let objs = objects zero_addr g in
  let aux (obj: obj_addr) : Lemma
    (requires Seq.mem obj objs)
    (ensures is_black obj g' ==>
      (forall (child: obj_addr). points_to g' obj child ==> not (is_truly_white child g')))
  = if obj = gr_addr then begin
      if not (is_black obj g') then ()
      else begin
        let pt_preserved (child: obj_addr) : Lemma
          (points_to g' gr_addr child == points_to g gr_addr child)
        = color_change_preserves_points_to_self g gr_addr Header.Black child
        in
        forall_intro pt_preserved;
        let child_not_tw (child: obj_addr) : Lemma
          (requires points_to g' gr_addr child)
          (ensures not (is_truly_white child g'))
        = pt_preserved child;
          if child = gr_addr then begin
            makeBlack_is_black gr_addr g;
            is_black_implies_not_blue child g';
            colors_exhaustive_and_exclusive child g'
          end else begin
            color_change_preserves_other_color gr_addr child g Header.Black;
            is_white_iff child g;
            is_white_iff child g';
            is_gray_iff child g;
            is_black_iff child g;
            hd_address_injective gr_addr child;
            color_change_header_locality gr_addr (hd_address child) g Header.Black;
            assert (read_word g' (hd_address child) == read_word g (hd_address child));
            assert (is_blue child g' == is_blue child g)
          end
        in
        forall_intro (move_requires child_not_tw)
      end
    end else begin
      color_change_preserves_other_color gr_addr obj g Header.Black;
      is_black_iff obj g;
      is_black_iff obj g';
      if not (is_black obj g') then ()
      else begin
        color_change_preserves_objects_mem g gr_addr Header.Black obj;
        let pt_preserved (child: obj_addr) : Lemma
          (points_to g' obj child == points_to g obj child)
        = color_change_preserves_points_to_other g gr_addr Header.Black obj child
        in
        forall_intro pt_preserved;
        let child_not_tw (child: obj_addr) : Lemma
          (requires points_to g' obj child)
          (ensures not (is_truly_white child g'))
        = pt_preserved child;
          if child = gr_addr then begin
            makeBlack_is_black gr_addr g;
            is_black_implies_not_blue child g';
            colors_exhaustive_and_exclusive child g'
          end else begin
            color_change_preserves_other_color gr_addr child g Header.Black;
            is_white_iff child g;
            is_white_iff child g';
            hd_address_injective gr_addr child;
            color_change_header_locality gr_addr (hd_address child) g Header.Black;
            assert (read_word g' (hd_address child) == read_word g (hd_address child));
            assert (is_blue child g' == is_blue child g)
          end
        in
        forall_intro (move_requires child_not_tw)
      end
    end
  in
  forall_intro (move_requires aux);
  assert (objects zero_addr g' == objs)
#pop-options

/// ---------------------------------------------------------------------------
/// 9.3: White → Blue preserves tri-color invariant
/// ---------------------------------------------------------------------------

/// Making a truly-white object blue preserves tri-color invariant.
/// Blue is not truly-white, so any black→truly_white edge TO w_addr is eliminated.
/// No new black→truly_white edges are created (blue is not black).
val make_blue_preserves_tri_color : (g: heap) -> (w_addr: obj_addr) ->
  Lemma (requires well_formed_heap g /\ tri_color_inv g /\ is_truly_white w_addr g /\
                  Seq.mem w_addr (objects zero_addr g))
        (ensures tri_color_inv (makeBlue w_addr g))

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1 --split_queries always"
let make_blue_preserves_tri_color g w_addr =
  makeBlue_preserves_objects w_addr g;
  let g' = makeBlue w_addr g in
  let objs = objects zero_addr g in
  let aux (obj: obj_addr) : Lemma
    (requires Seq.mem obj objs)
    (ensures is_black obj g' ==>
      (forall (child: obj_addr). points_to g' obj child ==> not (is_truly_white child g')))
  = if obj = w_addr then begin
      // w_addr is now blue (not black) → vacuous
      makeBlue_is_blue w_addr g;
      colors_exclusive_4 w_addr g'
    end else begin
      makeBlue_preserves_other_is_black w_addr obj g;
      if not (is_black obj g') then ()
      else begin
        let child_not_tw (child: obj_addr) : Lemma
          (requires points_to g' obj child)
          (ensures not (is_truly_white child g'))
        = makeBlue_preserves_points_to_other w_addr obj child g;
          if child = w_addr then
            makeBlue_not_truly_white w_addr g
          else
            makeBlue_preserves_other_is_truly_white w_addr child g
        in
        forall_intro (move_requires child_not_tw)
      end
    end
  in
  forall_intro (move_requires aux);
  assert (objects zero_addr g' == objs)
#pop-options

/// ---------------------------------------------------------------------------
/// 9.4: Blue → White preserves tri-color invariant
/// ---------------------------------------------------------------------------

/// Resetting a blue object to white preserves tri-color invariant,
/// PROVIDED no black object points to it.
/// This is safe when: (a) the blue object has no incoming edges from black objects,
/// or (b) all black objects pointing to it were marked in a prior pass.
///
/// Precondition: no black object in the heap points to b_addr.
val reset_blue_white_preserves_tri_color : (g: heap) -> (b_addr: obj_addr) ->
  Lemma (requires well_formed_heap g /\ tri_color_inv g /\ is_blue b_addr g /\
                  Seq.mem b_addr (objects zero_addr g) /\
                  (forall (obj: obj_addr). Seq.mem obj (objects zero_addr g) ==>
                    is_black obj g ==> not (points_to g obj b_addr)))
        (ensures tri_color_inv (resetBlue b_addr g))

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1 --split_queries always"
let reset_blue_white_preserves_tri_color g b_addr =
  let g' = resetBlue b_addr g in
  makeWhite_eq b_addr g;
  color_change_preserves_objects g b_addr Header.White;
  let objs = objects zero_addr g in
  let aux (obj: obj_addr) : Lemma
    (requires Seq.mem obj objs)
    (ensures is_black obj g' ==>
      (forall (child: obj_addr). points_to g' obj child ==> not (is_truly_white child g')))
  = if obj = b_addr then begin
      // b_addr becomes white (not black) → vacuous
      makeWhite_is_white b_addr g;
      colors_exhaustive_and_exclusive b_addr g'
    end else begin
      color_change_preserves_other_color b_addr obj g Header.White;
      is_black_iff obj g;
      is_black_iff obj g';
      if not (is_black obj g') then ()
      else begin
        let child_not_tw (child: obj_addr) : Lemma
          (requires points_to g' obj child)
          (ensures not (is_truly_white child g'))
        = color_change_preserves_points_to_other g b_addr Header.White obj child;
          if child = b_addr then begin
            // obj is black and points to b_addr
            // But precondition says no black object points to b_addr
            // So this case is impossible
            assert (points_to g obj b_addr);
            assert (is_black obj g);
            ()  // contradiction with precondition
          end else begin
            color_change_preserves_other_color b_addr child g Header.White;
            is_white_iff child g;
            is_white_iff child g';
            hd_address_injective b_addr child;
            color_change_header_locality b_addr (hd_address child) g Header.White;
            assert (read_word g' (hd_address child) == read_word g (hd_address child));
            assert (is_blue child g' == is_blue child g)
          end
        in
        forall_intro (move_requires child_not_tw)
      end
    end
  in
  forall_intro (move_requires aux);
  assert (objects zero_addr g' == objs)
#pop-options

/// ---------------------------------------------------------------------------
/// 9.5: Write barrier preserves tri-color invariant
/// ---------------------------------------------------------------------------

val write_barrier_preserves_tri_color :
  (g: heap) -> (src_black: obj_addr) -> (dst: obj_addr) ->
  Lemma (requires well_formed_heap g /\ tri_color_inv g /\ is_black src_black g /\
                  Seq.mem dst (objects zero_addr g))
        (ensures tri_color_inv (if is_truly_white dst g then makeGray dst g else g))

let write_barrier_preserves_tri_color g src_black dst =
  if is_truly_white dst g then
    make_gray_preserves_tri_color g dst
  else ()

/// ---------------------------------------------------------------------------
/// 9.6: Initial state satisfies tri-color invariant
/// ---------------------------------------------------------------------------

val initial_heap_satisfies_tri_color : (g: heap) ->
  Lemma (requires forall (obj: obj_addr).
                    Seq.mem obj (objects zero_addr g) ==> is_white obj g)
        (ensures tri_color_inv g)

let initial_heap_satisfies_tri_color g =
  let objs = objects zero_addr g in
  let aux (obj: obj_addr) : Lemma
    (requires Seq.mem obj objs)
    (ensures is_black obj g ==>
      (forall (child: obj_addr). points_to g obj child ==> not (is_truly_white child g)))
  = colors_exhaustive_and_exclusive obj g
  in
  forall_intro (move_requires aux)

/// ===========================================================================
/// Section 10: Mark Completion
/// ===========================================================================

/// After mark completes (no gray objects), each object is black, truly-white, or blue
val mark_complete_partition : (g: heap) ->
  Lemma (requires tri_color_inv g /\ no_gray_objects g)
        (ensures forall (obj: obj_addr).
                   Seq.mem obj (objects zero_addr g) ==>
                   is_black obj g \/ is_truly_white obj g \/ is_blue obj g)

let mark_complete_partition g =
  let aux (obj: obj_addr) : Lemma
    (requires Seq.mem obj (objects zero_addr g))
    (ensures is_black obj g \/ is_truly_white obj g \/ is_blue obj g)
  = colors_exhaustive_4 obj g
  in
  forall_intro (move_requires aux)
