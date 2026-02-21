/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.Object - Object Predicates for Concurrent GC
/// ---------------------------------------------------------------------------
///
/// This module provides object color predicates and header manipulation:
/// - is_black, is_white, is_gray: color predicates
/// - getColor, getWosize, getTag: header field extraction
/// - makeGray, makeBlack: color mutation operations

module Pulse.Spec.GC.Object

open FStar.Seq
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module UInt = FStar.UInt

open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Heap
open Pulse.Lib.Header

/// ---------------------------------------------------------------------------
/// Tag Constants
/// ---------------------------------------------------------------------------

let closure_tag : U64.t = 247UL
let infix_tag : U64.t = 249UL
let no_scan_tag : U64.t = 251UL

let no_scan_tag_val () : Lemma (no_scan_tag == U64.uint_to_t 251) = ()

/// ---------------------------------------------------------------------------
/// Header Masks and Shifts (kept for wosize extraction)
/// ---------------------------------------------------------------------------

let color_mask : U64.t = 0x300UL  // bits 8-9
let color_shift : U32.t = 8ul     // shift amount for color
let tag_mask : U64.t = 0xFFUL     // bits 0-7
let wosize_shift : U32.t = 10ul   // shift amount for wosize

/// ---------------------------------------------------------------------------
/// Header Field Extraction
/// ---------------------------------------------------------------------------

/// Helper: prove multiplication bound
private let field_offset_bound (field_idx: U64.t{U64.v field_idx < pow2 61}) : Lemma 
  (FStar.UInt.size FStar.Mul.(U64.v field_idx * 8) 64)
= 
  FStar.Math.Lemmas.pow2_plus 61 3;
  assert (FStar.Mul.(pow2 61 * pow2 3) == pow2 64);
  assert (FStar.Mul.(U64.v field_idx * 8) < pow2 64)

/// Convert address to field offset
let field_offset (field_idx: U64.t{U64.v field_idx < pow2 61}) : U64.t = 
  field_offset_bound field_idx;
  U64.mul field_idx mword

/// Field address calculation
let field_address (obj_addr: U64.t) (field_idx: U64.t{U64.v field_idx < pow2 61}) : U64.t =
  U64.add_mod obj_addr (field_offset field_idx)

/// Get color from header word (using Header.fst)
let getColor (header: U64.t) : color =
  get_color_bound (U64.v header);
  match unpack_color (get_color (U64.v header)) with
  | Some c -> c
  | None -> White  // Invalid defaults to White

/// Color encoding: White=0, Gray=1, Blue=2, Black=3 (matches OCaml 4.14)

/// getColor characterization in terms of raw color bits
let getColor_raw (hdr: U64.t)
  : Lemma (
      let c = get_color (U64.v hdr) in
      (c = 0 ==> getColor hdr = White) /\
      (c = 1 ==> getColor hdr = Gray) /\
      (c = 2 ==> getColor hdr = Blue) /\
      (c = 3 ==> getColor hdr = Black))
  = get_color_bound (U64.v hdr)

let getColor_spec hdr = ()

/// Gray or Black headers are always valid (have valid color bits)
let gray_or_black_valid (hdr: U64.t)
  : Lemma (requires getColor hdr == Gray \/ getColor hdr == Black)
          (ensures valid_header64 hdr)
  = valid_color_unpack (get_color (U64.v hdr))

/// Get tag from header word
#push-options "--z3rlimit 50"
let getTag (header: U64.t) : (t:U64.t{U64.v t < 256}) =
  get_tag_bound (U64.v header);
  U64.logand header tag_mask
#pop-options

let getTag_bound (hdr: U64.t) : Lemma (U64.v (getTag hdr) < 256) =
  get_tag_bound (U64.v hdr)

/// Helper lemma: shifting right by 10 gives a value < pow2 54
let wosize_shift_lemma (header: U64.t) 
  : Lemma (U64.v (U64.shift_right header wosize_shift) < pow2 54)
  =
  // Shifting right by n bits divides by 2^n (rounded down)
  // So shift_right header 10 gives us a value <= header / 2^10
  // Since header < 2^64, we have header / 2^10 < 2^64 / 2^10 = 2^54
  FStar.UInt.shift_right_value_lemma #64 (U64.v header) (U32.v wosize_shift);
  FStar.Math.Lemmas.pow2_plus 10 54;
  // pow2 10 * pow2 54 = pow2 64
  // header < pow2 64, so header / pow2 10 < pow2 54
  ()

/// Get word size from header word
let getWosize (header: U64.t) : wosize =
  wosize_shift_lemma header;
  U64.shift_right header wosize_shift

let getWosize_spec (hdr: U64.t) : Lemma (getWosize hdr == U64.shift_right hdr 10ul) = ()

let getTag_spec (hdr: U64.t) : Lemma (getTag hdr == U64.logand hdr 0xFFUL) = ()

/// getWosize returns a value < 2^54
let getWosize_bound (hdr: U64.t) : Lemma (U64.v (getWosize hdr) < pow2 54) = 
  wosize_shift_lemma hdr

/// ---------------------------------------------------------------------------
/// Header Construction
/// ---------------------------------------------------------------------------

/// Make a header from components (uses Header.fst pack)
let makeHeader (wz: wosize) (c: color) (tag: U64.t{U64.v tag < 256}) : U64.t =
  get_wosize_bound (U64.v (pack_header64 { wosize = U64.v wz; color = c; tag = U64.v tag }));
  pack_header64 { wosize = U64.v wz; color = c; tag = U64.v tag }

/// Change color in header (uses Header.fst set_color)
let colorHeader (header: U64.t) (new_color: color) : U64.t =
  set_color64 header (U64.uint_to_t (pack_color new_color))

/// colorHeader definition exposed for bridging
let colorHeader_spec (hdr: U64.t) (c: color)
  : Lemma (colorHeader hdr c == set_color64 hdr (U64.uint_to_t (pack_color c)))
  = ()

/// setColor for backwards compatibility (takes packed color)
let setColor (hdr: U64.t) (c: U64.t{U64.v c < 4}) : U64.t =
  set_color64 hdr c

/// ---------------------------------------------------------------------------
/// Core Bitwise Lemmas (now proven via Header.fst!)
/// ---------------------------------------------------------------------------

/// setColor followed by getColor returns the color
let getColor_setColor_packed (hdr: U64.t) (c: U64.t{U64.v c < 4}) 
  : Lemma (get_color (U64.v (setColor hdr c)) == U64.v c) = 
  getColor_setColor (U64.v hdr) (U64.v c)

/// colorHeader followed by getColor returns the color
let colorHeader_getColor (hdr: U64.t) (c: color)
  : Lemma (getColor (colorHeader hdr c) == c) =
  getColor_setColor (U64.v hdr) (pack_color c);
  pack_unpack_color c

/// Helper: U64.shift_right matches UInt.shift_right
private let shift_right_equiv (x: U64.t) (n: U32.t{U32.v n < 64}) 
  : Lemma (U64.v (U64.shift_right x n) == UInt.shift_right #64 (U64.v x) (U32.v n))
  = ()

/// Helper: U64.logand matches UInt.logand
private let logand_equiv (x y: U64.t) 
  : Lemma (U64.v (U64.logand x y) == UInt.logand #64 (U64.v x) (U64.v y))
  = ()

/// Helper: setColor produces set_color on values
private let setColor_value (hdr: U64.t) (c: U64.t{U64.v c < 4})
  : Lemma (U64.v (setColor hdr c) == Pulse.Lib.Header.set_color (U64.v hdr) (U64.v c))
  = U64.vu_inv (Pulse.Lib.Header.set_color (U64.v hdr) (U64.v c))

/// Helper: getWosize matches Header.get_wosize  
private let getWosize_Header (hdr: U64.t)
  : Lemma (U64.v (getWosize hdr) == Pulse.Lib.Header.get_wosize (U64.v hdr))
  = shift_right_equiv hdr wosize_shift

/// Helper: getTag matches Header.get_tag
private let getTag_Header (hdr: U64.t)
  : Lemma (U64.v (getTag hdr) == Pulse.Lib.Header.get_tag (U64.v hdr))
  = logand_equiv hdr tag_mask;
    // tag_mask = 0xFFUL = 255
    // Header.get_tag v = logand v mask_tag where mask_tag = 255
    Pulse.Lib.Header.mask_tag_value ();
    assert (U64.v tag_mask == Pulse.Lib.Header.mask_tag)

/// setColor preserves wosize (fully proven!)
#push-options "--z3rlimit 100"
let setColor_preserves_wosize_lemma (hdr: U64.t) (c: U64.t{U64.v c < 4}) 
  : Lemma (getWosize (setColor hdr c) == getWosize hdr) = 
  // Step 1: Connect setColor to Header.set_color
  setColor_value hdr c;
  // Now: U64.v (setColor hdr c) == set_color (U64.v hdr) (U64.v c)
  
  // Step 2: Use Header lemma
  Pulse.Lib.Header.setColor_preserves_wosize (U64.v hdr) (U64.v c);
  // Now: get_wosize (set_color (U64.v hdr) (U64.v c)) == get_wosize (U64.v hdr)
  
  // Step 3: Connect getWosize to Header.get_wosize
  getWosize_Header (setColor hdr c);
  getWosize_Header hdr;
  // Now: U64.v (getWosize (setColor hdr c)) == get_wosize (U64.v (setColor hdr c))
  //      U64.v (getWosize hdr) == get_wosize (U64.v hdr)
  
  // Combine: U64.v (getWosize (setColor hdr c)) == U64.v (getWosize hdr)
  // Therefore: getWosize (setColor hdr c) == getWosize hdr
  U64.v_inj (getWosize (setColor hdr c)) (getWosize hdr)
#pop-options

/// setColor preserves tag (fully proven!)
#push-options "--z3rlimit 100"
let setColor_preserves_tag_lemma (hdr: U64.t) (c: U64.t{U64.v c < 4}) 
  : Lemma (getTag (setColor hdr c) == getTag hdr) = 
  // Step 1: Connect setColor to Header.set_color  
  setColor_value hdr c;
  
  // Step 2: Use Header lemma
  Pulse.Lib.Header.setColor_preserves_tag (U64.v hdr) (U64.v c);
  
  // Step 3: Connect getTag to Header.get_tag
  getTag_Header (setColor hdr c);
  getTag_Header hdr;
  
  // Combine
  U64.v_inj (getTag (setColor hdr c)) (getTag hdr)
#pop-options

/// colorHeader preserves getWosize (exposed via .fsti for use in Fields)
let colorHeader_preserves_wosize (hdr: U64.t) (c: color)
  : Lemma (getWosize (colorHeader hdr c) == getWosize hdr) =
  let packed_c = U64.uint_to_t (pack_color c) in
  setColor_preserves_wosize_lemma hdr packed_c

/// colorHeader preserves getTag (exposed via .fsti for use in Fields)
let colorHeader_preserves_tag (hdr: U64.t) (c: color)
  : Lemma (getTag (colorHeader hdr c) == getTag hdr) =
  let packed_c = U64.uint_to_t (pack_color c) in
  setColor_preserves_tag_lemma hdr packed_c

/// makeHeader from extracted fields with new color == colorHeader
/// Requires valid header (color field < 3)
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
let makeHeader_eq_colorHeader (hdr: U64.t) (c: color)
  : Lemma (requires valid_header64 hdr)
          (ensures makeHeader (getWosize hdr) c (getTag hdr) == colorHeader hdr c)
  = getWosize_Header hdr;
    getTag_Header hdr;
    repack_set_color64 hdr c
#pop-options

/// Helper: word-aligned addresses that differ are separated by >= 8 bytes
/// This makes the "else" branch unreachable in read_write_different proofs
#push-options "--z3rlimit 50"
private let word_aligned_separate (a b: hp_addr)
  : Lemma (requires a <> b)
          (ensures U64.v a + 8 <= U64.v b \/ U64.v b + 8 <= U64.v a)
  = // Both a and b are multiples of 8 (by hp_addr type)
    let va = U64.v a in
    let vb = U64.v b in
    // Both are multiples of 8
    assert (va % 8 == 0);
    assert (vb % 8 == 0);
    // Difference is multiple of 8
    // (vb - va) % 8 == (vb - (va % 8)) % 8 == (vb - 0) % 8 == vb % 8 == 0
    let eight : pos = 8 in
    FStar.Math.Lemmas.lemma_mod_sub_distr vb va eight;
    // Now we know (vb - va) % 8 == (vb - 0) % 8 == vb % 8 == 0
    assert ((vb - va) % 8 == 0);
    // Similarly for (va - vb)
    FStar.Math.Lemmas.lemma_mod_sub_distr va vb eight;
    assert ((va - vb) % 8 == 0);
    // Since a <> b, the difference is non-zero, so it must be >= 8 or <= -8
    // If vb > va: vb - va > 0 and (vb - va) % 8 == 0, so vb - va >= 8
    // If va > vb: va - vb > 0 and (va - vb) % 8 == 0, so va - vb >= 8
    if vb > va then (
      if vb - va < 8 then FStar.Math.Lemmas.small_mod (vb - va) eight
    ) else (
      if va - vb < 8 then FStar.Math.Lemmas.small_mod (va - vb) eight
    )
#pop-options

/// ---------------------------------------------------------------------------
/// Object Color Predicates
/// ---------------------------------------------------------------------------

/// Read header of object at address
let read_header (g: heap) (obj_addr: obj_addr) : GTot U64.t =
  read_word g (hd_address obj_addr)

/// Get color of object in heap
let get_object_color (g: heap) (obj_addr: obj_addr) : GTot color =
  getColor (read_header g obj_addr)

/// color_of_object alias for fsti (returns color_sem now)
let color_of_object (h_addr: obj_addr) (g: heap) : GTot color =
  get_object_color g h_addr

/// color_of_object specification: reads header and extracts color
let color_of_object_spec (h_addr: obj_addr) (g: heap)
  : Lemma (color_of_object h_addr g == getColor (read_word g (hd_address h_addr))) =
  ()

/// Get tag of object at address
let tag_of_object (obj_addr: obj_addr) (g: heap) : GTot U64.t =
  getTag (read_header g obj_addr)

/// tag_of_object specification: reads header and extracts tag
let tag_of_object_spec (h_addr: obj_addr) (g: heap)
  : Lemma (tag_of_object h_addr g == getTag (read_word g (hd_address h_addr))) = 
  ()

/// Get word size of object
let wosize_of_object (obj_addr: obj_addr) (g: heap) : GTot U64.t =
  getWosize (read_header g obj_addr)

/// wosize_of_object returns a value < 2^54
let wosize_of_object_bound (h_addr: obj_addr) (g: heap)
  : Lemma (U64.v (wosize_of_object h_addr g) < pow2 54) = 
  wosize_shift_lemma (read_header g h_addr)

/// wosize_of_object specification: reads header and extracts wosize
let wosize_of_object_spec (h_addr: obj_addr) (g: heap)
  : Lemma (wosize_of_object h_addr g == getWosize (read_word g (hd_address h_addr))) = 
  ()

/// Is object black?
let is_black (obj_addr: obj_addr) (g: heap) : GTot bool =
  get_object_color g obj_addr = Black

/// Is object white?
let is_white (obj_addr: obj_addr) (g: heap) : GTot bool =
  get_object_color g obj_addr = White

/// Is object gray?
let is_gray (obj_addr: obj_addr) (g: heap) : GTot bool =
  get_object_color g obj_addr = Gray

/// Is object blue (free-list)?
let is_blue (obj_addr: obj_addr) (g: heap) : GTot bool =
  get_object_color g obj_addr = Blue

/// ---------------------------------------------------------------------------
/// Color Characterization Lemmas
/// ---------------------------------------------------------------------------

/// is_gray means color_of_object = Gray
let is_gray_iff (h_addr: obj_addr) (g: heap)
  : Lemma (is_gray h_addr g <==> color_of_object h_addr g = Gray) = ()

/// is_black means color_of_object = Black
let is_black_iff (h_addr: obj_addr) (g: heap)
  : Lemma (is_black h_addr g <==> color_of_object h_addr g = Black) = ()

/// is_white means color_of_object = White  
let is_white_iff (h_addr: obj_addr) (g: heap)
  : Lemma (is_white h_addr g <==> color_of_object h_addr g = White) = ()

/// is_blue means color_of_object = Blue
let is_blue_iff (h_addr: obj_addr) (g: heap)
  : Lemma (is_blue h_addr g <==> color_of_object h_addr g = Blue) = ()

/// ---------------------------------------------------------------------------
/// Color Disjointness Lemmas (trivial with algebraic color type!)
/// ---------------------------------------------------------------------------

let white_gray_disjoint (x: obj_addr) (y: obj_addr) (g: heap)
  : Lemma (requires is_white x g /\ is_gray y g)
          (ensures x <> y) = ()

let white_black_disjoint (x: obj_addr) (y: obj_addr) (g: heap)
  : Lemma (requires is_white x g /\ is_black y g)
          (ensures x <> y) = ()

let gray_black_disjoint (x: obj_addr) (y: obj_addr) (g: heap)
  : Lemma (requires is_gray x g /\ is_black y g)
          (ensures x <> y) = ()

/// Color depends only on header word
let color_of_header_eq (obj: obj_addr) (g1 g2: heap)
  : Lemma (requires read_word g1 (hd_address obj) == read_word g2 (hd_address obj))
          (ensures is_gray obj g1 == is_gray obj g2 /\
                   is_white obj g1 == is_white obj g2 /\
                   is_black obj g1 == is_black obj g2 /\
                   is_blue obj g1 == is_blue obj g2) = ()

/// ---------------------------------------------------------------------------
/// Tag Predicates
/// ---------------------------------------------------------------------------

let is_closure (h_addr: obj_addr) (g: heap) : GTot bool =
  tag_of_object h_addr g = closure_tag

let is_infix (h_addr: obj_addr) (g: heap) : GTot bool =
  tag_of_object h_addr g = infix_tag

let is_no_scan (h_addr: obj_addr) (g: heap) : GTot bool =
  U64.gte (tag_of_object h_addr g) no_scan_tag

let is_no_scan_spec (h_addr: obj_addr) (g: heap)
  : Lemma (is_no_scan h_addr g == U64.gte (tag_of_object h_addr g) no_scan_tag) = 
  ()

/// ---------------------------------------------------------------------------
/// Color Mutation Operations
/// ---------------------------------------------------------------------------

/// Change object color in heap (now takes color_sem)
let set_color (g: heap) (obj_addr: obj_addr) (c: color) : GTot heap =
  let hd_addr = hd_address obj_addr in
  let old_header = read_word g hd_addr in
  let new_header = colorHeader old_header c in
  write_word g hd_addr new_header

/// set_object_color alias for fsti (takes color_sem)
let set_object_color (h_addr: obj_addr) (g: heap) (c: color) : GTot heap =
  set_color g h_addr c

/// Make object black
let makeBlack (obj_addr: obj_addr) (g: heap) : GTot heap =
  set_color g obj_addr Black

/// Make object white
let makeWhite (obj_addr: obj_addr) (g: heap) : GTot heap =
  set_color g obj_addr White

/// Make object gray
let makeGray (obj_addr: obj_addr) (g: heap) : GTot heap =
  set_color g obj_addr Gray

/// Make object blue (free-list)
let makeBlue (obj_addr: obj_addr) (g: heap) : GTot heap =
  set_color g obj_addr Blue

/// Equation lemmas connecting make* to set_object_color
let makeBlack_eq (h_addr: obj_addr) (g: heap)
  : Lemma (makeBlack h_addr g == set_object_color h_addr g Black) = ()

let makeWhite_eq (h_addr: obj_addr) (g: heap)
  : Lemma (makeWhite h_addr g == set_object_color h_addr g White) = ()

let makeGray_eq (h_addr: obj_addr) (g: heap)
  : Lemma (makeGray h_addr g == set_object_color h_addr g Gray) = ()

let makeBlue_eq (h_addr: obj_addr) (g: heap)
  : Lemma (makeBlue h_addr g == set_object_color h_addr g Blue) = ()

let makeWhite_spec (obj: obj_addr) (g: heap)
  : Lemma (makeWhite obj g == write_word g (hd_address obj) (colorHeader (read_word g (hd_address obj)) White)) = ()

let makeBlack_spec (obj: obj_addr) (g: heap)
  : Lemma (makeBlack obj g == write_word g (hd_address obj) (colorHeader (read_word g (hd_address obj)) Black)) = ()

let makeGray_spec (obj: obj_addr) (g: heap)
  : Lemma (makeGray obj g == write_word g (hd_address obj) (colorHeader (read_word g (hd_address obj)) Gray)) = ()

let makeBlue_spec (obj: obj_addr) (g: heap)
  : Lemma (makeBlue obj g == write_word g (hd_address obj) (colorHeader (read_word g (hd_address obj)) Blue)) = ()

/// ---------------------------------------------------------------------------
/// Pointer Field Predicates
/// ---------------------------------------------------------------------------

/// Check if value looks like a pointer (word-aligned and non-null)
let is_pointer (v: U64.t) : bool = 
  U64.rem v 2UL = 0UL && v <> 0UL

/// Check if field value looks like a pointer
let is_pointer_field (field_val: U64.t) : bool =
  is_pointer field_val

/// Helper lemma: wosize is always < pow2 61
let wosize_fits_field_index (wz: wosize) 
  : Lemma (U64.v wz < pow2 61)
  = FStar.Math.Lemmas.pow2_lt_compat 61 54

/// Helper: check if any field points to target
/// Iterates through field indices 0 to wz-1 (wz is remaining count to check)
let rec exists_field_pointing_to (g: heap) (h: obj_addr) (wz: wosize) (target: obj_addr) 
  : GTot bool (decreases U64.v wz) =
  if wz = 0UL then false
  else begin
    // Use wz-1 as the field index (0-based indexing)
    let idx = U64.sub wz 1UL in
    wosize_fits_field_index wz;
    // idx < wz < pow2 54 < pow2 61
    FStar.Math.Lemmas.pow2_lt_compat 61 54;
    let field_addr_raw = field_address h idx in
    // Check field address validity (instead of assuming)
    if U64.v field_addr_raw >= heap_size || U64.v field_addr_raw % U64.v mword <> 0 then false
    else begin
      let field_addr : hp_addr = field_addr_raw in
      let field_val = read_word g field_addr in
      // Check if field_val is a valid pointer >= 8 to compare headers
      if is_pointer_field field_val && U64.v field_val >= U64.v mword 
         && U64.v field_val < heap_size && U64.v field_val % U64.v mword = 0 then (
        if hd_address field_val = hd_address target then true
        else exists_field_pointing_to g h idx target
      ) else exists_field_pointing_to g h idx target
    end
  end

/// Check if object h points to object target
let is_pointer_to_object (g: heap) (h: obj_addr) (target: obj_addr) : GTot bool =
  wosize_of_object_bound h g;
  let wz : wosize = wosize_of_object h g in
  exists_field_pointing_to g h wz target

/// ---------------------------------------------------------------------------
/// Color Change Preservation Lemmas
/// ---------------------------------------------------------------------------

/// Changing color preserves other fields
val color_change_preserves_wosize (g: heap) (obj_addr: obj_addr) (c: color)
  : Lemma (wosize_of_object obj_addr (set_color g obj_addr c) = 
           wosize_of_object obj_addr g)

let color_change_preserves_wosize g obj_addr c = 
  // We need to show that wosize extraction from the header is preserved
  // after changing color - now using the already-proven lemma!
  let hd_addr = hd_address obj_addr in
  let old_header = read_word g hd_addr in
  let new_header = colorHeader old_header c in
  
  // Key: read_word (write_word g hd_addr new_header) hd_addr = new_header
  // via read_write_same
  read_write_same g hd_addr new_header;
  
  // Now use setColor_preserves_wosize_lemma which proves
  // getWosize (setColor old_header c') = getWosize old_header
  let packed_c = U64.uint_to_t (pack_color c) in
  setColor_preserves_wosize_lemma old_header packed_c

val color_change_preserves_tag (g: heap) (obj_addr: obj_addr) (c: color)
  : Lemma (tag_of_object obj_addr (set_color g obj_addr c) = 
           tag_of_object obj_addr g)

let color_change_preserves_tag g obj_addr c = 
  // We need to show that tag extraction from the header is preserved
  // after changing color - now using the already-proven lemma!
  let hd_addr = hd_address obj_addr in
  let old_header = read_word g hd_addr in
  let new_header = colorHeader old_header c in
  
  // Key: read_word (write_word g hd_addr new_header) hd_addr = new_header
  // via read_write_same
  read_write_same g hd_addr new_header;
  
  // Now use setColor_preserves_tag_lemma which proves
  // getTag (setColor old_header c') = getTag old_header
  let packed_c = U64.uint_to_t (pack_color c) in
  setColor_preserves_tag_lemma old_header packed_c

/// Changing one object's color doesn't affect other objects
val color_change_other_object (g: heap) (obj1: hp_addr{U64.v obj1 >= U64.v mword}) (obj2: hp_addr{U64.v obj2 >= U64.v mword}) (c: color)
  : Lemma
      (requires hd_address obj1 <> hd_address obj2)
      (ensures get_object_color (set_color g obj1 c) obj2 = 
               get_object_color g obj2)

let color_change_other_object g obj1 obj2 c =
  // We need to show that changing obj1's color doesn't affect obj2's color
  // when their header addresses are different
  let hd_addr1 = hd_address obj1 in
  let hd_addr2 = hd_address obj2 in
  
  // Precondition: hd_addr1 <> hd_addr2
  // hd_addrs are word-aligned (hp_addr requires % mword == 0)
  // Since they're different and word-aligned, they're at least 8 bytes apart
  
  // set_color g obj1 c = write_word g hd_addr1 new_header1
  // get_object_color g obj2 = getColor (read_word g hd_addr2)
  
  // Use read_write_different from Heap
  if U64.v hd_addr1 + U64.v mword <= U64.v hd_addr2 then
    read_write_different g hd_addr1 hd_addr2 (colorHeader (read_word g hd_addr1) c)
  else if U64.v hd_addr2 + U64.v mword <= U64.v hd_addr1 then
    read_write_different g hd_addr1 hd_addr2 (colorHeader (read_word g hd_addr1) c)
  else (
    // This branch is unreachable: word_aligned_separate proves one of the above holds
    word_aligned_separate hd_addr1 hd_addr2
  )

/// ---------------------------------------------------------------------------
/// Object Enumeration (also used by GraphBridge)
/// ---------------------------------------------------------------------------

/// Enumerate all objects in heap starting from address
/// Objects are laid out consecutively: |header|field1|field2|...|fieldN|header|...
let rec objects (start: hp_addr) (g: heap) : GTot (Seq.seq hp_addr) (decreases (Seq.length g - U64.v start)) =
  if U64.v start + 8 >= Seq.length g then Seq.empty
  else
    let header = read_word g start in
    let wz = getWosize header in
    let obj_addr_raw = f_address start in
    // f_address uses U64.add — gives start + 8 directly
    f_address_spec start;
    assert (U64.v obj_addr_raw = U64.v start + 8);
    let obj_addr : hp_addr = obj_addr_raw in
    // Calculate next_start in nat arithmetic to avoid overflow issues
    let obj_size_nat = U64.v wz + 1 in  // wosize + 1 word for header
    let next_start_nat = U64.v start + FStar.Mul.(obj_size_nat * 8) in
    if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then Seq.empty
    else if next_start_nat >= heap_size then Seq.cons obj_addr Seq.empty
    else begin
      // Prove next_start_nat is in bounds for U64
      assert (next_start_nat < pow2 64);
      let next_start_raw = U64.uint_to_t next_start_nat in
      assert (U64.v next_start_raw = next_start_nat);
      assert (next_start_nat < heap_size);
      // next_start_nat % 8 == 0 because start % 8 == 0 and (obj_size_nat * 8) % 8 == 0
      FStar.Math.Lemmas.lemma_mod_plus_distr_l (U64.v start) (obj_size_nat * 8) 8;
      assert (U64.v next_start_raw % U64.v mword == 0);
      let next_start : hp_addr = next_start_raw in
      Seq.cons obj_addr (objects next_start g)
    end

/// Get all allocated block addresses (as hp_addr)
let allocated_blocks (g: heap) : GTot (Seq.seq hp_addr) =
  objects 0UL g

/// Coerce hp_addr to obj_addr when >= 8 is known
/// Used to convert addresses from objects list to obj_addr
let hp_to_obj (h: hp_addr{U64.v h >= U64.v mword}) : obj_addr = h

/// All object addresses in objects are > start (strictly greater, using f_address)
/// Key insight: f_address start = start + 8, so objects start at start + 8 or later
#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
let rec objects_addresses_gt_start (start: hp_addr) (g: heap) (x: hp_addr)
  : Lemma (ensures Seq.mem x (objects start g) ==> U64.v x > U64.v start)
          (decreases (Seq.length g - U64.v start))
  = if U64.v start + 8 >= Seq.length g then ()
    else begin
      let header = read_word g start in
      let wz = getWosize header in
      let obj_addr_raw = f_address start in
      f_address_spec start;
      let obj_addr : hp_addr = obj_addr_raw in
      let obj_size_nat = U64.v wz + 1 in
      let next_start_nat = U64.v start + FStar.Mul.(obj_size_nat * 8) in
      if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then ()
      else if next_start_nat >= heap_size then (
        // objects start g = cons obj_addr empty
        let obj_addr_hp : hp_addr = obj_addr in
        if Seq.mem x (Seq.cons obj_addr_hp Seq.empty) then (
          FStar.Seq.Properties.mem_cons obj_addr_hp Seq.empty;
          assert (x = obj_addr_hp);
          assert (U64.v obj_addr = U64.v start + 8);
          assert (U64.v obj_addr > U64.v start)
        )
      )
      else begin
        let next_start_raw = U64.uint_to_t next_start_nat in
        // Prove next_start is valid (same as in objects)
        assert (U64.v next_start_raw = next_start_nat);
        assert (next_start_nat < heap_size);
        FStar.Math.Lemmas.lemma_mod_plus_distr_l (U64.v start) (obj_size_nat * 8) 8;
        assert (U64.v next_start_raw % U64.v mword == 0);
        let next_start : hp_addr = next_start_raw in
        let rest = objects next_start g in
        let obj_addr_hp : hp_addr = obj_addr in
        if Seq.mem x (Seq.cons obj_addr_hp rest) then (
          FStar.Seq.Properties.mem_cons obj_addr_hp rest;
          if x = obj_addr_hp then (
            // obj_addr = start + 8 > start
            assert (U64.v obj_addr = U64.v start + 8);
            assert (U64.v obj_addr > U64.v start)
          ) else (
            // x is in rest
            objects_addresses_gt_start next_start g x;
            assert (U64.v x > U64.v next_start);
            assert (U64.v next_start >= U64.v start + 8);
            assert (U64.v x > U64.v start)
          )
        )
      end
    end
#pop-options

/// Object address not in later objects (for no-duplicates proof)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
let objects_addr_not_in_rest (start: hp_addr) (g: heap)
  : Lemma (requires U64.v start + 8 < Seq.length g)
          (ensures (
            let header = read_word g start in
            let wz = getWosize header in
            let obj_addr = f_address start in
            let obj_size_nat = U64.v wz + 1 in
            let next_start_nat = U64.v start + FStar.Mul.(obj_size_nat * 8) in
            next_start_nat <= Seq.length g /\ next_start_nat < pow2 64 ==>
            (U64.v (U64.uint_to_t next_start_nat) < heap_size /\ U64.v (U64.uint_to_t next_start_nat) % U64.v mword == 0 ==>
             U64.v obj_addr < heap_size /\ U64.v obj_addr % U64.v mword == 0 ==>
             ~(Seq.mem (obj_addr <: hp_addr) (objects ((U64.uint_to_t next_start_nat) <: hp_addr) g)))))
  = let header = read_word g start in
    let wz = getWosize header in
    let obj_addr = f_address start in
    let obj_size_nat = U64.v wz + 1 in
    let next_start_nat = U64.v start + FStar.Mul.(obj_size_nat * 8) in
    if next_start_nat <= Seq.length g && next_start_nat < pow2 64 then (
      let next_start_raw = U64.uint_to_t next_start_nat in
      assert (U64.v next_start_raw = next_start_nat);
      // The ensures clause gives us these facts as assumptions when needed
      // Just need to use them when the hypotheses are satisfied
      if next_start_nat < heap_size && U64.v obj_addr < heap_size && U64.v obj_addr % U64.v mword = 0 then (
        FStar.Math.Lemmas.lemma_mod_plus_distr_l (U64.v start) (obj_size_nat * 8) 8;
        assert (U64.v next_start_raw % U64.v mword == 0);
        let next_start : hp_addr = next_start_raw in
        let obj_addr_hp : hp_addr = obj_addr in
        // Use objects_addresses_gt_start: all objects in (objects next_start g) have addr > next_start
        // obj_addr = start + 8
        // next_start >= start + 8 (since obj_size >= 1)
        // If obj_addr in (objects next_start g), then obj_addr > next_start (by the lemma)
        // But obj_addr = start + 8 and next_start >= start + 8, so obj_addr <= next_start
        // Contradiction, so obj_addr not in (objects next_start g)
        objects_addresses_gt_start next_start g obj_addr_hp;
        assert (Seq.mem obj_addr_hp (objects next_start g) ==> U64.v obj_addr > U64.v next_start);
        f_address_spec start;
        assert (U64.v obj_addr = U64.v start + 8);
        assert (U64.v next_start >= U64.v start + 8);
        assert (U64.v obj_addr <= U64.v next_start)
      )
    )
#pop-options

/// All objects in objects list have addresses >= 8
/// Proof: f_address start = start + 8 (no overflow when start + 8 <= heap size < 2^64)
/// For objects 0UL g, first object is at f_address 0 = 8, rest are higher
#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let rec objects_addresses_ge_8 (g: heap) (x: hp_addr)
  : Lemma (requires Seq.mem x (objects 0UL g))
          (ensures U64.v x >= 8)
          (decreases Seq.length g)
  = let start = 0UL in
    if U64.v start + 8 >= Seq.length g then (
      // objects 0 g = empty, so x ∈ empty is false - vacuously true
      ()
    )
    else begin
      let header = read_word g start in
      let wz = getWosize header in
      let obj_addr_raw = f_address start in
      // f_address 0 = 0 + 8 = 8
      f_address_spec start;
      assert (U64.v obj_addr_raw = U64.v start + 8);
      let obj_addr : hp_addr = obj_addr_raw in
      let obj_size_nat = U64.v wz + 1 in
      let next_start_nat = U64.v start + FStar.Mul.(obj_size_nat * 8) in
      if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then (
        // objects 0 g = empty in this case - vacuously true
        ()
      ) else if next_start_nat >= heap_size then (
        // objects 0 g = cons obj_addr empty = cons 8 empty
        let obj_addr_hp : hp_addr = obj_addr in
        Seq.Properties.mem_cons obj_addr_hp Seq.empty;
        // x ∈ (cons obj_addr empty) means x = obj_addr
        assert (x = obj_addr_hp);
        // x = 8 >= 8
        assert (U64.v x = 8)
      ) else begin
        let next_start_raw = U64.uint_to_t next_start_nat in
        // Prove next_start is valid (same as in objects)
        assert (U64.v next_start_raw = next_start_nat);
        assert (next_start_nat < heap_size);
        FStar.Math.Lemmas.lemma_mod_plus_distr_l (U64.v start) (obj_size_nat * 8) 8;
        assert (U64.v next_start_raw % U64.v mword == 0);
        let next_start : hp_addr = next_start_raw in
        let obj_addr_hp : hp_addr = obj_addr in
        let rest = objects next_start g in
        // objects 0 g = cons obj_addr rest = cons 8 rest
        // x ∈ (cons obj_addr rest) means x = obj_addr or x ∈ rest
        Seq.Properties.mem_cons obj_addr_hp rest;
        if x = obj_addr_hp then (
          // x = 8 >= 8
          assert (U64.v x = 8)
        ) else (
          // x ∈ rest = objects next_start g
          assert (Seq.mem x rest);
          // next_start >= 8
          assert (U64.v next_start >= 8);
          // By objects_addresses_gt_start: all y ∈ objects next_start g have y > next_start
          objects_addresses_gt_start next_start g x;
          assert (U64.v x > U64.v next_start);
          assert (U64.v x > 8)
        )
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Color Mutation Correctness Lemmas (now trivial with Header.fst!)
/// ---------------------------------------------------------------------------

let makeBlack_is_black (h_addr: obj_addr) (g: heap)
  : Lemma (is_black h_addr (makeBlack h_addr g)) = 
  // Uses colorHeader_getColor from Header.fst
  colorHeader_getColor (read_header g h_addr) Black

let makeWhite_is_white (h_addr: obj_addr) (g: heap)
  : Lemma (is_white h_addr (makeWhite h_addr g)) = 
  colorHeader_getColor (read_header g h_addr) White

let makeGray_is_gray (h_addr: obj_addr) (g: heap)
  : Lemma (is_gray h_addr (makeGray h_addr g)) = 
  colorHeader_getColor (read_header g h_addr) Gray

let makeBlue_is_blue (h_addr: obj_addr) (g: heap)
  : Lemma (is_blue h_addr (makeBlue h_addr g)) = 
  colorHeader_getColor (read_header g h_addr) Blue

/// set_object_color with non-Blue color preserves ~(is_blue x) for all x
let set_color_preserves_not_blue (obj: obj_addr) (x: obj_addr) (g: heap) (c: color)
  : Lemma (requires c <> Blue /\ ~(is_blue x g))
          (ensures ~(is_blue x (set_object_color obj g c)))
  = if x = obj then colorHeader_getColor (read_header g obj) c
    else begin
      hd_address_injective obj x;
      color_change_other_object g obj x c
    end

/// ---------------------------------------------------------------------------
/// Color Change Preservation Lemmas (for fsti)
/// ---------------------------------------------------------------------------

let set_object_color_length (h_addr: obj_addr) (g: heap) (c: color)
  : Lemma (Seq.length (set_object_color h_addr g c) == Seq.length g) =
  // set_object_color = write_word g (hd_address h) (colorHeader ...)
  // write_word preserves Seq.length (from its postcondition)
  ()

let set_object_color_preserves_getWosize_at_hd (obj: obj_addr) (g: heap) (c: color)
  : Lemma (getWosize (read_word (set_object_color obj g c) (hd_address obj)) ==
           getWosize (read_word g (hd_address obj))) =
  wosize_of_object_spec obj g;
  wosize_of_object_spec obj (set_object_color obj g c);
  color_change_preserves_wosize g obj c

let color_preserves_wosize (h_addr: obj_addr) (g: heap) (c: color)
  : Lemma (wosize_of_object h_addr (set_object_color h_addr g c) == wosize_of_object h_addr g) =
  color_change_preserves_wosize g h_addr c

let color_preserves_tag (obj_addr: obj_addr) (g: heap) (c: color)
  : Lemma (tag_of_object obj_addr (set_object_color obj_addr g c) == tag_of_object obj_addr g) =
  color_change_preserves_tag g obj_addr c

let color_change_locality (obj_addr1: hp_addr{U64.v obj_addr1 >= U64.v mword}) (obj_addr2: hp_addr{U64.v obj_addr2 >= U64.v mword}) (g: heap) (c: color)
  : Lemma (requires hd_address obj_addr1 <> hd_address obj_addr2)
          (ensures color_of_object obj_addr2 (set_object_color obj_addr1 g c) == color_of_object obj_addr2 g) =
  color_change_other_object g obj_addr1 obj_addr2 c

let color_change_header_locality (obj_addr: obj_addr) (addr: hp_addr) (g: heap) (c: color)
  : Lemma (requires hd_address obj_addr <> addr)
          (ensures read_word (set_object_color obj_addr g c) addr == read_word g addr) =
  // set_object_color writes at hd_address obj_addr
  // We need: hd_address obj_addr <> addr and they don't overlap
  let hd = hd_address obj_addr in
  // Since hp_addrs are word-aligned and hd <> addr, they're at least 8 bytes apart
  // (either hd + 8 <= addr or addr + 8 <= hd)
  assert (hd <> addr);
  // Use read_write_different which requires non-overlapping ranges
  if U64.v hd + U64.v mword <= U64.v addr then
    read_write_different g hd addr (colorHeader (read_word g hd) c)
  else if U64.v addr + U64.v mword <= U64.v hd then
    read_write_different g hd addr (colorHeader (read_word g hd) c)
  else (
    // This branch is unreachable: word_aligned_separate proves one of the above holds
    word_aligned_separate hd addr
  )

let color_preserves_field (obj_addr: obj_addr) (g: heap) (c: color) (i: U64.t{U64.v i >= 1}) (field_addr: hp_addr{U64.v field_addr == U64.v (hd_address obj_addr) + U64.v mword * U64.v i})
  : Lemma (requires U64.v (hd_address obj_addr) + U64.v mword * (U64.v i + 1) <= heap_size)
          (ensures read_word (set_object_color obj_addr g c) field_addr == read_word g field_addr) =
  let hd = hd_address obj_addr in
  assert (U64.v field_addr >= U64.v hd + U64.v mword);
  read_write_different g hd field_addr (colorHeader (read_word g hd) c)

/// Combined SMT pattern: when the solver encounters read_word after set_object_color,
/// it automatically gets the key facts for proving objects enumeration preservation
let set_object_color_read_word (obj: obj_addr) (start: hp_addr) (g: heap) (c: color)
  : Lemma (ensures 
    Seq.length (set_object_color obj g c) == Seq.length g /\
    (hd_address obj <> start ==> read_word (set_object_color obj g c) start == read_word g start) /\
    (hd_address obj = start ==> getWosize (read_word (set_object_color obj g c) start) == getWosize (read_word g start)))
  [SMTPat (read_word (set_object_color obj g c) start)]
  =
  set_object_color_length obj g c;
  if hd_address obj = start then
    set_object_color_preserves_getWosize_at_hd obj g c
  else
    color_change_header_locality obj start g c

let color_preserves_is_no_scan (obj_addr: obj_addr) (g: heap) (c: color)
  : Lemma (is_no_scan obj_addr (set_object_color obj_addr g c) == is_no_scan obj_addr g) =
  color_preserves_tag obj_addr g c

let color_change_preserves_other_is_no_scan (obj1: obj_addr) (obj2: obj_addr) (g: heap) (c: color)
  : Lemma (requires obj1 <> obj2)
          (ensures is_no_scan obj2 (set_object_color obj1 g c) == is_no_scan obj2 g) =
  hd_address_injective obj1 obj2;
  color_change_header_locality obj1 (hd_address obj2) g c

let color_change_preserves_other_wosize (obj1: hp_addr{U64.v obj1 >= U64.v mword}) (obj2: hp_addr{U64.v obj2 >= U64.v mword}) (g: heap) (c: color)
  : Lemma (requires obj1 <> obj2)
          (ensures wosize_of_object obj2 (set_object_color obj1 g c) == wosize_of_object obj2 g) =
  // wosize is read from header at hd_address obj2
  // set_object_color writes at hd_address obj1
  // obj1 <> obj2 implies hd_address obj1 <> hd_address obj2 (by injectivity)
  hd_address_injective obj1 obj2;
  color_change_header_locality obj1 (hd_address obj2) g c

let color_change_preserves_other_read (obj1: hp_addr{U64.v obj1 >= U64.v mword}) (addr: hp_addr) (g: heap) (c: color)
  : Lemma (requires hd_address obj1 <> addr)
          (ensures read_word (set_object_color obj1 g c) addr == read_word g addr) =
  color_change_header_locality obj1 addr g c

let color_change_preserves_other_color (obj1: hp_addr{U64.v obj1 >= U64.v mword}) (obj2: hp_addr{U64.v obj2 >= U64.v mword}) (g: heap) (c: color)
  : Lemma (requires obj1 <> obj2)
          (ensures color_of_object obj2 (set_object_color obj1 g c) == color_of_object obj2 g) =
  hd_address_injective obj1 obj2;
  color_change_locality obj1 obj2 g c

/// ---------------------------------------------------------------------------
/// Aggregate Color Predicates
/// ---------------------------------------------------------------------------

/// No grey objects in address list (admits >= 8)
let rec noGreyObjects_aux (g: heap) (addrs: seq hp_addr) : GTot bool (decreases Seq.length addrs) =
  if Seq.length addrs = 0 then true
  else 
    let x = Seq.head addrs in
    if U64.v x >= U64.v mword && is_gray x g then false
    else noGreyObjects_aux g (Seq.tail addrs)
