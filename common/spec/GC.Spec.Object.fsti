/// ---------------------------------------------------------------------------
/// GC.Spec.Object - Object headers and colors
/// ---------------------------------------------------------------------------
///
/// This module provides:
/// - Color type (color_sem: White | Gray | Black)
/// - Header field extraction (wosize, color, tag)
/// - Color predicates (is_black, is_white, etc.)
///
/// Header layout (64 bits, little-endian):
///   bits 0-7   : tag (8 bits)
///   bits 8-9   : color (2 bits)  
///   bits 10-63 : wosize (54 bits)

module GC.Spec.Object

open FStar.Seq
open FStar.Mul

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap
open GC.Lib.Header

/// ---------------------------------------------------------------------------
/// Color Type (re-exported from Header)
/// ---------------------------------------------------------------------------

/// Color type is now algebraic (White | Gray | Black)
let color = color_sem

/// ---------------------------------------------------------------------------
/// Tag Constants
/// ---------------------------------------------------------------------------

val closure_tag : U64.t
val infix_tag : U64.t
val no_scan_tag : U64.t

/// Expose tag constant values (needed for Pulse bridge lemmas)
val no_scan_tag_val : unit -> Lemma (no_scan_tag == U64.uint_to_t 251)

/// ---------------------------------------------------------------------------
/// Header Masks and Shifts
/// ---------------------------------------------------------------------------

val color_mask : U64.t
val color_shift : U32.t
val tag_mask : U64.t
val wosize_shift : U32.t

/// ---------------------------------------------------------------------------
/// Header Field Extraction
/// ---------------------------------------------------------------------------

/// wosize = U64.t refined to < pow2 54
type wosize = w:U64.t{U64.v w < pow2 54}

/// Extract color from header word (bits 8-9)
val getColor (hdr: U64.t) : color

/// getColor characterization in terms of raw color bits (Header.get_color)
val getColor_raw : (hdr: U64.t) -> Lemma (
      let c = get_color (U64.v hdr) in
      (c = 0 ==> getColor hdr = White) /\
      (c = 1 ==> getColor hdr = Gray) /\
      (c = 2 ==> getColor hdr = Blue) /\
      (c = 3 ==> getColor hdr = Black))

/// Expose getColor definition (needed for Pulse bridge)
val getColor_spec : (hdr: U64.t) ->
  Lemma (getColor hdr == (match unpack_color (get_color (U64.v hdr)) with | Some c -> c | None -> White))

/// Gray or Black headers are always valid
val gray_or_black_valid : (hdr: U64.t) ->
  Lemma (requires getColor hdr == Gray \/ getColor hdr == Black)
        (ensures valid_header64 hdr)

/// Extract tag from header word (bits 0-7)
val getTag (hdr: U64.t) : t:U64.t{U64.v t < 256}

/// getTag returns a value < 256
val getTag_bound : (hdr: U64.t) -> Lemma (U64.v (getTag hdr) < 256)

/// Extract wosize from header word (bits 10-63)
val getWosize (hdr: U64.t) : wosize

/// getWosize computes shift_right hdr 10
val getWosize_spec : (hdr: U64.t) -> Lemma (getWosize hdr == U64.shift_right hdr 10ul)

/// getTag computes logand hdr 0xFF (exposed for bridge lemmas)
val getTag_spec : (hdr: U64.t) -> Lemma (getTag hdr == U64.logand hdr 0xFFUL)

/// getWosize returns a value < 2^54
val getWosize_bound : (hdr: U64.t) -> Lemma (U64.v (getWosize hdr) < pow2 54)

/// ---------------------------------------------------------------------------
/// Header Field Modification
/// ---------------------------------------------------------------------------

/// Construct header from components
inline_for_extraction
val makeHeader (wz: wosize) (c: color) (tag: U64.t{U64.v tag < 256}) : U64.t

/// Change color in header (takes color_sem) — spec only, use makeHeader for extraction
val colorHeader (header: U64.t) (new_color: color) : U64.t

/// All headers have valid color bits (get_color always < 4)
val all_headers_valid : (hdr: U64.t) -> Lemma (valid_header64 hdr)

/// colorHeader definition: colorHeader hdr c == set_color64 hdr (uint_to_t (pack_color c))
val colorHeader_spec : (hdr: U64.t) -> (c: color) ->
  Lemma (colorHeader hdr c == set_color64 hdr (U64.uint_to_t (pack_color c)))

/// Clear color bits and set new color (takes packed U64 for backwards compat)
val setColor (hdr: U64.t) (c: U64.t{U64.v c < 4}) : U64.t

/// colorHeader followed by getColor returns the color
val colorHeader_getColor : (hdr: U64.t) -> (c: color) ->
  Lemma (getColor (colorHeader hdr c) == c)

/// colorHeader preserves getWosize
val colorHeader_preserves_wosize : (hdr: U64.t) -> (c: color) ->
  Lemma (getWosize (colorHeader hdr c) == getWosize hdr)

/// colorHeader preserves getTag
val colorHeader_preserves_tag : (hdr: U64.t) -> (c: color) ->
  Lemma (getTag (colorHeader hdr c) == getTag hdr)

/// makeHeader from extracted fields with new color == colorHeader  
val makeHeader_eq_colorHeader : (hdr: U64.t) -> (c: color) ->
  Lemma (requires valid_header64 hdr)
        (ensures makeHeader (getWosize hdr) c (getTag hdr) == colorHeader hdr c)

/// ---------------------------------------------------------------------------
/// Object Color Predicates
/// ---------------------------------------------------------------------------

/// Get color of object at address (returns color_sem)
val color_of_object (h_addr: obj_addr) (g: heap) : GTot color

/// color_of_object specification: reads header and extracts color
val color_of_object_spec : (h_addr: obj_addr) -> (g: heap) ->
  Lemma (color_of_object h_addr g == getColor (read_word g (hd_address h_addr)))

/// Get tag of object at address
val tag_of_object (h_addr: obj_addr) (g: heap) : GTot U64.t

/// tag_of_object specification: reads header and extracts tag
val tag_of_object_spec : (h_addr: obj_addr) -> (g: heap) ->
  Lemma (tag_of_object h_addr g == getTag (read_word g (hd_address h_addr)))

/// Get wosize of object at address
val wosize_of_object (h_addr: obj_addr) (g: heap) : GTot U64.t

/// wosize_of_object returns a value < 2^54
val wosize_of_object_bound : (h_addr: obj_addr) -> (g: heap) ->
  Lemma (U64.v (wosize_of_object h_addr g) < pow2 54)

/// wosize_of_object specification: reads header and extracts wosize
val wosize_of_object_spec : (h_addr: obj_addr) -> (g: heap) ->
  Lemma (wosize_of_object h_addr g == getWosize (read_word g (hd_address h_addr)))

/// Color predicates
val is_black (h_addr: obj_addr) (g: heap) : GTot bool
val is_white (h_addr: obj_addr) (g: heap) : GTot bool
val is_gray (h_addr: obj_addr) (g: heap) : GTot bool
val is_blue (h_addr: obj_addr) (g: heap) : GTot bool

/// ---------------------------------------------------------------------------
/// Color Characterization Lemmas
/// ---------------------------------------------------------------------------

/// is_gray means color_of_object = Gray
val is_gray_iff (h_addr: obj_addr) (g: heap)
  : Lemma (is_gray h_addr g <==> color_of_object h_addr g = Gray)

/// is_black means color_of_object = Black
val is_black_iff (h_addr: obj_addr) (g: heap)
  : Lemma (is_black h_addr g <==> color_of_object h_addr g = Black)

/// is_white means color_of_object = White  
val is_white_iff (h_addr: obj_addr) (g: heap)
  : Lemma (is_white h_addr g <==> color_of_object h_addr g = White)

/// is_blue means color_of_object = Blue
val is_blue_iff (h_addr: obj_addr) (g: heap)
  : Lemma (is_blue h_addr g <==> color_of_object h_addr g = Blue)

/// ---------------------------------------------------------------------------
/// Color Disjointness Lemmas (trivial with algebraic type)
/// ---------------------------------------------------------------------------

val white_gray_disjoint (x: obj_addr) (y: obj_addr) (g: heap)
  : Lemma (requires is_white x g /\ is_gray y g)
          (ensures x <> y)

val white_black_disjoint (x: obj_addr) (y: obj_addr) (g: heap)
  : Lemma (requires is_white x g /\ is_black y g)
          (ensures x <> y)

val gray_black_disjoint (x: obj_addr) (y: obj_addr) (g: heap)
  : Lemma (requires is_gray x g /\ is_black y g)
          (ensures x <> y)

/// Color depends only on the header word — if read_word at hd_address is the same,
/// then color predicates are the same.
val color_of_header_eq : (obj: obj_addr) -> (g1: heap) -> (g2: heap) ->
  Lemma (requires read_word g1 (hd_address obj) == read_word g2 (hd_address obj))
        (ensures is_gray obj g1 == is_gray obj g2 /\
                 is_white obj g1 == is_white obj g2 /\
                 is_black obj g1 == is_black obj g2 /\
                 is_blue obj g1 == is_blue obj g2)

/// ---------------------------------------------------------------------------
/// Tag Predicates
/// ---------------------------------------------------------------------------

val is_closure (h_addr: obj_addr) (g: heap) : GTot bool
val is_infix (h_addr: obj_addr) (g: heap) : GTot bool
val is_no_scan (h_addr: obj_addr) (g: heap) : GTot bool

/// is_closure specification: true when tag == closure_tag
val is_closure_spec : (h_addr: obj_addr) -> (g: heap) ->
  Lemma (is_closure h_addr g == (tag_of_object h_addr g = closure_tag))

/// is_infix specification: true when tag == infix_tag
val is_infix_spec : (h_addr: obj_addr) -> (g: heap) ->
  Lemma (is_infix h_addr g == (tag_of_object h_addr g = infix_tag))

/// is_no_scan specification: true when tag >= no_scan_tag
val is_no_scan_spec : (h_addr: obj_addr) -> (g: heap) ->
  Lemma (is_no_scan h_addr g == U64.gte (tag_of_object h_addr g) no_scan_tag)

/// ---------------------------------------------------------------------------
/// Color Mutation Operations
/// ---------------------------------------------------------------------------

/// Set object color (takes color_sem)
val set_object_color (h_addr: obj_addr) (g: heap) (c: color) : GTot heap

/// Convenience wrappers
val makeBlack (h_addr: obj_addr) (g: heap) : GTot heap
val makeWhite (h_addr: obj_addr) (g: heap) : GTot heap
val makeGray (h_addr: obj_addr) (g: heap) : GTot heap
val makeBlue (h_addr: obj_addr) (g: heap) : GTot heap

/// Equation lemmas: make* = set_object_color with specific color
val makeBlack_eq : (h_addr: obj_addr) -> (g: heap) ->
  Lemma (makeBlack h_addr g == set_object_color h_addr g Black)

val makeWhite_eq : (h_addr: obj_addr) -> (g: heap) ->
  Lemma (makeWhite h_addr g == set_object_color h_addr g White)

val makeGray_eq : (h_addr: obj_addr) -> (g: heap) ->
  Lemma (makeGray h_addr g == set_object_color h_addr g Gray)

val makeBlue_eq : (h_addr: obj_addr) -> (g: heap) ->
  Lemma (makeBlue h_addr g == set_object_color h_addr g Blue)

/// Expose makeWhite as write_word + colorHeader (needed for Pulse bridge)
val makeWhite_spec : (obj: obj_addr) -> (g: heap) ->
  Lemma (makeWhite obj g == write_word g (hd_address obj) (colorHeader (read_word g (hd_address obj)) White))

/// Expose makeBlack as write_word + colorHeader (needed for Pulse bridge)
val makeBlack_spec : (obj: obj_addr) -> (g: heap) ->
  Lemma (makeBlack obj g == write_word g (hd_address obj) (colorHeader (read_word g (hd_address obj)) Black))

/// Expose makeGray as write_word + colorHeader (needed for Pulse bridge)
val makeGray_spec : (obj: obj_addr) -> (g: heap) ->
  Lemma (makeGray obj g == write_word g (hd_address obj) (colorHeader (read_word g (hd_address obj)) Gray))

/// Expose makeBlue as write_word + colorHeader (needed for Pulse bridge)
val makeBlue_spec : (obj: obj_addr) -> (g: heap) ->
  Lemma (makeBlue obj g == write_word g (hd_address obj) (colorHeader (read_word g (hd_address obj)) Blue))

/// ---------------------------------------------------------------------------
/// Object Enumeration
/// ---------------------------------------------------------------------------

/// Enumerate objects starting from address
val objects (start: hp_addr) (g: heap) : GTot (seq hp_addr)

/// Get all allocated blocks
val allocated_blocks (g: heap) : GTot (seq hp_addr)

/// Coerce hp_addr to obj_addr when >= 8 is known
val hp_to_obj (h: hp_addr{U64.v h >= U64.v mword}) : obj_addr

/// All objects in objects 0UL g have addresses >= 8
val objects_addresses_ge_8 (g: heap) (x: hp_addr)
  : Lemma (requires Seq.mem x (objects 0UL g))
          (ensures U64.v x >= U64.v mword)

/// ---------------------------------------------------------------------------
/// Color Mutation Correctness Lemmas
/// ---------------------------------------------------------------------------

val makeBlack_is_black : (h_addr: obj_addr) -> (g: heap) ->
  Lemma (is_black h_addr (makeBlack h_addr g))

val makeWhite_is_white : (h_addr: obj_addr) -> (g: heap) ->
  Lemma (is_white h_addr (makeWhite h_addr g))

val makeGray_is_gray : (h_addr: obj_addr) -> (g: heap) ->
  Lemma (is_gray h_addr (makeGray h_addr g))

val makeBlue_is_blue : (h_addr: obj_addr) -> (g: heap) ->
  Lemma (is_blue h_addr (makeBlue h_addr g))

/// set_object_color with non-Blue color preserves ~(is_blue x) for all x
val set_color_preserves_not_blue : (obj: obj_addr) -> (x: obj_addr) -> (g: heap) -> (c: color) ->
  Lemma (requires c <> Blue /\ ~(is_blue x g))
        (ensures ~(is_blue x (set_object_color obj g c)))

/// ---------------------------------------------------------------------------
/// Color Change Preservation Lemmas
/// ---------------------------------------------------------------------------

/// Color change preserves heap length
val set_object_color_length : (h_addr: obj_addr) -> (g: heap) -> (c: color) ->
  Lemma (Seq.length (set_object_color h_addr g c) == Seq.length g)

/// Color change preserves raw getWosize at the modified header
/// Key lemma for proving objects enumeration is preserved
val set_object_color_preserves_getWosize_at_hd : (obj: obj_addr) -> (g: heap) -> (c: color) ->
  Lemma (getWosize (read_word (set_object_color obj g c) (hd_address obj)) == 
         getWosize (read_word g (hd_address obj)))

/// Color change preserves wosize
val color_preserves_wosize : (h_addr: obj_addr) -> (g: heap) -> (c: color) ->
  Lemma (wosize_of_object h_addr (set_object_color h_addr g c) == wosize_of_object h_addr g)

/// Color change preserves tag
val color_preserves_tag : (oa: obj_addr) -> (g: heap) -> (c: color) ->
  Lemma (tag_of_object oa (set_object_color oa g c) == tag_of_object oa g)

/// Color change at obj1 doesn't affect color at obj2 (different objects)
val color_change_locality : (obj_addr1: obj_addr) -> (obj_addr2: obj_addr) -> (g: heap) -> (c: color) ->
  Lemma (requires hd_address obj_addr1 <> hd_address obj_addr2)
        (ensures color_of_object obj_addr2 (set_object_color obj_addr1 g c) == color_of_object obj_addr2 g)

/// Color change at obj preserves read_word at different address
val color_change_header_locality : (oa: obj_addr) -> (addr: hp_addr) -> (g: heap) -> (c: color) ->
  Lemma (requires hd_address oa <> addr)
        (ensures read_word (set_object_color oa g c) addr == read_word g addr)

/// Color change preserves field values
val color_preserves_field : (oa: obj_addr) -> (g: heap) -> (c: color) -> (i: U64.t{U64.v i >= 1}) -> 
  (field_addr: hp_addr{U64.v field_addr == U64.v (hd_address oa) + U64.v mword * U64.v i}) ->
  Lemma (requires U64.v (hd_address oa) + U64.v mword * (U64.v i + 1) <= heap_size)
        (ensures read_word (set_object_color oa g c) field_addr == read_word g field_addr)

/// Combined SMT pattern lemma: when the solver encounters read_word after set_object_color,
/// it automatically learns the key facts needed for objects enumeration preservation
val set_object_color_read_word : (obj: obj_addr) -> (start: hp_addr) -> (g: heap) -> (c: color) ->
  Lemma (ensures 
    Seq.length (set_object_color obj g c) == Seq.length g /\
    (hd_address obj <> start ==> read_word (set_object_color obj g c) start == read_word g start) /\
    (hd_address obj = start ==> getWosize (read_word (set_object_color obj g c) start) == getWosize (read_word g start)))
  [SMTPat (read_word (set_object_color obj g c) start)]

/// Color change preserves is_no_scan
val color_preserves_is_no_scan : (oa: obj_addr) -> (g: heap) -> (c: color) ->
  Lemma (is_no_scan oa (set_object_color oa g c) == is_no_scan oa g)

/// Color change at obj1 preserves is_no_scan at obj2 (different objects)
val color_change_preserves_other_is_no_scan : (obj1: obj_addr) -> (obj2: obj_addr) -> (g: heap) -> (c: color) ->
  Lemma (requires obj1 <> obj2)
        (ensures is_no_scan obj2 (set_object_color obj1 g c) == is_no_scan obj2 g)

/// Color change at obj1 preserves wosize at obj2 (different objects)
val color_change_preserves_other_wosize : (obj1: obj_addr) -> (obj2: obj_addr) -> (g: heap) -> (c: color) ->
  Lemma (requires obj1 <> obj2)
        (ensures wosize_of_object obj2 (set_object_color obj1 g c) == wosize_of_object obj2 g)

/// Color change at obj1 preserves read_word at any different address
val color_change_preserves_other_read : (obj1: obj_addr) -> (addr: hp_addr) -> (g: heap) -> (c: color) ->
  Lemma (requires hd_address obj1 <> addr)
        (ensures read_word (set_object_color obj1 g c) addr == read_word g addr)

/// Color change at obj1 preserves color at obj2 (different objects)
val color_change_preserves_other_color : (obj1: obj_addr) -> (obj2: obj_addr) -> (g: heap) -> (c: color) ->
  Lemma (requires obj1 <> obj2)
        (ensures color_of_object obj2 (set_object_color obj1 g c) == color_of_object obj2 g)

/// ---------------------------------------------------------------------------
/// Infix Object Support
/// ---------------------------------------------------------------------------

/// Raw computation of parent closure address from infix object.
/// For an infix object at obj_addr `a` with wosize (offset) `w`:
///   infix_hdr = a - 8 (hd_address a)
///   parent_obj_addr = infix_hdr - w * 8
/// The offset in the infix header's wosize field is from the parent closure's
/// first-field address to the infix header.
val parent_closure_addr_nat (infix_obj: obj_addr) (g: heap) : GTot int

/// parent_closure_addr_nat specification: depends only on wosize_of_object
val parent_closure_addr_nat_spec : (infix_obj: obj_addr) -> (g: heap) ->
  Lemma (parent_closure_addr_nat infix_obj g ==
         U64.v infix_obj - 8 - FStar.Mul.(U64.v (wosize_of_object infix_obj g) * 8))

/// Resolve an address: if infix, return parent closure; otherwise return self.
/// Defensive: if the computed parent address is invalid, returns the input unchanged.
val resolve_object (addr: obj_addr) (g: heap) : GTot obj_addr

/// resolve_object identity for non-infix objects
val resolve_non_infix : (addr: obj_addr) -> (g: heap) ->
  Lemma (requires ~(is_infix addr g))
        (ensures resolve_object addr g == addr)

/// resolve_object for infix objects with valid parent
val resolve_infix_spec : (addr: obj_addr) -> (g: heap) ->
  Lemma (requires is_infix addr g /\
                  (let p = parent_closure_addr_nat addr g in
                   p >= 8 /\ p < heap_size /\ p % 8 == 0))
        (ensures resolve_object addr g == U64.uint_to_t (parent_closure_addr_nat addr g))

/// Infix well-formedness: every infix object in the heap has a valid parent closure
val infix_wf (g: heap) (objs: seq obj_addr) : prop

/// Elimination: extract facts for a specific infix object
val infix_wf_elim : (g: heap) -> (objs: seq obj_addr) -> (h: obj_addr) ->
  Lemma (requires infix_wf g objs /\ Seq.mem h objs /\ is_infix h g)
        (ensures (let p = parent_closure_addr_nat h g in
                  p >= 8 /\ p < heap_size /\ p % 8 == 0 /\
                  Seq.mem (U64.uint_to_t p) objs /\
                  is_closure (U64.uint_to_t p) g))

/// Introduction: establish infix_wf from pointwise proof
val infix_wf_intro : (g: heap) -> (objs: seq obj_addr) ->
  (pf: (h: obj_addr -> Lemma (requires Seq.mem h objs /\ is_infix h g)
                              (ensures (let p = parent_closure_addr_nat h g in
                                        p >= 8 /\ p < heap_size /\ p % 8 == 0 /\
                                        Seq.mem (U64.uint_to_t p) objs /\
                                        is_closure (U64.uint_to_t p) g)))) ->
  Lemma (ensures infix_wf g objs)

/// Color change preserves is_infix
val color_change_preserves_is_infix : (obj: obj_addr) -> (addr: obj_addr) -> (g: heap) -> (c: color) ->
  Lemma (ensures is_infix addr (set_object_color obj g c) == is_infix addr g)

/// Color change preserves is_closure
val color_change_preserves_is_closure : (obj: obj_addr) -> (addr: obj_addr) -> (g: heap) -> (c: color) ->
  Lemma (ensures is_closure addr (set_object_color obj g c) == is_closure addr g)

/// Color change preserves resolve_object (colors don't change tags or wosize)
val color_change_preserves_resolve : (obj: obj_addr) -> (addr: obj_addr) -> (g: heap) -> (c: color) ->
  Lemma (ensures resolve_object addr (set_object_color obj g c) == resolve_object addr g)

/// Color change preserves infix_wf
val color_change_preserves_infix_wf : (obj: obj_addr) -> (g: heap) -> (c: color) -> (objs: seq obj_addr) ->
  Lemma (requires infix_wf g objs)
        (ensures infix_wf (set_object_color obj g c) objs)

/// resolve_object maps into the same objects list (under infix_wf)
val resolve_object_in_objects : (addr: obj_addr) -> (g: heap) -> (objs: seq obj_addr) ->
  Lemma (requires Seq.mem addr objs /\ infix_wf g objs)
        (ensures Seq.mem (resolve_object addr g) objs)

/// ---------------------------------------------------------------------------
/// Aggregate Color Predicates
/// ---------------------------------------------------------------------------

/// No grey objects in address list
val noGreyObjects_aux (g: heap) (addrs: seq hp_addr) : GTot bool
