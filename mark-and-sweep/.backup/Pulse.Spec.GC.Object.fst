/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.Object - Object headers and colors (Semantic Types Version)
/// ---------------------------------------------------------------------------
///
/// This module provides:
/// - Color type and constants (re-exported from Header)
/// - Header field extraction via semantic types
/// - Color predicates (is_black, is_white, etc.)
///
/// Header layout (64 bits):
///   bits 0-7   : tag (8 bits)
///   bits 8-9   : color (2 bits: blue=0, white=1, gray=2, black=3)
///   bits 10-63 : wosize (54 bits)

module Pulse.Spec.GC.Object

open FStar.Seq
open FStar.Mul

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Heap

/// Import semantic types from Header
module Header = Pulse.Lib.Header

/// ---------------------------------------------------------------------------
/// Re-export Color Type from Header
/// ---------------------------------------------------------------------------

/// Open Header to get color_sem constructors (Blue, White, Gray, Black)
open Pulse.Lib.Header

/// Pack/unpack for colors (re-export)
let pack_color = Header.pack_color
let unpack_color = Header.unpack_color

/// ---------------------------------------------------------------------------
/// Legacy Color Constants (for backward compatibility)
/// ---------------------------------------------------------------------------

/// U64.t color values - defined via pack_color for consistency
let blue : (c:U64.t{U64.v c < 4}) = U64.uint_to_t (Header.pack_color Blue)    // = 0UL
let white : (c:U64.t{U64.v c < 4}) = U64.uint_to_t (Header.pack_color White)  // = 1UL  
let gray : (c:U64.t{U64.v c < 4}) = U64.uint_to_t (Header.pack_color Gray)    // = 2UL
let black : (c:U64.t{U64.v c < 4}) = U64.uint_to_t (Header.pack_color Black)  // = 3UL

/// Key connection: U64.t color = pack_color of semantic color
let blue_eq : squash (U64.v blue = Header.pack_color Blue) = ()
let white_eq : squash (U64.v white = Header.pack_color White) = ()
let gray_eq : squash (U64.v gray = Header.pack_color Gray) = ()
let black_eq : squash (U64.v black = Header.pack_color Black) = ()

/// ---------------------------------------------------------------------------
/// Tag Constants
/// ---------------------------------------------------------------------------

let closure_tag : U64.t = 247UL
let infix_tag : U64.t = 249UL
let no_scan_tag : U64.t = 251UL

/// ---------------------------------------------------------------------------
/// Header Field Extraction (Using Semantic Types)
/// ---------------------------------------------------------------------------

/// Get color from header as U64.t (legacy interface)
let getColor (hdr: U64.t) : U64.t =
  U64.uint_to_t (Header.get_color (U64.v hdr))

/// Get tag from header
let getTag (hdr: U64.t) : U64.t =
  U64.uint_to_t (Header.get_tag (U64.v hdr))

/// Get wosize from header
let getWosize (hdr: U64.t) : U64.t =
  U64.uint_to_t (Header.get_wosize (U64.v hdr))

/// Set color in header (legacy interface)
let setColor (hdr: U64.t) (c: U64.t{U64.v c < 4}) : U64.t =
  U64.uint_to_t (Header.set_color (U64.v hdr) (U64.v c))

/// getColor always returns a value < 4
let getColor_bound (hdr: U64.t) : Lemma (U64.v (getColor hdr) < 4) =
  Header.get_color_bound (U64.v hdr)

/// getColor returns one of the four color constants  
let getColor_is_color (hdr: U64.t)
  : Lemma (getColor hdr = blue \/ getColor hdr = white \/
           getColor hdr = gray \/ getColor hdr = black)
  = getColor_bound hdr;
    // getColor hdr < 4, and blue=0, white=1, gray=2, black=3
    // So it must be one of them
    assert_norm (U64.v blue = 0);
    assert_norm (U64.v white = 1);
    assert_norm (U64.v gray = 2);
    assert_norm (U64.v black = 3)

/// ---------------------------------------------------------------------------
/// Color Predicates on Heap (Using Semantic Types)
/// ---------------------------------------------------------------------------

/// Get semantic color of object at header address
let color_of_object_sem (h_addr: hp_addr) (g: heap) : color_sem =
  let hdr = read_word g h_addr in
  match Header.unpack_color (Header.get_color (U64.v hdr)) with
  | Some c -> c
  | None -> Blue  // Should not happen for valid headers

/// Get color as U64.t (legacy interface)
let color_of_object (h_addr: hp_addr) (g: heap) : U64.t =
  let hdr = read_word g h_addr in
  getColor hdr

/// Object is black (reachable) - uses U64.t comparison for compatibility
let is_black (h_addr: hp_addr) (g: heap) : bool =
  color_of_object h_addr g = black

/// Object is white (not yet visited)
let is_white (h_addr: hp_addr) (g: heap) : bool =
  color_of_object h_addr g = white

/// Object is gray (visited but not scanned)
let is_gray (h_addr: hp_addr) (g: heap) : bool =
  color_of_object h_addr g = gray

/// Object is blue (free/unallocated)
let is_blue (h_addr: hp_addr) (g: heap) : bool =
  color_of_object h_addr g = blue

/// ---------------------------------------------------------------------------
/// Tag Predicates
/// ---------------------------------------------------------------------------

/// Get tag of object at header address
let tag_of_object (h_addr: hp_addr) (g: heap) : U64.t =
  let hdr = read_word g h_addr in
  getTag hdr

/// Get wosize of object at header address
let wosize_of_object (h_addr: hp_addr) (g: heap) : U64.t =
  let hdr = read_word g h_addr in
  getWosize hdr

/// Object is a closure
let is_closure (h_addr: hp_addr) (g: heap) : bool =
  tag_of_object h_addr g = closure_tag

/// Object is an infix object
let is_infix (h_addr: hp_addr) (g: heap) : bool =
  tag_of_object h_addr g = infix_tag

/// Object should not be scanned (no pointers)
let is_no_scan (h_addr: hp_addr) (g: heap) : bool =
  U64.gte (tag_of_object h_addr g) no_scan_tag

/// ---------------------------------------------------------------------------
/// Color Change Operations
/// ---------------------------------------------------------------------------

/// Set object color (using semantic color)
let set_object_color_sem (h_addr: hp_addr) (g: heap) (c: color_sem) : heap =
  let hdr = read_word g h_addr in
  let new_hdr = U64.uint_to_t (Header.set_color (U64.v hdr) (Header.pack_color c)) in
  write_word g h_addr new_hdr

/// Set object color (legacy interface)
let set_object_color (h_addr: hp_addr) (g: heap) (c: U64.t{U64.v c < 4}) : heap =
  let hdr = read_word g h_addr in
  let new_hdr = setColor hdr c in
  write_word g h_addr new_hdr

/// Make object black - uses U64.t color for simplicity
let makeBlack (h_addr: hp_addr) (g: heap) : heap =
  set_object_color h_addr g black

/// Make object white
let makeWhite (h_addr: hp_addr) (g: heap) : heap =
  set_object_color h_addr g white

/// Make object gray
let makeGray (h_addr: hp_addr) (g: heap) : heap =
  set_object_color h_addr g gray

/// Make object blue (free it)
let makeBlue (h_addr: hp_addr) (g: heap) : heap =
  set_object_color h_addr g blue

/// ---------------------------------------------------------------------------
/// Key Lemmas (Trivial with Semantic Types)
/// ---------------------------------------------------------------------------

/// getColor followed by setColor returns the color
let getColor_setColor (hdr: U64.t) (c: U64.t{U64.v c < 4})
  : Lemma (getColor (setColor hdr c) == c)
  = Header.getColor_setColor (U64.v hdr) (U64.v c)

/// setColor preserves wosize
let setColor_preserves_wosize (hdr: U64.t) (c: U64.t{U64.v c < 4})
  : Lemma (getWosize (setColor hdr c) == getWosize hdr)
  = Header.setColor_preserves_wosize (U64.v hdr) (U64.v c)

/// setColor preserves tag
let setColor_preserves_tag (hdr: U64.t) (c: U64.t{U64.v c < 4})
  : Lemma (getTag (setColor hdr c) == getTag hdr)
  = Header.setColor_preserves_tag (U64.v hdr) (U64.v c)

/// ---------------------------------------------------------------------------
/// Color Change Correctness Lemmas (Trivial with getColor_setColor!)
/// ---------------------------------------------------------------------------

/// After making black, object is black
let makeBlack_is_black (h_addr: hp_addr) (g: heap)
  : Lemma (is_black h_addr (makeBlack h_addr g))
  = read_write_same g h_addr (setColor (read_word g h_addr) black);
    getColor_setColor (read_word g h_addr) black

/// After making white, object is white
let makeWhite_is_white (h_addr: hp_addr) (g: heap)
  : Lemma (is_white h_addr (makeWhite h_addr g))
  = read_write_same g h_addr (setColor (read_word g h_addr) white);
    getColor_setColor (read_word g h_addr) white

/// After making gray, object is gray
let makeGray_is_gray (h_addr: hp_addr) (g: heap)
  : Lemma (is_gray h_addr (makeGray h_addr g))
  = read_write_same g h_addr (setColor (read_word g h_addr) gray);
    getColor_setColor (read_word g h_addr) gray

/// After making blue, object is blue
let makeBlue_is_blue (h_addr: hp_addr) (g: heap)
  : Lemma (is_blue h_addr (makeBlue h_addr g))
  = read_write_same g h_addr (setColor (read_word g h_addr) blue);
    getColor_setColor (read_word g h_addr) blue

/// ---------------------------------------------------------------------------
/// Preservation Lemmas
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50"

/// Color change preserves wosize
let color_preserves_wosize (h_addr: hp_addr) (g: heap) (c: U64.t{U64.v c < 4})
  : Lemma (wosize_of_object h_addr (set_object_color h_addr g c) == wosize_of_object h_addr g)
  = let hdr = read_word g h_addr in
    let new_hdr = setColor hdr c in
    read_write_same g h_addr new_hdr;
    setColor_preserves_wosize hdr c

/// Color change preserves tag
let color_preserves_tag (h_addr: hp_addr) (g: heap) (c: U64.t{U64.v c < 4})
  : Lemma (tag_of_object h_addr (set_object_color h_addr g c) == tag_of_object h_addr g)
  = let hdr = read_word g h_addr in
    let new_hdr = setColor hdr c in
    read_write_same g h_addr new_hdr;
    setColor_preserves_tag hdr c

#pop-options

/// ---------------------------------------------------------------------------
/// Locality Lemmas
/// ---------------------------------------------------------------------------

/// Color change at one object doesn't affect other objects
let color_change_locality (h_addr1: hp_addr) (h_addr2: hp_addr) (g: heap) (c: U64.t{U64.v c < 4})
  : Lemma (requires h_addr1 <> h_addr2 /\
                    (U64.v h_addr1 + U64.v mword <= U64.v h_addr2 \/
                     U64.v h_addr2 + U64.v mword <= U64.v h_addr1))
          (ensures color_of_object h_addr2 (set_object_color h_addr1 g c) == color_of_object h_addr2 g)
  = read_write_different g h_addr1 h_addr2 (setColor (read_word g h_addr1) c)

/// Color change at one object doesn't affect header at different address
let color_change_header_locality (h_addr1: hp_addr) (h_addr2: hp_addr) (g: heap) (c: U64.t{U64.v c < 4})
  : Lemma (requires h_addr1 <> h_addr2 /\
                    (U64.v h_addr1 + U64.v mword <= U64.v h_addr2 \/
                     U64.v h_addr2 + U64.v mword <= U64.v h_addr1))
          (ensures read_word (set_object_color h_addr1 g c) h_addr2 == read_word g h_addr2)
  = read_write_different g h_addr1 h_addr2 (setColor (read_word g h_addr1) c)

/// Color change preserves fields (color only modifies header)
let color_preserves_field (h_addr: hp_addr) (g: heap) (c: U64.t{U64.v c < 4}) (i: U64.t{U64.v i >= 1})
  : Lemma (requires U64.v h_addr + U64.v mword * (U64.v i + 1) <= heap_size)
          (ensures read_word (set_object_color h_addr g c) (U64.add h_addr (U64.mul mword i)) ==
                   read_word g (U64.add h_addr (U64.mul mword i)))
  = let field_addr = U64.add h_addr (U64.mul mword i) in
    read_write_different g h_addr field_addr (setColor (read_word g h_addr) c)

/// Color change preserves is_no_scan
let color_preserves_is_no_scan (h_addr: hp_addr) (g: heap) (c: U64.t{U64.v c < 4})
  : Lemma (is_no_scan h_addr (set_object_color h_addr g c) == is_no_scan h_addr g)
  = color_preserves_tag h_addr g c

/// ---------------------------------------------------------------------------
/// makeBlack/makeGray Locality Lemmas (trivial via color_change_locality)
/// ---------------------------------------------------------------------------

/// makeBlack on h1 preserves is_black predicate at different address h2
let makeBlack_preserves_other_black (h1: hp_addr) (h2: hp_addr) (g: heap)
  : Lemma (requires h1 <> h2 /\
                    (U64.v h1 + U64.v mword <= U64.v h2 \/
                     U64.v h2 + U64.v mword <= U64.v h1))
          (ensures is_black h2 (makeBlack h1 g) == is_black h2 g)
  = color_change_locality h1 h2 g black

/// makeBlack on h1 preserves is_white predicate at different address h2
let makeBlack_preserves_other_white (h1: hp_addr) (h2: hp_addr) (g: heap)
  : Lemma (requires h1 <> h2 /\
                    (U64.v h1 + U64.v mword <= U64.v h2 \/
                     U64.v h2 + U64.v mword <= U64.v h1))
          (ensures is_white h2 (makeBlack h1 g) == is_white h2 g)
  = color_change_locality h1 h2 g black

/// makeBlack on h1 preserves is_gray predicate at different address h2
let makeBlack_preserves_other_gray (h1: hp_addr) (h2: hp_addr) (g: heap)
  : Lemma (requires h1 <> h2 /\
                    (U64.v h1 + U64.v mword <= U64.v h2 \/
                     U64.v h2 + U64.v mword <= U64.v h1))
          (ensures is_gray h2 (makeBlack h1 g) == is_gray h2 g)
  = color_change_locality h1 h2 g black

/// makeGray on h1 preserves is_black predicate at different address h2
let makeGray_preserves_other_black (h1: hp_addr) (h2: hp_addr) (g: heap)
  : Lemma (requires h1 <> h2 /\
                    (U64.v h1 + U64.v mword <= U64.v h2 \/
                     U64.v h2 + U64.v mword <= U64.v h1))
          (ensures is_black h2 (makeGray h1 g) == is_black h2 g)
  = color_change_locality h1 h2 g gray

/// makeBlue on h1 preserves is_black predicate at different address h2
let makeBlue_preserves_other_black (h1: hp_addr) (h2: hp_addr) (g: heap)
  : Lemma (requires h1 <> h2 /\
                    (U64.v h1 + U64.v mword <= U64.v h2 \/
                     U64.v h2 + U64.v mword <= U64.v h1))
          (ensures is_black h2 (makeBlue h1 g) == is_black h2 g)
  = color_change_locality h1 h2 g blue

/// makeWhite on h1 preserves is_black predicate at different address h2
let makeWhite_preserves_other_black (h1: hp_addr) (h2: hp_addr) (g: heap)
  : Lemma (requires h1 <> h2 /\
                    (U64.v h1 + U64.v mword <= U64.v h2 \/
                     U64.v h2 + U64.v mword <= U64.v h1))
          (ensures is_black h2 (makeWhite h1 g) == is_black h2 g)
  = color_change_locality h1 h2 g white

/// ---------------------------------------------------------------------------
/// No Gray Objects Predicate
/// ---------------------------------------------------------------------------

/// Check if no gray objects exist in a region
let rec noGreyObjects_aux (g: heap) (addrs: seq hp_addr)
  : Tot bool (decreases Seq.length addrs) =
  if Seq.length addrs = 0 then true
  else
    let h_addr = Seq.head addrs in
    (not (is_gray h_addr g)) && noGreyObjects_aux g (Seq.tail addrs)

/// ---------------------------------------------------------------------------
/// All Objects White Predicate (for state reset)
/// ---------------------------------------------------------------------------

let rec allWhiteOrBlue_aux (g: heap) (addrs: seq hp_addr)
  : Tot bool (decreases Seq.length addrs) =
  if Seq.length addrs = 0 then true
  else
    let h_addr = Seq.head addrs in
    (is_white h_addr g || is_blue h_addr g) && allWhiteOrBlue_aux g (Seq.tail addrs)

/// ---------------------------------------------------------------------------
/// Color Preservation Lemmas (for use with locality)
/// ---------------------------------------------------------------------------

/// If color_of_object is preserved and object was black, it stays black
let color_preserved_black (h: hp_addr) (g1 g2: heap)
  : Lemma (requires color_of_object h g1 == color_of_object h g2 /\ is_black h g1)
          (ensures is_black h g2)
  = ()

/// If color_of_object is preserved and object was white, it stays white
let color_preserved_white (h: hp_addr) (g1 g2: heap)
  : Lemma (requires color_of_object h g1 == color_of_object h g2 /\ is_white h g1)
          (ensures is_white h g2)
  = ()

/// If color_of_object is preserved and object was gray, it stays gray  
let color_preserved_gray (h: hp_addr) (g1 g2: heap)
  : Lemma (requires color_of_object h g1 == color_of_object h g2 /\ is_gray h g1)
          (ensures is_gray h g2)
  = ()

/// If color_of_object is preserved and object was blue, it stays blue
let color_preserved_blue (h: hp_addr) (g1 g2: heap)
  : Lemma (requires color_of_object h g1 == color_of_object h g2 /\ is_blue h g1)
          (ensures is_blue h g2)
  = ()
