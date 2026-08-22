(*
   Pulse GC - Object Module (Shared Infrastructure)
   
   This module defines object headers, colors, and object predicates
   for the verified garbage collector.
   
   Uses algebraic color type (color_sem) from GC.Lib.Header.
*)

module GC.Impl.Object

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Impl.Heap
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Seq = FStar.Seq
module Header = GC.Lib.Header
module SpecObject = GC.Spec.Object
module SpecHeap = GC.Spec.Heap

/// ---------------------------------------------------------------------------
/// Object Header Layout (64-bit word)
/// ---------------------------------------------------------------------------
///
/// | wosize (54 bits) | color (2 bits) | tag (8 bits) |
/// |    bits 10-63    |   bits 8-9     |   bits 0-7   |
///

/// ---------------------------------------------------------------------------
/// Types
/// ---------------------------------------------------------------------------

/// Object size in words (54 bits, max 2^54 - 1)
type wosize = w:U64.t{U64.v w <= pow2 54 - 1}

/// Object color — algebraic type from GC.Lib.Header
type color = Header.color_sem

/// Object tag (8 bits, values 0-255)
type tag = t:U64.t{U64.v t <= 255}

/// ---------------------------------------------------------------------------
/// Color constants
/// ---------------------------------------------------------------------------

let white : color = Header.White
let gray  : color = Header.Gray
let blue  : color = Header.Blue
let black : color = Header.Black

/// Pack color to numeric for header encoding — directly returns U64 literal
/// so KaRaMeL extracts clean C without going through uint_t 64.
inline_for_extraction
let pack_color (c: color) : (r:U64.t{U64.v r == Header.pack_color c}) =
  match c with
  | Header.White -> 0UL
  | Header.Gray  -> 1UL
  | Header.Blue  -> 2UL
  | Header.Black -> 3UL

/// ---------------------------------------------------------------------------
/// Special tag values
/// ---------------------------------------------------------------------------

let infix_tag    : tag = 249UL
let no_scan_tag  : tag = 251UL

/// ---------------------------------------------------------------------------
/// Header field extraction
/// ---------------------------------------------------------------------------

/// Extract wosize from header (bits 10-63)
let getWosize (hdr: U64.t) : wosize =
  FStar.UInt.shift_right_value_lemma #64 (U64.v hdr) 10;
  FStar.Math.Lemmas.lemma_div_lt_nat (U64.v hdr) 64 10;
  U64.shift_right hdr 10ul

/// Extract color from header (bits 8-9) — directly matches U64 value
/// so KaRaMeL extracts clean C without option type or uint_t 64.
inline_for_extraction
let getColor (hdr: U64.t) : color =
  let raw = U64.logand (U64.shift_right hdr 8ul) 3UL in
  if raw = 0UL then Header.White
  else if raw = 1UL then Header.Gray
  else if raw = 2UL then Header.Blue
  else Header.Black

/// Extract tag from header (bits 0-7)
let getTag (hdr: U64.t) : tag =
  FStar.UInt.logand_le #64 (U64.v hdr) 255;
  U64.logand hdr 0xFFUL

/// ---------------------------------------------------------------------------
/// Header construction
/// ---------------------------------------------------------------------------

/// Create a header from wosize, color, and tag
let makeHeader (wz: wosize) (c: color) (t: tag) : U64.t =
  let c_num = pack_color c in
  let wz_shifted = U64.shift_left wz 10ul in
  let c_shifted = U64.shift_left c_num 8ul in
  U64.logor wz_shifted (U64.logor c_shifted t)

/// ---------------------------------------------------------------------------
/// Bridge: Object.fst's makeHeader ↔ Header.fst's pack_header
/// ---------------------------------------------------------------------------
///
/// makeHeader and pack_header compute the same OR of three terms
/// (wz<<10, c<<8, t) but in different argument order. We prove
/// equality bit-by-bit using logor_definition + nth_lemma.

module UInt = FStar.UInt
#push-options "--z3rlimit 25 --fuel 0 --ifuel 0"

/// U64.v (makeHeader wz c t) == pack_header {wosize=U64.v wz; color=c; tag=U64.v t}
let makeHeader_eq_pack_header (wz: wosize) (c: color) (t: tag)
  : Lemma (U64.v (makeHeader wz c t) ==
           Header.pack_header ({Header.wosize=U64.v wz; Header.color=c; Header.tag=U64.v t}))
  = let lhs = U64.v (makeHeader wz c t) in
    let rhs = Header.pack_header ({Header.wosize=U64.v wz; Header.color=c; Header.tag=U64.v t}) in
    let w = U64.v wz in
    let col = Header.pack_color c in
    let tg = U64.v t in
    // LHS = logor (w<<10) (logor (col<<8) tg)
    // RHS = logor tg (logor (col<<8) (w<<10))
    // Equal bit-by-bit since (A || (B || C)) <==> (C || (B || A))
    let aux (i: nat{i < 64}) : Lemma (UInt.nth #64 lhs i == UInt.nth #64 rhs i) =
      UInt.logor_definition #64 (UInt.shift_left #64 w 10) (UInt.logor #64 (UInt.shift_left #64 col 8) tg) i;
      UInt.logor_definition #64 (UInt.shift_left #64 col 8) tg i;
      UInt.logor_definition #64 tg (UInt.logor #64 (UInt.shift_left #64 col 8) (UInt.shift_left #64 w 10)) i;
      UInt.logor_definition #64 (UInt.shift_left #64 col 8) (UInt.shift_left #64 w 10) i
    in
    FStar.Classical.forall_intro aux;
    UInt.nth_lemma #64 lhs rhs

#pop-options

/// Header roundtrip: makeHeader then getWosize
/// Header roundtrip: makeHeader then getColor
/// Header roundtrip: makeHeader then getTag
/// makeHeader from extracted fields with new color == set_color64
/// This is the key bridge: extracting wosize/tag and reconstructing with a new color
/// equals the bitwise set_color64 operation.
#push-options "--z3rlimit 150 --fuel 0 --ifuel 0"
let makeHeader_eq_set_color64 (hdr: U64.t) (c: color)
  : Lemma (requires Header.valid_header64 hdr)
          (ensures makeHeader (getWosize hdr) c (getTag hdr) ==
                   Header.set_color64 hdr (U64.uint_to_t (Header.pack_color c)))
  = let wz = getWosize hdr in
    let tag = getTag hdr in
    // Step 2: Connect getWosize/getTag to Header.get_wosize/get_tag
    Header.get_wosize_bound (U64.v hdr);
    Header.get_tag_bound (U64.v hdr);
    Header.mask_tag_value ();
    let h_sem : Header.header_sem = { Header.wosize = Header.get_wosize (U64.v hdr);
                                       Header.color = c;
                                       Header.tag = Header.get_tag (U64.v hdr) } in
    // Step 1: Lib.makeHeader → pack_header (at value level)
    makeHeader_eq_pack_header wz c tag;
    // Step 3: repack_set_color64 gives pack_header64{extracted fields} == set_color64
    Header.repack_set_color64 hdr c;
    // Step 4: pack_header64 roundtrip via U64.v
    U64.vu_inv (Header.pack_header h_sem);
    // Chain: U64.v (makeHeader wz c tag) == pack_header h_sem == U64.v (set_color64 ...)
    U64.v_inj (makeHeader wz c tag) (Header.set_color64 hdr (U64.uint_to_t (Header.pack_color c)))
#pop-options

/// ---------------------------------------------------------------------------
/// Object color predicates
/// ---------------------------------------------------------------------------

let color_of_object (hdr: U64.t) : color =
  getColor hdr

let is_white_object (hdr: U64.t) : bool =
  getColor hdr = white

let is_gray_object (hdr: U64.t) : bool =
  getColor hdr = gray

let is_black_object (hdr: U64.t) : bool =
  getColor hdr = black

/// ---------------------------------------------------------------------------
/// Object predicates (slprops)
/// ---------------------------------------------------------------------------

/// ---------------------------------------------------------------------------
/// Color operations
/// ---------------------------------------------------------------------------
/// ---------------------------------------------------------------------------
/// Pointer detection
/// ---------------------------------------------------------------------------
/// ---------------------------------------------------------------------------
/// Semantic aliases
/// ---------------------------------------------------------------------------

let is_black = is_black_object
let is_white = is_white_object
let is_gray = is_gray_object

/// ---------------------------------------------------------------------------
/// Bridge lemmas: Pulse Lib.Object ↔ Spec.Object
/// ---------------------------------------------------------------------------

/// Lib.getWosize == Spec.getWosize (both compute shift_right 10)
let getWosize_eq (hdr: U64.t) : Lemma (getWosize hdr == SpecObject.getWosize hdr) =
  SpecObject.getWosize_spec hdr

/// Lib.getTag == Spec.getTag (both compute logand with 0xFF)
let getTag_eq (hdr: U64.t) : Lemma (getTag hdr == SpecObject.getTag hdr) =
  SpecObject.getTag_spec hdr

/// Lib.getColor == Spec.getColor (both extract bits 8-9)
#push-options "--z3rlimit 12"
let getColor_eq (hdr: U64.t) : Lemma (getColor hdr == SpecObject.getColor hdr) =
  Header.get_color_val (U64.v hdr);
  Header.get_color_bound (U64.v hdr);
  SpecObject.getColor_raw hdr
#pop-options

/// Lib.makeHeader on extracted fields == Spec.colorHeader
let lib_makeHeader_eq_colorHeader (hdr: U64.t) (c: color)
  : Lemma (requires Header.valid_header64 hdr)
          (ensures makeHeader (getWosize hdr) c (getTag hdr) == SpecObject.colorHeader hdr c)
  = makeHeader_eq_set_color64 hdr c;
    SpecObject.colorHeader_spec hdr c
