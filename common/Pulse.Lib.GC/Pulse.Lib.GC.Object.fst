(*
   Pulse GC - Object Module (Shared Infrastructure)
   
   This module defines object headers, colors, and object predicates
   for the verified garbage collector.
   
   Uses algebraic color type (color_sem) from Pulse.Lib.Header.
*)

module Pulse.Lib.GC.Object

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.GC.Heap
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Seq = FStar.Seq
module Header = Pulse.Lib.Header

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

/// Object color — algebraic type from Pulse.Lib.Header
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

/// Pack color to numeric for header encoding
let pack_color (c: color) : U64.t = U64.uint_to_t (Header.pack_color c)

/// ---------------------------------------------------------------------------
/// Special tag values
/// ---------------------------------------------------------------------------

let closure_tag  : tag = 247UL
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

/// Extract color from header (bits 8-9) — returns algebraic color
#push-options "--z3rlimit 50"
let getColor (hdr: U64.t) : color =
  let raw = U64.logand (U64.shift_right hdr 8ul) 3UL in
  // raw is 0-3, so unpack always succeeds
  match Header.unpack_color (U64.v raw) with
  | Some c -> c
  | None -> Header.White // unreachable: raw <= 3
#pop-options

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

/// Local proof that logor #64 1 2 == 3 (Header.fst's copy is private)
private let logor_1_2_is_3 () : Lemma (UInt.logor #64 1 2 == 3) =
  UInt.logor_disjoint #64 2 1 1; UInt.logor_commutative #64 1 2

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"

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
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
let makeHeader_getWosize (wz: wosize) (c: color) (t: tag)
  : Lemma (getWosize (makeHeader wz c t) == wz)
  = let h : Header.header_sem = {Header.wosize=U64.v wz; Header.color=c; Header.tag=U64.v t} in
    makeHeader_eq_pack_header wz c t;
    Header.get_wosize_pack_header h
#pop-options

/// Header roundtrip: makeHeader then getColor
#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
let makeHeader_getColor (wz: wosize) (c: color) (t: tag)
  : Lemma (getColor (makeHeader wz c t) == c)
  = let h : Header.header_sem = {Header.wosize=U64.v wz; Header.color=c; Header.tag=U64.v t} in
    makeHeader_eq_pack_header wz c t;
    Header.get_color_pack_header h;
    Header.pack_unpack_color c;
    logor_1_2_is_3 ();
    Header.mask_tag_value ()
#pop-options

/// Header roundtrip: makeHeader then getTag
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
let makeHeader_getTag (wz: wosize) (c: color) (t: tag)
  : Lemma (getTag (makeHeader wz c t) == t)
  = let h : Header.header_sem = {Header.wosize=U64.v wz; Header.color=c; Header.tag=U64.v t} in
    makeHeader_eq_pack_header wz c t;
    Header.get_tag_pack_header h;
    Header.mask_tag_value ()
#pop-options

/// makeHeader from extracted fields with new color == set_color64
/// This is the key bridge: extracting wosize/tag and reconstructing with a new color
/// equals the bitwise set_color64 operation.
#push-options "--z3rlimit 600 --fuel 0 --ifuel 0"
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

let is_object (heap: heap_t) (h: hp_addr) 
              (wz: wosize) (c: color) (t: tag) 
    : slprop =
  exists* (s: heap_state).
    is_heap heap s **
    pure (
      getWosize (spec_read_word s (U64.v h)) == wz /\
      getColor (spec_read_word s (U64.v h)) == c /\
      getTag (spec_read_word s (U64.v h)) == t
    )

let isWhiteObject (heap: heap_t) (h: hp_addr) : slprop =
  exists* wz t. is_object heap h wz white t

let isGrayObject (heap: heap_t) (h: hp_addr) : slprop =
  exists* wz t. is_object heap h wz gray t

let isBlackObject (heap: heap_t) (h: hp_addr) : slprop =
  exists* wz t. is_object heap h wz black t

/// ---------------------------------------------------------------------------
/// Color operations
/// ---------------------------------------------------------------------------

/// Ghost helper: package is_heap + pure facts into is_object  
ghost fn package_is_object (heap: heap_t) (h: hp_addr) 
                             (wz: wosize) (c: color) (t: tag)
                             (new_hdr: U64.t) (old_s: heap_state)
  requires is_heap heap (spec_write_word old_s (U64.v h) new_hdr) ** 
           pure (getWosize new_hdr == wz /\
                 getColor new_hdr == c /\
                 getTag new_hdr == t /\
                 U64.v h + 8 <= heap_size)
  ensures is_object heap h wz c t
{
  read_write_same old_s (U64.v h) new_hdr;
  fold (is_object heap h wz c t)
}

#push-options "--z3rlimit 200"
fn colorHeader (heap: heap_t) (h: hp_addr) (new_color: color)
  requires is_object heap h 'wz 'old_color 't
  ensures is_object heap h 'wz new_color 't
{
  unfold is_object;
  with old_s. _;
  hp_addr_plus_8 h;
  let hdr = read_word heap h;
  let wz = getWosize hdr;
  let t = getTag hdr;
  let new_hdr = makeHeader wz new_color t;
  makeHeader_getWosize wz new_color t;
  makeHeader_getColor wz new_color t;
  makeHeader_getTag wz new_color t;
  write_word heap h new_hdr;
  package_is_object heap h wz new_color t new_hdr old_s;
  rewrite (is_object heap h wz new_color t)
       as (is_object heap h 'wz new_color 't)
}
#pop-options

/// ---------------------------------------------------------------------------
/// Pointer detection
/// ---------------------------------------------------------------------------

let isPointer (v: U64.t) : bool =
  U64.v v >= U64.v mword &&
  U64.v v < heap_size &&
  U64.v v % U64.v mword = 0

/// ---------------------------------------------------------------------------
/// Semantic aliases
/// ---------------------------------------------------------------------------

let get_color = color_of_object
let get_wosize = getWosize
let get_tag = getTag
let is_black = is_black_object
let is_white = is_white_object
let is_gray = is_gray_object
