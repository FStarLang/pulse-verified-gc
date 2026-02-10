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

let blue  : color = Header.Blue
let white : color = Header.White
let gray  : color = Header.Gray
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
  U64.shift_right hdr 10ul

/// Extract color from header (bits 8-9) — returns algebraic color
let getColor (hdr: U64.t) : color =
  let raw = U64.logand (U64.shift_right hdr 8ul) 3UL in
  // raw is 0-3, so unpack always succeeds
  match Header.unpack_color (U64.v raw) with
  | Some c -> c
  | None -> Header.Blue // unreachable: raw <= 3

/// Extract tag from header (bits 0-7)
let getTag (hdr: U64.t) : tag =
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

/// Header roundtrip: make then extract gets back original fields
/// TODO: prove from bitvector properties
assume val makeHeader_getWosize : (wz: wosize) -> (c: color) -> (t: tag) ->
  Lemma (getWosize (makeHeader wz c t) == wz)

assume val makeHeader_getColor : (wz: wosize) -> (c: color) -> (t: tag) ->
  Lemma (getColor (makeHeader wz c t) == c)

assume val makeHeader_getTag : (wz: wosize) -> (c: color) -> (t: tag) ->
  Lemma (getTag (makeHeader wz c t) == t)

/// ---------------------------------------------------------------------------
/// Object color predicates
/// ---------------------------------------------------------------------------

let color_of_object (hdr: U64.t) : color =
  getColor hdr

let is_blue_object (hdr: U64.t) : bool =
  getColor hdr = blue

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
  exists* (s: Seq.seq U8.t) (hdr: U64.t).
    is_heap heap s **
    pure (
      hdr == spec_read_word s (U64.v h) /\
      getWosize hdr == wz /\
      getColor hdr == c /\
      getTag hdr == t
    )

let isBlueObject (heap: heap_t) (h: hp_addr) : slprop =
  exists* wz t. is_object heap h wz blue t

let isWhiteObject (heap: heap_t) (h: hp_addr) : slprop =
  exists* wz t. is_object heap h wz white t

let isGrayObject (heap: heap_t) (h: hp_addr) : slprop =
  exists* wz t. is_object heap h wz gray t

let isBlackObject (heap: heap_t) (h: hp_addr) : slprop =
  exists* wz t. is_object heap h wz black t

/// ---------------------------------------------------------------------------
/// Color operations
/// ---------------------------------------------------------------------------

fn colorHeader (heap: heap_t) (h: hp_addr) (new_color: color)
  requires is_object heap h 'wz 'old_color 't
  ensures is_object heap h 'wz new_color 't
{
  unfold is_object;
  let hdr = read_word heap h;
  let wz = getWosize hdr;
  let t = getTag hdr;
  let new_hdr = makeHeader wz new_color t;
  makeHeader_getWosize wz new_color t;
  makeHeader_getColor wz new_color t;
  makeHeader_getTag wz new_color t;
  write_word heap h new_hdr;
  // TODO: need read_write_same lemma to close the gap
  admit()
}

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
let is_blue = is_blue_object
