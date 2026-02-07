(*
   Pulse GC - Object Module
   
   This module defines object headers, colors, and object predicates
   for the verified garbage collector.
   
   Based on: Proofs/Spec.Object.fsti
*)

module Pulse.Lib.GC.Object

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.GC.Heap
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Seq = FStar.Seq

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

/// Object color (2 bits, values 0-3)
type color = c:U64.t{U64.v c <= 3}

/// Object tag (8 bits, values 0-255)
type tag = t:U64.t{U64.v t <= 255}

/// ---------------------------------------------------------------------------
/// Color constants
/// ---------------------------------------------------------------------------

let blue  : color = 0UL  // Free/unallocated
let white : color = 1UL  // Unmarked (potentially garbage)
let gray  : color = 2UL  // Marked but not scanned
let black : color = 3UL  // Marked and scanned (reachable)

/// ---------------------------------------------------------------------------
/// Special tag values
/// ---------------------------------------------------------------------------

let closure_tag  : tag = 247UL  // Closure object
let infix_tag    : tag = 249UL  // Infix object (inside closure)
let no_scan_tag  : tag = 251UL  // Object with no pointers to scan

/// ---------------------------------------------------------------------------
/// Header field extraction
/// ---------------------------------------------------------------------------

/// Extract wosize from header (bits 10-63)
let getWosize (hdr: U64.t) : wosize =
  U64.shift_right hdr 10ul

/// Extract color from header (bits 8-9)
let getColor (hdr: U64.t) : color =
  U64.logand (U64.shift_right hdr 8ul) 3UL

/// Extract tag from header (bits 0-7)
let getTag (hdr: U64.t) : tag =
  U64.logand hdr 0xFFUL

/// ---------------------------------------------------------------------------
/// Header construction
/// ---------------------------------------------------------------------------

/// Create a header from wosize, color, and tag
let makeHeader (wz: wosize) (c: color) (t: tag) : U64.t =
  let wz_shifted = U64.shift_left wz 10ul in
  let c_shifted = U64.shift_left c 8ul in
  U64.logor wz_shifted (U64.logor c_shifted t)

/// ---------------------------------------------------------------------------
/// Object color predicates
/// ---------------------------------------------------------------------------

/// Get color of object at given header address
let color_of_object (hdr: U64.t) : color =
  getColor hdr

/// Check if object is blue (free)
let is_blue_object (hdr: U64.t) : bool =
  getColor hdr = blue

/// Check if object is white (unmarked)
let is_white_object (hdr: U64.t) : bool =
  getColor hdr = white

/// Check if object is gray (marked, not scanned)
let is_gray_object (hdr: U64.t) : bool =
  getColor hdr = gray

/// Check if object is black (marked and scanned)
let is_black_object (hdr: U64.t) : bool =
  getColor hdr = black

/// ---------------------------------------------------------------------------
/// Object predicates (slprops)
/// ---------------------------------------------------------------------------

/// An object at address h with given properties
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

/// Object is blue (free)
let isBlueObject (heap: heap_t) (h: hp_addr) : slprop =
  exists* wz t. is_object heap h wz blue t

/// Object is white (unmarked)
let isWhiteObject (heap: heap_t) (h: hp_addr) : slprop =
  exists* wz t. is_object heap h wz white t

/// Object is gray (to be scanned)
let isGrayObject (heap: heap_t) (h: hp_addr) : slprop =
  exists* wz t. is_object heap h wz gray t

/// Object is black (reachable)
let isBlackObject (heap: heap_t) (h: hp_addr) : slprop =
  exists* wz t. is_object heap h wz black t

/// ---------------------------------------------------------------------------
/// Color operations
/// ---------------------------------------------------------------------------

/// Color an object with a new color (modifies header in place)
fn colorHeader (heap: heap_t) (h: hp_addr) (new_color: color)
  requires is_object heap h 'wz 'old_color 't
  ensures is_object heap h 'wz new_color 't
{
  // Read current header
  let hdr = read_word heap h;
  
  // Create new header with updated color
  let wz = getWosize hdr;
  let t = getTag hdr;
  let new_hdr = makeHeader wz new_color t;
  
  // Write new header
  write_word heap h new_hdr;
  
  // Fold the updated predicate
  fold (is_object heap h 'wz new_color 't)
}

/// ---------------------------------------------------------------------------
/// Pointer detection
/// ---------------------------------------------------------------------------

/// Check if a value looks like a pointer (word-aligned, within heap)
let isPointer (v: U64.t) : bool =
  U64.v v >= U64.v mword /\
  U64.v v < heap_size /\
  U64.v v % U64.v mword == 0

/// ---------------------------------------------------------------------------
/// Semantic aliases (cleaner names)
/// ---------------------------------------------------------------------------

let get_color = color_of_object
let get_wosize = getWosize
let get_tag = getTag
let is_black = is_black_object
let is_white = is_white_object
let is_gray = is_gray_object
let is_blue = is_blue_object
