/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.Heap - the heap operations of the page allocator
/// ---------------------------------------------------------------------------
///
/// The specification reads and writes the heap through guarded helpers:
/// `GC.Spec.Pages.Shape.hdr g a` is the word at `a`, or 0 where `a` is not a
/// word of the heap, and `GC.Spec.Pages.Blocks.wr g a v` writes `v` at `a`,
/// or nothing.  `hdr_at` and `wr` do the same in memory, so code built from
/// them follows the specification even where it does not know that an
/// address is in the heap.
///
/// The header values the specification writes (`ohdr`, `bhdr`, `blue_hdr`,
/// `colorHeader`) are computed here with `GC.Impl.Object`'s `makeHeader`,
/// which extracts to shifts and ors, and proved equal.

module GC.Impl.Pages.Heap

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Impl.Heap
open GC.Impl.Pages.Params

module U64 = FStar.UInt64
module Seq = FStar.Seq
module Base = GC.Spec.Base
module SH = GC.Spec.Heap
module SO = GC.Spec.Object
module IO = GC.Impl.Object
module Hd = GC.Lib.Header
module Sh = GC.Spec.Pages.Shape
module B = GC.Spec.Pages.Blocks
module In = GC.Spec.Pages.Init

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Header values
/// ---------------------------------------------------------------------------

/// A header of wosize `wz`, colour `c` and tag 0, as the specification's
/// `makeHeader` builds it.
inline_for_extraction
let mk_hdr (wz: U64.t{U64.v wz < pow2 54}) (c: Hd.color_sem)
  : r: U64.t{r == SO.makeHeader wz c 0UL}
  = IO.makeHeader_eq_pack_header wz c 0UL;
    SO.makeHeader_is_pack_header64 wz c 0UL;
    let r = IO.makeHeader wz c 0UL in
    U64.v_inj r (SO.makeHeader wz c 0UL);
    r

/// The header `h` with its colour set to `c`.
inline_for_extraction
let recolour_hdr (h: U64.t) (c: Hd.color_sem) : r: U64.t{r == SO.colorHeader h c}
  = SO.all_headers_valid h;
    IO.lib_makeHeader_eq_colorHeader h c;
    IO.makeHeader (IO.getWosize h) c (IO.getTag h)

inline_for_extraction
let get_wosize (h: U64.t) : r: U64.t{r == SO.getWosize h /\ U64.v r < pow2 54}
  = IO.getWosize_eq h;
    SO.getWosize_bound h;
    IO.getWosize h

inline_for_extraction
let get_color (h: U64.t) : r: Hd.color_sem{r == SO.getColor h}
  = IO.getColor_eq h;
    IO.getColor h

let pow54_lt_64 () : Lemma (pow2 54 < pow2 64) = FStar.Math.Lemmas.pow2_lt_compat 64 54

/// `ohdr wz`: a fresh white object of wosize `wz`.
inline_for_extraction
let ohdr_u64 (wz: U64.t{U64.v wz < pow2 54}) : r: U64.t{r == B.ohdr (U64.v wz)}
  = pow54_lt_64 ();
    mk_hdr wz Hd.White

/// `bhdr w`: a blue block of `w` words.
inline_for_extraction
let bhdr_u64 (w: U64.t{U64.v w >= 1 /\ U64.v w <= pow2 54}) : r: U64.t{r == B.bhdr (U64.v w)}
  = pow54_lt_64 ();
    mk_hdr (U64.sub w 1UL) Hd.Blue

/// `blue_hdr w`, the same for a block of fewer than `pow2 20` words.
inline_for_extraction
let blue_hdr_u64 (w: U64.t{U64.v w >= 1 /\ U64.v w < pow2 20}) : r: U64.t{r == In.blue_hdr (U64.v w)}
  = FStar.Math.Lemmas.pow2_lt_compat 54 20;
    FStar.Math.Lemmas.pow2_lt_compat 64 20;
    mk_hdr (U64.sub w 1UL) Hd.Blue

/// ---------------------------------------------------------------------------
/// Addresses
/// ---------------------------------------------------------------------------

let page_base_bound (i: nat{i <= n_pages})
  : Lemma (page_base i <= Base.heap_size /\ page_base i % 8 == 0)
  = page_base_mono i n_pages;
    page_base_aligned i

/// The start of page `i`.
inline_for_extraction
let page_base_u64 (i: U64.t{U64.v i <= n_pages}) : r: U64.t{U64.v r == page_base (U64.v i)}
  = page_base_bound (U64.v i);
    cls_bounds 0;
    assert_norm (pow2 20 * 8 < pow2 64);
    FStar.Math.Lemmas.pow2_lt_compat 64 57;
    U64.add zero_addr (U64.mul i (U64.mul page_wsize_u64 8UL))

/// ---------------------------------------------------------------------------
/// Guarded reads and writes
/// ---------------------------------------------------------------------------

let in_heap (a: U64.t) : bool = U64.lt a heap_size_u64 && U64.rem a 8UL = 0UL

/// `Shape.hdr g a`.
fn hdr_at (heap: heap_t) (a: U64.t)
  requires is_heap heap 'g
  returns v: U64.t
  ensures is_heap heap 'g ** pure (v == Sh.hdr 'g (U64.v a))
{
  if in_heap a {
    read_word heap a
  } else {
    0UL
  }
}

/// `Blocks.wr g a v`.
fn wr (heap: heap_t) (a: U64.t) (v: U64.t)
  requires is_heap heap 'g
  ensures is_heap heap (B.wr 'g (U64.v a) v)
{
  if in_heap a {
    write_word heap a v;
    rewrite (is_heap heap (SH.write_word 'g a v)) as (is_heap heap (B.wr 'g (U64.v a) v))
  } else {
    rewrite (is_heap heap 'g) as (is_heap heap (B.wr 'g (U64.v a) v))
  }
}
