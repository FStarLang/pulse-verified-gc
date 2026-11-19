/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.Alloc - the page allocator, in Pulse
/// ---------------------------------------------------------------------------
///
/// `alloc heap t wz col` allocates an object of wosize `wz` with a header of
/// colour `col`, and returns its address, or 0 when there is no room.  It
/// computes exactly the specification's allocator in that colour,
/// `GC.Spec.Pages.AllocPhase.alloc_col col`, for every heap, state, size and
/// colour:
///   - `alloc_white` is `GC.Spec.Pages.Alloc.alloc`: a small block takes a
///     slot of its class (`GC.Impl.Pages.Pool`), a large one a listed block
///     or a new run (`GC.Impl.Pages.Large`);
///   - the new header is then given the colour `col`.
///
/// As OCaml's `caml_alloc_shr`, it leaves the object's fields as they were;
/// the caller writes them (`GC.Spec.Pages.Theorems.fields_written`).  With
/// the specification's theorems (`alloc_col_correct`, and `alloc_correct`
/// for white) this is the allocator's correctness.

module GC.Impl.Pages.Alloc

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Inv
open GC.Impl.Heap
open GC.Impl.Pages.Params
open GC.Impl.Pages.State
open GC.Impl.Pages.Heap

module U64 = FStar.UInt64
module Base = GC.Spec.Base
module Hd = GC.Lib.Header
module SO = GC.Spec.Object
module Sh = GC.Spec.Pages.Shape
module B = GC.Spec.Pages.Blocks
module P = GC.Spec.Pages.Pool
module A = GC.Spec.Pages.Alloc
module AP = GC.Spec.Pages.AllocPhase
module PL = GC.Impl.Pages.Pool
module LI = GC.Impl.Pages.Large
module Rd = GC.Impl.Pages.Ready
module AT = GC.Spec.Pages.AllocTag
module IO = GC.Impl.Object

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let alloc_unfold (g: Base.heap) (st: pstate) (wz: nat)
  : Lemma (A.alloc g st wz ==
           (if wz + 1 >= pow2 54 then (g, st, 0UL)
            else if wz + 1 <= small_max then P.small_alloc_as false g st wz
            else A.large_alloc_as false g st wz))
  = ()

/// White allocation: `GC.Spec.Pages.Alloc.alloc`.  `heads_ready` holds
/// under `pages_ok` (`Ready.pages_ok_ready`), which `alloc_meets` assumes.
fn alloc_white (heap: heap_t) (t: pstate_t) (wz: U64.t) (#st: erased pstate)
  requires is_heap heap 'g ** pages_st t st ** pure (Rd.heads_ready st)
  returns o: U64.t
  ensures exists* g' st'. is_heap heap g' ** pages_st t st' **
          pure ((g', st', o) == A.alloc 'g st (U64.v wz))
{
  alloc_unfold 'g st (U64.v wz);
  LI.bounds ();
  assert_norm (pow2 54 - 1 == 0x3FFFFFFFFFFFFF);
  if (U64.gte wz 0x3FFFFFFFFFFFFFUL) {
    0UL
  } else {
    let sm = PL.small_max_u64 ();
    if (U64.lte (U64.add wz 1UL) sm) {
      PL.small_alloc heap t wz
    } else {
      LI.large_alloc heap t wz
    }
  }
}

let col_unfold (col: Hd.color_sem) (g: Base.heap) (st: pstate) (wz: nat)
  : Lemma (AP.alloc_col col g st wz ==
           (let (g', st', o) = A.alloc g st wz in
            if o = 0UL then (g', st', o)
            else if U64.v o >= 8
            then (B.wr g' (U64.v o - 8) (SO.colorHeader (Sh.hdr g' (U64.v o - 8)) col), st', o)
            else (g', st', o)))
  = ()

/// **The page allocator**, with the new object's colour as a parameter:
/// `GC.Spec.Pages.AllocPhase.alloc_col col`.  `heads_ready` holds under
/// `pages_ok_mc` (`Ready.mc_ready`), which `alloc_col_correct` assumes.
fn alloc (heap: heap_t) (t: pstate_t) (wz: U64.t) (col: Hd.color_sem) (#st: erased pstate)
  requires is_heap heap 'g ** pages_st t st ** pure (Rd.heads_ready st)
  returns o: U64.t
  ensures exists* g' st'. is_heap heap g' ** pages_st t st' **
          pure ((g', st', o) == AP.alloc_col col 'g st (U64.v wz))
{
  col_unfold col 'g st (U64.v wz);
  let o = alloc_white heap t wz;
  if (o = 0UL) {
    0UL
  } else {
    if (U64.gte o 8UL) {
      let a = U64.sub o 8UL;
      let h = hdr_at heap a;
      wr heap a (recolour_hdr h col);
      o
    } else {
      o
    }
  }
}

/// ---------------------------------------------------------------------------
/// With a tag (plan §27.1)
/// ---------------------------------------------------------------------------

/// The header `h`, at its wosize, with colour `c` and tag `tag`.
inline_for_extraction noextract
let tag_hdr (h: U64.t) (c: Hd.color_sem) (tag: U64.t{U64.v tag < 256}) : r: U64.t{r == AT.tag_hdr h c tag}
  = let wz = get_wosize h in
    IO.makeHeader_eq_pack_header wz c tag;
    SO.makeHeader_is_pack_header64 wz c tag;
    let r = IO.makeHeader wz c tag in
    U64.v_inj r (SO.makeHeader wz c tag);
    r

let col_tag_unfold (col: Hd.color_sem) (tag: AT.tag_t) (g: Base.heap) (st: pstate) (wz: nat)
  : Lemma (AT.alloc_col_tag col tag g st wz ==
           (let (g', st', o) = A.alloc g st wz in
            if o = 0UL then (g', st', o)
            else if U64.v o >= 8
            then (B.wr g' (U64.v o - 8) (AT.tag_hdr (Sh.hdr g' (U64.v o - 8)) col tag), st', o)
            else (g', st', o)))
  = ()

/// **The page allocator with a colour and a tag**, as OCaml's
/// `caml_alloc_shr (wosize, tag)`: the new header is written once more,
/// with both (`GC.Spec.Pages.AllocTag.alloc_col_tag`).
fn alloc_tag (heap: heap_t) (t: pstate_t) (wz: U64.t) (col: Hd.color_sem) (tag: U64.t{U64.v tag < 256})
  (#st: erased pstate)
  requires is_heap heap 'g ** pages_st t st ** pure (Rd.heads_ready st)
  returns o: U64.t
  ensures exists* g' st'. is_heap heap g' ** pages_st t st' **
          pure ((g', st', o) == AT.alloc_col_tag col tag 'g st (U64.v wz))
{
  col_tag_unfold col tag 'g st (U64.v wz);
  let o = alloc_white heap t wz;
  if (o = 0UL) {
    0UL
  } else {
    if (U64.gte o 8UL) {
      let a = U64.sub o 8UL;
      let h = hdr_at heap a;
      wr heap a (tag_hdr h col tag);
      o
    } else {
      o
    }
  }
}
