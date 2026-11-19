/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.AllocTag - the page allocator with a tag
/// ---------------------------------------------------------------------------
///
/// Plan §27.1.  As OCaml's `caml_alloc_shr (wosize, tag)`, the allocator
/// writes the new object's header once, with its colour and its tag:
/// `alloc_col_tag col tag` is the page allocator of stage 2
/// (`GC.Spec.Pages.Alloc.alloc`) with the new header set to wosize `wz`,
/// colour `col` and tag `tag`.  `alloc_tag ph` takes the colour from the
/// phase (`I.new_colour`), as `GC.Spec.Pages.Allocator.alloc` does.
///
/// A minor collection allocates every promoted copy with the tag of the
/// nursery object it copies (`GC.Gen.Promote.promoted_tag`).
///
/// This module holds the definitions and their equations only; what the
/// allocator guarantees is `GC.Spec.Pages.AllocTagOk`.

module GC.Spec.Pages.AllocTag

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Pages.Inv

module U64 = FStar.UInt64
module I = GC.Spec.AllocIface
module A = GC.Spec.Pages.Alloc
module AP = GC.Spec.Pages.AllocPhase
module PA = GC.Spec.Pages.Allocator
module Sh = GC.Spec.Pages.Shape
module B = GC.Spec.Pages.Blocks

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// A tag: a byte.
let tag_t = t: U64.t{U64.v t < 256}

/// The header `h`, at its wosize, with colour `col` and tag `tag`.
let tag_hdr (h: U64.t) (col: color) (tag: tag_t) : U64.t = makeHeader (getWosize h) col tag

/// **The page allocator with a colour and a tag.**
let alloc_col_tag (col: color) (tag: tag_t) (g: heap) (st: pstate) (wz: nat)
  : GTot (heap & pstate & U64.t) =
  let (g', st', o) = A.alloc g st wz in
  if o = 0UL then (g', st', o)
  else if U64.v o >= 8 then (B.wr g' (U64.v o - 8) (tag_hdr (Sh.hdr g' (U64.v o - 8)) col tag), st', o)
  else (g', st', o)

/// **... with the colour of the phase.**
let alloc_tag (ph: I.phase) (g: heap) (st: pstate) (wz: nat) (tag: tag_t)
  : GTot (heap & pstate & U64.t) =
  alloc_col_tag (I.new_colour ph) tag g st wz

/// It is the coloured allocator (`AP.alloc_col`) with the header written
/// again: the same object, state and failure, and the heap with the new
/// header replaced.
let alloc_col_tag_eq (col: color) (tag: tag_t) (g: heap) (st: pstate) (wz: nat)
  : Lemma (let (g1, st1, o1) = AP.alloc_col col g st wz in
           let (g2, st2, o2) = alloc_col_tag col tag g st wz in
           st2 == st1 /\ o2 == o1 /\
           (o1 == 0UL ==> g2 == g1) /\
           (o1 =!= 0UL /\ U64.v o1 >= 8 ==>
              g2 == B.wr g1 (U64.v o1 - 8) (tag_hdr (Sh.hdr g1 (U64.v o1 - 8)) col tag)))
  = let (g', st', o) = A.alloc g st wz in
    if o <> 0UL && U64.v o >= 8 then begin
      let a = U64.v o - 8 in
      let h = Sh.hdr g' a in
      let g1 = AP.recolour g' o col in
      assert (g1 == B.wr g' a (colorHeader h col));
      (if a < heap_size && a % 8 = 0 then B.wr_read g' a (colorHeader h col) (mk_hp_addr a));
      assert (a < heap_size /\ a % 8 == 0 ==> Sh.hdr g1 a == colorHeader h col);
      assert (~(a < heap_size /\ a % 8 == 0) ==> g1 == g');
      colorHeader_preserves_wosize h col;
      let r (b: hp_addr)
        : Lemma (read_word (B.wr g1 a (tag_hdr h col tag)) b == read_word (B.wr g' a (tag_hdr h col tag)) b)
        = B.wr_read g1 a (tag_hdr h col tag) b;
          B.wr_read g' a (tag_hdr h col tag) b;
          B.wr_read g' a (colorHeader h col) b
      in
      if a < heap_size && a % 8 = 0 then begin
        assert (tag_hdr (Sh.hdr g1 a) col tag == tag_hdr h col tag);
        FStar.Classical.forall_intro r;
        GC.Gen.HeapExtensional.heap_read_word_ext (B.wr g1 a (tag_hdr h col tag)) (B.wr g' a (tag_hdr h col tag))
      end
    end

/// ---------------------------------------------------------------------------
/// What the caller writes
/// ---------------------------------------------------------------------------

/// `g''` is `g'` with the fields of `x` written: if `x` is scannable, with
/// values the caller may store (`I.field_ok_with free`), none of them a
/// pointer into the body of `x` itself; if `x` holds raw data (a no-scan
/// tag), with anything.  A promoted copy's fields are its nursery fields:
/// in a scannable object, a value that is not a major pointer or a pointer
/// to a block that was in use before the allocation, so never into the new
/// block; in a no-scan object, bytes.
let away (x: obj_addr) (wz: nat) (v: U64.t) : prop =
  GC.Spec.Fields.is_pointer v ==> U64.v v <= U64.v x \/ U64.v v >= U64.v x + wz * 8

let fields_written_away (free: GC.Spec.Fields.free_def) (g' g'': heap) (x: obj_addr) : prop =
  (forall (a: hp_addr).
     U64.v a < U64.v x \/ U64.v a >= U64.v x + U64.v (wosize_of_object x g') * 8 ==>
     read_word g'' a == read_word g' a) /\
  (~(is_no_scan x g') ==>
     (forall (a: hp_addr).
        U64.v x <= U64.v a /\ U64.v a < U64.v x + U64.v (wosize_of_object x g') * 8 ==>
        I.field_ok_with free g'' (read_word g'' a) /\
        away x (U64.v (wosize_of_object x g')) (read_word g'' a)))
