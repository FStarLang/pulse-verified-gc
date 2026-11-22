/// ---------------------------------------------------------------------------
/// GC.Spec.Top.Low - the bytes below the heap, and words read through the
/// representation
/// ---------------------------------------------------------------------------
///
/// The byte heap's representation (GC.Spec.Top.Abs.brepr) reads the words
/// from `zero_addr` on.  The bytes below it are no block's, and the page
/// allocator never writes them; but its invariants are stated on the whole
/// byte heap.  So the page instance keeps them in its own state and runs on
/// `set_low g lo`: `g` with the bytes below `zero_addr` taken from `lo`.
/// That heap has the same reading as `g` (`cabs_set_low`).
///
/// Also here: a word is determined by its reading, as a header
/// (`abs_hdr_inj`) or as a value (`absv_inj`).

module GC.Spec.Top.Low

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Walk
open GC.Lib.Header
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let low_t = s: Seq.seq U8.t{Seq.length s == base}

let low (g: heap) : low_t = base_facts (); Seq.slice g 0 base

let set_low_byte (g: heap) (lo: low_t) (i: nat{i < heap_size}) : U8.t =
  if i < base then Seq.index lo i else Seq.index g i

let set_low (g: heap) (lo: low_t) : heap = Seq.init heap_size (set_low_byte g lo)

let set_low_index (g: heap) (lo: low_t) (i: nat{i < heap_size})
  : Lemma (Seq.index (set_low g lo) i == (if i < base then Seq.index lo i else Seq.index g i))
  = ()

let read_set_low (g: heap) (lo: low_t) (a: hp_addr)
  : Lemma (requires U64.v a >= base) (ensures read_word (set_low g lo) a == read_word g a)
  = read_word_spec (set_low g lo) a;
    read_word_spec g a

let set_low_self (g: heap) : Lemma (set_low g (low g) == g)
  = base_facts ();
    Seq.lemma_eq_intro (set_low g (low g)) g

let low_set_low (g: heap) (lo: low_t) : Lemma (low (set_low g lo) == lo)
  = base_facts ();
    Seq.lemma_eq_intro (low (set_low g lo)) lo

/// Two heaps with the same words from `zero_addr` on have the same reading.
let cabs_same_above (g g': heap)
  : Lemma (requires forall (a: hp_addr). U64.v a >= base ==> read_word g' a == read_word g a)
          (ensures R.heq (cabs g') (cabs g))
  = walk_frame_from g g' zero_addr;
    let wd (m: nat) : Lemma (word g' m == word g m /\ on_walk g' m == on_walk g m)
      = if pos m < heap_size then begin pos_aligned m; base_facts () end in
    FStar.Classical.forall_intro wd;
    assert (forall (m: nat). abs_hd g' m == abs_hd g m);
    let fw (w: nat) : Lemma (is_fw g' w == is_fw g w)
      = is_fw_iff g' w; is_fw_iff g w;
        assert (forall (o: nat). M.covers (abs g') o w == M.covers (abs g) o w) in
    FStar.Classical.forall_intro fw

let cabs_set_low (g: heap) (lo: low_t) : Lemma (R.heq (cabs (set_low g lo)) (cabs g))
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (read_set_low g lo));
    cabs_same_above g (set_low g lo)

/// ---------------------------------------------------------------------------
/// Words, from their reading
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let absv_inj (v v': U64.t) : Lemma (requires absv v == absv v') (ensures v == v')
  = base_facts ();
    if is_pointer v then begin
      assert (is_pointer v');
      FStar.Math.Lemmas.lemma_div_exact (U64.v v - 8 - base) 8;
      FStar.Math.Lemmas.lemma_div_exact (U64.v v' - 8 - base) 8
    end
    else if is_young_w v then begin
      assert (is_young_w v');
      FStar.Math.Lemmas.lemma_div_exact (U64.v v - 8) 8;
      FStar.Math.Lemmas.lemma_div_exact (U64.v v' - 8) 8
    end
    else ()
#pop-options

let abs_col_inj (c c': color_sem) : Lemma (requires abs_col c == abs_col c') (ensures c == c') = ()

let unpack_color_inj (w w': FStar.UInt.uint_t 64)
  : Lemma (requires w < 4 /\ w' < 4 /\ unpack_color w == unpack_color w') (ensures w == w')
  = ()

/// The words of a header: its wosize, colour and tag bits are the whole word.
#push-options "--z3rlimit 40"
let abs_hdr_inj (v v': U64.t) : Lemma (requires abs_hdr v == abs_hdr v') (ensures v == v')
  = let w = U64.v v in
    let w' = U64.v v' in
    getWosize_spec v; getWosize_spec v';
    tag_low_byte v; tag_low_byte v';
    getTag_spec v; getTag_spec v';
    mask_tag_value ();
    FStar.UInt.logand_mask #64 w 8;
    FStar.UInt.logand_mask #64 w' 8;
    assert_norm (pow2 8 == 256);
    assert (get_tag w == w % 256 /\ get_tag w' == w' % 256);
    assert (get_wosize w == U64.v (getWosize v) /\ get_wosize w' == U64.v (getWosize v'));
    get_color_bound w; get_color_bound w';
    getColor_spec v; getColor_spec v';
    valid_color_unpack (get_color w); valid_color_unpack (get_color w');
    abs_col_inj (getColor v) (getColor v');
    unpack_color_inj (get_color w) (get_color w');
    unpack_header_total w; unpack_header_total w';
    assert (unpack_header w == unpack_header w');
    unpack_pack_header w;
    unpack_pack_header w'
#pop-options
