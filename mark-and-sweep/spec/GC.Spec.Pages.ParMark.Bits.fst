/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.ParMark.Bits - setting a mark bit, as the parallel mark's CAS does
/// ---------------------------------------------------------------------------
///
/// The parallel mark claims an object by a 32-bit CAS on the bitmap word that
/// holds its header's bit (docs/pages-parallel-gc-design.md §1.1): it reads the
/// word `old`, and replaces it by `old | (1 << k)` if it still holds `old`.
/// `bword bs a` is that word, `set_word` the new value, and `set_bit bs a` the
/// bitmap after a successful CAS.  `set_bit_marked`: exactly the bit of `a`
/// is added.

module GC.Spec.Pages.ParMark.Bits

open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Bitmap

module U32 = FStar.UInt32
module Seq = FStar.Seq
module UI = FStar.UInt

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The word with bit `k` set.
let set_word (x: U32.t) (k: U32.t{U32.v k < 32}) : U32.t =
  U32.logor x (U32.shift_left 1ul k)

let set_word_bit (x: U32.t) (k: U32.t{U32.v k < 32}) (j: nat{j < 32})
  : Lemma (bit_of (set_word x k) j == (bit_of x j || j = U32.v k))
  = let m = U32.shift_left 1ul k in
    UI.shift_left_value_lemma #32 1 (U32.v k);
    FStar.Math.Lemmas.pow2_lt_compat 32 (U32.v k);
    FStar.Math.Lemmas.small_mod (pow2 (U32.v k)) (pow2 32);
    assert (U32.v m == pow2 (U32.v k));
    UI.pow2_nth_lemma #32 (U32.v k) (31 - j);
    UI.logor_definition #32 (U32.v x) (U32.v m) (31 - j);
    nth_div 32 (U32.v x) j;
    nth_div 32 (U32.v (set_word x k)) j

/// The bitmap word that holds the bit of `a` (0 outside the pages).
let bword (bs: Seq.seq U32.t) (a: nat) : U32.t =
  if in_pages a && Seq.length bs = bm_len then begin
    widx_bound a;
    Seq.index bs (widx a / 32)
  end else 0ul

/// The bitmap after a CAS that sets the bit of `a`.
let set_bit (bs: Seq.seq U32.t) (a: nat) : Seq.seq U32.t =
  if in_pages a && Seq.length bs = bm_len then begin
    widx_bound a;
    let w = widx a / 32 in
    Seq.upd bs w (set_word (Seq.index bs w) (U32.uint_to_t (widx a % 32)))
  end else bs

let set_bit_len (bs: Seq.seq U32.t) (a: nat)
  : Lemma (Seq.length (set_bit bs a) == Seq.length bs)
  = if in_pages a && Seq.length bs = bm_len then widx_bound a

/// **Setting a bit adds exactly that bit.**
let set_bit_marked (bs: Seq.seq U32.t) (a: nat) (x: nat)
  : Lemma (marked (set_bit bs a) x ==
           (marked bs x || (x = a && in_pages a && Seq.length bs = bm_len)) /\
           Seq.length (set_bit bs a) == Seq.length bs)
  = set_bit_len bs a;
    if in_pages a && Seq.length bs = bm_len && in_pages x then begin
      widx_bound a;
      widx_bound x;
      let w = widx a / 32 in
      let k = U32.uint_to_t (widx a % 32) in
      set_word_bit (Seq.index bs w) k (widx x % 32);
      if x <> a && widx x / 32 = w && widx x % 32 = widx a % 32 then widx_inj a x
    end

/// The bit of `a` is the bit of its word.
let marked_bword (bs: Seq.seq U32.t) (a: nat)
  : Lemma (requires in_pages a /\ Seq.length bs == bm_len)
          (ensures marked bs a == bit_of (bword bs a) (widx a % 32))
  = ()

/// Bits only grow: `bs'` has every bit of `bs`.
let grows (bs bs': Seq.seq U32.t) : prop =
  Seq.length bs' == Seq.length bs /\ (forall (x: nat). marked bs x ==> marked bs' x)

let grows_refl (bs: Seq.seq U32.t) : Lemma (grows bs bs) = ()

let grows_set (bs: Seq.seq U32.t) (a: nat)
  : Lemma (grows bs (set_bit bs a))
  = FStar.Classical.forall_intro (set_bit_marked bs a)
