/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Bitmap - the mark bitmap, and the heap it stands for
/// ---------------------------------------------------------------------------
///
/// The parallel collector keeps the marks in a bitmap outside the heap
/// (docs/pages-parallel-gc-design.md §1.2): one bit per heap word of the
/// pages, counted from `zero_addr`, in 32-bit words, so that page `i`'s bits
/// are words `[i * bpp, (i + 1) * bpp)`.  `marked bs a` reads the bit of the
/// word at address `a`.
///
/// The sweep specifications are not changed: they read header colours.  The
/// heap they are given is **`with_marks g bs`**: the real heap `g` with the
/// header of every marked word made black (§3).  It is `wm g (marked bs)`,
/// where `wm g m` blackens the headers at the addresses `m` holds; the pool
/// page sweep, which clears a page's bits only at its end, uses `wm` with
/// the marks below a slot left out (`win`).
///
/// The lemmas say how `wm` meets the heap's reads and writes (`wm_read`,
/// `wm_write`, `wm_unmark`), when two mark sets give the same heap
/// (`wm_ext`), and what clearing a bit or a page does to `marked`
/// (`clear_bit_marked`, `zero_page_marked`, `bit_test`).

module GC.Spec.Pages.Bitmap

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Seq = FStar.Seq
module UI = FStar.UInt
module HE = GC.Gen.HeapExtensional
module Hdr = GC.Lib.Header

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The layout
/// ---------------------------------------------------------------------------

/// Bitmap words per page.
let bpp : nat = page_wsize / 32

/// The bitmap's length: the pages' bits.
let bm_len : nat = n_pages * bpp

let zw : nat = U64.v zero_addr

/// A word of the pages.
let in_pages (a: nat) : bool = zw <= a && a < pages_end && a % 8 = 0

/// The word's index, from `zero_addr`.
let widx (a: nat) : nat = if a >= zw then (a - zw) / 8 else 0

let bpp_mul () : Lemma (page_wsize == 32 * bpp /\ page_bytes == 256 * bpp)
  = page_wsize_bm ()

/// `x / d < m` when `x < d * m`.
let div_lt (x: nat) (d: pos) (m: nat)
  : Lemma (requires x < d * m) (ensures x / d < m)
  = FStar.Math.Lemmas.lemma_div_mod x d

/// `m <= x / d` when `d * m <= x`.
let div_ge (x: nat) (d: pos) (m: nat)
  : Lemma (requires d * m <= x) (ensures m <= x / d)
  = FStar.Math.Lemmas.lemma_div_mod x d

/// The bitmap word that holds an address's bit.
let widx_bound (a: nat)
  : Lemma (requires in_pages a) (ensures widx a / 32 < bm_len)
  = bpp_mul ();
    assert (a - zw < n_pages * page_bytes);
    FStar.Math.Lemmas.paren_mul_right n_pages 256 bpp;
    FStar.Math.Lemmas.swap_mul n_pages 256;
    FStar.Math.Lemmas.paren_mul_left 8 32 (n_pages * bpp);
    div_lt (a - zw) 8 (32 * (n_pages * bpp));
    div_lt (widx a) 32 (n_pages * bpp)

/// An address's bitmap word is its page's.
let widx_page (i: nat{i < n_pages}) (a: nat)
  : Lemma (requires page_base i <= a /\ a < page_base (i + 1) /\ a % 8 == 0)
          (ensures in_pages a /\ i * bpp <= widx a / 32 /\ widx a / 32 < (i + 1) * bpp)
  = bpp_mul ();
    page_base_mono (i + 1) n_pages;
    assert (widx a == (a - zw) / 8);
    assert (i * page_bytes <= a - zw /\ a - zw < (i + 1) * page_bytes);
    FStar.Math.Lemmas.paren_mul_right i 256 bpp;
    FStar.Math.Lemmas.swap_mul i 256;
    FStar.Math.Lemmas.paren_mul_left 8 32 (i * bpp);
    FStar.Math.Lemmas.paren_mul_right (i + 1) 256 bpp;
    FStar.Math.Lemmas.swap_mul (i + 1) 256;
    FStar.Math.Lemmas.paren_mul_left 8 32 ((i + 1) * bpp);
    div_ge (a - zw) 8 (32 * (i * bpp));
    div_lt (a - zw) 8 (32 * ((i + 1) * bpp));
    div_ge (widx a) 32 (i * bpp);
    div_lt (widx a) 32 ((i + 1) * bpp)

/// Bit `k` of a word.
let bit_of (x: U32.t) (k: nat) : bool = (U32.v x / pow2 k) % 2 = 1

/// **The bit of the word at `a`.**
let marked (bs: Seq.seq U32.t) (a: nat) : bool =
  if in_pages a && Seq.length bs = bm_len then begin
    widx_bound a;
    bit_of (Seq.index bs (widx a / 32)) (widx a % 32)
  end else false

/// ---------------------------------------------------------------------------
/// The heap the marks stand for
/// ---------------------------------------------------------------------------

/// The word at `a`, its header made black if `a` is marked.
let mark_val (g: heap) (m: nat -> bool) (a: hp_addr) : U64.t =
  if m (U64.v a) then colorHeader (read_word g a) Black else read_word g a

let word_of (i: nat{i < heap_size}) : hp_addr =
  FStar.Math.Lemmas.lemma_mod_lt i 8;
  mk_hp_addr (i - i % 8)

/// `g` with the header at every address of `m` made black.
let wm (g: heap) (m: nat -> bool) : heap =
  Seq.init heap_size (fun (i: nat{i < heap_size}) ->
    let a = word_of i in
    Seq.index (write_word g a (mark_val g m a)) i)

/// **The heap the bitmap stands for.**
let with_marks (g: heap) (bs: Seq.seq U32.t) : heap = wm g (marked bs)

let word_of_at (a: hp_addr) (j: nat{j < 8})
  : Lemma (U64.v a + j < heap_size /\ word_of (U64.v a + j) == a)
  = FStar.Math.Lemmas.lemma_mod_plus j (U64.v a / 8) 8

#push-options "--z3rlimit 40"
/// **Reading the heap the marks stand for.**
let wm_read (g: heap) (m: nat -> bool) (a: hp_addr)
  : Lemma (read_word (wm g m) a == mark_val g m a)
  = let v = mark_val g m a in
    let g' = write_word g a v in
    let h = wm g m in
    let byte (j: nat{j < 8}) : Lemma (Seq.index h (U64.v a + j) == Seq.index g' (U64.v a + j))
      = word_of_at a j
    in
    byte 0; byte 1; byte 2; byte 3; byte 4; byte 5; byte 6; byte 7;
    read_word_spec h a;
    read_word_spec g' a;
    read_write_same g a v
#pop-options

/// Two mark sets that agree on the words give the same heap.
let wm_ext (g: heap) (m1 m2: nat -> bool)
  : Lemma (requires forall (a: hp_addr). m1 (U64.v a) == m2 (U64.v a))
          (ensures wm g m1 == wm g m2)
  = let aux (a: nat) : Lemma (a < heap_size /\ a % 8 == 0 ==>
                              read_word (wm g m1) (U64.uint_to_t a) == read_word (wm g m2) (U64.uint_to_t a))
      = if a < heap_size && a % 8 = 0 then begin
          wm_read g m1 (U64.uint_to_t a);
          wm_read g m2 (U64.uint_to_t a)
        end
    in
    FStar.Classical.forall_intro aux;
    HE.heap_read_word_ext (wm g m1) (wm g m2)

/// With no marks, the heap is itself.
let wm_none (g: heap) (m: nat -> bool)
  : Lemma (requires forall (a: hp_addr). not (m (U64.v a))) (ensures wm g m == g)
  = let aux (a: nat) : Lemma (a < heap_size /\ a % 8 == 0 ==>
                              read_word (wm g m) (U64.uint_to_t a) == read_word g (U64.uint_to_t a))
      = if a < heap_size && a % 8 = 0 then wm_read g m (U64.uint_to_t a)
    in
    FStar.Classical.forall_intro aux;
    HE.heap_read_word_ext (wm g m) g

let rw (g: heap) (a: hp_addr) (x: hp_addr) (v: U64.t)
  : Lemma (read_word (write_word g a v) x == (if x = a then v else read_word g x))
  = if x = a then read_write_same g a v else read_write_different g a x v

/// **A write where there is no mark** is the same write to the heap the
/// marks stand for.
let wm_write (g: heap) (m: nat -> bool) (a: hp_addr) (v: U64.t)
  : Lemma (requires not (m (U64.v a)))
          (ensures wm (write_word g a v) m == write_word (wm g m) a v)
  = let aux (x: nat) : Lemma (x < heap_size /\ x % 8 == 0 ==>
                              read_word (wm (write_word g a v) m) (U64.uint_to_t x) ==
                              read_word (write_word (wm g m) a v) (U64.uint_to_t x))
      = if x < heap_size && x % 8 = 0 then begin
          let y : hp_addr = U64.uint_to_t x in
          wm_read (write_word g a v) m y;
          wm_read g m y;
          rw g a y v;
          rw (wm g m) a y v
        end
    in
    FStar.Classical.forall_intro aux;
    HE.heap_read_word_ext (wm (write_word g a v) m) (write_word (wm g m) a v)

/// Two mark sets that differ only at `a`, marked in `m1`: the heap of `m1`
/// is the heap of `m2` with the header at `a` made black.
let wm_unmark (g: heap) (m1 m2: nat -> bool) (a: hp_addr)
  : Lemma (requires m1 (U64.v a) /\ not (m2 (U64.v a)) /\
                    (forall (x: hp_addr). x <> a ==> m1 (U64.v x) == m2 (U64.v x)))
          (ensures wm g m1 == write_word (wm g m2) a (colorHeader (read_word g a) Black))
  = let v = colorHeader (read_word g a) Black in
    let aux (x: nat) : Lemma (x < heap_size /\ x % 8 == 0 ==>
                              read_word (wm g m1) (U64.uint_to_t x) ==
                              read_word (write_word (wm g m2) a v) (U64.uint_to_t x))
      = if x < heap_size && x % 8 = 0 then begin
          let y : hp_addr = U64.uint_to_t x in
          wm_read g m1 y;
          wm_read g m2 y;
          rw (wm g m2) a y v
        end
    in
    FStar.Classical.forall_intro aux;
    HE.heap_read_word_ext (wm g m1) (write_word (wm g m2) a v)

/// Making a header black writes the same heap the marks stand for when its
/// mark is cleared at the same time.
let wm_blacken (g: heap) (m1 m2: nat -> bool) (a: hp_addr)
  : Lemma (requires m1 (U64.v a) /\ not (m2 (U64.v a)) /\
                    (forall (x: hp_addr). x <> a ==> m1 (U64.v x) == m2 (U64.v x)))
          (ensures wm (write_word g a (colorHeader (read_word g a) Black)) m2 == wm g m1)
  = wm_unmark g m1 m2 a;
    wm_write g m2 a (colorHeader (read_word g a) Black)

/// ---------------------------------------------------------------------------
/// Colours
/// ---------------------------------------------------------------------------

/// **A white header made black and then white again is itself.**
let whiten_black (h: U64.t)
  : Lemma (requires getColor h == White)
          (ensures colorHeader (colorHeader h Black) White == h)
  = let v = U64.v h in
    Hdr.get_color_bound v;
    Hdr.valid_color_unpack (Hdr.get_color v);
    let hs = Some?.v (Hdr.unpack_header v) in
    Hdr.unpack_pack_header v;
    getColor_spec h;
    assert (hs.color == White);
    colorHeader_spec h Black;
    Hdr.pack_set_color hs Black;
    let hb = Hdr.set_color_sem hs Black in
    colorHeader_spec (colorHeader h Black) White;
    Hdr.pack_set_color hb White;
    assert (Hdr.set_color_sem hb White == hs)

let black_black (h: U64.t) : Lemma (getColor (colorHeader h Black) == Black)
  = colorHeader_getColor h Black

/// ---------------------------------------------------------------------------
/// Bits
/// ---------------------------------------------------------------------------

/// Bit `k` of `a`, as `FStar.UInt.nth` numbers bits (the highest first).
#push-options "--fuel 1 --z3rlimit 40"
let rec nth_div (n: pos) (a: UI.uint_t n) (k: nat{k < n})
  : Lemma (ensures UI.nth #n a (n - 1 - k) == ((a / pow2 k) % 2 = 1)) (decreases k)
  = UI.to_vec_lemma_2 #n a (UI.from_vec #n (UI.to_vec #n a));
    if k = 0 then ()
    else begin
      assert (n > 1);
      let a' : UI.uint_t (n - 1) = a / 2 in
      nth_div (n - 1) a' (k - 1);
      FStar.Math.Lemmas.division_multiplication_lemma a 2 (pow2 (k - 1));
      FStar.Math.Lemmas.pow2_plus 1 (k - 1);
      FStar.Seq.Base.lemma_index_app1 (UI.to_vec #(n - 1) (a / 2)) (Seq.create 1 (a % 2 = 1)) (n - 1 - k)
    end
#pop-options

/// The test the sweep makes: shift the word right by `k`, keep the low bit.
let bit_test (x: U32.t) (k: U32.t{U32.v k < 32})
  : Lemma (U32.logand (U32.shift_right x k) 1ul <> 0ul <==> bit_of x (U32.v k))
  = UI.shift_right_value_lemma #32 (U32.v x) (U32.v k);
    UI.logand_mask #32 (U32.v (U32.shift_right x k)) 1;
    assert_norm (pow2 1 - 1 == 1)

/// The word with bit `k` cleared.
let clear_word (x: U32.t) (k: U32.t{U32.v k < 32}) : U32.t =
  U32.logand x (U32.lognot (U32.shift_left 1ul k))

let clear_word_bit (x: U32.t) (k: U32.t{U32.v k < 32}) (j: nat{j < 32})
  : Lemma (bit_of (clear_word x k) j == (bit_of x j && j <> U32.v k))
  = let m = U32.shift_left 1ul k in
    UI.shift_left_value_lemma #32 1 (U32.v k);
    FStar.Math.Lemmas.pow2_lt_compat 32 (U32.v k);
    FStar.Math.Lemmas.small_mod (pow2 (U32.v k)) (pow2 32);
    assert (U32.v m == pow2 (U32.v k));
    UI.pow2_nth_lemma #32 (U32.v k) (31 - j);
    UI.lognot_definition #32 (U32.v m) (31 - j);
    UI.logand_definition #32 (U32.v x) (U32.v (U32.lognot m)) (31 - j);
    nth_div 32 (U32.v x) j;
    nth_div 32 (U32.v (clear_word x k)) j

/// A word with no bit set is 0.
#push-options "--fuel 1"
let rec no_bit_zero (n: nat) (v: nat)
  : Lemma (requires v < pow2 n /\ (forall (k: nat). k < n ==> (v / pow2 k) % 2 = 0))
          (ensures v == 0) (decreases n)
  = if n = 0 then ()
    else begin
      assert ((v / pow2 0) % 2 = 0);
      let aux (k: nat) : Lemma (k < n - 1 ==> ((v / 2) / pow2 k) % 2 = 0)
        = if k < n - 1 then begin
            FStar.Math.Lemmas.division_multiplication_lemma v 2 (pow2 k);
            FStar.Math.Lemmas.pow2_plus 1 k;
            assert ((v / pow2 (k + 1)) % 2 = 0)
          end
      in
      FStar.Classical.forall_intro aux;
      FStar.Math.Lemmas.pow2_plus 1 (n - 1);
      FStar.Math.Lemmas.lemma_div_lt_nat v n 1;
      no_bit_zero (n - 1) (v / 2)
    end
#pop-options

let not_bit (x: U32.t) (k: nat)
  : Lemma (requires not (bit_of x k)) (ensures (U32.v x / pow2 k) % 2 = 0)
  = let t = U32.v x / pow2 k in
    FStar.Math.Lemmas.lemma_mod_lt t 2

let word_zero (x: U32.t)
  : Lemma (requires forall (k: nat). k < 32 ==> not (bit_of x k)) (ensures x == 0ul)
  = let aux (k: nat) : Lemma (k < 32 ==> (U32.v x / pow2 k) % 2 = 0)
      = if k < 32 then not_bit x k
    in
    FStar.Classical.forall_intro aux;
    no_bit_zero 32 (U32.v x)

let zero_bits (k: nat) : Lemma (not (bit_of 0ul k)) = ()

/// ---------------------------------------------------------------------------
/// Clearing bits
/// ---------------------------------------------------------------------------

/// The bitmap with the bit of `a` cleared.
let clear_bit (bs: Seq.seq U32.t) (a: nat) : Seq.seq U32.t =
  if in_pages a && Seq.length bs = bm_len then begin
    widx_bound a;
    let w = widx a / 32 in
    Seq.upd bs w (clear_word (Seq.index bs w) (U32.uint_to_t (widx a % 32)))
  end else bs

/// Two word addresses with the same bitmap word and bit are the same.
let widx_inj (a b: nat)
  : Lemma (requires in_pages a /\ in_pages b /\ widx a / 32 == widx b / 32 /\ widx a % 32 == widx b % 32)
          (ensures a == b)
  = FStar.Math.Lemmas.euclidean_division_definition (widx a) 32;
    FStar.Math.Lemmas.euclidean_division_definition (widx b) 32;
    FStar.Math.Lemmas.euclidean_division_definition (a - zw) 8;
    FStar.Math.Lemmas.euclidean_division_definition (b - zw) 8;
    FStar.Math.Lemmas.lemma_mod_sub_distr a zw 8;
    FStar.Math.Lemmas.lemma_mod_sub_distr b zw 8

let clear_bit_len (bs: Seq.seq U32.t) (a: nat)
  : Lemma (Seq.length (clear_bit bs a) == Seq.length bs)
  = if in_pages a && Seq.length bs = bm_len then widx_bound a

let clear_bit_marked (bs: Seq.seq U32.t) (a: nat) (x: nat)
  : Lemma (marked (clear_bit bs a) x == (marked bs x && x <> a) /\ Seq.length (clear_bit bs a) == Seq.length bs)
  = clear_bit_len bs a;
    if in_pages a && Seq.length bs = bm_len && in_pages x then begin
      widx_bound a;
      widx_bound x;
      let w = widx a / 32 in
      let k = U32.uint_to_t (widx a % 32) in
      clear_word_bit (Seq.index bs w) k (widx x % 32);
      if x <> a && widx x / 32 = w && widx x % 32 = widx a % 32 then widx_inj a x
    end

/// The bitmap with page `i`'s words set to 0.
let zero_page (bs: Seq.seq U32.t) (i: nat) : Seq.seq U32.t =
  Seq.init (Seq.length bs) (fun (j: nat{j < Seq.length bs}) ->
    if i * bpp <= j && j < (i + 1) * bpp then 0ul else Seq.index bs j)

let page_of_word (a: nat) : nat = if a >= zw then (a - zw) / page_bytes else 0

let zero_page_marked (bs: Seq.seq U32.t) (i: nat{i < n_pages}) (x: nat)
  : Lemma (marked (zero_page bs i) x == (marked bs x && not (page_base i <= x && x < page_base (i + 1))) /\
           Seq.length (zero_page bs i) == Seq.length bs)
  = if in_pages x && Seq.length bs = bm_len then begin
      widx_bound x;
      let w = widx x / 32 in
      bpp_mul ();
      let j = page_of_word x in
      FStar.Math.Lemmas.lemma_div_mod (x - zw) page_bytes;
      assert (j < n_pages);
      assert (page_base j <= x /\ x < page_base (j + 1));
      widx_page j x;
      if j = i then ()
      else if j < i then begin
        FStar.Math.Lemmas.lemma_mult_le_right bpp (j + 1) i
      end else begin
        FStar.Math.Lemmas.lemma_mult_le_right bpp (i + 1) j;
        page_base_mono (i + 1) j
      end
    end

/// A page with no mark has only zero words.
let page_words_zero (bs: Seq.seq U32.t) (i: nat{i < n_pages})
  : Lemma (requires Seq.length bs == bm_len /\
                    (forall (x: nat). page_base i <= x /\ x < page_base (i + 1) ==> not (marked bs x)))
          (ensures zero_page bs i == bs)
  = bpp_mul ();
    let aux (j: nat{j < Seq.length bs}) : Lemma (Seq.index (zero_page bs i) j == Seq.index bs j)
      = if i * bpp <= j && j < (i + 1) * bpp then begin
          let bits (k: nat) : Lemma (k < 32 ==> not (bit_of (Seq.index bs j) k))
            = if k < 32 then begin
                let x = zw + (j * 32 + k) * 8 in
                assert (widx x == j * 32 + k);
                FStar.Math.Lemmas.lemma_div_plus k j 32;
                FStar.Math.Lemmas.lemma_mod_plus k j 32;
                assert (i * page_wsize <= j * 32 + k);
                assert (j * 32 + k < (i + 1) * page_wsize);
                assert (page_base i <= x /\ x < page_base (i + 1));
                page_base_mono (i + 1) n_pages;
                FStar.Math.Lemmas.lemma_mod_plus 0 (j * 32 + k) 8;
                assert (in_pages x)
              end
          in
          FStar.Classical.forall_intro bits;
          word_zero (Seq.index bs j)
        end
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro (zero_page bs i) bs

/// ---------------------------------------------------------------------------
/// Windows: marks left out over a stretch
/// ---------------------------------------------------------------------------

/// The marks of `bs` outside `[lo, hi)`.
let win (bs: Seq.seq U32.t) (lo hi: nat) (a: nat) : bool = marked bs a && not (lo <= a && a < hi)
