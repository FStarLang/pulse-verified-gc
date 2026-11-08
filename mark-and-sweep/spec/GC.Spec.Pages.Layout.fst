/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Layout - pages, size classes and slots, as arithmetic
/// ---------------------------------------------------------------------------
///
/// The major heap `[zero_addr, heap_size)` is divided into `n_pages` pages of
/// `page_wsize` words, starting at `zero_addr`.  What is left after the last
/// whole page, fewer than `page_wsize` words, is the heap's tail; the runtime
/// rounds the heap so that it is empty, but nothing here relies on that.
///
/// A page of class `c` holds `n_slots c` slots of `cls c` words, from the
/// page start; the `tail_words c` words left over form the page tail.
///
/// Every address here is a byte offset, as a `nat`.  Only the parameters'
/// conditions (`GC.Spec.Pages.Params.params_cond`) are used, never their
/// values.

module GC.Spec.Pages.Layout

open GC.Spec.Base
open GC.Spec.Pages.Params

module U64 = FStar.UInt64

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Size classes
/// ---------------------------------------------------------------------------

let rec cls_mono (c d: nat)
  : Lemma (requires c <= d /\ d < n_cls)
          (ensures cls c <= cls d)
          (decreases (d - c))
  = params_ok ();
    if c = d then () else cls_mono c (d - 1)

/// Every class is at least 2 words and fits in a page.
let cls_bounds (c: nat{c < n_cls})
  : Lemma (2 <= cls c /\ cls c <= small_max /\ small_max <= page_wsize /\
           page_wsize < pow2 20)
  = params_ok ();
    cls_mono 0 c;
    cls_mono c (n_cls - 1)

/// A size that has a class: 1 to `small_max` words, header included.
let small_size = w:pos{w <= small_max}

#push-options "--fuel 1"
let rec class_from (w: small_size) (c: nat{c < n_cls})
  : Tot (r: nat{c <= r /\ r < n_cls}) (decreases (n_cls - c))
  = if w <= cls c || c + 1 >= n_cls then c else class_from w (c + 1)
#pop-options

/// The class of a block of `w` words: the smallest class that holds it.
let class_of (w: small_size) : r: nat{r < n_cls} = class_from w 0

#push-options "--fuel 1"
let rec class_from_fits (w: small_size) (c: nat{c < n_cls})
  : Lemma (ensures w <= cls (class_from w c)) (decreases (n_cls - c))
  = if w <= cls c then ()
    else if c + 1 >= n_cls then (assert (c == n_cls - 1))
    else class_from_fits w (c + 1)

let rec class_from_least (w: small_size) (c: nat{c < n_cls}) (d: nat)
  : Lemma (requires (forall (e: nat). e < c ==> cls e < w) /\ d < class_from w c)
          (ensures cls d < w)
          (decreases (n_cls - c))
  = if w <= cls c || c + 1 >= n_cls then ()
    else class_from_least w (c + 1) d
#pop-options

/// The class of `w` holds `w` words ...
let class_of_fits (w: small_size)
  : Lemma (w <= cls (class_of w))
  = class_from_fits w 0

/// ... and no smaller class does.
let class_of_least (w: small_size) (d: nat)
  : Lemma (requires d < class_of w)
          (ensures cls d < w)
  = class_from_least w 0 d

/// ---------------------------------------------------------------------------
/// Pages
/// ---------------------------------------------------------------------------

let page_bytes : pos = page_wsize * 8

let n_pages : nat = (heap_size - U64.v zero_addr) / page_bytes

/// The start of page `i`; page `n_pages` is the start of the heap's tail.
let page_base (i: nat) : nat = U64.v zero_addr + i * page_bytes

/// The end of the last whole page.
let pages_end : nat = page_base n_pages

let in_page (i: nat) (a: nat) : bool = page_base i <= a && a < page_base (i + 1)

let page_base_aligned (i: nat)
  : Lemma (page_base i % 8 == 0)
  = assert (U64.v zero_addr % 8 == 0);
    FStar.Math.Lemmas.lemma_mod_plus (U64.v zero_addr) (i * page_wsize) 8

let pages_end_bound ()
  : Lemma (pages_end <= heap_size /\ heap_size - pages_end < page_bytes)
  = FStar.Math.Lemmas.lemma_div_mod (heap_size - U64.v zero_addr) page_bytes

/// Pages are laid out in order, inside the heap.
let page_base_mono (i j: nat)
  : Lemma (requires i <= j /\ j <= n_pages)
          (ensures page_base i <= page_base j /\ page_base j <= pages_end /\
                   pages_end <= heap_size /\
                   (i < j ==> page_base i + page_bytes <= page_base j))
  = pages_end_bound ();
    FStar.Math.Lemmas.lemma_mult_le_right page_bytes i j;
    FStar.Math.Lemmas.lemma_mult_le_right page_bytes j n_pages;
    if i < j then FStar.Math.Lemmas.lemma_mult_le_right page_bytes (i + 1) j

/// The page an address in `[zero_addr, pages_end)` lies in.
let page_of (a: nat{U64.v zero_addr <= a /\ a < pages_end}) : nat =
  (a - U64.v zero_addr) / page_bytes

let page_of_spec (a: nat{U64.v zero_addr <= a /\ a < pages_end})
  : Lemma (page_of a < n_pages /\ in_page (page_of a) a)
  = FStar.Math.Lemmas.lemma_div_mod (a - U64.v zero_addr) page_bytes;
    let i = page_of a in
    if i >= n_pages then begin
      FStar.Math.Lemmas.lemma_mult_le_right page_bytes n_pages i;
      assert False
    end

/// Two pages are disjoint.
let in_page_unique (i j: nat) (a: nat)
  : Lemma (requires in_page i a /\ in_page j a) (ensures i == j)
  = if i < j then FStar.Math.Lemmas.lemma_mult_le_right page_bytes (i + 1) j
    else if j < i then FStar.Math.Lemmas.lemma_mult_le_right page_bytes (j + 1) i

/// ---------------------------------------------------------------------------
/// Slots
/// ---------------------------------------------------------------------------

/// The number of slots in a page of class `c`; at least one, by C3.
let n_slots (c: nat{c < n_cls}) : pos =
  cls_bounds c;
  FStar.Math.Lemmas.lemma_div_le (cls c) page_wsize (cls c);
  page_wsize / cls c

/// The words a page of class `c` has after its last slot.
let tail_words (c: nat{c < n_cls}) : nat = page_wsize % cls c

/// The start of slot `k` of page `i`, of class `c`.
let slot_base (i: nat) (c: nat{c < n_cls}) (k: nat) : nat = page_base i + k * cls c * 8

/// The end of the last slot: the start of the page tail.
let slots_end (i: nat) (c: nat{c < n_cls}) : nat = slot_base i c (n_slots c)

let slot_base_aligned (i: nat) (c: nat{c < n_cls}) (k: nat)
  : Lemma (slot_base i c k % 8 == 0)
  = page_base_aligned i;
    FStar.Math.Lemmas.lemma_mod_plus (page_base i) (k * cls c) 8

/// Slot `k + 1` starts where slot `k` ends.
let slot_base_succ (i: nat) (c: nat{c < n_cls}) (k: nat)
  : Lemma (slot_base i c (k + 1) == slot_base i c k + cls c * 8)
  = FStar.Math.Lemmas.distributivity_add_left k 1 (cls c * 8)

/// The slots and the tail exactly fill the page.
let slots_fill_page (i: nat) (c: nat{c < n_cls})
  : Lemma (slots_end i c + tail_words c * 8 == page_base (i + 1) /\
           page_base i < slots_end i c /\ slots_end i c <= page_base (i + 1))
  = cls_bounds c;
    FStar.Math.Lemmas.lemma_div_mod page_wsize (cls c);
    FStar.Math.Lemmas.distributivity_add_left i 1 page_bytes

/// A slot lies inside its page.
let slot_in_page (i: nat) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (page_base i <= slot_base i c k /\
           slot_base i c k + cls c * 8 <= slots_end i c)
  = slot_base_succ i c k;
    FStar.Math.Lemmas.lemma_mult_le_right (cls c * 8) (k + 1) (n_slots c)
