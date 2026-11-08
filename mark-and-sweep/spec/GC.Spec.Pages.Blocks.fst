/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Blocks - the blocks the allocator writes
/// ---------------------------------------------------------------------------
///
/// The allocator writes two kinds of block:
///   - a fresh object: a white header of tag 0, its fields all 0;
///   - a free block or a filler: a blue header of tag 0.
/// The fields of a fresh object are cleared so that the heap is well formed
/// at once (a free slot's first field links to another free block, which
/// `no_pointer_to_blue` forbids in an object that is not free).
///
/// `two_blocks` walks a stretch laid out as one block, or as one block and a
/// second right after it, and shows each is a good new block in the sense
/// of `GC.Spec.Pages.Replace`.

module GC.Spec.Pages.Blocks

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Walk
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Replace

module U64 = FStar.UInt64
module Seq = FStar.Seq

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Headers
/// ---------------------------------------------------------------------------

let ohdr (wz: nat{wz < pow2 54}) : U64.t =
  FStar.Math.Lemmas.pow2_lt_compat 64 54;
  makeHeader (U64.uint_to_t wz) White 0UL

let bhdr (w: pos{w <= pow2 54}) : U64.t =
  FStar.Math.Lemmas.pow2_lt_compat 64 54;
  makeHeader (U64.uint_to_t (w - 1)) Blue 0UL

let ohdr_spec (wz: nat{wz < pow2 54})
  : Lemma (U64.v (getWosize (ohdr wz)) == wz /\ getColor (ohdr wz) == White /\
           getTag (ohdr wz) == 0UL)
  = FStar.Math.Lemmas.pow2_lt_compat 64 54;
    makeHeader_getWosize (U64.uint_to_t wz) White 0UL;
    makeHeader_getColor (U64.uint_to_t wz) White 0UL;
    makeHeader_getTag (U64.uint_to_t wz) White 0UL

let bhdr_spec (w: pos{w <= pow2 54})
  : Lemma (U64.v (getWosize (bhdr w)) + 1 == w /\ getColor (bhdr w) == Blue /\
           getTag (bhdr w) == 0UL)
  = FStar.Math.Lemmas.pow2_lt_compat 64 54;
    makeHeader_getWosize (U64.uint_to_t (w - 1)) Blue 0UL;
    makeHeader_getColor (U64.uint_to_t (w - 1)) Blue 0UL;
    makeHeader_getTag (U64.uint_to_t (w - 1)) Blue 0UL

/// ---------------------------------------------------------------------------
/// Writes
/// ---------------------------------------------------------------------------

/// Write a word at a byte offset; nothing if it is not a word of the heap.
let wr (g: heap) (a: nat) (v: U64.t) : GTot heap =
  if a < heap_size && a % 8 = 0 then write_word g (mk_hp_addr a) v else g

let wr_read (g: heap) (a: nat) (v: U64.t) (x: hp_addr)
  : Lemma (read_word (wr g a v) x == (if U64.v x = a then v else read_word g x))
  = if a < heap_size && a % 8 = 0 then begin
      if U64.v x = a then read_write_same g (mk_hp_addr a) v
      else read_write_different g (mk_hp_addr a) x v
    end

/// Clear the `n` words from `a`.
#push-options "--fuel 1"
let rec zeros (g: heap) (a: nat) (n: nat) : GTot heap (decreases n) =
  if n = 0 then g else wr (zeros g a (n - 1)) (a + (n - 1) * 8) 0UL

let rec zeros_read (g: heap) (a: nat) (n: nat) (x: hp_addr)
  : Lemma (requires a % 8 == 0)
          (ensures read_word (zeros g a n) x ==
                   (if a <= U64.v x && U64.v x < a + n * 8 then 0UL else read_word g x))
          (decreases n)
  = if n = 0 then ()
    else begin
      zeros_read g a (n - 1) x;
      wr_read (zeros g a (n - 1)) (a + (n - 1) * 8) 0UL x;
      if a <= U64.v x && U64.v x < a + n * 8 && U64.v x >= a + (n - 1) * 8 then begin
        FStar.Math.Lemmas.lemma_mod_plus a (n - 1) 8;
        assert (U64.v x == a + (n - 1) * 8)
      end
    end
#pop-options

/// A fresh object of wosize `wz` with its header at `h`, its fields as they
/// were.
let put_hdr (g: heap) (h: nat) (wz: nat{wz < pow2 54}) : GTot heap = wr g h (ohdr wz)

/// The same, with its fields cleared.
let put_obj (g: heap) (h: nat) (wz: nat{wz < pow2 54}) : GTot heap =
  zeros (put_hdr g h wz) (h + 8) wz

/// The allocator's object write: `clr` says whether it clears the fields.
/// The spec allocator does not; its proofs go through the cleared heap.
let put_obj_as (clr: bool) (g: heap) (h: nat) (wz: nat{wz < pow2 54}) : GTot heap =
  if clr then put_obj g h wz else put_hdr g h wz

let put_obj_read (g: heap) (h: nat) (wz: nat{wz < pow2 54}) (x: hp_addr)
  : Lemma (requires h % 8 == 0)
          (ensures read_word (put_obj g h wz) x ==
                   (if U64.v x = h then ohdr wz
                    else if h < U64.v x && U64.v x < h + (wz + 1) * 8 then 0UL
                    else read_word g x))
  = zeros_read (wr g h (ohdr wz)) (h + 8) wz x;
    wr_read g h (ohdr wz) x

/// A blue header of `w` words at `h`.
let put_blue (g: heap) (h: nat) (w: pos{w <= pow2 54}) : GTot heap = wr g h (bhdr w)

let hdr_wr (g: heap) (a: nat) (v: U64.t)
  : Lemma (requires a < heap_size /\ a % 8 == 0)
          (ensures hdr (wr g a v) a == v)
  = wr_read g a v (mk_hp_addr a)

/// Clearing words past the heap changes nothing.
#push-options "--fuel 1"
let rec zeros_beyond (g: heap) (a: nat) (n: nat)
  : Lemma (requires a >= heap_size) (ensures zeros g a n == g) (decreases n)
  = if n = 0 then () else zeros_beyond g a (n - 1)
#pop-options

/// `gc` is `gr` with the fields of the new object `obj`, of wosize `wz`,
/// cleared; and `gr` holds the object's header.  It relates the heap the
/// allocator makes to the one it would make if it cleared the fields.
let clears (gr gc: heap) (obj: U64.t) (wz: nat{wz < pow2 54}) : prop =
  gc == (if obj = 0UL then gr else zeros gr (U64.v obj) wz) /\
  (U64.v obj >= 8 /\ U64.v obj - 8 < heap_size /\ U64.v obj % 8 == 0 ==>
     hdr gr (U64.v obj - 8) == ohdr wz)

let put_obj_clears (g: heap) (a: nat) (wz: nat{wz < pow2 54}) (obj: U64.t)
  : Lemma (requires U64.v obj == a + 8 \/ (obj == 0UL /\ a + 8 >= pow2 64))
          (ensures clears (put_obj_as false g a wz) (put_obj_as true g a wz) obj wz)
  = if obj = 0UL then zeros_beyond (put_hdr g a wz) (a + 8) wz
    else if a < heap_size && a % 8 = 0 then hdr_wr g a (ohdr wz)

/// ---------------------------------------------------------------------------
/// Good new blocks
/// ---------------------------------------------------------------------------

/// A fresh object is a good new block.
let obj_block (g: heap) (h: nat) (wz: nat{wz < pow2 54})
  : Lemma (requires h % 8 == 0 /\ h + (wz + 1) * 8 <= heap_size /\
                    hdr g h == ohdr wz /\
                    (forall (x: hp_addr). h < U64.v x /\ U64.v x < h + (wz + 1) * 8 ==>
                       read_word g x == 0UL))
          (ensures new_block_ok g h /\ words_at g h == wz + 1 /\ color_at g h == White)
  = ohdr_spec wz;
    infix_tag_val ()

/// A blue block is a good new block.
let blue_block_ok (g: heap) (h: nat) (w: pos{w <= pow2 54})
  : Lemma (requires hdr g h == bhdr w)
          (ensures new_block_ok g h /\ words_at g h == w /\ color_at g h == Blue)
  = bhdr_spec w;
    infix_tag_val ()

/// ---------------------------------------------------------------------------
/// One or two blocks
/// ---------------------------------------------------------------------------

/// The walk over one block of `w1` words at `a`, then, if `w2 > 0`, one of
/// `w2` words: it ends at `a + (w1 + w2) * 8` and stops only at the blocks.
let two_blocks (g: heap) (a: nat) (w1: pos) (w2: nat)
  : Lemma (requires a % 8 == 0 /\ a + (w1 + w2) * 8 <= heap_size /\
                    words_at g a == w1 /\ new_block_ok g a /\
                    (w2 > 0 ==> words_at g (a + w1 * 8) == w2 /\ new_block_ok g (a + w1 * 8)))
          (ensures steps_to g a (a + (w1 + w2) * 8) /\
                   (forall (b: nat). steps_to g a b /\ b < a + (w1 + w2) * 8 ==>
                      new_block_ok g b /\ (b == a \/ (w2 > 0 /\ b == a + w1 * 8))))
  = let e = a + (w1 + w2) * 8 in
    let m = a + w1 * 8 in
    block_steps g a w1;
    if w2 > 0 then begin
      aligned_plus_mul8 a w1;
      block_steps g m w2;
      steps_to_trans g a m e
    end;
    let pos (b: nat)
      : Lemma (requires steps_to g a b /\ b < e)
              (ensures b == a \/ (w2 > 0 /\ b == m))
      = steps_to_le g a b;
        if b > a then begin
          steps_to_refl g a;
          block_before g a a b;
          assert (m <= b);
          steps_to_refl g m;
          if w2 > 0 && b > m then begin
            block_before g m m b;
            assert (m + w2 * 8 <= b);
            assert False
          end
          else if w2 = 0 then assert False
          else assert (b == m)
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires pos)

/// Inside one block, the walk stops only at its start.
let one_block_pos (g: heap) (a b: nat)
  : Lemma (requires steps_to g a b /\ b < a + words_at g a * 8)
          (ensures b == a)
  = steps_to_le g a b;
    if b > a then (steps_to_refl g a; block_before g a a b)
