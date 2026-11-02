/// ---------------------------------------------------------------------------
/// GC.Spec.Allocator.Cursor - allocation while the heap may be being swept
/// ---------------------------------------------------------------------------
///
/// With an incremental sweep the program allocates between sweep slices, so
/// the allocator has to know where the sweep's cursor is (OCaml 4.14's
/// `caml_allocation_color` and `caml_fl_merge`):
///
///   * **Colour by position.**  An object allocated *in front of* the cursor
///     (its header at or above it) is black, so the sweep keeps it and whitens
///     it when it gets there.  One allocated *behind* the cursor is white: the
///     sweep has already passed.  "Not sweeping" is the cursor at the end of
///     the heap (`idle_cursor`), where everything is behind and white -- the
///     allocator needs no phase flag.
///
///   * **`swept_tail`.**  The sweep appends after `swept_tail`, the last list
///     cell behind its cursor (`GC.Spec.FusedSweep`).  If an allocation takes
///     that very cell off the list -- an exact fit, or a one-word leftover --
///     `swept_tail` moves back to the cell before it on the list (or to 0, the
///     list-head sentinel).  A split keeps the cell, and allocation never
///     touches `last_fragment`, which is never on the list.  Outside a sweep
///     `swept_tail` is 0 and passes through unchanged.
///
/// Both are stated as a layer over `GC.Spec.Allocator.alloc_spec`, whose
/// first-fit search, block writes and lemmas are reused unchanged:
///
///   * `alloc_at g fp wz tag cursor` is `alloc_spec g fp wz tag` with the allocated
///     object's header rewritten black when it lies in front of the cursor;
///   * `alloc_find` names the block first-fit takes and its list predecessor,
///     step by step alongside `alloc_search`, and `alloc_tail` is the new
///     `swept_tail`.
///
/// `alloc_at_idle` and `alloc_tail_idle` are the stop-the-world case: at
/// `idle_cursor` and `swept_tail = 0` the allocator is exactly `alloc_spec`.

module GC.Spec.Allocator.Cursor

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Allocator

module U64 = FStar.UInt64

/// Black colour bits (3).
let black_bits : U64.t = 3UL

/// The size the search looks for: a request of 0 words is served as 1.
let req_wz (wz: nat) : nat = if wz = 0 then 1 else wz

/// The cursor when no sweep is running: the end of the heap.
let idle_cursor : U64.t = heap_size_u64

/// An object at `obj` is in front of the cursor: its header is at or above it.
let in_front (cursor: U64.t) (obj: U64.t) : bool =
  U64.v obj >= U64.v cursor + U64.v mword

/// ---------------------------------------------------------------------------
/// Colour by position
/// ---------------------------------------------------------------------------

/// Allocation at sweep cursor `cursor`: first-fit from `fp` as `alloc_spec`,
/// the object's header black when it lies in front of the cursor.
let alloc_at (g: heap) (fp: U64.t) (wz: nat) (tag: U64.t{U64.v tag < 256}) (cursor: U64.t)
  : GTot alloc_result =
  let r = alloc_spec g fp wz tag in
  let w = req_wz wz in
  if r.obj_out <> 0UL && in_front cursor r.obj_out &&
     U64.v r.obj_out < heap_size && U64.v r.obj_out % U64.v mword = 0 && w < pow2 54
  then begin
    FStar.Math.Lemmas.pow2_lt_compat 64 54;
    { r with heap_out = write_word r.heap_out (hd_address (r.obj_out <: obj_addr))
                                   (make_header (U64.uint_to_t w) black_bits tag) }
  end
  else r

/// Not sweeping: the allocator is `alloc_spec`.
val alloc_at_idle (g: heap) (fp: U64.t) (wz: nat) (tag: U64.t{U64.v tag < 256})
  : Lemma (alloc_at g fp wz tag idle_cursor == alloc_spec g fp wz tag)

/// Only the heap can differ from `alloc_spec`'s, and only at the object's
/// header.
val alloc_at_fields (g: heap) (fp: U64.t) (wz: nat) (tag: U64.t{U64.v tag < 256}) (cursor: U64.t)
  : Lemma (let r = alloc_spec g fp wz tag in
           let r' = alloc_at g fp wz tag cursor in
           r'.fp_out == r.fp_out /\ r'.obj_out == r.obj_out /\
           (r.obj_out == 0UL ==> r'.heap_out == r.heap_out) /\
           (forall (a: hp_addr). U64.v a + 8 <> U64.v r.obj_out ==>
              read_word r'.heap_out a == read_word r.heap_out a))

/// ---------------------------------------------------------------------------
/// The block first-fit takes
/// ---------------------------------------------------------------------------

/// `cur` is a block `alloc_search` takes for a request of `wz` words: a valid
/// object address, big enough, with room for the right-justified object.
let fits_at (g: heap) (cur: U64.t) (wz: nat) : prop =
  U64.v cur >= U64.v zero_addr + U64.v mword /\ U64.v cur < heap_size /\
  U64.v cur % U64.v mword = 0 /\
  (let hd = hd_address (cur <: obj_addr) in
   let bwz = U64.v (getWosize (read_word g hd)) in
   bwz >= wz /\ U64.v hd + (bwz - wz) * 8 + 8 < heap_size)

/// `(prev, cur)`: the block `alloc_search g _ prev cur wz fuel` takes and the
/// cell before it on the list (`0` for the head), or `cur = 0` when the
/// search fails.  It follows `alloc_search`'s steps and guards exactly.
let rec alloc_find (g: heap) (prev cur: U64.t) (wz: nat) (fuel: nat)
  : GTot (U64.t & U64.t) (decreases fuel)
  = if fuel = 0 then (prev, 0UL)
    else if U64.v cur < U64.v zero_addr + U64.v mword then (prev, 0UL)
    else if U64.v cur >= heap_size then (prev, 0UL)
    else if U64.v cur % U64.v mword <> 0 then (prev, 0UL)
    else begin
      let obj : obj_addr = cur in
      let hd = hd_address obj in
      let block_wz = U64.v (getWosize (read_word g hd)) in
      if block_wz >= wz then begin
        let alloc_hd_nat = U64.v hd + (block_wz - wz) * 8 in
        if alloc_hd_nat + 8 >= heap_size || alloc_hd_nat >= pow2 64 ||
           alloc_hd_nat % 8 <> 0
        then (prev, 0UL)
        else (prev, cur)
      end
      else alloc_find g cur (spec_next_fp g obj) wz (fuel - 1)
    end

/// The search's result is the one at the block `alloc_find` names: nothing when
/// it names none, and otherwise the found arm at that block and predecessor.
val alloc_find_search (g: heap) (head prev cur: U64.t) (wz: nat) (tag: U64.t{U64.v tag < 256}) (fuel: nat)
  : Lemma (let (p, c) = alloc_find g prev cur wz fuel in
           let r = alloc_search g head prev cur wz tag fuel in
           (c == 0UL ==> r == { heap_out = g; fp_out = head; obj_out = 0UL }) /\
           (c <> 0UL ==> fits_at g c wz /\ r == alloc_search g head p c wz tag 1))

/// Step lemmas, in the shape of `alloc_search`'s (for the loop of the
/// implementation).
val alloc_find_fuel_0 (g: heap) (prev cur: U64.t) (wz: nat)
  : Lemma (alloc_find g prev cur wz 0 == (prev, 0UL))

val alloc_find_invalid (g: heap) (prev cur: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    (U64.v cur < U64.v zero_addr + U64.v mword \/
                     U64.v cur >= heap_size \/
                     U64.v cur % U64.v mword <> 0))
          (ensures alloc_find g prev cur wz fuel == (prev, 0UL))

val alloc_find_advance (g: heap) (prev cur: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v cur >= U64.v zero_addr + U64.v mword /\
                    U64.v cur < heap_size /\
                    U64.v cur % U64.v mword = 0 /\
                    U64.v (getWosize (read_word g (hd_address (cur <: obj_addr)))) < wz)
          (ensures alloc_find g prev cur wz fuel ==
                   alloc_find g cur (spec_next_fp g (cur <: obj_addr)) wz (fuel - 1))

val alloc_find_found (g: heap) (prev cur: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires fuel > 0 /\ fits_at g cur wz)
          (ensures alloc_find g prev cur wz fuel == (prev, cur))

val alloc_find_found_oob (g: heap) (prev cur: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v cur >= U64.v zero_addr + U64.v mword /\
                    U64.v cur < heap_size /\
                    U64.v cur % U64.v mword = 0 /\
                    (let hd = hd_address (cur <: obj_addr) in
                     let bwz = U64.v (getWosize (read_word g hd)) in
                     bwz >= wz /\
                     (let ahn = U64.v hd + (bwz - wz) * 8 in
                      ahn + 8 >= heap_size \/ ahn >= pow2 64 \/ ahn % 8 <> 0)))
          (ensures alloc_find g prev cur wz fuel == (prev, 0UL))

/// ---------------------------------------------------------------------------
/// `swept_tail`
/// ---------------------------------------------------------------------------

/// The wosize of the block whose object address is `x`, when `x` is one.
let block_wz (g: heap) (x: U64.t) : nat =
  if U64.v x >= U64.v mword && U64.v x < heap_size && U64.v x % U64.v mword = 0
  then U64.v (getWosize (read_word g (hd_address (x <: obj_addr))))
  else 0

/// The first-fit block and its predecessor for a request of `wz` words.
let alloc_choice (g: heap) (fp: U64.t) (wz: nat) : GTot (U64.t & U64.t) =
  alloc_find g 0UL fp (req_wz wz) heap_words

/// The allocation takes the block at `c` off the list: it is used whole, or
/// with a one-word leftover that cannot hold a link.
let takes_off (g: heap) (c: U64.t) (wz: nat) : bool =
  c <> 0UL && block_wz g c < req_wz wz + 2

/// `swept_tail` after an allocation of `wz` words from the list at `fp`: if the
/// allocation takes `swept_tail`'s own cell off the list, the cell before it.
let alloc_tail (g: heap) (fp: U64.t) (wz: nat) (t: U64.t) : GTot U64.t =
  let (p, c) = alloc_choice g fp wz in
  if c = t && takes_off g c wz then p else t

/// Not sweeping: `swept_tail = 0` passes through.
val alloc_tail_idle (g: heap) (fp: U64.t) (wz: nat)
  : Lemma (alloc_tail g fp wz 0UL == 0UL)
