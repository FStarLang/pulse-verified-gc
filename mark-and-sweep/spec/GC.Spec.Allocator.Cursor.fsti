/// ---------------------------------------------------------------------------
/// GC.Spec.Allocator.Cursor - allocation while the heap may be being swept
/// ---------------------------------------------------------------------------
///
/// The allocator over the collector's phase (`GC.Spec.Phase`), as OCaml 4.14
/// allocates (`caml_alloc_shr`, `caml_allocation_color`, `caml_fl_merge`):
///
///   * **The colour.**  `GC.Spec.Allocator.alloc_search` takes the phase and
///     writes the colour `allocation_color` gives into the header, once:
///     white when idle; while sweeping, black in front of the cursor (the
///     sweep keeps it and whitens it when it gets there) and white behind it.
///
///   * **`swept_tail`.**  The sweep appends after `swept_tail`, the last list
///     cell behind its cursor (`GC.Spec.FusedSweep`).  If an allocation takes
///     that very cell off the list -- an exact fit, or a one-word leftover --
///     `swept_tail` moves back to the cell before it on the list (or to 0, the
///     list-head sentinel).  A split keeps the cell, and allocation never
///     touches `last_fragment`, which is never on the list.
///
/// `alloc_phase g fp ph wz tag` is both: the first-fit allocation at phase
/// `ph`, and the phase after it (`phase_after_alloc`, with the new
/// `swept_tail`).  `alloc_find` names the block first-fit takes and its list
/// predecessor, step by step alongside `alloc_search`.
///
/// `alloc_phase_idle` is the stop-the-world case: at `Idle` the allocator is
/// exactly `alloc_spec`, and the phase stays `Idle`.  Only the header colour
/// depends on the phase (`alloc_phase_fields`).

module GC.Spec.Allocator.Cursor

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Allocator
open GC.Spec.FusedSweep

module U64 = FStar.UInt64

/// The size the search looks for: a request of 0 words is served as 1.
let req_wz (wz: nat) : nat = if wz = 0 then 1 else wz

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
val alloc_find_search (g: heap) (head prev cur: U64.t) (wz: nat) (ph: gc_phase) (tag: U64.t{U64.v tag < 256}) (fuel: nat)
  : Lemma (let (p, c) = alloc_find g prev cur wz fuel in
           let r = alloc_search g head prev cur wz ph tag fuel in
           (c == 0UL ==> r == { heap_out = g; fp_out = head; obj_out = 0UL }) /\
           (c <> 0UL ==> fits_at g c wz /\ r == alloc_search g head p c wz ph tag 1))

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

/// ---------------------------------------------------------------------------
/// The allocator over the phase
/// ---------------------------------------------------------------------------

/// The phase after an allocation of `wz` words from the list at `fp`: the
/// sweep state with its new `swept_tail`.
let phase_after_alloc (g: heap) (fp: U64.t) (wz: nat) (ph: gc_phase) : GTot gc_phase =
  match ph with
  | Idle -> Idle
  | Sweeping st -> Sweeping { st with swept_tail = alloc_tail g fp wz st.swept_tail }

/// Allocate `wz` words with tag `tag` at phase `ph`: first-fit from `fp`, the
/// header written once with the phase's colour; and the phase after.
let alloc_phase (g: heap) (fp: U64.t) (ph: gc_phase) (wz: nat) (tag: U64.t{U64.v tag < 256})
  : GTot (alloc_result & gc_phase) =
  (alloc_search g fp 0UL fp (req_wz wz) ph tag heap_words, phase_after_alloc g fp wz ph)

/// Not sweeping: the allocator is `alloc_spec`, and the phase stays `Idle`.
val alloc_phase_idle (g: heap) (fp: U64.t) (wz: nat) (tag: U64.t{U64.v tag < 256})
  : Lemma (alloc_phase g fp Idle wz tag == (alloc_spec g fp wz tag, Idle))
          [SMTPat (alloc_phase g fp Idle wz tag)]

/// Only the heap depends on the phase -- and only through the new object's
/// colour -- so the new head and the object are `alloc_spec`'s, and a failed
/// allocation changes nothing.
val alloc_phase_fields (g: heap) (fp: U64.t) (ph: gc_phase) (wz: nat) (tag: U64.t{U64.v tag < 256})
  : Lemma (let r = fst (alloc_phase g fp ph wz tag) in
           let r0 = alloc_spec g fp wz tag in
           r.fp_out == r0.fp_out /\ r.obj_out == r0.obj_out /\
           (r.obj_out == 0UL ==> r.heap_out == g))

/// A failed allocation leaves the phase alone: it takes no cell off the list.
val alloc_phase_oom_phase (g: heap) (fp: U64.t) (ph: gc_phase) (wz: nat) (tag: U64.t{U64.v tag < 256})
  : Lemma (requires (fst (alloc_phase g fp ph wz tag)).obj_out == 0UL)
          (ensures snd (alloc_phase g fp ph wz tag) == ph)

/// The header of a new object of `w` fields, colour `col` and tag `tag`.
let new_header (w: nat) (col: color_bits) (tag: U64.t{U64.v tag < 256}) : U64.t =
  if w < pow2 54 then begin
    FStar.Math.Lemmas.pow2_lt_compat 64 54;
    make_header (U64.uint_to_t w) col tag
  end else 0UL

/// **The heap depends on the phase only through the new header's colour**:
/// it is `alloc_spec`'s heap, whose new header is white, with that header
/// rewritten in the colour the phase gives its address.
val alloc_phase_heap (g: heap) (fp: U64.t) (ph: gc_phase) (wz: nat) (tag: U64.t{U64.v tag < 256})
  : Lemma (let r = fst (alloc_phase g fp ph wz tag) in
           let r0 = alloc_spec g fp wz tag in
           r.obj_out <> 0UL ==>
             (is_obj r.obj_out /\ req_wz wz < pow2 54 /\
              (let hd = hd_address (r.obj_out <: obj_addr) in
               read_word r0.heap_out hd == new_header (req_wz wz) white_color tag /\
               r.heap_out == write_word r0.heap_out hd (new_header (req_wz wz) (allocation_color ph hd) tag))))

/// Phases that colour alike allocate alike.
val alloc_phase_colour_congr (g: heap) (fp: U64.t) (ph ph': gc_phase) (wz: nat) (tag: U64.t{U64.v tag < 256})
  : Lemma (requires forall (a: U64.t). allocation_color ph a == allocation_color ph' a)
          (ensures fst (alloc_phase g fp ph wz tag) == fst (alloc_phase g fp ph' wz tag))
