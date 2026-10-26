/// ---------------------------------------------------------------------------
/// GC.Spec.FusedSweep - the sweep, one block at a time
/// ---------------------------------------------------------------------------
///
/// The sweep that follows marking, as OCaml 4.14's first-fit sweep does it:
/// one pass over the heap that turns survivors white, frees garbage, and merges
/// every run of adjacent free blocks into one, editing the free list in place.
///
/// The free list is kept across collections and runs in address order
/// (`GC.Spec.FreeList.Ascending`).  The sweep walks the heap upwards with a
/// cursor, so the list splits at the cursor: behind it, the blocks the sweep
/// has finished, ending at `swept_tail`; in front of it, the list as marking
/// left it.  Appending a new free block after `swept_tail` is one link write,
/// and the block after `swept_tail` on the list is always the first list block
/// at or above the cursor.
///
/// Sweep state, between steps:
///
///   cursor         the header address of the next block to visit
///   swept_tail     the last list block behind the cursor, or 0 (the list-head
///                  sentinel: the next link written goes into the head)
///   last_fragment  the object address of the block just behind the cursor,
///                  when that block is free but header-only (no room for a
///                  link, so not on the list); otherwise 0
///
/// The block just before the cursor is free exactly when `last_fragment` is
/// set or `swept_tail`'s block ends at the cursor (`prev_free`).
///
/// One step reads the header at the cursor *in the current heap*:
///
///   black   a survivor: turn it white;
///   free or white, and the previous block is free: grow the previous block
///           over this one (`grow`); unlink this block if it was on the list;
///           a header-only block that grows gains room for a link and is
///           linked in after `swept_tail`;
///   blue, previous not free: leave it; if it is on the list it becomes
///           `swept_tail`, otherwise it is a fragment;
///   white, previous not free: free it; link it after `swept_tail` if it has
///           room for a link, otherwise it is a fragment.
///
/// The correctness argument is a loop invariant on this step
/// (`GC.Spec.FusedSweep.Inv`), with one lemma per case.

module GC.Spec.FusedSweep

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object

module U64 = FStar.UInt64
module Header = GC.Lib.Header

/// ---------------------------------------------------------------------------
/// State
/// ---------------------------------------------------------------------------

type sweep_state = {
  cursor: U64.t;
  swept_tail: U64.t;
  last_fragment: U64.t;
}

let sweep_start : sweep_state =
  { cursor = zero_addr; swept_tail = 0UL; last_fragment = 0UL }

/// ---------------------------------------------------------------------------
/// Helpers
/// ---------------------------------------------------------------------------

/// `x` is a well-formed object address.
let is_obj (x: U64.t) : bool =
  U64.v x >= U64.v mword && U64.v x < heap_size && U64.v x % U64.v mword = 0

/// The wosize of the block whose object address is `x` (0 when `x` is not one).
let wosize_at (g: heap) (x: U64.t) : nat =
  if is_obj x then U64.v (getWosize (read_word g (hd_address (x <: obj_addr)))) else 0

/// The header of a free block of `wz` fields.
let free_header (wz: nat{wz < pow2 54}) : U64.t =
  FStar.Math.Lemmas.pow2_lt_compat 64 54;
  makeHeader (U64.uint_to_t wz) Header.Blue 0UL

/// The link that follows `swept_tail` on the list: the head itself when
/// `swept_tail` is the sentinel.
let after_tail (g: heap) (fp: U64.t) (t: U64.t) : U64.t =
  if t = 0UL then fp
  else if is_obj t then read_word g (t <: hp_addr)
  else 0UL

/// Make `v` follow `swept_tail` on the list.
let set_after_tail (g: heap) (fp: U64.t) (t: U64.t) (v: U64.t) : heap & U64.t =
  if t = 0UL then (g, v)
  else if is_obj t then (write_word g (t <: hp_addr) v, fp)
  else (g, fp)

/// The block just before the cursor is free.
let prev_free (g: heap) (st: sweep_state) : bool =
  st.last_fragment <> 0UL ||
  (st.swept_tail <> 0UL &&
   U64.v st.swept_tail + wosize_at g st.swept_tail * 8 = U64.v st.cursor)

/// The cursor is at a header the sweep can read.
let cursor_ok (st: sweep_state) : bool =
  U64.v st.cursor + 8 < heap_size && U64.v st.cursor % U64.v mword = 0

/// The position after the block at the cursor.
let step_next (g: heap) (st: sweep_state{cursor_ok st}) : nat =
  U64.v st.cursor + (U64.v (getWosize (read_word g (st.cursor <: hp_addr))) + 1) * 8

/// The sweep can take a step: the block at the cursor fits in the heap.
let can_sweep (g: heap) (st: sweep_state) : bool =
  cursor_ok st && step_next g st <= heap_size

/// ---------------------------------------------------------------------------
/// One step
/// ---------------------------------------------------------------------------

/// The state after a step that leaves `swept_tail` and clears `last_fragment`.
let advance (st: sweep_state) (nx: U64.t) : sweep_state =
  { cursor = nx; swept_tail = st.swept_tail; last_fragment = 0UL }

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let sweep_step (g: heap) (fp: U64.t) (st: sweep_state{can_sweep g st})
  : r: (heap & U64.t & sweep_state){U64.v (Mktuple3?._3 r).cursor == step_next g st}
  = let c : hp_addr = st.cursor in
    let hdr = read_word g c in
    let wz = getWosize hdr in
    let b : hp_addr = U64.add st.cursor mword in
    let nx : U64.t = U64.uint_to_t (step_next g st) in
    let col = getColor hdr in
    if col = Header.Black then
      // A survivor: turn it white, keeping its size and tag.
      (write_word g c (makeHeader wz Header.White (getTag hdr)), fp, advance st nx)
    else begin
      // On the list: blue with room for a link.
      let linked = col = Header.Blue && U64.v wz >= 1 in
      if prev_free g st then begin
        // Grow the free block before the cursor over this one.
        let p = if st.last_fragment <> 0UL then st.last_fragment else st.swept_tail in
        if not (is_obj p) || wosize_at g p + U64.v wz + 1 >= pow2 54
        then (g, fp, advance st nx)   // unreachable under the invariant
        else begin
          let g1 = write_word g (hd_address (p <: obj_addr))
                              (free_header (wosize_at g p + U64.v wz + 1)) in
          if st.last_fragment <> 0UL then begin
            // A header-only block grew a link field: it joins the list after
            // `swept_tail`, in place of this block if this one was linked.
            let nxt = if linked then read_word g b else after_tail g fp st.swept_tail in
            let g2 = write_word g1 (p <: hp_addr) nxt in
            let r = set_after_tail g2 fp st.swept_tail p in
            (fst r, snd r, { cursor = nx; swept_tail = p; last_fragment = 0UL })
          end
          else if linked then begin
            // `swept_tail` grew over a list block: unlink it.
            let r = set_after_tail g1 fp st.swept_tail (read_word g b) in
            (fst r, snd r, advance st nx)
          end
          else (g1, fp, advance st nx)
        end
      end
      else if col = Header.Blue then begin
        // Already free, and not adjacent to a free block: leave it.
        if U64.v wz >= 1
        then (g, fp, { cursor = nx; swept_tail = b; last_fragment = 0UL })
        else (g, fp, { cursor = nx; swept_tail = st.swept_tail; last_fragment = b })
      end
      else begin
        // Garbage, not adjacent to a free block: free it.
        let g1 = write_word g c (free_header (U64.v wz)) in
        if U64.v wz >= 1 then begin
          let g2 = write_word g1 b (after_tail g fp st.swept_tail) in
          let r = set_after_tail g2 fp st.swept_tail b in
          (fst r, snd r, { cursor = nx; swept_tail = b; last_fragment = 0UL })
        end
        else (g1, fp, { cursor = nx; swept_tail = st.swept_tail; last_fragment = b })
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The pass
/// ---------------------------------------------------------------------------

/// Step until the cursor reaches the end of the heap.
let rec sweep_from (g: heap) (fp: U64.t) (st: sweep_state)
  : Tot (heap & U64.t) (decreases (heap_size - U64.v st.cursor))
  = if not (can_sweep g st) then (g, fp)
    else begin
      let r = sweep_step g fp st in
      let (g', fp', st') = r in
      sweep_from g' fp' st'
    end

/// The fused sweep: whiten survivors, free garbage, merge adjacent free blocks,
/// and keep the free list (headed by `fp`) exact and ascending.  Returns the
/// heap and the head of the free list.
let fused_sweep_coalesce (g: heap) (fp: U64.t) : heap & U64.t =
  sweep_from g fp sweep_start

/// One unfolding of the pass.
let sweep_from_step (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires can_sweep g st)
          (ensures (let (g', fp', st') = sweep_step g fp st in
                    sweep_from g fp st == sweep_from g' fp' st'))
  = ()

/// The pass stops where it cannot step.
let sweep_from_stop (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires not (can_sweep g st))
          (ensures sweep_from g fp st == (g, fp))
  = ()
