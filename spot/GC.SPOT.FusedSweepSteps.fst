/// ---------------------------------------------------------------------------
/// GC.SPOT.FusedSweepSteps - the fused sweep's step on small concrete heaps
/// ---------------------------------------------------------------------------
///
/// Unit tests of `GC.Spec.FusedSweep.sweep_step` for the cases that are new
/// with the in-place, ascending free list, on hand-built heap prefixes at the
/// start of the heap (`zero_addr`, the start of the only extent):
///
///   * `frag_at_start_joins_list`: a header-only free block at the very start
///     of the heap absorbs the garbage block after it, gains a link field and
///     becomes the head of the list (merge at an extent's start, and a
///     fragment that grows linkable);
///   * `old_cell_absorbed_and_unlinked`: a list block left by the previous
///     cycle sits right after `swept_tail`'s block; it is merged into it and
///     unlinked, so the list stays exact;
///   * `old_cell_kept`: a list block from the previous cycle that is not next
///     to a free block is left alone -- no write at all -- and becomes
///     `swept_tail`;
///   * `survivor_whitened`: a black block is turned white, nothing else.
///
/// Each statement gives the exact heap words and sweep state after the step.

module GC.SPOT.FusedSweepSteps

module U64 = FStar.UInt64
module Seq = FStar.Seq
module Header = GC.Lib.Header

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.FusedSweep

module Inv = GC.Spec.FusedSweep.Inv
module Step = GC.Spec.FusedSweep.Step

#set-options "--fuel 0 --ifuel 1 --z3rlimit 40"

/// Room for the four-word fixtures after `zero_addr`.
let room = U64.v zero_addr + 64 <= heap_size

let z : U64.t = zero_addr

let at (k: nat{k <= 7}) (r: unit{room}) : hp_addr =
  mk_hp_addr (U64.v zero_addr + 8 * k)

let small_wz (wz: nat{wz < 4}) : wosize =
  assert_norm (4 < pow2 54); U64.uint_to_t wz

let hdr (wz: nat{wz < 4}) (c: color) : U64.t =
  makeHeader (small_wz wz) c 0UL

let hdr_facts (wz: nat{wz < 4}) (c: color)
  : Lemma (U64.v (getWosize (hdr wz c)) == wz /\ getColor (hdr wz c) == c /\
           getTag (hdr wz c) == 0UL)
  = makeHeader_getWosize (small_wz wz) c 0UL;
    makeHeader_getColor (small_wz wz) c 0UL;
    makeHeader_getTag (small_wz wz) c 0UL

/// The header of a free block of three fields.
let fh3 : U64.t = assert_norm (3 < pow2 54); free_header 3

/// Reading through one write.
let rw (g: heap) (x: hp_addr) (v: U64.t) (a: hp_addr)
  : Lemma (read_word (write_word g x v) a == (if a = x then v else read_word g a))
  = if a = x then read_write_same g x v else read_write_different g x a v

let hd_of (r: unit{room}) (k: nat{1 <= k /\ k <= 7})
  : Lemma (hd_address (at k r <: obj_addr) == at (k - 1) r)
  = hd_address_spec (at k r <: obj_addr)

/// ---------------------------------------------------------------------------
/// A fragment at the start of the heap absorbs garbage and joins the list
/// ---------------------------------------------------------------------------

/// [z: fragment (blue, wosize 0)] [z+8: garbage (white, wosize 2)] ...,
/// cursor at z+8, `last_fragment` = z+8, no `swept_tail` yet.
let frag_heap (g: heap) (r: unit{room}) : heap =
  write_word (write_word g (at 0 r) (hdr 0 Header.Blue)) (at 1 r) (hdr 2 Header.White)

#push-options "--z3rlimit 60"
let frag_at_start_joins_list (g: heap) (fp: U64.t) (r: unit{room})
  : Lemma (let g0 = frag_heap g r in
           let st = { cursor = at 1 r; swept_tail = 0UL; last_fragment = at 1 r } in
           can_sweep g0 st /\
           (let (g', fp', st') = sweep_step g0 fp st in
            // the fragment's header now covers both blocks ...
            read_word g' (at 0 r) == fh3 /\
            // ... its new link field continues the list ...
            read_word g' (at 1 r) == fp /\
            // ... and it is the list's head and the new swept_tail
            fp' == (at 1 r <: U64.t) /\
            st' == { cursor = at 4 r; swept_tail = at 1 r; last_fragment = 0UL }))
  = let g0 = frag_heap g r in
    let st = { cursor = at 1 r; swept_tail = 0UL; last_fragment = at 1 r } in
    hdr_facts 0 Header.Blue; hdr_facts 2 Header.White;
    FStar.Classical.forall_intro (rw g (at 0 r) (hdr 0 Header.Blue));
    FStar.Classical.forall_intro (rw (write_word g (at 0 r) (hdr 0 Header.Blue)) (at 1 r) (hdr 2 Header.White));
    hd_of r 1;
    assert (read_word g0 (at 1 r) == hdr 2 Header.White);
    assert (read_word g0 (at 0 r) == hdr 0 Header.Blue);
    assert (can_sweep g0 st);
    assert_norm (3 < pow2 54);
    Step.step_eq_merge g0 fp st;
    let g1 = write_word g0 (at 0 r) (fh3) in
    FStar.Classical.forall_intro (rw g0 (at 0 r) (fh3));
    FStar.Classical.forall_intro (rw g1 (at 1 r) fp);
    assert (U64.uint_to_t (step_next g0 st) == at 4 r)
#pop-options

/// ---------------------------------------------------------------------------
/// A block of the previous cycle's list, next to swept_tail's block, is
/// absorbed and unlinked
/// ---------------------------------------------------------------------------

/// [z: free (wosize 1), link -> z+24 = swept_tail] [z+16: free (wosize 1),
/// on the list from the previous cycle, link = nxt], cursor at z+16.
let old_heap (g: heap) (nxt: U64.t) (r: unit{room}) : heap =
  let g1 = write_word g (at 0 r) (hdr 1 Header.Blue) in
  let g2 = write_word g1 (at 1 r) (at 3 r) in
  let g3 = write_word g2 (at 2 r) (hdr 1 Header.Blue) in
  write_word g3 (at 3 r) nxt

#push-options "--z3rlimit 80"
let old_heap_reads (g: heap) (nxt: U64.t) (r: unit{room})
  : Lemma (let h = old_heap g nxt r in
           read_word h (at 0 r) == hdr 1 Header.Blue /\ read_word h (at 1 r) == (at 3 r <: U64.t) /\
           read_word h (at 2 r) == hdr 1 Header.Blue /\ read_word h (at 3 r) == nxt)
  = let g1 = write_word g (at 0 r) (hdr 1 Header.Blue) in
    let g2 = write_word g1 (at 1 r) (at 3 r) in
    let g3 = write_word g2 (at 2 r) (hdr 1 Header.Blue) in
    FStar.Classical.forall_intro (rw g (at 0 r) (hdr 1 Header.Blue));
    FStar.Classical.forall_intro (rw g1 (at 1 r) (at 3 r));
    FStar.Classical.forall_intro (rw g2 (at 2 r) (hdr 1 Header.Blue));
    FStar.Classical.forall_intro (rw g3 (at 3 r) nxt)
#pop-options

#push-options "--z3rlimit 60"
let old_cell_absorbed_and_unlinked (g: heap) (fp nxt: U64.t) (r: unit{room})
  : Lemma (let g0 = old_heap g nxt r in
           let st = { cursor = at 2 r; swept_tail = at 1 r; last_fragment = 0UL } in
           can_sweep g0 st /\
           (let (g', fp', st') = sweep_step g0 fp st in
            // swept_tail's block grows over the old list block ...
            read_word g' (at 0 r) == fh3 /\
            // ... which is unlinked: swept_tail now links where it linked
            read_word g' (at 1 r) == nxt /\
            fp' == fp /\
            st' == { cursor = at 4 r; swept_tail = at 1 r; last_fragment = 0UL }))
  = let g0 = old_heap g nxt r in
    let st = { cursor = at 2 r; swept_tail = at 1 r; last_fragment = 0UL } in
    old_heap_reads g nxt r;
    hdr_facts 1 Header.Blue;
    hd_of r 1;
    assert (wosize_at g0 (at 1 r) == 1);
    assert (prev_free g0 st);
    assert (can_sweep g0 st);
    assert_norm (3 < pow2 54);
    Step.step_eq_merge g0 fp st;
    let g1 = write_word g0 (at 0 r) (fh3) in
    FStar.Classical.forall_intro (rw g0 (at 0 r) (fh3));
    FStar.Classical.forall_intro (rw g1 (at 1 r) nxt);
    assert (U64.uint_to_t (step_next g0 st) == at 4 r)
#pop-options

/// ---------------------------------------------------------------------------
/// A list block of the previous cycle with no free neighbour is left alone
/// ---------------------------------------------------------------------------

/// [z: survivor-to-be (black, wosize 1)] [z+16: free (wosize 1), on the
/// list], cursor at z+16 after the survivor was passed.
let kept_heap (g: heap) (r: unit{room}) : heap =
  write_word (write_word g (at 0 r) (hdr 1 Header.White)) (at 2 r) (hdr 1 Header.Blue)

#push-options "--z3rlimit 60"
let old_cell_kept (g: heap) (fp: U64.t) (r: unit{room})
  : Lemma (let g0 = kept_heap g r in
           let st = { cursor = at 2 r; swept_tail = 0UL; last_fragment = 0UL } in
           can_sweep g0 st /\
           sweep_step g0 fp st ==
             (g0, fp, { cursor = at 4 r; swept_tail = at 3 r; last_fragment = 0UL }))
  = let g0 = kept_heap g r in
    let st = { cursor = at 2 r; swept_tail = 0UL; last_fragment = 0UL } in
    hdr_facts 1 Header.White; hdr_facts 1 Header.Blue;
    FStar.Classical.forall_intro (rw g (at 0 r) (hdr 1 Header.White));
    FStar.Classical.forall_intro (rw (write_word g (at 0 r) (hdr 1 Header.White)) (at 2 r) (hdr 1 Header.Blue));
    assert (read_word g0 (at 2 r) == hdr 1 Header.Blue);
    assert (not (prev_free g0 st));
    assert (can_sweep g0 st);
    Step.step_eq_blue g0 fp st;
    assert (U64.uint_to_t (step_next g0 st) == at 4 r);
    assert (Step.bx_of st == at 3 r)
#pop-options

/// ---------------------------------------------------------------------------
/// A survivor is whitened
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 60"
let survivor_whitened (g: heap) (fp t: U64.t) (r: unit{room})
  : Lemma (let g0 = write_word g (at 0 r) (hdr 1 Header.Black) in
           let st = { cursor = at 0 r; swept_tail = t; last_fragment = 0UL } in
           can_sweep g0 st /\
           sweep_step g0 fp st ==
             (write_word g0 (at 0 r) (hdr 1 Header.White), fp,
              { cursor = at 2 r; swept_tail = t; last_fragment = 0UL }))
  = let g0 = write_word g (at 0 r) (hdr 1 Header.Black) in
    let st = { cursor = at 0 r; swept_tail = t; last_fragment = 0UL } in
    hdr_facts 1 Header.Black;
    read_write_same g (at 0 r) (hdr 1 Header.Black);
    assert (can_sweep g0 st);
    Step.step_eq_black g0 fp st;
    assert (Inv.white_header (hdr 1 Header.Black) == hdr 1 Header.White);
    assert (U64.uint_to_t (step_next g0 st) == at 2 r)
#pop-options
