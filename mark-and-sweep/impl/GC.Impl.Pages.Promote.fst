/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.Promote - promoting one nursery object with the page allocator
/// ---------------------------------------------------------------------------
///
/// Plan §30.  akhil's `GC.Gen.Impl.Promote.promote_one` allocates the copy
/// from his free list (`GC.Impl.Allocator.allocate`).  This one allocates it
/// with the tagged page allocator of the phase (`AllocInc.alloc_ph`), for any
/// allocator `a` of the promotion's contract that is the page allocator of
/// that phase (`Promote.Sim.at_phase`), and computes exactly the model's
/// `Promote.promote_object a`.
///
/// The nursery readers and the field copy are akhil's
/// (`GC.Gen.Impl.Promote`), copied: his module also holds his allocator's
/// promotion, which the page allocator's C must not take in.

module GC.Impl.Pages.Promote

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Impl.MinorHeap
open GC.Impl.Heap
open GC.Spec.Pages.Inv
open GC.Impl.Pages.State
open GC.Gen.Promote
open GC.Spec.Pages.Promote

module R = Pulse.Lib.Reference
module U64 = FStar.UInt64
module I = GC.Spec.AllocIface
module AT = GC.Spec.Pages.AllocTag
module WBL = GC.Gen.WriteBodyLemmas
module Sim = GC.Spec.Pages.Promote.Sim
module AI = GC.Impl.Pages.AllocInc

/// ---------------------------------------------------------------------------
/// Reading a nursery header (akhil's)
/// ---------------------------------------------------------------------------

inline_for_extraction
fn read_minor_wosize (minor: minor_heap_t) (obj: U64.t)
  requires is_minor minor 'md 'mb **
           pure (U64.v obj >= 8 /\ U64.v obj < minor_heap_size /\ U64.v obj % 8 == 0)
  returns wosize: U64.t
  ensures is_minor minor 'md 'mb **
          pure (U64.v wosize == minor_wosize {data='md; bump='mb} obj)
{
  let hdr = minor_read minor (U64.sub obj 8UL);
  U64.shift_right hdr 10ul
}

inline_for_extraction
fn read_minor_tag (minor: minor_heap_t) (obj: U64.t)
  requires is_minor minor 'md 'mb **
           pure (U64.v obj >= 8 /\ U64.v obj < minor_heap_size /\ U64.v obj % 8 == 0)
  returns tag: U64.t
  ensures is_minor minor 'md 'mb **
          pure (U64.v tag == minor_tag {data='md; bump='mb} obj)
{
  let hdr = minor_read minor (U64.sub obj 8UL);
  U64.logand hdr 0xFFUL
}

/// The fields the collector scans: none in a no-scan object (tag >= 251).
inline_for_extraction
fn read_minor_scan_wosize (minor: minor_heap_t) (obj: U64.t)
  requires is_minor minor 'md 'mb **
           pure (U64.v obj >= 8 /\ U64.v obj < minor_heap_size /\ U64.v obj % 8 == 0)
  returns wosize: U64.t
  ensures is_minor minor 'md 'mb **
          pure (U64.v wosize == minor_scan_wosize {data='md; bump='mb} obj)
{
  let tag = read_minor_tag minor obj;
  if (U64.gte tag 251UL) { 0UL } else { read_minor_wosize minor obj }
}

/// ---------------------------------------------------------------------------
/// Copying the fields (akhil's)
/// ---------------------------------------------------------------------------

let field_in_bounds (limit obj_addr wosize jv: nat)
  : Lemma (requires limit < pow2 57 /\ obj_addr + wosize * 8 <= limit /\ obj_addr % 8 == 0 /\ jv < wosize)
          (ensures jv * 8 < pow2 64 /\ obj_addr + jv * 8 < pow2 64 /\ obj_addr + jv * 8 + 8 <= limit /\
                   (obj_addr + jv * 8) % 8 == 0 /\ jv + 1 < pow2 64)
  = FStar.Math.Lemmas.lemma_mult_le_right 8 (jv + 1) wosize;
    assert_norm (pow2 57 < pow2 64);
    FStar.Math.Lemmas.cancel_mul_mod jv 8;
    FStar.Math.Lemmas.modulo_addition_lemma obj_addr 8 jv

inline_for_extraction
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
fn copy_fields_loop (minor: minor_heap_t) (major: heap_t) (src_obj: U64.t) (dst_obj: U64.t) (wosize: U64.t)
  requires is_minor minor 'md 'mb **
           is_heap major 'ms **
           pure (U64.v src_obj >= 8 /\ U64.v src_obj % 8 == 0 /\
                 U64.v src_obj + U64.v wosize * 8 <= minor_heap_size /\
                 U64.v dst_obj >= 8 /\ U64.v dst_obj % 8 == 0 /\
                 U64.v dst_obj + U64.v wosize * 8 <= heap_size /\
                 U64.v wosize > 0)
  ensures exists* ms2. is_minor minor 'md 'mb ** is_heap major ms2 **
          pure (ms2 == WBL.copy_fields {data='md; bump='mb} 'ms src_obj dst_obj 0 (U64.v wosize))
{
  let mut i = 0UL;
  while (U64.lt !i wosize)
    invariant exists* ms_i iv.
      is_minor minor 'md 'mb **
      is_heap major ms_i **
      R.pts_to i iv **
      pure (U64.v iv <= U64.v wosize /\
            WBL.copy_fields {data='md; bump='mb} ms_i src_obj dst_obj (U64.v iv) (U64.v wosize) ==
            WBL.copy_fields {data='md; bump='mb} 'ms src_obj dst_obj 0 (U64.v wosize))
    decreases (U64.v wosize - U64.v !i)
  {
    let iv = !i;
    field_in_bounds minor_heap_size (U64.v src_obj) (U64.v wosize) (U64.v iv);
    field_in_bounds heap_size (U64.v dst_obj) (U64.v wosize) (U64.v iv);
    let src_addr = U64.add src_obj (U64.mul iv 8UL);
    let field_val = minor_read minor src_addr;
    let dst_addr = U64.add dst_obj (U64.mul iv 8UL);
    assert (pure (U64.v iv < U64.v wosize /\
                  U64.v dst_obj + U64.v iv * 8 + 8 <= heap_size /\
                  (U64.v dst_obj + U64.v iv * 8) % 8 == 0 /\
                  U64.v dst_addr == U64.v dst_obj + U64.v iv * 8 /\
                  U64.v src_addr == U64.v src_obj + U64.v iv * 8));
    write_word major dst_addr field_val;
    i := U64.add iv 1UL
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// Promoting one object
/// ---------------------------------------------------------------------------

/// The tag of a nursery object is the tag its copy takes.
let tag_is_promoted (ms: minor_state) (obj: U64.t) (tag: U64.t)
  : Lemma (requires U64.v tag == minor_tag ms obj)
          (ensures U64.v tag < 256 /\ tag == promoted_tag ms obj)
  = minor_tag_bound ms obj

/// **Promote `obj`** (of `wz > 0` words, not infix) with the allocator `a`
/// of phase `ph`: exactly `promote_object a`.  Returns the copy, or 0 if
/// the allocation failed, in which case nothing changed.
#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
fn promote_one (minor: minor_heap_t) (major: heap_t) (t: pstate_t) (marking: bool) (obj: U64.t) (wz: U64.t{U64.v wz > 0})
  (#a: erased (tal pstate)) (#ph: erased I.phase) (#st: erased pstate)
  requires is_minor minor 'md 'mb ** is_heap major 'g ** pages_st t st **
           pure (Sim.at_phase a ph /\ marking == I.Marking? ph /\ a.inv 'g st /\
                 U64.v obj >= 8 /\ U64.v obj < minor_heap_size /\ U64.v obj % 8 == 0 /\
                 U64.v wz == minor_wosize {data='md; bump='mb} obj /\ U64.v wz > 0 /\
                 U64.v obj + U64.v wz * 8 <= minor_heap_size /\
                 minor_tag {data='md; bump='mb} obj <> 249)
  returns o: U64.t
  ensures exists* g' st'. is_minor minor 'md 'mb ** is_heap major g' ** pages_st t st' **
          pure ((g', st', o) == promote_object a {data='md; bump='mb} 'g obj st (U64.v wz))
{
  let tag = read_minor_tag minor obj;
  tag_is_promoted {data='md; bump='mb} obj tag;
  Sim.at_phase_inv a ph 'g st;
  Sim.at_phase_contract a ph;
  Sim.at_phase_alloc a ph 'g st (U64.v wz) tag;
  Sim.alloc_room a 'g st (U64.v wz) tag;
  let o = AI.alloc_ph major t wz tag marking #ph #st;
  with g1 st1. assert (is_heap major g1 ** pages_st t st1);
  if (U64.eq o 0UL) {
    o
  } else {
    copy_fields_loop minor major obj o wz;
    o
  }
}
#pop-options
