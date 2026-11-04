/// ---------------------------------------------------------------------------
/// GC.Gen.Impl.UpdatePtrs — Rewrite roots after promotion
/// ---------------------------------------------------------------------------
///
/// Implements rewrite_roots: for each root that is a minor pointer with a
/// forwarding entry, replace it with the new major-heap address.

module GC.Gen.Impl.UpdatePtrs

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Gen.Base
open GC.Impl.Heap
open GC.Gen.RefTable
module PromoteSpec = GC.Gen.Promote
open GC.Gen.PromoteUpdate
module SpecHeap = GC.Spec.Heap
module AllocLemmas = GC.Spec.Allocator.Lemmas
open GC.Gen.ForwardingArray

/// ---------------------------------------------------------------------------
/// Rewrite one root at a given index (factored out for clean branch merging)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"
inline_for_extraction
fn rewrite_at_index (roots: array U64.t) (fwd_arr: array U64.t) (iv: SZ.t)
  requires pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pure (SZ.v iv < Seq.length 'rs /\
                 Seq.length 'farr == fwd_array_size)
  ensures exists* rs2.
    pts_to roots rs2 **
    pts_to fwd_arr 'farr **
    pure (rs2 == rewrite_at_spec 'rs 'farr (SZ.v iv))
{
  let r = roots.(iv);
  if U64.gte r 8UL {
    if U64.lt r minor_heap_size_u64 {
      if U64.eq (U64.rem r 8UL) 0UL {
        let idx = SZ.uint64_to_sizet (U64.div r 8UL);
        let fwd_val = fwd_arr.(idx);
        if U64.eq fwd_val 0UL {
          roots.(iv) <- r
        } else {
          roots.(iv) <- fwd_val
        }
      } else {
        roots.(iv) <- r
      }
    } else {
      roots.(iv) <- r
    }
  } else {
    roots.(iv) <- r
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// Rewrite roots loop
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"
inline_for_extraction
fn rewrite_roots_impl
  (roots: array U64.t)
  (fwd_arr: array U64.t)
  (n: SZ.t)
  (#fwd: erased PromoteSpec.forwarding_map)
  requires pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pure (SZ.v n == Seq.length 'rs /\
                 Seq.length 'farr == fwd_array_size /\
                 represents_fwd 'farr fwd)
  ensures exists* rs2.
    pts_to roots rs2 **
    pts_to fwd_arr 'farr **
    pure (Seq.length rs2 == Seq.length 'rs /\
          rs2 == PromoteSpec.rewrite_roots 'rs fwd)
{
  let mut i = 0sz;
  while (SZ.lt !i n)
    invariant exists* rs_i iv.
      pts_to roots rs_i **
      pts_to fwd_arr 'farr **
      R.pts_to i iv **
      pure (SZ.v iv <= Seq.length 'rs /\
            SZ.v n == Seq.length 'rs /\
            Seq.length rs_i == Seq.length 'rs /\
            Seq.length 'farr == fwd_array_size /\
            represents_fwd 'farr fwd /\
            (forall (j: nat). j < SZ.v iv ==>
              Seq.index rs_i j == PromoteSpec.rewrite_root (Seq.index 'rs j) fwd) /\
            (forall (j: nat). j >= SZ.v iv /\ j < Seq.length 'rs ==>
              Seq.index rs_i j == Seq.index 'rs j))
    decreases (SZ.v n - SZ.v !i)
  {
    let iv = !i;
    rewrite_at_index roots fwd_arr iv;
    rewrite_root_arr_spec 'farr fwd (Seq.index 'rs (SZ.v iv));
    i := SZ.add iv 1sz
  };
  // After loop: iv == n, so forall j < n. Seq.index rs_final j == rewrite_root ...
  // Bind the array witness and establish the connection
  with rs_final. assert (pts_to roots rs_final);
  assert (pure (Seq.length rs_final == Seq.length 'rs));
  assert (pure (forall (j: nat). j < Seq.length 'rs ==>
    Seq.index rs_final j == PromoteSpec.rewrite_root (Seq.index 'rs j) fwd));
  PromoteSpec.rewrite_roots_pointwise 'rs fwd rs_final;
  PromoteSpec.rewrite_roots_length 'rs fwd
}
#pop-options

/// ---------------------------------------------------------------------------
/// Update pointers in one object's fields
/// ---------------------------------------------------------------------------

module U8 = FStar.UInt8

/// Factored-out helper: handle one field in the pointer update loop.
/// Reads field, checks if minor pointer + forwarded, conditionally writes.
#push-options "--z3rlimit 25 --fuel 0 --ifuel 0"
inline_for_extraction
fn update_one_field (major: heap_t) (fwd_arr: array U64.t)
                    (obj: U64.t) (wosize: U64.t) (iv: U64.t)
                    (#fwd: erased PromoteSpec.forwarding_map)
  requires is_heap major 'ms **
           pts_to fwd_arr 'farr **
           pure (U64.v iv < U64.v wosize /\
                 U64.v obj >= 8 /\ U64.v obj % 8 == 0 /\
                 U64.v obj + U64.v wosize * 8 <= heap_size /\
                 U64.v wosize > 0 /\
                 Seq.length 'farr == fwd_array_size /\
                 represents_fwd 'farr fwd)
  ensures exists* ms2.
    is_heap major ms2 **
    pts_to fwd_arr 'farr **
    pure (PromoteSpec.update_object_pointers ms2 obj (U64.v wosize) fwd (U64.v iv + 1) ==
          PromoteSpec.update_object_pointers 'ms obj (U64.v wosize) fwd (U64.v iv))
{
  let field_addr_u64 = U64.add obj (U64.mul iv 8UL);
  let field_val_raw = read_word major field_addr_u64;
  let field_val = to_minor_offset_u64 field_val_raw;
  // Invoke the unfold lemma to establish the one-step equality
  PromoteSpec.update_object_pointers_step 'ms obj (U64.v wosize) fwd (U64.v iv);
  if U64.gte field_val 8UL {
    if U64.lt field_val minor_heap_size_u64 {
      if U64.eq (U64.rem field_val 8UL) 0UL {
        // Minor pointer — look up forwarding
        let idx = SZ.uint64_to_sizet (U64.div field_val 8UL);
        let fwd_val = fwd_arr.(idx);
        if U64.eq fwd_val 0UL {
          ()
        } else {
          write_word major field_addr_u64 fwd_val
        }
      } else {
        ()
      }
    } else {
      ()
    }
  } else {
    ()
  }
}
#pop-options

/// Update pointers in one object: iterate fields [0, wosize) and rewrite
/// minor-heap pointers via the forwarding array.
#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"
inline_for_extraction
fn update_one_object (major: heap_t) (fwd_arr: array U64.t)
                     (obj: U64.t) (wosize: U64.t)
                     (#fwd: erased PromoteSpec.forwarding_map)
  requires is_heap major 'ms **
           pts_to fwd_arr 'farr **
           pure (U64.v obj >= 8 /\ U64.v obj % 8 == 0 /\
                 U64.v obj + U64.v wosize * 8 <= heap_size /\
                 Seq.length 'farr == fwd_array_size /\
                 represents_fwd 'farr fwd)
  ensures exists* ms2.
    is_heap major ms2 **
    pts_to fwd_arr 'farr **
    pure (ms2 == PromoteSpec.update_object_pointers 'ms obj (U64.v wosize) fwd 0)
{
  let mut i = 0UL;
  while (U64.lt !i wosize)
    invariant exists* ms_i iv.
      is_heap major ms_i **
      pts_to fwd_arr 'farr **
      R.pts_to i iv **
      pure (U64.v iv <= U64.v wosize /\
            U64.v obj >= 8 /\ U64.v obj % 8 == 0 /\
            U64.v obj + U64.v wosize * 8 <= heap_size /\
            Seq.length 'farr == fwd_array_size /\
            represents_fwd 'farr fwd /\
            PromoteSpec.update_object_pointers ms_i obj (U64.v wosize) fwd (U64.v iv) ==
            PromoteSpec.update_object_pointers 'ms obj (U64.v wosize) fwd 0)
    decreases (U64.v wosize - U64.v !i)
  {
    let iv = !i;
    update_one_field major fwd_arr obj wosize iv #fwd;
    i := U64.add iv 1UL
  };
  // After loop: iv == wosize, so update_object_pointers ms_final ... wosize == ms_final
  with ms_final. assert (is_heap major ms_final);
  with iv_final. assert (R.pts_to i iv_final);
  PromoteSpec.update_object_pointers_done ms_final obj (U64.v wosize) fwd (U64.v iv_final);
  // Now we know:
  //   (1) update_object_pointers ms_final obj wosize fwd (v iv_final) == ms_final  [from done lemma]
  //   (2) update_object_pointers ms_final obj wosize fwd (v iv_final) == update_object_pointers 'ms obj wosize fwd 0  [from invariant]
  // Therefore ms_final == update_object_pointers 'ms obj wosize fwd 0
  assert (pure (ms_final == PromoteSpec.update_object_pointers 'ms obj (U64.v wosize) fwd 0))
}
#pop-options

/// ---------------------------------------------------------------------------
/// Rewrite heap slots (ref_table entries)
/// ---------------------------------------------------------------------------

/// Factored-out helper: handle one heap slot.
/// Reads from heap at the given address, checks if it's a forwarded minor
/// pointer, and rewrites if so.
#push-options "--z3rlimit 25 --fuel 0 --ifuel 0"
inline_for_extraction
fn rewrite_one_heap_slot
  (major: heap_t)
  (fwd_arr: array U64.t)
  (slot_addr: U64.t)
  (#fwd: erased PromoteSpec.forwarding_map)
  requires is_heap major 'ms **
           pts_to fwd_arr 'farr **
           pure (U64.v slot_addr < heap_size /\
                 U64.v slot_addr % 8 == 0 /\
                 Seq.length 'farr == fwd_array_size /\
                 represents_fwd 'farr fwd)
  ensures exists* ms2.
    is_heap major ms2 **
    pts_to fwd_arr 'farr **
    pure (ms2 == rewrite_one_slot_spec 'ms fwd slot_addr)
{
  let field_val_raw = read_word major slot_addr;
  let field_val = to_minor_offset_u64 field_val_raw;
  if U64.gte field_val 8UL {
    if U64.lt field_val minor_heap_size_u64 {
      if U64.eq (U64.rem field_val 8UL) 0UL {
        let idx = SZ.uint64_to_sizet (U64.div field_val 8UL);
        let fwd_val = fwd_arr.(idx);
        if not (U64.eq fwd_val 0UL) {
          write_word major slot_addr fwd_val
        }
      }
    }
  }
}
#pop-options

/// Rewrite heap slots loop
#push-options "--z3rlimit 25 --fuel 0 --ifuel 0"
fn rewrite_heap_slots
  (major: heap_t)
  (fwd_arr: array U64.t)
  (slots: array U64.t)
  (n: SZ.t)
  (#fwd: erased PromoteSpec.forwarding_map)
  requires is_heap major 'ms **
           pts_to fwd_arr 'farr **
           pts_to slots 'sl **
           pure (SZ.v n <= Seq.length 'sl /\
                 Seq.length 'farr == fwd_array_size /\
                 valid_slot_addrs 'sl (SZ.v n) /\
                 represents_fwd 'farr fwd)
  ensures exists* ms2.
    is_heap major ms2 **
    pts_to fwd_arr 'farr **
    pts_to slots 'sl **
    pure (ms2 == rewrite_slots_iter 'ms fwd 'sl (SZ.v n) 0)
{
  rewrite_slots_iter_done 'ms fwd 'sl 0 0;
  let mut i = 0sz;
  while (SZ.lt !i n)
    invariant exists* ms_i iv.
      is_heap major ms_i **
      pts_to fwd_arr 'farr **
      pts_to slots 'sl **
      R.pts_to i iv **
      pure (SZ.v iv <= SZ.v n /\
            SZ.v n <= Seq.length 'sl /\
            Seq.length 'farr == fwd_array_size /\
            valid_slot_addrs 'sl (SZ.v n) /\
            represents_fwd 'farr fwd /\
            ms_i == rewrite_slots_iter 'ms fwd 'sl (SZ.v iv) 0)
    decreases (SZ.v n - SZ.v !i)
  {
    let iv = !i;
    let slot_addr = slots.(iv);
    with ms_cur. assert (is_heap major ms_cur);
    rewrite_one_heap_slot major fwd_arr slot_addr #fwd;
    with ms_new. assert (is_heap major ms_new);
    // ms_new == rewrite_one_slot_spec ms_cur fwd slot_addr
    // ms_cur == rewrite_slots_iter 'ms fwd 'sl iv 0
    // By snoc lemma: rewrite_slots_iter 'ms fwd 'sl (iv+1) 0
    //   == rewrite_one_slot_spec (rewrite_slots_iter 'ms fwd 'sl iv 0) fwd 'sl[iv]
    //   == rewrite_one_slot_spec ms_cur fwd slot_addr == ms_new
    rewrite_slots_iter_snoc 'ms fwd 'sl (SZ.v iv) 0;
    i := SZ.add iv 1sz
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// Update promoted objects (fwd_arr iteration)
/// ---------------------------------------------------------------------------

module SpecObj = GC.Spec.Object
module SpecHeapM = GC.Spec.Heap

/// The main loop implementation
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
fn update_promoted_objects (major: heap_t) (fwd_arr: array U64.t)
                           (#fwd: erased PromoteSpec.forwarding_map)
  requires is_heap major 'ms **
           pts_to fwd_arr 'farr **
           pure (Seq.length 'farr == fwd_array_size /\
                 represents_fwd 'farr fwd /\
                 valid_fwd_entries 'farr)
  ensures exists* ms2.
    is_heap major ms2 **
    pts_to fwd_arr 'farr **
    pure (ms2 == update_promoted_iter 'ms 'farr fwd 0)
{
  let fwd_size = SZ.uint64_to_sizet (U64.div minor_heap_size_u64 8UL);
  let mut i = 0sz;
  while (SZ.lt !i fwd_size)
    invariant exists* ms_i iv.
      is_heap major ms_i **
      pts_to fwd_arr 'farr **
      R.pts_to i iv **
      pure (SZ.v iv <= fwd_array_size /\
            Seq.length 'farr == fwd_array_size /\
            represents_fwd 'farr fwd /\
            valid_fwd_entries 'farr /\
            update_promoted_iter ms_i 'farr fwd (SZ.v iv) ==
            update_promoted_iter 'ms 'farr fwd 0)
    decreases (SZ.v fwd_size - SZ.v !i)
  {
    let iv = !i;
    let major_addr = fwd_arr.(iv);
    with ms_cur. assert (is_heap major ms_cur);
    if U64.eq major_addr 0UL {
      // Zero entry — skip
      update_promoted_iter_zero ms_cur 'farr fwd (SZ.v iv);
      i := SZ.add iv 1sz
    } else {
      // Non-zero: read header
      let hdr_pos = U64.sub major_addr 8UL;
      hdr_addr_wf major_addr;
      let hdr = read_word major hdr_pos;
      let wosize = U64.shift_right hdr 10ul;
      SpecObj.getWosize_spec hdr;
      let tag = U64.logand hdr 0xFFUL;
      SpecObj.getTag_spec hdr;
      SpecObj.getTag_bound hdr;
      SpecObj.no_scan_tag_val ();
      SpecObj.infix_tag_val ();
      if U64.gt wosize 0UL {
        let is_scannable = U64.lt tag 251UL && not (U64.eq tag 249UL);
        if is_scannable {
          // Scannable non-infix promoted object with wosize > 0
          // Prove wosize * 8 doesn't overflow: wosize < 2^54, so wosize * 8 < 2^57 < 2^64
          SpecObj.getWosize_bound hdr;
          assert (pure (U64.v wosize < pow2 54));
          assert_norm (pow2 54 * 8 < pow2 64);
          FStar.Math.Lemmas.lemma_mult_le_right 8 (U64.v wosize) (pow2 54 - 1);
          // And major_addr + wosize*8 fits: major_addr <= heap_size < 2^57
          assert_norm (pow2 57 + pow2 54 * 8 < pow2 64);
          let body_end = U64.add major_addr (U64.mul wosize 8UL);
          if U64.lte body_end heap_size_u64 {
            // Body fits — call update_one_object
            // Help Z3 connect runtime values to spec preconditions
            assert (pure (U64.v major_addr >= 8 /\ U64.v major_addr % 8 == 0));
            assert (pure ((U64.v major_addr - 8) + 8 <= heap_size));
            assert (pure ((U64.v major_addr - 8) % 8 == 0));
            assert (pure (hdr == SpecHeapM.read_word ms_cur (U64.uint_to_t (U64.v major_addr - 8))));
            assert (pure (wosize == SpecObj.getWosize hdr));
            assert (pure (tag == SpecObj.getTag hdr));
            assert (pure (U64.v wosize > 0));
            assert (pure (U64.lt tag SpecObj.no_scan_tag));
            // Connect boolean U64.eq to propositional inequality
            assert (pure (U64.v tag <> U64.v SpecObj.infix_tag));
            assert (pure (U64.v major_addr + U64.v wosize * 8 <= heap_size));
            update_promoted_iter_scan ms_cur 'farr fwd (SZ.v iv);
            update_one_object major fwd_arr major_addr wosize #fwd;
            i := SZ.add iv 1sz
          } else {
            // Body overflow — skip (defensive)
            update_promoted_iter_skip ms_cur 'farr fwd (SZ.v iv);
            i := SZ.add iv 1sz
          }
        } else {
          // tag >= no_scan_tag OR tag == infix_tag — skip
          update_promoted_iter_skip ms_cur 'farr fwd (SZ.v iv);
          i := SZ.add iv 1sz
        }
      } else {
        // wosize == 0 — skip
        update_promoted_iter_skip ms_cur 'farr fwd (SZ.v iv);
        i := SZ.add iv 1sz
      }
    }
  };
  // After loop: iv == fwd_array_size
  with ms_final. assert (is_heap major ms_final);
  with iv_final. assert (R.pts_to i iv_final);
  update_promoted_iter_done ms_final 'farr fwd (SZ.v iv_final)
}
#pop-options
